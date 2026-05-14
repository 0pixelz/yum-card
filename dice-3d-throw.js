// 3D dice throw overlay — drag-and-flick gesture, Three.js + cannon-es.
// Exposes window.throw3DDie() → Promise<1-6>. Falls back to random on failure.
// Also exposes window.throw3DDice(count) → Promise<number[]> for auto-tossing
// several smaller dice at once (used by the in-game roll button when the
// "Roll dice in 3D" preference is enabled).
(function () {
  'use strict';

  let THREE, CANNON;
  let scene, camera, renderer;
  let world, dieBody, dieMesh, floorMesh;
  let floorPMat = null, diePMat = null;
  let overlay, canvasEl, statusEl, cancelBtn;
  let rafId = null;
  let lastTime = 0;
  let resolveFn = null;
  let dragging = false;
  let throwing = false;
  let pointerSamples = [];
  let lastDragP = null; // previous pointer (x,z) on the drag plane, for tumble-on-drag
  let settleStart = 0;
  let dragPlane;
  let raycaster;
  let pickOffset = { x: 0, z: 0 };

  // ── Multi-die mode state ─────────────────────────────────────────
  // 'single' = drag-and-flick one die (who-goes-first). 'multi' = flick-throw
  // N smaller dice all at once (Pokémon-GO-style swipe). 'spectator' =
  // non-interactive playback of an opponent's throw — meshes are posed from
  // network-streamed transforms, no physics drives them.
  let mode = 'single';
  let _onFrameCb = null, _onOpenCb = null, _onCloseCb = null;
  let _onSpectatorHideCb = null;
  let multiDiceBodies = [];
  let multiDiceMeshes = [];
  let multiThrowing = false;
  let multiReady = false;          // dice are parked, awaiting a flick
  let multiDragging = false;
  let multiPointerSamples = [];
  let multiSettleStart = 0;
  let multiResolve = null;
  let multiGeom = null;
  let multiMats = null;
  let multiLanes = [];             // pre-computed {dx,dz} fan offsets per die
  let multiLastDragP = null;

  // BoxGeometry material order: [+X, -X, +Y, -Y, +Z, -Z]
  // Standard die: opposite faces sum to 7.
  const FACE_NUMBERS = [1, 6, 2, 5, 3, 4];
  const FACE_KEYS    = ['+X','-X','+Y','-Y','+Z','-Z'];

  const DIE_SIZE = 1.0;
  const DIE_BEVEL = DIE_SIZE * 0.13; // corner/edge radius — gives a soft "casino die" silhouette
  const FLOOR_Y = 0;
  const DRAG_Y = DIE_SIZE; // hover height while dragging

  // Play-area bounds — sized so the die always stays inside the camera's
  // visible footprint on the floor (see initScene for camera/FOV).
  const WALL_FRONT =  2.6;   // wall closest to camera (max +Z)
  const WALL_BACK  = -5.0;   // wall farthest from camera (min -Z)
  const WALL_SIDE  =  2.4;   // ±X side walls
  const DIE_HALF   =  DIE_SIZE / 2;
  // Pointer-drag bounds: keep the die center safely inside the walls.
  const DRAG_X_LIMIT = WALL_SIDE  - DIE_HALF - 0.05;
  const DRAG_Z_MIN   = WALL_BACK  + DIE_HALF + 0.05;
  const DRAG_Z_MAX   = WALL_FRONT - DIE_HALF - 0.05;
  const clamp = (v, lo, hi) => v < lo ? lo : (v > hi ? hi : v);

  // ── Sound effects ────────────────────────────────────────────────
  // Reuses the global `soundEnabled` flag and yumSound localStorage key set in
  // app.js so the dice overlay obeys the same mute toggle as the rest of the app.
  let _diceAudioCtx = null;
  let _lastTapTime = 0;
  function diceCtx() {
    if (_diceAudioCtx) return _diceAudioCtx;
    const AC = window.AudioContext || window.webkitAudioContext;
    if (!AC) return null;
    _diceAudioCtx = new AC();
    return _diceAudioCtx;
  }
  function soundOn() {
    if (typeof window.soundEnabled === 'boolean') return window.soundEnabled;
    return localStorage.getItem('yumSound') !== 'off';
  }
  function playThrowClatter() {
    if (!soundOn()) return;
    if (typeof SFX !== 'undefined' && typeof SFX.roll === 'function') { SFX.roll(); return; }
    // Fallback if SFX isn't loaded yet
    const ctx = diceCtx(); if (!ctx) return;
    const now = ctx.currentTime;
    for (let i = 0; i < 4; i++) {
      const t = now + i * 0.05;
      const osc = ctx.createOscillator(), g = ctx.createGain();
      osc.type = 'sawtooth';
      osc.frequency.setValueAtTime(180 + Math.random() * 120, t);
      g.gain.setValueAtTime(0.15, t);
      g.gain.exponentialRampToValueAtTime(0.0001, t + 0.07);
      osc.connect(g); g.connect(ctx.destination);
      osc.start(t); osc.stop(t + 0.08);
    }
  }
  function playImpactTap(speed) {
    if (!soundOn()) return;
    const ctx = diceCtx(); if (!ctx) return;
    const now = ctx.currentTime;
    // Throttle so a single step with multiple contact points doesn't stack.
    if (now - _lastTapTime < 0.035) return;
    _lastTapTime = now;
    const vol = Math.min(0.22, 0.05 + speed * 0.018);
    const baseFreq = 160 + Math.random() * 90;
    const osc = ctx.createOscillator(), g = ctx.createGain();
    osc.type = 'square';
    osc.frequency.setValueAtTime(baseFreq, now);
    osc.frequency.exponentialRampToValueAtTime(baseFreq * 0.5, now + 0.06);
    g.gain.setValueAtTime(vol, now);
    g.gain.exponentialRampToValueAtTime(0.0001, now + 0.08);
    osc.connect(g); g.connect(ctx.destination);
    osc.start(now); osc.stop(now + 0.09);
  }

  function roundRect(ctx, x, y, w, h, r) {
    ctx.beginPath();
    ctx.moveTo(x + r, y);
    ctx.arcTo(x + w, y,     x + w, y + h, r);
    ctx.arcTo(x + w, y + h, x,     y + h, r);
    ctx.arcTo(x,     y + h, x,     y,     r);
    ctx.arcTo(x,     y,     x + w, y,     r);
    ctx.closePath();
  }

  // Yamio brand palette (mirrors :root vars in css/style.css)
  const BRAND = {
    bg:     '#1a1a2e',
    card:   '#16213e',
    panel:  '#0f3460',
    accent: '#e94560',
    gold:   '#f5a623',
    green:  '#4ecdc4',
    white:  '#f0f0f0'
  };

  // The 3D die's faces are styled after the brand dice mark (#yum-mark):
  // warm gold radial face with dark-brown pips. The canvas is filled edge to
  // edge so the rounded corners of the geometry show face color too.
  function makeFaceTexture(num) {
    const S = 512;
    const c = document.createElement('canvas');
    c.width = S; c.height = S;
    const ctx = c.getContext('2d');

    // Saturated orange face — punchier than the SVG brand mark so the die
    // doesn't average down to beige at game scale.
    const faceGrad = ctx.createRadialGradient(S * 0.32, S * 0.28, 16, S * 0.5, S * 0.5, S * 0.95);
    faceGrad.addColorStop(0,    '#ffd49a');
    faceGrad.addColorStop(0.32, '#ffa84a');
    faceGrad.addColorStop(0.72, '#ef7a12');
    faceGrad.addColorStop(1,    '#a8480a');
    ctx.fillStyle = faceGrad;
    ctx.fillRect(0, 0, S, S);

    // Soft inset border — looks like the bevel edge from the brand mark
    ctx.strokeStyle = 'rgba(70,30,5,0.55)';
    ctx.lineWidth = 10;
    ctx.strokeRect(28, 28, S - 56, S - 56);
    ctx.strokeStyle = 'rgba(255,210,138,0.45)';
    ctx.lineWidth = 3;
    ctx.strokeRect(40, 40, S - 80, S - 80);

    // Dark-brown pips (match the brand mark color, larger radius for the higher-res canvas)
    const pip = (x, y) => {
      // soft drop shadow beneath the pip for depth
      const sh = ctx.createRadialGradient(x, y + 4, 8, x, y + 6, 56);
      sh.addColorStop(0, 'rgba(58,26,5,0.45)');
      sh.addColorStop(1, 'rgba(58,26,5,0)');
      ctx.fillStyle = sh;
      ctx.beginPath(); ctx.arc(x, y + 4, 56, 0, Math.PI * 2); ctx.fill();
      // pip — slight gradient for a recessed look
      const pg = ctx.createRadialGradient(x - 14, y - 14, 4, x, y, 44);
      pg.addColorStop(0,    '#5a2a08');
      pg.addColorStop(0.5,  '#3a1a05');
      pg.addColorStop(1,    '#1a0a02');
      ctx.fillStyle = pg;
      ctx.beginPath(); ctx.arc(x, y, 44, 0, Math.PI * 2); ctx.fill();
      // small specular highlight
      ctx.fillStyle = 'rgba(255,210,138,0.34)';
      ctx.beginPath(); ctx.arc(x - 14, y - 14, 8, 0, Math.PI * 2); ctx.fill();
    };
    // Standard pip positions, scaled from 256→512 (×2)
    const P = {
      1: [[256,256]],
      2: [[152,152],[360,360]],
      3: [[144,144],[256,256],[368,368]],
      4: [[152,152],[360,152],[152,360],[360,360]],
      5: [[144,144],[368,144],[256,256],[144,368],[368,368]],
      6: [[152,136],[360,136],[152,256],[360,256],[152,376],[360,376]]
    };
    P[num].forEach(([x, y]) => pip(x, y));

    const tex = new THREE.CanvasTexture(c);
    tex.anisotropy = 16;
    return tex;
  }

  // Build a rounded-box geometry: start from a segmented BoxGeometry, then
  // push each vertex outward from the inner box (the cube shrunk by `radius`)
  // along the offset direction so the corners and edges become spherical.
  function makeRoundedBoxGeometry(size, radius, segs) {
    const half = size / 2;
    const inner = half - radius;
    const geo = new THREE.BoxGeometry(size, size, size, segs, segs, segs);
    const pos = geo.attributes.position;
    for (let i = 0; i < pos.count; i++) {
      const x = pos.getX(i), y = pos.getY(i), z = pos.getZ(i);
      // nearest point on the inner cube
      const cx = Math.max(-inner, Math.min(inner, x));
      const cy = Math.max(-inner, Math.min(inner, y));
      const cz = Math.max(-inner, Math.min(inner, z));
      const dx = x - cx, dy = y - cy, dz = z - cz;
      const len = Math.hypot(dx, dy, dz);
      if (len > 1e-4) {
        const k = radius / len;
        pos.setXYZ(i, cx + dx * k, cy + dy * k, cz + dz * k);
      }
    }
    geo.computeVertexNormals();
    return geo;
  }

  // Draws the Yamio brand dice mark (matches the #yum-mark SVG in index.html).
  // Origin = top-left of the mark, size = side length on the canvas.
  function drawYamioMark(ctx, x, y, size) {
    const s = size / 64; // viewBox is 64x64
    ctx.save();
    ctx.translate(x, y);
    ctx.scale(s, s);

    // Warm orange radial glow behind the dice
    const glow = ctx.createRadialGradient(32, 32, 4, 32, 32, 30);
    glow.addColorStop(0, 'rgba(255,140,30,0.7)');
    glow.addColorStop(1, 'rgba(255,140,30,0)');
    ctx.fillStyle = glow;
    ctx.beginPath(); ctx.arc(32, 32, 30, 0, Math.PI * 2); ctx.fill();

    // Drop-shadow ellipse beneath
    ctx.fillStyle = 'rgba(0,0,0,0.35)';
    ctx.beginPath(); ctx.ellipse(32, 58, 22, 3.5, 0, 0, Math.PI * 2); ctx.fill();

    // Rounded-square die face — saturated orange so the small mark reads
    // as "orange" on the floor instead of washing out to beige.
    const dieFace = ctx.createRadialGradient(
      10 + 44 * 0.32, 8 + 44 * 0.28, 2,
      10 + 44 * 0.32, 8 + 44 * 0.28, 44 * 0.95
    );
    dieFace.addColorStop(0,    '#ffd49a');
    dieFace.addColorStop(0.32, '#ffa84a');
    dieFace.addColorStop(0.72, '#ef7a12');
    dieFace.addColorStop(1,    '#a8480a');
    ctx.fillStyle = dieFace;
    roundRect(ctx, 10, 8, 44, 44, 9);
    ctx.fill();
    ctx.strokeStyle = '#4a1f04';
    ctx.lineWidth = 1.4;
    ctx.stroke();

    // 6 pips arranged 2 cols × 3 rows
    ctx.fillStyle = '#3a1a05';
    const pips = [[21,19],[43,19],[21,30],[43,30],[21,41],[43,41]];
    for (const [px, py] of pips) {
      ctx.beginPath(); ctx.arc(px, py, 2.9, 0, Math.PI * 2); ctx.fill();
    }
    ctx.restore();
  }

  function makeFloorTexture() {
    // 4K canvas — high enough that the YAMIO wordmark stays crisp even when the
    // camera dollies in and views the floor at an angle.
    const S = 4096;
    const c = document.createElement('canvas');
    c.width = S; c.height = S;
    const ctx = c.getContext('2d');

    // Very dark blue background — matches the main lobby (almost black with a
    // faint navy lift in the upper center).
    const g = ctx.createRadialGradient(S/2, S * 0.40, 80, S/2, S * 0.55, S * 0.72);
    g.addColorStop(0,    '#10132e');
    g.addColorStop(0.55, '#0a0c1f');
    g.addColorStop(1,    '#05061a');
    ctx.fillStyle = g;
    ctx.fillRect(0, 0, S, S);

    // Subtle gold accent ring under the throw area
    ctx.strokeStyle = 'rgba(245,166,35,0.15)';
    ctx.lineWidth = 10;
    ctx.beginPath(); ctx.arc(S/2, S * 0.58, S * 0.34, 0, Math.PI * 2); ctx.stroke();

    // ── Yamio brand logo (dice mark + wordmark, like the main lobby) ──
    const text = 'YAMIO';
    const fontSize = 280;
    const letterSpacing = fontSize * 0.18;            // matches CSS letter-spacing
    ctx.font = `900 ${fontSize}px 'Bebas Neue', 'Impact', 'Arial Narrow', sans-serif`;
    ctx.textBaseline = 'middle';
    ctx.textAlign = 'left';

    const widths = text.split('').map(ch => ctx.measureText(ch).width);
    const wordW = widths.reduce((a, b) => a + b, 0) + letterSpacing * (text.length - 1);
    const markSize = fontSize * 1.25;                 // .yum-brand-mark ≈ 1.15em + extra room
    const gap = fontSize * 0.35;                      // .yum-brand-logo gap = 0.4em
    const totalW = markSize + gap + wordW;
    const cy = S * 0.46;                              // mid-floor, around the camera's lookAt — sits visually centered on screen
    const logoX = (S - totalW) / 2;

    // Dice mark on the left
    drawYamioMark(ctx, logoX, cy - markSize / 2, markSize);

    // Wordmark "YAMIO" — orange-biased gold→red gradient. We hold the
    // saturated orange across most of the word and only roll into red at
    // the very end so the wordmark reads "orange" overall on the floor,
    // matching the lobby header's vivid look.
    const wordX = logoX + markSize + gap;
    const wordGrad = ctx.createLinearGradient(
      wordX, cy - fontSize * 0.5,
      wordX + wordW, cy + fontSize * 0.5
    );
    wordGrad.addColorStop(0,    '#ffb347');
    wordGrad.addColorStop(0.55, '#f5871a');
    wordGrad.addColorStop(1,    BRAND.accent);

    // Warm orange glow pass under the letters — tighter blur so the
    // saturated color isn't diluted into a beige halo.
    ctx.save();
    ctx.shadowColor = 'rgba(239,122,18,0.55)';
    ctx.shadowBlur = 36;
    ctx.fillStyle = wordGrad;
    let x = wordX;
    for (let i = 0; i < text.length; i++) {
      ctx.fillText(text[i], x, cy);
      x += widths[i] + letterSpacing;
    }
    ctx.restore();

    // Two crisp gradient passes for extra punch (no shadow)
    ctx.fillStyle = wordGrad;
    for (let pass = 0; pass < 2; pass++) {
      x = wordX;
      for (let i = 0; i < text.length; i++) {
        ctx.fillText(text[i], x, cy);
        x += widths[i] + letterSpacing;
      }
    }
    // Dark outline so the letters pop against the very dark floor
    ctx.strokeStyle = 'rgba(0,0,0,0.6)';
    ctx.lineWidth = 4;
    x = wordX;
    for (let i = 0; i < text.length; i++) {
      ctx.strokeText(text[i], x, cy);
      x += widths[i] + letterSpacing;
    }

    const tex = new THREE.CanvasTexture(c);
    tex.anisotropy = 16;
    return tex;
  }

  // Resolves once 'Bebas Neue' is loaded (or after a short timeout) so the
  // floor texture is painted with the brand font, not the fallback.
  function ensureBrandFont() {
    if (!document.fonts || !document.fonts.load) return Promise.resolve();
    return Promise.race([
      document.fonts.load("700 64px 'Bebas Neue'").catch(() => null),
      new Promise(res => setTimeout(res, 1200))
    ]);
  }

  function buildOverlay() {
    overlay = document.createElement('div');
    overlay.id = 'dice3dOverlay';
    overlay.innerHTML =
      '<div class="d3d-title">YAMIO</div>' +
      '<div class="d3d-canvas-wrap"><canvas id="dice3dCanvas"></canvas></div>' +
      '<div class="d3d-status" id="dice3dStatus">Drag the dice and flick to throw</div>' +
      '<button class="d3d-cancel" id="dice3dCancel">Skip throw</button>';
    document.body.appendChild(overlay);
    canvasEl = overlay.querySelector('#dice3dCanvas');
    statusEl = overlay.querySelector('#dice3dStatus');
    cancelBtn = overlay.querySelector('#dice3dCancel');
    cancelBtn.addEventListener('click', () => {
      if (mode === 'spectator') {
        // "Hide" the live view of an opponent's roll — purely local; the
        // roll continues on their side and the regular post-roll dice update
        // will appear in the roller card via the existing liveDice channel.
        if (_onSpectatorHideCb) { try { _onSpectatorHideCb(); } catch (_) {} }
        closeOverlay();
        return;
      }
      if (multiResolve) {
        const r = multiResolve; multiResolve = null;
        const n = multiDiceBodies.length || 5;
        const arr = [];
        for (let i = 0; i < n; i++) arr.push(Math.floor(Math.random() * 6) + 1);
        closeOverlay();
        r(arr);
        return;
      }
      if (!resolveFn) return;
      const r = resolveFn; resolveFn = null;
      closeOverlay();
      r(Math.floor(Math.random() * 6) + 1);
    });
  }

  function initScene() {
    scene = new THREE.Scene();
    // Very dark navy — matches the main lobby background
    scene.fog = new THREE.Fog(0x08091a, 12, 26);
    scene.background = new THREE.Color(0x0d0f24);

    const w = canvasEl.clientWidth || 1;
    const h = canvasEl.clientHeight || 1;
    // Slightly wider FOV than before (50°) so the camera covers the full
    // walled play area even on portrait phones.
    camera = new THREE.PerspectiveCamera(50, w / h, 0.1, 100);
    camera.position.set(0, 7.5, 7);
    camera.lookAt(0, 0.2, -1.3);

    renderer = new THREE.WebGLRenderer({ canvas: canvasEl, antialias: true, alpha: true });
    renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
    renderer.setSize(w, h, false);
    renderer.shadowMap.enabled = true;
    renderer.shadowMap.type = THREE.PCFSoftShadowMap;
    renderer.outputColorSpace = THREE.SRGBColorSpace;

    scene.add(new THREE.AmbientLight(0xffffff, 0.55));
    const key = new THREE.DirectionalLight(0xffffff, 1.15);
    key.position.set(4, 9, 6);
    key.castShadow = true;
    key.shadow.mapSize.set(1024, 1024);
    const s = 5;
    key.shadow.camera.left = -s; key.shadow.camera.right = s;
    key.shadow.camera.top = s;   key.shadow.camera.bottom = -s;
    key.shadow.camera.near = 1;  key.shadow.camera.far = 25;
    scene.add(key);
    // Warm gold rim light + teal fill — matches brand accents
    const rim = new THREE.DirectionalLight(0xf5a623, 0.45);
    rim.position.set(-5, 4, -3);
    scene.add(rim);
    const fill = new THREE.DirectionalLight(0x4ecdc4, 0.18);
    fill.position.set(3, 2, -6);
    scene.add(fill);

    // Branded floor: dark navy + the Yamio main-screen logo baked into the texture
    const floorTex = makeFloorTexture();
    const floorMat = new THREE.MeshStandardMaterial({
      map: floorTex, roughness: 0.88, metalness: 0.04
    });
    floorMesh = new THREE.Mesh(new THREE.PlaneGeometry(16, 16), floorMat);
    floorMesh.rotation.x = -Math.PI / 2;
    floorMesh.receiveShadow = true;
    scene.add(floorMesh);

    // Outer near-black surround so the play area sits in deep darkness
    const surroundMat = new THREE.MeshStandardMaterial({
      color: 0x07081a, roughness: 0.98, metalness: 0.0
    });
    const surround = new THREE.Mesh(new THREE.PlaneGeometry(60, 60), surroundMat);
    surround.rotation.x = -Math.PI / 2;
    surround.position.y = -0.02;
    surround.receiveShadow = true;
    scene.add(surround);

    const geo = makeRoundedBoxGeometry(DIE_SIZE, DIE_BEVEL, 6);
    const mats = FACE_NUMBERS.map(n => new THREE.MeshStandardMaterial({
      map: makeFaceTexture(n),
      roughness: 0.28,
      metalness: 0.12,
      color: 0xffffff
    }));
    dieMesh = new THREE.Mesh(geo, mats);
    dieMesh.castShadow = true;
    scene.add(dieMesh);

    world = new CANNON.World({ gravity: new CANNON.Vec3(0, -32, 0) });
    world.allowSleep = true;
    world.broadphase = new CANNON.NaiveBroadphase();

    floorPMat = new CANNON.Material('floor');
    diePMat = new CANNON.Material('die');
    world.addContactMaterial(new CANNON.ContactMaterial(floorPMat, diePMat, {
      friction: 0.45, restitution: 0.32
    }));
    world.addContactMaterial(new CANNON.ContactMaterial(diePMat, diePMat, {
      friction: 0.2, restitution: 0.2
    }));

    const floorBody = new CANNON.Body({ mass: 0, shape: new CANNON.Plane(), material: floorPMat });
    floorBody.quaternion.setFromEuler(-Math.PI / 2, 0, 0);
    world.addBody(floorBody);

    // Invisible walls — keep die in the camera-visible play area.
    const walls = [
      { p: [0, 0, WALL_BACK],   r: [0, 0, 0] },
      { p: [0, 0, WALL_FRONT],  r: [0, Math.PI, 0] },
      { p: [-WALL_SIDE, 0, 0],  r: [0,  Math.PI / 2, 0] },
      { p: [ WALL_SIDE, 0, 0],  r: [0, -Math.PI / 2, 0] }
    ];
    walls.forEach(d => {
      const b = new CANNON.Body({ mass: 0, shape: new CANNON.Plane(), material: floorPMat });
      b.position.set(d.p[0], d.p[1], d.p[2]);
      b.quaternion.setFromEuler(d.r[0], d.r[1], d.r[2]);
      world.addBody(b);
    });

    dieBody = new CANNON.Body({
      mass: 1.2,
      shape: new CANNON.Box(new CANNON.Vec3(DIE_SIZE / 2, DIE_SIZE / 2, DIE_SIZE / 2)),
      material: diePMat,
      allowSleep: true,
      sleepSpeedLimit: 0.14,
      sleepTimeLimit: 0.45,
      linearDamping: 0.16,
      angularDamping: 0.16
    });
    world.addBody(dieBody);

    // Tap sound on each meaningful bounce while the throw is in flight.
    dieBody.addEventListener('collide', (e) => {
      if (!throwing) return;
      const c = e && e.contact;
      const v = c && typeof c.getImpactVelocityAlongNormal === 'function'
        ? Math.abs(c.getImpactVelocityAlongNormal())
        : 0;
      if (v >= 1.4) playImpactTap(v);
    });

    dragPlane = new THREE.Plane(new THREE.Vector3(0, 1, 0), -DRAG_Y);
    raycaster = new THREE.Raycaster();
  }

  function resetDie() {
    dieBody.type = CANNON.Body.DYNAMIC;
    dieBody.position.set(0, 0.9, DRAG_Z_MAX - 0.4);
    dieBody.velocity.set(0, 0, 0);
    dieBody.angularVelocity.set(0, 0, 0);
    dieBody.quaternion.setFromEuler(
      Math.random() * 0.5, Math.random() * 0.5, Math.random() * 0.5
    );
    dieBody.wakeUp();
  }

  function onResize() {
    if (!renderer) return;
    const w = canvasEl.clientWidth || 1;
    const h = canvasEl.clientHeight || 1;
    camera.aspect = w / h;
    camera.updateProjectionMatrix();
    renderer.setSize(w, h, false);
  }

  function pointerNDC(ev) {
    const rect = canvasEl.getBoundingClientRect();
    return {
      x: ((ev.clientX - rect.left) / rect.width) * 2 - 1,
      y: -((ev.clientY - rect.top) / rect.height) * 2 + 1
    };
  }

  function pointerOnDragPlane(ev) {
    const ndc = pointerNDC(ev);
    raycaster.setFromCamera(ndc, camera);
    const hit = new THREE.Vector3();
    if (!raycaster.ray.intersectPlane(dragPlane, hit)) return null;
    return hit;
  }

  function hitTestDie(ev) {
    const ndc = pointerNDC(ev);
    raycaster.setFromCamera(ndc, camera);
    return raycaster.intersectObject(dieMesh).length > 0;
  }

  function onPointerDown(ev) {
    if (mode === 'multi') return onPointerDownMulti(ev);
    if (throwing) return;
    // Allow grabbing the die, OR starting a flick anywhere if pointer is below die.
    const hitsDie = hitTestDie(ev);
    if (!hitsDie) {
      // Permissive: still let user flick from anywhere — pickup snaps die under finger.
    }
    ev.preventDefault();
    dragging = true;
    dieBody.type = CANNON.Body.KINEMATIC;
    dieBody.velocity.set(0, 0, 0);
    dieBody.angularVelocity.set(0, 0, 0);
    // Fresh random "in-hand" spin axis so the player can't keep a face up
    // by holding still — tick() applies this every frame while dragging.
    {
      const ax = Math.random() * 2 - 1;
      const ay = Math.random() * 2 - 1;
      const az = Math.random() * 2 - 1;
      const al = Math.hypot(ax, ay, az) || 1;
      dieBody._spinAxis = { x: ax / al, y: ay / al, z: az / al };
      dieBody._spinRate = 9 + Math.random() * 5;
    }
    pointerSamples = [];
    try { canvasEl.setPointerCapture(ev.pointerId); } catch (_) {}
    const p = pointerOnDragPlane(ev);
    if (p) {
      if (hitsDie) {
        pickOffset.x = dieBody.position.x - p.x;
        pickOffset.z = dieBody.position.z - p.z;
      } else {
        pickOffset.x = 0; pickOffset.z = 0;
        const cx = clamp(p.x, -DRAG_X_LIMIT, DRAG_X_LIMIT);
        const cz = clamp(p.z, DRAG_Z_MIN, DRAG_Z_MAX);
        dieBody.position.set(cx, DRAG_Y, cz);
      }
      pointerSamples.push({ t: performance.now(), x: p.x, z: p.z });
      lastDragP = { x: p.x, z: p.z };
    } else {
      lastDragP = null;
    }
    statusEl.textContent = 'Flick to throw!';
  }

  // Tumble-on-drag: while a die is being held, finger motion spins it like
  // it's rolling under your fingertip. Angle = distance × SPIN_GAIN (well above
  // the natural arc-length-over-radius rate, so the die spins visibly fast).
  const SPIN_GAIN = 9.0;
  function applyTumbleTo(body, dx, dz, gain) {
    const dist = Math.hypot(dx, dz);
    if (dist < 0.0005) return;
    const ax = -dz / dist;        // roll axis = horizontal perpendicular to motion
    const az =  dx / dist;
    const angle = dist * (gain || SPIN_GAIN);
    const half = angle * 0.5;
    const s = Math.sin(half), cw = Math.cos(half);
    const dqx = ax * s, dqy = 0, dqz = az * s, dqw = cw;
    const q = body.quaternion;
    const cx = q.x, cy = q.y, cz = q.z, cw2 = q.w;
    const nx = dqw * cx + dqx * cw2 + dqy * cz - dqz * cy;
    const ny = dqw * cy - dqx * cz + dqy * cw2 + dqz * cx;
    const nz = dqw * cz + dqx * cy - dqy * cx + dqz * cw2;
    const nw = dqw * cw2 - dqx * cx - dqy * cy - dqz * cz;
    q.set(nx, ny, nz, nw);
  }
  function applyTumble(dx, dz) { applyTumbleTo(dieBody, dx, dz); }

  // Rotate a body's quaternion by `angle` radians around an arbitrary axis
  // (world-space premultiply). Used for the continuous in-hand spin so the
  // player can't keep a die at a chosen face by holding still.
  function spinBodyAroundAxis(body, axis, angle) {
    const half = angle * 0.5;
    const s = Math.sin(half), cw = Math.cos(half);
    const dqx = axis.x * s, dqy = axis.y * s, dqz = axis.z * s, dqw = cw;
    const q = body.quaternion;
    const cx = q.x, cy = q.y, cz = q.z, cw2 = q.w;
    const nx = dqw * cx + dqx * cw2 + dqy * cz - dqz * cy;
    const ny = dqw * cy - dqx * cz + dqy * cw2 + dqz * cx;
    const nz = dqw * cz + dqx * cy - dqy * cx + dqz * cw2;
    const nw = dqw * cw2 - dqx * cx - dqy * cy - dqz * cz;
    q.set(nx, ny, nz, nw);
  }

  function onPointerMove(ev) {
    if (mode === 'multi') return onPointerMoveMulti(ev);
    if (!dragging) return;
    const p = pointerOnDragPlane(ev);
    if (!p) return;
    if (lastDragP) applyTumble(p.x - lastDragP.x, p.z - lastDragP.z);
    lastDragP = { x: p.x, z: p.z };
    const tx = clamp(p.x + pickOffset.x, -DRAG_X_LIMIT, DRAG_X_LIMIT);
    const tz = clamp(p.z + pickOffset.z, DRAG_Z_MIN, DRAG_Z_MAX);
    dieBody.position.set(tx, DRAG_Y, tz);
    const now = performance.now();
    pointerSamples.push({ t: now, x: p.x, z: p.z });
    while (pointerSamples.length > 2 && now - pointerSamples[0].t > 200) {
      pointerSamples.shift();
    }
  }

  function onPointerUp(ev) {
    if (mode === 'multi') return onPointerUpMulti(ev);
    if (!dragging) return;
    dragging = false;
    lastDragP = null;
    try { canvasEl.releasePointerCapture(ev.pointerId); } catch (_) {}

    // Velocity from samples in last ~120ms.
    const now = performance.now();
    while (pointerSamples.length > 2 && now - pointerSamples[0].t > 120) {
      pointerSamples.shift();
    }
    let vx = 0, vz = 0;
    if (pointerSamples.length >= 2) {
      const a = pointerSamples[0];
      const b = pointerSamples[pointerSamples.length - 1];
      const dt = Math.max(0.016, (b.t - a.t) / 1000);
      vx = (b.x - a.x) / dt;
      vz = (b.z - a.z) / dt;
    }

    dieBody.type = CANNON.Body.DYNAMIC;
    dieBody.wakeUp();
    // Stop the in-hand auto-spin now that the die is physics-driven.
    dieBody._spinAxis = null;

    const speed = Math.hypot(vx, vz);
    if (speed < 0.6) {
      // Drop without throw — heavier toss + random spin so the player can't
      // keep a chosen face by releasing softly.
      dieBody.velocity.set(
        (Math.random() - 0.5) * 1.8,
        3.4 + Math.random() * 1.4,
        -1.0 - Math.random() * 1.8
      );
      dieBody.angularVelocity.set(
        (Math.random() - 0.5) * 18,
        (Math.random() - 0.5) * 14,
        (Math.random() - 0.5) * 18
      );
    } else {
      const minS = 4, maxS = 22;
      const mag = Math.max(minS, Math.min(maxS, speed * 1.3));
      const k = mag / Math.max(0.01, speed);
      const VX = vx * k;
      const VZ = vz * k;
      const VY = 4.5 + Math.min(7, speed * 0.35);
      dieBody.velocity.set(VX, VY, VZ);
      const spin = 14 + Math.min(26, speed * 1.8);
      dieBody.angularVelocity.set(
        -VZ * 0.7 + (Math.random() - 0.5) * spin,
        (Math.random() - 0.5) * spin * 0.7,
         VX * 0.7 + (Math.random() - 0.5) * spin
      );
    }

    throwing = true;
    settleStart = performance.now();
    statusEl.textContent = 'Rolling…';
    playThrowClatter();
  }

  function topFaceFor(body) {
    const q = new THREE.Quaternion(
      body.quaternion.x, body.quaternion.y,
      body.quaternion.z, body.quaternion.w
    );
    const normals = [
      new THREE.Vector3( 1, 0, 0),
      new THREE.Vector3(-1, 0, 0),
      new THREE.Vector3( 0, 1, 0),
      new THREE.Vector3( 0,-1, 0),
      new THREE.Vector3( 0, 0, 1),
      new THREE.Vector3( 0, 0,-1)
    ];
    let bestY = -Infinity, bestIdx = 2;
    for (let i = 0; i < 6; i++) {
      const w = normals[i].clone().applyQuaternion(q);
      if (w.y > bestY) { bestY = w.y; bestIdx = i; }
    }
    return FACE_NUMBERS[bestIdx];
  }

  function topFaceNumber() { return topFaceFor(dieBody); }

  function tick(now) {
    rafId = requestAnimationFrame(tick);
    const dt = lastTime ? Math.min(0.05, (now - lastTime) / 1000) : 1 / 60;
    lastTime = now;
    world.step(1 / 60, dt, 3);
    // While the player is holding the dice, spin each one around its own
    // axis so the orientation at release is unpredictable (no cheating).
    if (mode === 'single' && dragging && dieBody._spinAxis) {
      spinBodyAroundAxis(dieBody, dieBody._spinAxis, dieBody._spinRate * dt);
    }
    if (mode === 'multi' && multiDragging) {
      for (let i = 0; i < multiDiceBodies.length; i++) {
        const b = multiDiceBodies[i];
        if (b._spinAxis) spinBodyAroundAxis(b, b._spinAxis, b._spinRate * dt);
      }
    }
    if (dieMesh) {
      dieMesh.position.copy(dieBody.position);
      dieMesh.quaternion.copy(dieBody.quaternion);
    }
    for (let i = 0; i < multiDiceMeshes.length; i++) {
      multiDiceMeshes[i].position.copy(multiDiceBodies[i].position);
      multiDiceMeshes[i].quaternion.copy(multiDiceBodies[i].quaternion);
    }
    if ((mode === 'multi' || mode === 'spectator') && _onFrameCb) {
      try { _onFrameCb(); } catch (_) {}
    }
    renderer.render(scene, camera);

    if (mode === 'single' && throwing) {
      const elapsed = now - settleStart;
      const v = dieBody.velocity.length();
      const a = dieBody.angularVelocity.length();
      const settled =
        dieBody.sleepState === CANNON.Body.SLEEPING ||
        (elapsed > 900 && v < 0.06 && a < 0.06);
      if (settled || elapsed > 7500) {
        throwing = false;
        const val = topFaceNumber();
        statusEl.innerHTML = 'You rolled <b style="color:var(--gold)">' + val + '</b>!';
        setTimeout(() => {
          if (!resolveFn) return;
          const r = resolveFn; resolveFn = null;
          closeOverlay();
          r(val);
        }, 750);
      }
    } else if (mode === 'multi' && multiThrowing) {
      const elapsed = now - multiSettleStart;
      const allSettled = multiDiceBodies.every(b => {
        if (b.sleepState === CANNON.Body.SLEEPING) return true;
        return elapsed > 900 &&
          b.velocity.length() < 0.07 &&
          b.angularVelocity.length() < 0.07;
      });
      if (allSettled || elapsed > 8500) {
        multiThrowing = false;
        const results = multiDiceBodies.map(topFaceFor);
        statusEl.innerHTML = 'You rolled <b style="color:var(--gold)">' +
          results.join(' · ') + '</b>!';
        setTimeout(() => {
          if (!multiResolve) return;
          const r = multiResolve; multiResolve = null;
          closeOverlay();
          r(results);
        }, 700);
      }
    }
  }

  function closeOverlay() {
    const closingMode = mode;
    overlay.classList.remove('open');
    setTimeout(() => {
      if (overlay) overlay.style.display = 'none';
      if (rafId) { cancelAnimationFrame(rafId); rafId = null; }
      lastTime = 0;
      throwing = false; dragging = false;
      multiThrowing = false; multiReady = false; multiDragging = false;
      multiPointerSamples = [];
      multiLastDragP = null;
      multiLanes = [];
      teardownMultiDice();
      if (dieMesh) dieMesh.visible = true;
      // Restore interactive UI for the next non-spectator open.
      if (cancelBtn) cancelBtn.style.display = '';
      if (canvasEl) canvasEl.style.pointerEvents = '';
      if (overlay) {
        const t = overlay.querySelector('.d3d-title');
        if (t) t.textContent = 'YAMIO';
      }
      mode = 'single';
      if ((closingMode === 'multi' || closingMode === 'spectator') && _onCloseCb) {
        try { _onCloseCb(closingMode); } catch (_) {}
      }
    }, 280);
  }

  function teardownMultiDice() {
    for (const m of multiDiceMeshes) { try { scene && scene.remove(m); } catch (_) {} }
    for (const b of multiDiceBodies) { try { world && world.removeBody(b); } catch (_) {} }
    multiDiceMeshes = [];
    multiDiceBodies = [];
  }

  function buildMultiAssets(size) {
    const bevel = size * 0.13;
    if (multiGeom) { try { multiGeom.dispose(); } catch (_) {} }
    multiGeom = makeRoundedBoxGeometry(size, bevel, 6);
    if (!multiMats) {
      multiMats = FACE_NUMBERS.map(n => new THREE.MeshStandardMaterial({
        map: makeFaceTexture(n),
        roughness: 0.28,
        metalness: 0.12,
        color: 0xffffff
      }));
    }
  }

  function setupMultiDice(count) {
    teardownMultiDice();
    // Smaller dice so all 5 fit in the play area together.
    const SIZE = 0.62;
    const HALF = SIZE / 2;
    buildMultiAssets(SIZE);

    // Pre-compute fan offsets so the dice spread sideways around the finger.
    multiLanes = [];
    for (let i = 0; i < count; i++) {
      const lane = count === 1 ? 0 : (i / (count - 1) - 0.5) * 2.0; // -1..1
      const dz = (i % 2 === 0 ? 0 : 0.35);                          // light zig-zag
      multiLanes.push({ dx: lane, dz: dz });
    }

    // Park the dice in a fan near the player. Kinematic so they don't fall
    // while you line up a flick. On pickup they follow your finger and
    // tumble; on release the swipe vector becomes their velocity.
    for (let i = 0; i < count; i++) {
      const mesh = new THREE.Mesh(multiGeom, multiMats);
      mesh.castShadow = true;
      scene.add(mesh);
      multiDiceMeshes.push(mesh);

      const body = new CANNON.Body({
        mass: 0.6,
        shape: new CANNON.Box(new CANNON.Vec3(HALF, HALF, HALF)),
        material: diePMat,
        allowSleep: true,
        sleepSpeedLimit: 0.16,
        sleepTimeLimit: 0.45,
        linearDamping: 0.18,
        angularDamping: 0.18
      });
      const lane = multiLanes[i];
      body.position.set(lane.dx, HALF + 0.02, DRAG_Z_MAX - 0.2 + lane.dz);
      body.quaternion.setFromEuler(
        Math.random() * 0.35, Math.random() * 0.35, Math.random() * 0.35
      );
      body.type = CANNON.Body.KINEMATIC;
      body.velocity.set(0, 0, 0);
      body.angularVelocity.set(0, 0, 0);
      // Per-die "auto spin" axis used while the dice are held in the hand —
      // prevents the player from picking a face by holding still.
      const ax = Math.random() * 2 - 1;
      const ay = Math.random() * 2 - 1;
      const az = Math.random() * 2 - 1;
      const al = Math.hypot(ax, ay, az) || 1;
      body._spinAxis = { x: ax / al, y: ay / al, z: az / al };
      body._spinRate = 9 + Math.random() * 5; // rad/s — ~1.5-2 rotations/sec
      body.addEventListener('collide', (e) => {
        if (!multiThrowing) return;
        const c = e && e.contact;
        const v = c && typeof c.getImpactVelocityAlongNormal === 'function'
          ? Math.abs(c.getImpactVelocityAlongNormal())
          : 0;
        if (v >= 1.4) playImpactTap(v);
      });
      world.addBody(body);
      multiDiceBodies.push(body);
    }
    multiReady = true;
    multiThrowing = false;
    multiDragging = false;
    multiPointerSamples = [];
    multiLastDragP = null;
    multiSettleStart = 0;
  }

  // Move every multi die so it sits at (fingerX + lane.dx, fingerZ + lane.dz),
  // hovering at DRAG_Y. The whole group "tracks" the finger as one handful.
  function placeMultiAtFinger(px, pz) {
    for (let i = 0; i < multiDiceBodies.length; i++) {
      const lane = multiLanes[i] || { dx: 0, dz: 0 };
      const tx = clamp(px + lane.dx, -DRAG_X_LIMIT, DRAG_X_LIMIT);
      const tz = clamp(pz + lane.dz, DRAG_Z_MIN, DRAG_Z_MAX);
      multiDiceBodies[i].position.set(tx, DRAG_Y, tz);
    }
  }

  function multiFlick(vx, vz, speed) {
    const minS = 4, maxS = 22;
    const mag = Math.max(minS, Math.min(maxS, speed * 1.3));
    const k = mag / Math.max(0.01, speed);
    const VX = vx * k;
    const VZ = vz * k;
    const VY = 3.8 + Math.min(7, speed * 0.35);
    multiDiceBodies.forEach((b) => {
      b.type = CANNON.Body.DYNAMIC;
      b.wakeUp();
      b._spinAxis = null;
      const jitter = 1.5;
      b.velocity.set(
        VX + (Math.random() - 0.5) * jitter,
        VY + (Math.random() - 0.5) * 0.8,
        VZ + (Math.random() - 0.5) * jitter
      );
      const spin = 16 + Math.min(28, speed * 2.0);
      b.angularVelocity.set(
        -VZ * 0.7 + (Math.random() - 0.5) * spin,
        (Math.random() - 0.5) * spin * 0.7,
         VX * 0.7 + (Math.random() - 0.5) * spin
      );
    });
  }

  function multiSoftDrop() {
    // Weak / no flick → still toss the dice in the air with heavy spin so
    // they can't be released face-up.
    multiDiceBodies.forEach((b) => {
      b.type = CANNON.Body.DYNAMIC;
      b.wakeUp();
      b._spinAxis = null;
      b.velocity.set(
        (Math.random() - 0.5) * 2.2,
        3.4 + Math.random() * 1.6,
        -1.2 - Math.random() * 2.4
      );
      const spin = 18;
      b.angularVelocity.set(
        (Math.random() - 0.5) * spin,
        (Math.random() - 0.5) * spin,
        (Math.random() - 0.5) * spin
      );
    });
  }

  function onPointerDownMulti(ev) {
    if (!multiReady || multiThrowing) return;
    ev.preventDefault();
    multiDragging = true;
    multiPointerSamples = [];
    try { canvasEl.setPointerCapture(ev.pointerId); } catch (_) {}
    const p = pointerOnDragPlane(ev);
    if (p) {
      multiPointerSamples.push({ t: performance.now(), x: p.x, z: p.z });
      multiLastDragP = { x: p.x, z: p.z };
      // Lift all dice off the floor and snap the group to the finger.
      multiDiceBodies.forEach(b => {
        b.velocity.set(0, 0, 0);
        b.angularVelocity.set(0, 0, 0);
      });
      placeMultiAtFinger(p.x, p.z);
    }
    statusEl.textContent = 'Spin them up — flick to throw!';
  }

  function onPointerMoveMulti(ev) {
    if (!multiDragging) return;
    const p = pointerOnDragPlane(ev);
    if (!p) return;
    if (multiLastDragP) {
      const dx = p.x - multiLastDragP.x;
      const dz = p.z - multiLastDragP.z;
      // Tumble each die under the fingertip. Slightly lower gain than the
      // single-die mode so the cluster doesn't spin as a chaotic blur.
      for (let i = 0; i < multiDiceBodies.length; i++) {
        applyTumbleTo(multiDiceBodies[i], dx, dz, 7.5);
      }
    }
    multiLastDragP = { x: p.x, z: p.z };
    placeMultiAtFinger(p.x, p.z);
    const now = performance.now();
    multiPointerSamples.push({ t: now, x: p.x, z: p.z });
    while (multiPointerSamples.length > 2 && now - multiPointerSamples[0].t > 200) {
      multiPointerSamples.shift();
    }
  }

  function onPointerUpMulti(ev) {
    if (!multiDragging) return;
    multiDragging = false;
    multiLastDragP = null;
    try { canvasEl.releasePointerCapture(ev.pointerId); } catch (_) {}

    const now = performance.now();
    while (multiPointerSamples.length > 2 && now - multiPointerSamples[0].t > 120) {
      multiPointerSamples.shift();
    }
    let vx = 0, vz = 0;
    if (multiPointerSamples.length >= 2) {
      const a = multiPointerSamples[0];
      const b = multiPointerSamples[multiPointerSamples.length - 1];
      const dt = Math.max(0.016, (b.t - a.t) / 1000);
      vx = (b.x - a.x) / dt;
      vz = (b.z - a.z) / dt;
    }
    const speed = Math.hypot(vx, vz);
    if (speed < 0.6) multiSoftDrop();
    else multiFlick(vx, vz, speed);

    multiReady = false;
    multiThrowing = true;
    multiSettleStart = performance.now();
    statusEl.textContent = 'Rolling…';
    playThrowClatter();
  }

  let libsPromise = null;
  function ensureLibs() {
    if (THREE && CANNON) return Promise.resolve();
    if (libsPromise) return libsPromise;
    libsPromise = Promise.all([
      import('https://unpkg.com/three@0.160.0/build/three.module.js'),
      import('https://unpkg.com/cannon-es@0.20.0/dist/cannon-es.js')
    ]).then(([t, c]) => { THREE = t; CANNON = c; });
    return libsPromise;
  }

  window.throw3DDie = function () {
    return Promise.all([ensureLibs(), ensureBrandFont()]).then(() => {
      if (!overlay) buildOverlay();
      if (!renderer) {
        try { initScene(); }
        catch (e) {
          console.warn('3D dice init failed', e);
          return Math.floor(Math.random() * 6) + 1;
        }
      }
      mode = 'single';
      teardownMultiDice();
      if (dieMesh) dieMesh.visible = true;
      resetDie();
      statusEl.textContent = 'Drag the dice and flick to throw';
      cancelBtn.textContent = 'Skip throw';
      overlay.style.display = 'flex';
      requestAnimationFrame(() => {
        overlay.classList.add('open');
        onResize();
      });

      if (!canvasEl._d3dBound) {
        canvasEl._d3dBound = true;
        canvasEl.addEventListener('pointerdown', onPointerDown);
        canvasEl.addEventListener('pointermove', onPointerMove);
        canvasEl.addEventListener('pointerup', onPointerUp);
        canvasEl.addEventListener('pointercancel', onPointerUp);
        window.addEventListener('resize', onResize);
      }

      if (!rafId) {
        lastTime = 0;
        rafId = requestAnimationFrame(tick);
      }

      return new Promise(res => { resolveFn = res; });
    }).catch(e => {
      console.warn('throw3DDie failed, using random fallback', e);
      return Math.floor(Math.random() * 6) + 1;
    });
  };

  // Auto-toss `count` smaller dice in the same 3D scene. Resolves with an
  // array of face values (1..6) in the same order the dice were spawned.
  window.throw3DDice = function (count) {
    const n = Math.max(1, Math.min(5, (count | 0) || 5));
    const randomArr = () => {
      const a = [];
      for (let i = 0; i < n; i++) a.push(Math.floor(Math.random() * 6) + 1);
      return a;
    };
    return Promise.all([ensureLibs(), ensureBrandFont()]).then(() => {
      if (!overlay) buildOverlay();
      if (!renderer) {
        try { initScene(); }
        catch (e) { console.warn('3D dice init failed', e); return randomArr(); }
      }
      mode = 'multi';
      // Park the single die out of view so it doesn't share the scene visibly.
      if (dieBody) { dieBody.type = CANNON.Body.STATIC; dieBody.position.set(0, -20, 0); }
      if (dieMesh) dieMesh.visible = false;
      setupMultiDice(n);
      if (_onOpenCb) { try { _onOpenCb(n); } catch (_) {} }
      statusEl.textContent = 'Grab the dice and flick to throw';
      cancelBtn.textContent = 'Skip throw';
      overlay.style.display = 'flex';
      requestAnimationFrame(() => {
        overlay.classList.add('open');
        onResize();
      });

      if (!canvasEl._d3dBound) {
        canvasEl._d3dBound = true;
        canvasEl.addEventListener('pointerdown', onPointerDown);
        canvasEl.addEventListener('pointermove', onPointerMove);
        canvasEl.addEventListener('pointerup', onPointerUp);
        canvasEl.addEventListener('pointercancel', onPointerUp);
        window.addEventListener('resize', onResize);
      }

      if (!rafId) {
        lastTime = 0;
        rafId = requestAnimationFrame(tick);
      }

      return new Promise(res => { multiResolve = res; });
    }).catch(e => {
      console.warn('throw3DDice failed, using random fallback', e);
      return randomArr();
    });
  };

  // ── Spectator mode: render an opponent's live 3D throw ───────────
  // No physics, no pointer input — just pose `count` multi-style dice from
  // network-streamed transforms. Returns { setFrame, close } once ready.
  window.dice3DSpectate = function (opts) {
    const o = opts || {};
    const n = Math.max(1, Math.min(5, (o.count | 0) || 5));
    return Promise.all([ensureLibs(), ensureBrandFont()]).then(() => {
      if (!overlay) buildOverlay();
      if (!renderer) {
        try { initScene(); }
        catch (e) { console.warn('3D dice init failed (spectator)', e); return null; }
      }
      mode = 'spectator';
      if (dieBody) { dieBody.type = CANNON.Body.STATIC; dieBody.position.set(0, -20, 0); }
      if (dieMesh) dieMesh.visible = false;
      setupMultiDice(n);
      // Freeze all bodies — meshes will follow body.position which we slam
      // each frame from the incoming stream.
      multiDiceBodies.forEach(b => {
        b.type = CANNON.Body.STATIC;
        b.velocity.set(0, 0, 0);
        b.angularVelocity.set(0, 0, 0);
        b._spinAxis = null;
      });
      multiReady = false; multiThrowing = false; multiDragging = false;

      const title = overlay.querySelector('.d3d-title');
      if (title) title.textContent = (o.title || 'OPPONENT').toUpperCase();
      statusEl.textContent = o.status || 'Watching opponent…';
      cancelBtn.textContent = 'Hide';
      cancelBtn.style.display = '';
      canvasEl.style.pointerEvents = 'none';
      overlay.style.display = 'flex';
      requestAnimationFrame(() => {
        overlay.classList.add('open');
        onResize();
      });

      if (!rafId) {
        lastTime = 0;
        rafId = requestAnimationFrame(tick);
      }

      return {
        setFrame(transforms) {
          if (mode !== 'spectator' || !transforms) return;
          const len = Math.min(transforms.length, multiDiceBodies.length);
          for (let i = 0; i < len; i++) {
            const t = transforms[i];
            if (!t || !t.p || !t.q) continue;
            multiDiceBodies[i].position.set(t.p[0], t.p[1], t.p[2]);
            multiDiceBodies[i].quaternion.set(t.q[0], t.q[1], t.q[2], t.q[3]);
          }
        },
        setStatus(text) {
          if (statusEl) statusEl.textContent = text || '';
        },
        close() {
          if (mode === 'spectator') closeOverlay();
        }
      };
    }).catch(e => {
      console.warn('dice3DSpectate failed', e);
      return null;
    });
  };

  // ── Public bridge for the multiplayer streaming module ───────────
  window.dice3DBridge = {
    isMultiActive() {
      return mode === 'multi' && (multiReady || multiDragging || multiThrowing);
    },
    isSpectatorActive() { return mode === 'spectator'; },
    getMode() { return mode; },
    getMultiState() {
      if (mode !== 'multi') return null;
      const transforms = [];
      for (let i = 0; i < multiDiceMeshes.length; i++) {
        const m = multiDiceMeshes[i];
        transforms.push({
          p: [m.position.x, m.position.y, m.position.z],
          q: [m.quaternion.x, m.quaternion.y, m.quaternion.z, m.quaternion.w]
        });
      }
      return {
        n: multiDiceMeshes.length,
        ready: multiReady,
        dragging: multiDragging,
        throwing: multiThrowing,
        transforms: transforms
      };
    },
    setOnFrame(fn) { _onFrameCb = (typeof fn === 'function') ? fn : null; },
    setOnOpen(fn)  { _onOpenCb  = (typeof fn === 'function') ? fn : null; },
    setOnClose(fn) { _onCloseCb = (typeof fn === 'function') ? fn : null; },
    setOnSpectatorHide(fn) {
      _onSpectatorHideCb = (typeof fn === 'function') ? fn : null;
    }
  };
})();

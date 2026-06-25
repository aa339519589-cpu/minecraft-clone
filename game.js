import * as THREE from 'three';
import { PointerLockControls } from 'three/addons/controls/PointerLockControls.js';

// ============================================================
//  常量
// ============================================================
const W = 48;            // 世界 X 大小
const D = 48;            // 世界 Z 大小
const H = 24;            // 世界 Y 高度
const GRAVITY = -22;
const JUMP_SPEED = 9;
const WALK_SPEED = 4.8;
const SPRINT_SPEED = 7.2;
const REACH = 7;
const P_RADIUS = 0.3;
const P_HEIGHT = 1.7;
const P_EYE = 1.55;

const BT = {
    AIR: 0, GRASS: 1, DIRT: 2, STONE: 3,
    WOOD: 4, LEAVES: 5, PLANKS: 6, BRICK: 7,
    SAND: 8, SNOW: 9, COBBLESTONE: 10, BEDROCK: 11,
};
const BLOCK_LIST = [
    { id: BT.GRASS, name: '草方块' },
    { id: BT.DIRT, name: '泥土' },
    { id: BT.STONE, name: '石头' },
    { id: BT.WOOD, name: '原木' },
    { id: BT.LEAVES, name: '树叶' },
    { id: BT.PLANKS, name: '木板' },
    { id: BT.BRICK, name: '砖块' },
    { id: BT.SAND, name: '沙子' },
];

// ============================================================
//  状态
// ============================================================
const world = new Int8Array(W * H * D);
const meshes = new Map();   // key: "x,y,z" -> THREE.Mesh
let scene, camera, renderer, controls;
let selectedSlot = 0;
let isLocked = false;
let velocity = new THREE.Vector3();
let onGround = false;
let keys = { w: false, a: false, s: false, d: false, shift: false };
let crosshairEl, toolbarEl, blockInfoEl, fpsEl, blockerEl;
let clock = new THREE.Clock();
let raycaster = new THREE.Raycaster();
let pointer = new THREE.Vector2();

// ============================================================
//  工具
// ============================================================
function idx(x, y, z) {
    return (x * H + y) * D + z;
}

function getBlock(x, y, z) {
    if (x < 0 || x >= W || y < 0 || y >= H || z < 0 || z >= D) return BT.AIR;
    return world[idx(x, y, z)];
}

function setBlock(x, y, z, type) {
    if (x < 0 || x >= W || y < 0 || y >= H || z < 0 || z >= D) return;
    world[idx(x, y, z)] = type;
}

function blockKey(x, y, z) { return `${x},${y},${z}`; }

// 简单的伪随机噪声
function noise2D(x, z, seed = 0) {
    let n = Math.sin(x * 12.9898 + z * 78.233 + seed) * 43758.5453;
    return n - Math.floor(n);
}

function smoothNoise(x, z, scale, seed) {
    const sx = x / scale, sz = z / scale;
    const ix = Math.floor(sx), iz = Math.floor(sz);
    const fx = sx - ix, fz = sz - iz;
    const sx2 = fx * fx * (3 - 2 * fx);
    const sz2 = fz * fz * (3 - 2 * fz);
    const v00 = noise2D(ix, iz, seed);
    const v10 = noise2D(ix + 1, iz, seed);
    const v01 = noise2D(ix, iz + 1, seed);
    const v11 = noise2D(ix + 1, iz + 1, seed);
    const v0 = v00 + (v10 - v00) * sx2;
    const v1 = v01 + (v11 - v01) * sx2;
    return v0 + (v1 - v0) * sz2;
}

function fbm(x, z) {
    let v = 0, amp = 1, freq = 1, total = 0;
    for (let i = 0; i < 3; i++) {
        v += smoothNoise(x, z, 12 / freq, i * 100) * amp;
        total += amp;
        amp *= 0.5;
        freq *= 2;
    }
    return v / total;
}

// ============================================================
//  纹理生成
// ============================================================
function createPixelTexture(size, drawFn) {
    const canvas = document.createElement('canvas');
    canvas.width = size;
    canvas.height = size;
    const ctx = canvas.getContext('2d');
    const imgData = ctx.createImageData(size, size);
    drawFn(imgData.data, size);
    ctx.putImageData(imgData, 0, 0);
    const tex = new THREE.CanvasTexture(canvas);
    tex.magFilter = THREE.NearestFilter;
    tex.minFilter = THREE.NearestFilter;
    return tex;
}

function makeGrassTop() {
    return createPixelTexture(16, (d, s) => {
        for (let y = 0; y < s; y++) for (let x = 0; x < s; x++) {
            const i = (y * s + x) * 4;
            const n = noise2D(x, y, 42);
            const base = n < 0.5 ? [0.31, 0.56, 0.22] : [0.35, 0.62, 0.25];
            if (n < 0.15) { d[i] = 0.25; d[i + 1] = 0.48; d[i + 2] = 0.18; }
            else if (n > 0.85) { d[i] = 0.42; d[i + 1] = 0.70; d[i + 2] = 0.30; }
            else { d[i] = base[0] * 255; d[i + 1] = base[1] * 255; d[i + 2] = base[2] * 255; }
            d[i + 3] = 255;
        }
    });
}

function makeGrassSide() {
    return createPixelTexture(16, (d, s) => {
        for (let y = 0; y < s; y++) for (let x = 0; x < s; x++) {
            const i = (y * s + x) * 4;
            const n = noise2D(x, y, 77);
            if (y < 6) {
                d[i] = 0.45 + n * 0.08;
                d[i + 1] = 0.30 + n * 0.08;
                d[i + 2] = 0.18 + n * 0.06;
            } else if (y < 8) {
                const t = (y - 6) / 2;
                d[i] = (0.45 * (1 - t) + 0.32 * t + n * 0.06) * 255;
                d[i + 1] = (0.30 * (1 - t) + 0.55 * t + n * 0.06) * 255;
                d[i + 2] = (0.18 * (1 - t) + 0.20 * t + n * 0.04) * 255;
            } else {
                d[i] = (0.32 + n * 0.08) * 255;
                d[i + 1] = (0.55 + n * 0.10) * 255;
                d[i + 2] = (0.20 + n * 0.06) * 255;
            }
            d[i + 3] = 255;
        }
    });
}

function makeDirtTex() {
    return createPixelTexture(16, (d, s) => {
        for (let y = 0; y < s; y++) for (let x = 0; x < s; x++) {
            const i = (y * s + x) * 4;
            const n = noise2D(x, y, 123);
            d[i] = (0.47 + n * 0.14) * 255;
            d[i + 1] = (0.33 + n * 0.12) * 255;
            d[i + 2] = (0.20 + n * 0.10) * 255;
            d[i + 3] = 255;
        }
    });
}

function makeStoneTex() {
    return createPixelTexture(16, (d, s) => {
        for (let y = 0; y < s; y++) for (let x = 0; x < s; x++) {
            const i = (y * s + x) * 4;
            const n = noise2D(x, y, 55);
            const v = 0.45 + n * 0.25;
            d[i] = v * 255;
            d[i + 1] = v * 255;
            d[i + 2] = v * 255;
            d[i + 3] = 255;
        }
    });
}

function makeWoodSide() {
    return createPixelTexture(16, (d, s) => {
        for (let y = 0; y < s; y++) for (let x = 0; x < s; x++) {
            const i = (y * s + x) * 4;
            const n = noise2D(x, y, 200);
            const isBark = (x < 2 || x > 13 || (y > 1 && y < 14 && (x < 3 || x > 12)));
            if (isBark) {
                const stripe = Math.sin(y * 1.8 + x * 0.3) * 0.08;
                d[i] = (0.38 + n * 0.08 + stripe) * 255;
                d[i + 1] = (0.25 + n * 0.06 + stripe) * 255;
                d[i + 2] = (0.14 + n * 0.06 + stripe) * 255;
            } else {
                d[i] = (0.52 + n * 0.06) * 255;
                d[i + 1] = (0.38 + n * 0.06) * 255;
                d[i + 2] = (0.22 + n * 0.06) * 255;
            }
            d[i + 3] = 255;
        }
    });
}

function makeWoodTop() {
    return createPixelTexture(16, (d, s) => {
        for (let y = 0; y < s; y++) for (let x = 0; x < s; x++) {
            const i = (y * s + x) * 4;
            const n = noise2D(x, y, 333);
            const ring = Math.abs(Math.sqrt((x - 7.5) ** 2 + (y - 7.5) ** 2) - 4);
            const isRing = ring < 1.2;
            if (isRing) {
                d[i] = (0.48 + n * 0.06) * 255;
                d[i + 1] = (0.34 + n * 0.06) * 255;
                d[i + 2] = (0.18 + n * 0.04) * 255;
            } else {
                d[i] = (0.58 + n * 0.08) * 255;
                d[i + 1] = (0.42 + n * 0.08) * 255;
                d[i + 2] = (0.26 + n * 0.06) * 255;
            }
            d[i + 3] = 255;
        }
    });
}

function makeLeavesTex() {
    return createPixelTexture(16, (d, s) => {
        for (let y = 0; y < s; y++) for (let x = 0; x < s; x++) {
            const i = (y * s + x) * 4;
            const n = noise2D(x, y, 77);
            if (n < 0.25) {
                d[i] = 0; d[i + 1] = 0; d[i + 2] = 0; d[i + 3] = 0;
            } else {
                const v = 0.15 + n * 0.25;
                d[i] = (0.10 + v) * 255;
                d[i + 1] = (0.45 + v) * 255;
                d[i + 2] = (0.12 + v * 0.5) * 255;
                d[i + 3] = 220;
            }
        }
    });
}

function makePlanksTex() {
    return createPixelTexture(16, (d, s) => {
        for (let y = 0; y < s; y++) for (let x = 0; x < s; x++) {
            const i = (y * s + x) * 4;
            const n = noise2D(x, y, 512);
            const stripe = Math.sin(y * 3.0) * 0.06;
            d[i] = (0.70 + n * 0.08 + stripe) * 255;
            d[i + 1] = (0.55 + n * 0.08 + stripe) * 255;
            d[i + 2] = (0.38 + n * 0.06 + stripe) * 255;
            d[i + 3] = 255;
        }
    });
}

function makeBrickTex() {
    return createPixelTexture(16, (d, s) => {
        for (let y = 0; y < s; y++) for (let x = 0; x < s; x++) {
            const i = (y * s + x) * 4;
            const n = noise2D(x, y, 99);
            const isMortar = (y === 7 || y === 8 || x === 7 || x === 8 ||
                (y >= 3 && y <= 4 && x >= 0 && x <= 6) ||
                (y >= 11 && y <= 12 && x >= 0 && x <= 6) ||
                (y >= 3 && y <= 4 && x >= 9) ||
                (y >= 11 && y <= 12 && x >= 9));
            if (isMortar) {
                d[i] = 190;
                d[i + 1] = 180;
                d[i + 2] = 160;
            } else {
                d[i] = (0.65 + n * 0.15) * 255;
                d[i + 1] = (0.30 + n * 0.10) * 255;
                d[i + 2] = (0.18 + n * 0.08) * 255;
            }
            d[i + 3] = 255;
        }
    });
}

function makeSandTex() {
    return createPixelTexture(16, (d, s) => {
        for (let y = 0; y < s; y++) for (let x = 0; x < s; x++) {
            const i = (y * s + x) * 4;
            const n = noise2D(x, y, 244);
            const v = 0.78 + n * 0.12;
            d[i] = (v + 0.10) * 255;
            d[i + 1] = (v + 0.02) * 255;
            d[i + 2] = (v - 0.10) * 255;
            d[i + 3] = 255;
        }
    });
}

function makeSnowTex() {
    return createPixelTexture(16, (d, s) => {
        for (let y = 0; y < s; y++) for (let x = 0; x < s; x++) {
            const i = (y * s + x) * 4;
            const n = noise2D(x, y, 88);
            const v = 0.90 + n * 0.10;
            d[i] = v * 255;
            d[i + 1] = v * 255;
            d[i + 2] = v * 255;
            d[i + 3] = 255;
        }
    });
}

// ============================================================
//  方块材质工厂
// ============================================================
const texCache = new Map();

function getTex(name) {
    if (!texCache.has(name)) {
        const fn = {
            grassTop: makeGrassTop, grassSide: makeGrassSide,
            dirt: makeDirtTex, stone: makeStoneTex,
            woodSide: makeWoodSide, woodTop: makeWoodTop,
            leaves: makeLeavesTex, planks: makePlanksTex,
            brick: makeBrickTex, sand: makeSandTex,
            snow: makeSnowTex,
        }[name];
        if (fn) texCache.set(name, fn());
    }
    return texCache.get(name);
}

function getBlockMaterial(type) {
    switch (type) {
        case BT.GRASS:
            const tTop = getTex('grassTop');
            const tSide = getTex('grassSide');
            const tDirt = getTex('dirt');
            return [tSide, tSide, tTop, tDirt, tSide, tSide];
        case BT.DIRT:
            return getTex('dirt');
        case BT.STONE:
            return getTex('stone');
        case BT.WOOD:
            return [getTex('woodSide'), getTex('woodSide'), getTex('woodTop'), getTex('woodTop'), getTex('woodSide'), getTex('woodSide')];
        case BT.LEAVES:
            return getTex('leaves');
        case BT.PLANKS:
            return getTex('planks');
        case BT.BRICK:
            return getTex('brick');
        case BT.SAND:
            return getTex('sand');
        case BT.SNOW:
            return getTex('snow');
        case BT.COBBLESTONE:
            return getTex('stone');
        case BT.BEDROCK:
            return getTex('stone');
        default:
            return new THREE.MeshLambertMaterial({ color: 0x888888 });
    }
}

function isExposed(x, y, z) {
    return getBlock(x + 1, y, z) === BT.AIR ||
        getBlock(x - 1, y, z) === BT.AIR ||
        getBlock(x, y + 1, z) === BT.AIR ||
        getBlock(x, y - 1, z) === BT.AIR ||
        getBlock(x, y, z + 1) === BT.AIR ||
        getBlock(x, y, z - 1) === BT.AIR;
}

function isTransparent(type) {
    return type === BT.AIR || type === BT.LEAVES;
}

// ============================================================
//  世界生成
// ============================================================
function generateWorld() {
    // 地形高度图
    for (let x = 0; x < W; x++) {
        for (let z = 0; z < D; z++) {
            const cx = x - W / 2, cz = z - D / 2;
            const h = fbm(cx * 0.06, cz * 0.06);
            const height = Math.floor(h * 5 + 4);

            for (let y = 0; y < H; y++) {
                let blockType = BT.AIR;
                if (y === 0) {
                    blockType = BT.BEDROCK;
                } else if (y < height - 2) {
                    blockType = BT.STONE;
                } else if (y < height) {
                    blockType = BT.DIRT;
                } else if (y === height) {
                    blockType = BT.GRASS;
                    if (height > 8) blockType = BT.SNOW;
                    else if (height < 3) blockType = BT.SAND;
                }
                setBlock(x, y, z, blockType);
            }
        }
    }

    // 树木
    const treeCount = 60;
    for (let i = 0; i < treeCount; i++) {
        const tx = 4 + Math.floor(Math.random() * (W - 8));
        const tz = 4 + Math.floor(Math.random() * (D - 8));
        // 找地面高度
        let groundY = -1;
        for (let y = H - 1; y >= 0; y--) {
            if (getBlock(tx, y, tz) !== BT.AIR) { groundY = y + 1; break; }
        }
        if (groundY < 2 || groundY > H - 6) continue;
        // 只在草或泥土上种树
        const below = getBlock(tx, groundY - 1, tz);
        if (below !== BT.GRASS && below !== BT.DIRT) continue;
        // 树干
        const trunkH = 4 + Math.floor(Math.random() * 2);
        for (let y = 0; y < trunkH; y++) {
            setBlock(tx, groundY + y, tz, BT.WOOD);
        }
        // 树冠
        const leafBase = groundY + trunkH - 2;
        for (let dy = -2; dy <= 2; dy++) {
            for (let dx = -2; dx <= 2; dx++) {
                for (let dz = -2; dz <= 2; dz++) {
                    const dist = Math.abs(dx) + Math.abs(dz) + Math.abs(dy) * 0.8;
                    if (dist > 2.8) continue;
                    const lx = tx + dx, ly = leafBase + dy, lz = tz + dz;
                    if (lx >= 0 && lx < W && ly >= 0 && ly < H && lz >= 0 && lz < D) {
                        if (getBlock(lx, ly, lz) === BT.AIR) {
                            setBlock(lx, ly, lz, BT.LEAVES);
                        }
                    }
                }
            }
        }
    }

    // 花/装饰（小彩色方块）
    for (let i = 0; i < 30; i++) {
        const fx = 1 + Math.floor(Math.random() * (W - 2));
        const fz = 1 + Math.floor(Math.random() * (D - 2));
        for (let y = H - 1; y >= 0; y--) {
            if (getBlock(fx, y, fz) !== BT.AIR) {
                if (getBlock(fx, y, fz) === BT.GRASS && getBlock(fx, y + 1, fz) === BT.AIR) {
                    // 不放花了，保持简洁
                }
                break;
            }
        }
    }
}

// ============================================================
//  方块网格管理
// ============================================================
function buildWorldMesh() {
    // 清除旧网格
    for (const [key, mesh] of meshes) {
        scene.remove(mesh);
        mesh.geometry.dispose();
        if (Array.isArray(mesh.material)) mesh.material.forEach(m => m.dispose());
        else mesh.material.dispose();
    }
    meshes.clear();

    // 为每种方块类型收集位置
    const typePositions = new Map();

    for (let x = 0; x < W; x++) {
        for (let y = 0; y < H; y++) {
            for (let z = 0; z < D; z++) {
                const type = getBlock(x, y, z);
                if (type === BT.AIR) continue;
                if (type === BT.LEAVES) {
                    // 树叶单独处理
                    createSingleBlock(x, y, z, type);
                    continue;
                }
                if (!isExposed(x, y, z)) continue;

                if (!typePositions.has(type)) {
                    typePositions.set(type, []);
                }
                typePositions.get(type).push({ x, y, z });
            }
        }
    }

    // 为每种类型创建 InstancedMesh
    for (const [type, positions] of typePositions) {
        if (positions.length === 0) continue;

        const geo = new THREE.BoxGeometry(1, 1, 1);
        const mat = getBlockMaterial(type);
        const matFinal = Array.isArray(mat) ? mat.map(m => new THREE.MeshLambertMaterial({ map: m })) : new THREE.MeshLambertMaterial({ map: mat });

        const mesh = new THREE.InstancedMesh(geo, matFinal, positions.length);
        mesh.castShadow = true;
        mesh.receiveShadow = true;

        const dummy = new THREE.Object3D();
        for (let i = 0; i < positions.length; i++) {
            const p = positions[i];
            dummy.position.set(p.x - W / 2 + 0.5, p.y + 0.5, p.z - D / 2 + 0.5);
            dummy.updateMatrix();
            mesh.setMatrixAt(i, dummy.matrix);
            meshes.set(blockKey(p.x, p.y, p.z), mesh);
        }
        mesh.instanceMatrix.needsUpdate = true;
        scene.add(mesh);
    }

    // 收集树叶（已单独创建）
}

function createSingleBlock(x, y, z, type) {
    const key = blockKey(x, y, z);
    if (meshes.has(key)) return;

    const geo = new THREE.BoxGeometry(1, 1, 1);
    const mat = getBlockMaterial(type);
    const matFinal = Array.isArray(mat) ? mat.map(m => {
        const ml = new THREE.MeshLambertMaterial({ map: m, transparent: true, opacity: 0.85 });
        return ml;
    }) : new THREE.MeshLambertMaterial({ map: mat, transparent: true, opacity: 0.85 });

    const mesh = new THREE.Mesh(geo, matFinal);
    mesh.position.set(x - W / 2 + 0.5, y + 0.5, z - D / 2 + 0.5);
    mesh.castShadow = true;
    mesh.receiveShadow = true;
    scene.add(mesh);
    meshes.set(key, mesh);
}

function removeBlockMesh(x, y, z) {
    const key = blockKey(x, y, z);
    const existing = meshes.get(key);
    if (existing && existing.isInstancedMesh) {
        // 对于 InstancedMesh，需要重建世界
        // 简单处理：先修改world数据，然后重建
        return false; // 标记需要重建
    }
    if (existing) {
        scene.remove(existing);
        existing.geometry.dispose();
        if (Array.isArray(existing.material)) existing.material.forEach(m => m.dispose());
        else existing.material.dispose();
        meshes.delete(key);
    }
    return true;
}

// ============================================================
//  场景初始化
// ============================================================
function initScene() {
    scene = new THREE.Scene();
    scene.background = new THREE.Color(0x87CEEB); // 天空蓝
    scene.fog = new THREE.Fog(0x87CEEB, 40, 70);

    // 相机
    camera = new THREE.PerspectiveCamera(75, window.innerWidth / window.innerHeight, 0.1, 100);
    camera.position.set(0, 20, 0);

    // 渲染器
    renderer = new THREE.WebGLRenderer({ antialias: true });
    renderer.setSize(window.innerWidth, window.innerHeight);
    renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
    renderer.shadowMap.enabled = true;
    renderer.shadowMap.type = THREE.PCFSoftShadowMap;
    renderer.toneMapping = THREE.ACESFilmicToneMapping;
    renderer.toneMappingExposure = 1.2;
    document.body.prepend(renderer.domElement);

    // 灯光
    const ambient = new THREE.AmbientLight(0x8899bb, 0.5);
    scene.add(ambient);

    const sun = new THREE.DirectionalLight(0xffeedd, 1.4);
    sun.position.set(30, 40, 20);
    sun.castShadow = true;
    sun.shadow.mapSize.width = 2048;
    sun.shadow.mapSize.height = 2048;
    sun.shadow.camera.near = 0.5;
    sun.shadow.camera.far = 80;
    sun.shadow.camera.left = -35;
    sun.shadow.camera.right = 35;
    sun.shadow.camera.top = 35;
    sun.shadow.camera.bottom = -35;
    scene.add(sun);

    const hemi = new THREE.HemisphereLight(0x87CEEB, 0x3e7a3e, 0.6);
    scene.add(hemi);

    // 云（装饰）
    createClouds();

    window.addEventListener('resize', () => {
        camera.aspect = window.innerWidth / window.innerHeight;
        camera.updateProjectionMatrix();
        renderer.setSize(window.innerWidth, window.innerHeight);
    });
}

function createClouds() {
    const cloudGroup = new THREE.Group();
    const cloudMat = new THREE.MeshLambertMaterial({
        color: 0xffffff,
        transparent: true,
        opacity: 0.6,
        depthWrite: false,
    });

    for (let i = 0; i < 20; i++) {
        const size = 5 + Math.random() * 10;
        const cloud = new THREE.Mesh(new THREE.BoxGeometry(size, 0.8, size * 0.6), cloudMat);
        cloud.position.set(
            (Math.random() - 0.5) * 60,
            18 + Math.random() * 4,
            (Math.random() - 0.5) * 60
        );
        cloud.rotation.y = Math.random() * Math.PI * 2;
        cloudGroup.add(cloud);
    }
    scene.add(cloudGroup);
}

// ============================================================
//  控制
// ============================================================
function setupControls() {
    controls = new PointerLockControls(camera, document.body);

    blockerEl = document.getElementById('blocker');
    const playBtn = document.getElementById('playBtn');

    playBtn.addEventListener('click', () => {
        controls.lock();
    });

    controls.addEventListener('lock', () => {
        blockerEl.classList.add('hidden');
        crosshairEl.classList.add('show');
        toolbarEl.classList.add('show');
        fpsEl.classList.add('show');
        isLocked = true;
    });

    controls.addEventListener('unlock', () => {
        blockerEl.classList.remove('hidden');
        crosshairEl.classList.remove('show');
        toolbarEl.classList.remove('show');
        fpsEl.classList.remove('show');
        isLocked = false;
    });

    // 键盘
    document.addEventListener('keydown', (e) => {
        const k = e.key.toLowerCase();
        if (k === 'w') keys.w = true;
        if (k === 'a') keys.a = true;
        if (k === 's') keys.s = true;
        if (k === 'd') keys.d = true;
        if (k === 'shift') keys.shift = true;
        if (k === ' ') { e.preventDefault(); if (isLocked && onGround) { velocity.y = JUMP_SPEED; onGround = false; } }
        if (k === 'f' && isLocked) { document.fullscreenElement ? document.exitFullscreen() : document.body.requestFullscreen(); }
        const num = parseInt(k);
        if (num >= 1 && num <= 8) {
            selectedSlot = num - 1;
            updateToolbar();
        }
    });

    document.addEventListener('keyup', (e) => {
        const k = e.key.toLowerCase();
        if (k === 'w') keys.w = false;
        if (k === 'a') keys.a = false;
        if (k === 's') keys.s = false;
        if (k === 'd') keys.d = false;
        if (k === 'shift') keys.shift = false;
    });

    // 鼠标
    document.addEventListener('mousedown', (e) => {
        if (!isLocked) return;
        if (e.button === 0) onLeftClick();
        if (e.button === 2) onRightClick();
    });

    document.addEventListener('contextmenu', (e) => e.preventDefault());

    // 滚轮切换方块
    document.addEventListener('wheel', (e) => {
        if (!isLocked) return;
        if (e.deltaY > 0) selectedSlot = (selectedSlot + 1) % BLOCK_LIST.length;
        else selectedSlot = (selectedSlot - 1 + BLOCK_LIST.length) % BLOCK_LIST.length;
        updateToolbar();
    });
}

// ============================================================
//  UI
// ============================================================
function setupUI() {
    crosshairEl = document.getElementById('crosshair');
    toolbarEl = document.getElementById('toolbar');
    blockInfoEl = document.getElementById('block-info');
    fpsEl = document.getElementById('fps');

    // 工具栏
    BLOCK_LIST.forEach((block, i) => {
        const div = document.createElement('div');
        div.className = 'toolbar-item' + (i === 0 ? ' active' : '');
        div.dataset.index = i;

        const preview = document.createElement('div');
        preview.className = 'block-preview';
        // 生成预览纹理
        const mat = getBlockMaterial(block.id);
        let color = '#888';
        if (mat instanceof THREE.CanvasTexture) {
            preview.style.backgroundImage = `url(${mat.image.toDataURL()})`;
            preview.style.backgroundSize = 'cover';
        } else {
            // 用颜色
            const colors = {
                1: '#5a8f3c', 2: '#8B5E3C', 3: '#808080',
                4: '#6B4226', 5: '#2d5a1e', 6: '#C4A46B',
                7: '#B87333', 8: '#E8D5A3', 9: '#f0f0f0',
            };
            preview.style.backgroundColor = colors[block.id] || '#888';
        }
        div.appendChild(preview);

        const hint = document.createElement('span');
        hint.className = 'key-hint';
        hint.textContent = i + 1;
        div.appendChild(hint);

        div.addEventListener('click', () => {
            selectedSlot = i;
            updateToolbar();
        });

        toolbarEl.appendChild(div);
    });

    blockInfoEl.classList.add('show');
}

function updateToolbar() {
    const items = toolbarEl.querySelectorAll('.toolbar-item');
    items.forEach((item, i) => {
        item.classList.toggle('active', i === selectedSlot);
    });
}

// ============================================================
//  交互
// ============================================================
function getIntersection() {
    pointer.set(0, 0);
    raycaster.setFromCamera(pointer, camera);
    // 收集所有方块网格
    const targets = [];
    for (const [key, mesh] of meshes) {
        if (mesh && mesh.parent) targets.push(mesh);
    }
    const intersects = raycaster.intersectObjects(targets, false);
    return intersects.length > 0 ? intersects[0] : null;
}

function getBlockFromIntersect(intersect) {
    if (!intersect) return null;
    const mesh = intersect.object;
    if (mesh.isInstancedMesh) {
        const instanceId = intersect.instanceId;
        if (instanceId === undefined) return null;
        // 需要反向查找位置
        const dummy = new THREE.Object3D();
        mesh.getMatrixAt(instanceId, dummy.matrix);
        dummy.matrix.decompose(dummy.position, dummy.quaternion, dummy.scale);
        const bx = Math.round(dummy.position.x - 0.5 + W / 2);
        const by = Math.round(dummy.position.y - 0.5);
        const bz = Math.round(dummy.position.z - 0.5 + D / 2);
        return { x: bx, y: by, z: bz, type: getBlock(bx, by, bz) };
    } else {
        // 单个 mesh
        const pos = mesh.position;
        const bx = Math.round(pos.x - 0.5 + W / 2);
        const by = Math.round(pos.y - 0.5);
        const bz = Math.round(pos.z - 0.5 + D / 2);
        return { x: bx, y: by, z: bz, type: getBlock(bx, by, bz) };
    }
}

function onLeftClick() {
    const hit = getIntersection();
    if (!hit) return;
    const block = getBlockFromIntersect(hit);
    if (!block || block.type === BT.AIR) return;

    // 破坏方块
    setBlock(block.x, block.y, block.z, BT.AIR);
    rebuildWorld();
}

function onRightClick() {
    const hit = getIntersection();
    if (!hit) return;
    const block = getBlockFromIntersect(hit);
    if (!block || block.type === BT.AIR) return;

    // 计算放置位置（在点击面的外侧）
    const normal = hit.face.normal.clone();
    // 对于 InstancedMesh，需要转换法线方向
    if (hit.object.isInstancedMesh) {
        // 法线已经在世界空间
    } else {
        normal.transformDirection(hit.object.matrixWorld);
    }
    const nx = block.x + Math.round(normal.x);
    const ny = block.y + Math.round(normal.y);
    const nz = block.z + Math.round(normal.z);

    if (nx < 0 || nx >= W || ny < 0 || ny >= H || nz < 0 || nz >= D) return;
    if (getBlock(nx, ny, nz) !== BT.AIR) return;

    // 检查是否在玩家位置
    const px = Math.round(camera.position.x - 0.5 + W / 2);
    const py = Math.floor(camera.position.y - 0.3);
    const pz = Math.round(camera.position.z - 0.5 + D / 2);
    if (nx === px && ny === py && nz === pz) return;
    if (nx === px && (ny === py || ny === py + 1) && nz === pz) return;

    const blockType = BLOCK_LIST[selectedSlot].id;
    setBlock(nx, ny, nz, blockType);
    rebuildWorld();
}

// ============================================================
//  重建世界
// ============================================================
let rebuildQueued = false;

function rebuildWorld() {
    if (rebuildQueued) return;
    rebuildQueued = true;
    requestAnimationFrame(() => {
        rebuildQueued = false;
        // 保存旧网格引用
        const oldMeshes = new Map(meshes);
        meshes.clear();
        
        // 构建新网格（会添加到 scene）
        buildWorldMesh();

        // 移除旧网格
        for (const [key, mesh] of oldMeshes) {
            if (!meshes.has(key)) {
                scene.remove(mesh);
                mesh.geometry.dispose();
                if (Array.isArray(mesh.material)) mesh.material.forEach(m => m.dispose());
                else mesh.material.dispose();
            }
        }
    });
}

// ============================================================
//  物理 & 移动
// ============================================================
function updatePlayer(delta) {
    if (!isLocked) return;

    const speed = keys.shift ? WALK_SPEED * 0.5 : (keys.w || keys.s || keys.a || keys.d ? WALK_SPEED : 0);

    // 方向
    const forward = new THREE.Vector3();
    camera.getWorldDirection(forward);
    forward.y = 0;
    forward.normalize();

    const right = new THREE.Vector3();
    right.crossVectors(forward, new THREE.Vector3(0, 1, 0)).normalize();

    const moveVec = new THREE.Vector3();
    if (keys.w) moveVec.add(forward);
    if (keys.s) moveVec.sub(forward);
    if (keys.a) moveVec.sub(right);
    if (keys.d) moveVec.add(right);
    if (moveVec.length() > 0) {
        moveVec.normalize().multiplyScalar(speed * delta);
    }

    // 重力
    velocity.y += GRAVITY * delta;

    // 完整移动向量
    const totalMove = new THREE.Vector3(moveVec.x, velocity.y * delta, moveVec.z);

    // 碰撞检测 - 分别处理各轴
    const pos = camera.position.clone();

    for (const axis of ['x', 'y', 'z']) {
        const moveVal = totalMove[axis];
        if (Math.abs(moveVal) < 0.0001) continue;

        const testPos = pos.clone();
        testPos[axis] += moveVal;

        // 检查玩家碰撞箱
        const minX = Math.floor(testPos.x - P_RADIUS);
        const maxX = Math.floor(testPos.x + P_RADIUS);
        const minY = Math.floor(testPos.y - 0.1);
        const maxY = Math.floor(testPos.y + P_HEIGHT);
        const minZ = Math.floor(testPos.z - P_RADIUS);
        const maxZ = Math.floor(testPos.z + P_RADIUS);

        let collided = false;
        for (let bx = minX; bx <= maxX && !collided; bx++) {
            for (let bz = minZ; bz <= maxZ && !collided; bz++) {
                for (let by = minY; by <= maxY && !collided; by++) {
                    const wx = bx + W / 2;
                    const wz = bz + D / 2;
                    const blockType = getBlock(Math.floor(wx), by, Math.floor(wz));
                    if (blockType !== BT.AIR) {
                        // AABB 碰撞检测
                        const bMin = new THREE.Vector3(bx, by, bz);
                        const bMax = new THREE.Vector3(bx + 1, by + 1, bz + 1);
                        const pMin = new THREE.Vector3(testPos.x - P_RADIUS, testPos.y - 0.1, testPos.z - P_RADIUS);
                        const pMax = new THREE.Vector3(testPos.x + P_RADIUS, testPos.y + P_HEIGHT, testPos.z + P_RADIUS);

                        if (pMin.x < bMax.x && pMax.x > bMin.x &&
                            pMin.y < bMax.y && pMax.y > bMin.y &&
                            pMin.z < bMax.z && pMax.z > bMin.z) {
                            collided = true;
                            break;
                        }
                    }
                }
            }
        }

        if (!collided) {
            pos[axis] += moveVal;
        } else if (axis === 'y') {
            velocity.y = 0;
            onGround = moveVal < 0;
        }
    }

    camera.position.copy(pos);

    // 防止掉出世界
    if (camera.position.y < -5) {
        // 重生
        respawnPlayer();
    }
}

function respawnPlayer() {
    // 找到世界中心的地面
    const cx = Math.floor(W / 2), cz = Math.floor(D / 2);
    for (let y = H - 1; y >= 0; y--) {
        if (getBlock(cx, y, cz) !== BT.AIR) {
            camera.position.set(0, y + 2.5, 0);
            velocity.set(0, 0, 0);
            onGround = false;
            return;
        }
    }
}

// ============================================================
//  更新方块信息显示
// ============================================================
function updateBlockInfo() {
    if (!isLocked) {
        blockInfoEl.classList.remove('show');
        return;
    }

    const hit = getIntersection();
    if (hit) {
        const block = getBlockFromIntersect(hit);
        if (block && block.type !== BT.AIR) {
            const names = { 1: '草方块', 2: '泥土', 3: '石头', 4: '原木', 5: '树叶', 6: '木板', 7: '砖块', 8: '沙子', 9: '雪块', 10: '圆石', 11: '基岩' };
            const name = names[block.type] || '未知';
            blockInfoEl.querySelector('.block-name').textContent = name;
            blockInfoEl.querySelector('.block-coord').textContent = `${block.x}, ${block.y}, ${block.z}`;
            blockInfoEl.classList.add('show');
            return;
        }
    }
    blockInfoEl.classList.remove('show');
}

// ============================================================
//  主循环
// ============================================================
let frameCount = 0;
let fpsTime = 0;

function animate() {
    requestAnimationFrame(animate);

    const delta = Math.min(clock.getDelta(), 0.05);

    updatePlayer(delta);
    updateBlockInfo();

    renderer.render(scene, camera);

    // FPS
    frameCount++;
    fpsTime += delta;
    if (fpsTime >= 0.5) {
        fpsEl.textContent = `${Math.round(frameCount / fpsTime)} FPS`;
        frameCount = 0;
        fpsTime = 0;
    }
}

// ============================================================
//  启动
// ============================================================
function init() {
    initScene();
    setupUI();
    setupControls();

    // 生成世界
    generateWorld();
    buildWorldMesh();

    // 放置玩家
    respawnPlayer();

    // 启动循环
    animate();

    console.log('✅ MiniCraft 已启动！');
}

// 启动
init();

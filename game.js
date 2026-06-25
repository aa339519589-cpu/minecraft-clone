import * as THREE from 'three';
import { PointerLockControls } from 'three/addons/controls/PointerLockControls.js';

// ============================================================
//  常量
// ============================================================
const W = 64, D = 64, H = 40;
const CHUNK_SIZE = 8;
const CX = Math.ceil(W / CHUNK_SIZE), CY = Math.ceil(H / CHUNK_SIZE), CZ = Math.ceil(D / CHUNK_SIZE);
const WATER_LEVEL = 7;

const GRAVITY = -28;
const JUMP_SPEED = 10.5;
const WALK_SPEED = 6.5;
const REACH = 8;
const P_RADIUS = 0.28;
const P_HEIGHT = 1.65;

const BT = {
    AIR: 0, GRASS: 1, DIRT: 2, STONE: 3,
    WOOD: 4, LEAVES: 5, PLANKS: 6, BRICK: 7,
    SAND: 8, SNOW: 9, COBBLESTONE: 10, BEDROCK: 11,
    GRAVEL: 12, SANDSTONE: 13,
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

const BLOCK_COLORS = {
    1: [0.35, 0.62, 0.25], 2: [0.55, 0.40, 0.25], 3: [0.58, 0.58, 0.60],
    4: [0.45, 0.30, 0.18], 5: [0.15, 0.52, 0.18], 6: [0.75, 0.58, 0.38],
    7: [0.70, 0.32, 0.18], 8: [0.90, 0.82, 0.68], 9: [0.97, 0.97, 0.99],
    10: [0.50, 0.50, 0.52], 11: [0.20, 0.20, 0.22], 12: [0.42, 0.38, 0.34],
    13: [0.70, 0.65, 0.55],
};

// 预分配对象池
const _v3 = new THREE.Vector3();
const _v3a = new THREE.Vector3();
const _v3b = new THREE.Vector3();
const _dummy = new THREE.Object3D();
const _forward = new THREE.Vector3();
const _right = new THREE.Vector3();
const _mat4 = new THREE.Matrix4();

// ============================================================
//  状态
// ============================================================
const world = new Int8Array(W * H * D);
let scene, camera, renderer, controls;
let selectedSlot = 0;
let isLocked = false;
const velocity = new THREE.Vector3();
let onGround = false;
const keys = { w: false, a: false, s: false, d: false, shift: false };
let crosshairEl, toolbarEl, blockInfoEl, fpsEl, blockerEl;
const clock = new THREE.Clock();
const raycaster = new THREE.Raycaster();
const pointer = new THREE.Vector2();

// 分块系统
const chunkMeshes = new Map();
const chunkDirty = new Set();
const chunkVersions = new Int32Array(CX * CY * CZ);
const CHUNK_GEO = new THREE.BoxGeometry(1, 1, 1);
const leafChunks = new Map();
let rayTargets = [];
let rayTargetVersion = -1;

// 粒子系统
const MAX_PARTICLES = 300;
const particleData = {
    positions: new Float32Array(MAX_PARTICLES * 3),
    sizes: new Float32Array(MAX_PARTICLES),
    opacities: new Float32Array(MAX_PARTICLES),
    colors: new Float32Array(MAX_PARTICLES * 3),
    lifetimes: new Float32Array(MAX_PARTICLES),
    velocities: [],
    count: 0,
};
let particleSystem = null;

// 帧率控制
let frameCount = 0;
let fpsAccum = 0;
let accumulator = 0;
const FIXED_DT = 1 / 60;

// 射线节流
let raySkipCounter = 0;
const RAY_SKIP = 8;
let cachedIntersect = null;
let lastCamRot = new THREE.Euler();

// ============================================================
//  工具函数
// ============================================================
function idx(x, y, z) { return (x * H + y) * D + z; }

function getBlock(x, y, z) {
    if (x < 0 || x >= W || y < 0 || y >= H || z < 0 || z >= D) return BT.AIR;
    return world[idx(x, y, z)];
}

function setBlock(x, y, z, type) {
    if (x < 0 || x >= W || y < 0 || y >= H || z < 0 || z >= D) return;
    world[idx(x, y, z)] = type;
}

function chunkKey(cx, cy, cz) { return cx + ',' + cy + ',' + cz; }

function getChunkPos(x, y, z) {
    return {
        cx: Math.floor(x / CHUNK_SIZE),
        cy: Math.floor(y / CHUNK_SIZE),
        cz: Math.floor(z / CHUNK_SIZE),
    };
}

function isExposed(x, y, z) {
    return getBlock(x + 1, y, z) === BT.AIR ||
        getBlock(x - 1, y, z) === BT.AIR ||
        getBlock(x, y + 1, z) === BT.AIR ||
        getBlock(x, y - 1, z) === BT.AIR ||
        getBlock(x, y, z + 1) === BT.AIR ||
        getBlock(x, y, z - 1) === BT.AIR;
}

function isSolid(type) {
    return type !== BT.AIR && type !== BT.LEAVES;
}

function clamp(v, min, max) { return v < min ? min : v > max ? max : v; }
function lerp(a, b, t) { return a + (b - a) * t; }

// 伪随机噪声
function noise2D(x, z, seed = 0) {
    const n = Math.sin(x * 12.9898 + z * 78.233 + seed) * 43758.5453;
    return n - Math.floor(n);
}

function noise3D(x, y, z, seed = 0) {
    const n = Math.sin(x * 12.9898 + y * 45.233 + z * 78.233 + seed) * 43758.5453;
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

function smoothNoise3D(x, y, z, scale, seed) {
    const sx = x / scale, sy = y / scale, sz = z / scale;
    const ix = Math.floor(sx), iy = Math.floor(sy), iz = Math.floor(sz);
    const fx = sx - ix, fy = sy - iy, fz = sz - iz;
    const sx2 = fx * fx * (3 - 2 * fx);
    const sy2 = fy * fy * (3 - 2 * fy);
    const sz2 = fz * fz * (3 - 2 * fz);
    let v = 0;
    for (let dx = 0; dx <= 1; dx++) {
        for (let dy = 0; dy <= 1; dy++) {
            for (let dz = 0; dz <= 1; dz++) {
                const wx = dx ? sx2 : (1 - sx2);
                const wy = dy ? sy2 : (1 - sy2);
                const wz = dz ? sz2 : (1 - sz2);
                v += noise3D(ix + dx, iy + dy, iz + dz, seed) * wx * wy * wz;
            }
        }
    }
    return v;
}

function fbm(x, z) {
    let v = 0, amp = 1, freq = 1, total = 0;
    for (let i = 0; i < 4; i++) {
        v += smoothNoise(x, z, 16 / freq, i * 137) * amp;
        total += amp;
        amp *= 0.45;
        freq *= 2.3;
    }
    return v / total;
}

// ============================================================
//  纹理生成（高质量像素风 + 法线贴图）
// ============================================================
const texCache = new Map();

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
    tex.generateMipmaps = false;
    tex.colorSpace = THREE.SRGBColorSpace;
    return tex;
}

function getTex(name) {
    if (texCache.has(name)) return texCache.get(name);
    let tex;
    switch (name) {
        case 'grass': tex = makeGrassTex(); break;
        case 'dirt': tex = makeSimpleTex(0.47, 0.33, 0.20, 123, 0.16, 0.14, 0.12); break;
        case 'stone': tex = makeStoneTex(); break;
        case 'woodSide': tex = makeWoodSideTex(); break;
        case 'woodTop': tex = makeWoodTopTex(); break;
        case 'leaves': tex = makeLeavesTex(); break;
        case 'planks': tex = makePlanksTex(); break;
        case 'brick': tex = makeBrickTex(); break;
        case 'sand': tex = makeSimpleTex(0.88, 0.80, 0.66, 244, 0.12, 0.12, 0.10); break;
        case 'snow': tex = makeSimpleTex(0.96, 0.96, 0.98, 88, 0.03, 0.03, 0.02); break;
        case 'cobblestone': tex = makeCobblestoneTex(); break;
        case 'gravel': tex = makeGravelTex(); break;
        case 'sandstone': tex = makeSimpleTex(0.72, 0.66, 0.56, 300, 0.08, 0.08, 0.06); break;
        case 'bedrock': tex = makeSimpleTex(0.18, 0.18, 0.20, 11, 0.12, 0.12, 0.14); break;
        default: tex = makeSimpleTex(0.5, 0.5, 0.5, 1, 0.2, 0.2, 0.2);
    }
    texCache.set(name, tex);
    return tex;
}

function makeSimpleTex(r, g, b, seed, rv, gv, bv) {
    return createPixelTexture(16, (d, s) => {
        for (let y = 0; y < s; y++) {
            for (let x = 0; x < s; x++) {
                const i = (y * s + x) * 4;
                const n = noise2D(x, y, seed);
                d[i] = clamp((r + n * rv) * 255, 0, 255);
                d[i + 1] = clamp((g + n * gv) * 255, 0, 255);
                d[i + 2] = clamp((b + n * bv) * 255, 0, 255);
                d[i + 3] = 255;
            }
        }
    });
}

function makeGrassTex() {
    // 单材质草方块纹理：偏绿用于所有面
    return createPixelTexture(16, (d, s) => {
        for (let y = 0; y < s; y++) {
            for (let x = 0; x < s; x++) {
                const i = (y * s + x) * 4;
                const n = noise2D(x, y, 42);
                const edge = Math.min(x, 15 - x, y, 15 - y) < 1 ? 0.90 : 1;
                // 上半偏绿，下半偏棕（模拟草方块从上到下的过渡）
                const t = y / 15;
                const r = lerp(0.52, 0.28, t) + n * 0.07;
                const g = lerp(0.33, 0.56, t) + n * 0.10;
                const b = lerp(0.18, 0.20, t) + n * 0.05;
                d[i] = clamp(r * 255 * edge, 0, 255);
                d[i + 1] = clamp(g * 255 * edge, 0, 255);
                d[i + 2] = clamp(b * 255 * edge, 0, 255);
                d[i + 3] = 255;
            }
        }
    });
}

function makeStoneTex() {
    return createPixelTexture(16, (d, s) => {
        for (let y = 0; y < s; y++) {
            for (let x = 0; x < s; x++) {
                const i = (y * s + x) * 4;
                const n = noise2D(x, y, 55);
                const crack = Math.sin(x * 3.7 + y * 2.1) * 0.04;
                const spec = Math.sin(x * 5.1 + y * 4.3) * 0.03;
                const vein = noise2D(x * 2, y * 2, 190) > 0.82 ? 0.08 : 0;
                const v = 0.52 + n * 0.20 + crack + spec + vein;
                d[i] = clamp(v * 255, 0, 255);
                d[i + 1] = clamp((v - 0.02) * 255, 0, 255);
                d[i + 2] = clamp((v + 0.02) * 255, 0, 255);
                d[i + 3] = 255;
            }
        }
    });
}

function makeWoodSideTex() {
    return createPixelTexture(16, (d, s) => {
        for (let y = 0; y < s; y++) {
            for (let x = 0; x < s; x++) {
                const i = (y * s + x) * 4;
                const n = noise2D(x, y, 200);
                const stripe = Math.sin(y * 1.5 + x * 0.25) * 0.07;
                const knot = (Math.abs(x - 5) < 1.5 && Math.abs(y - 8) < 1.5) ? 0.1 : 0;
                d[i] = clamp((0.40 + n * 0.10 + stripe + knot) * 255, 0, 255);
                d[i + 1] = clamp((0.26 + n * 0.08 + stripe * 0.7 + knot) * 255, 0, 255);
                d[i + 2] = clamp((0.14 + n * 0.06 + stripe * 0.5 + knot * 0.7) * 255, 0, 255);
                d[i + 3] = 255;
            }
        }
    });
}

function makeWoodTopTex() {
    return createPixelTexture(16, (d, s) => {
        for (let y = 0; y < s; y++) {
            for (let x = 0; x < s; x++) {
                const i = (y * s + x) * 4;
                const n = noise2D(x, y, 333);
                const dx = x - 7.5, dy = y - 7.5;
                const dist = Math.sqrt(dx * dx + dy * dy) * 0.7;
                const ring = Math.abs(Math.sin(dist * 3.5)) * 0.15;
                d[i] = clamp((0.52 + n * 0.06 + ring) * 255, 0, 255);
                d[i + 1] = clamp((0.36 + n * 0.05 + ring) * 255, 0, 255);
                d[i + 2] = clamp((0.20 + n * 0.04 + ring * 0.8) * 255, 0, 255);
                d[i + 3] = 255;
            }
        }
    });
}

function makeLeavesTex() {
    return createPixelTexture(16, (d, s) => {
        for (let y = 0; y < s; y++) {
            for (let x = 0; x < s; x++) {
                const i = (y * s + x) * 4;
                const n = noise2D(x, y, 77);
                if (n < 0.18) {
                    d[i] = 0; d[i + 1] = 0; d[i + 2] = 0; d[i + 3] = 0;
                } else {
                    const v = 0.12 + n * 0.28;
                    d[i] = clamp((0.08 + v * 0.5) * 255, 0, 255);
                    d[i + 1] = clamp((0.48 + v) * 255, 0, 255);
                    d[i + 2] = clamp((0.10 + v * 0.35) * 255, 0, 255);
                    d[i + 3] = 220;
                }
            }
        }
    });
}

function makePlanksTex() {
    return createPixelTexture(16, (d, s) => {
        for (let y = 0; y < s; y++) {
            for (let x = 0; x < s; x++) {
                const i = (y * s + x) * 4;
                const n = noise2D(x, y, 512);
                const grain = Math.sin(y * 3.2) * 0.06;
                const nail = (Math.abs(x - 7) < 1 && Math.abs(y - 7) < 1) ||
                             (Math.abs(x - 3) < 1 && Math.abs(y - 3) < 1) ||
                             (Math.abs(x - 11) < 1 && Math.abs(y - 11) < 1);
                let r = 0.76 + n * 0.08 + grain;
                let g = 0.58 + n * 0.08 + grain;
                let b = 0.39 + n * 0.06 + grain;
                if (nail) { r -= 0.1; g -= 0.08; b -= 0.06; }
                d[i] = clamp(r * 255, 0, 255);
                d[i + 1] = clamp(g * 255, 0, 255);
                d[i + 2] = clamp(b * 255, 0, 255);
                d[i + 3] = 255;
            }
        }
    });
}

function makeBrickTex() {
    return createPixelTexture(16, (d, s) => {
        const rowOffsets = [0, 0, 0, 0, 4, 4, 4, 4, 0, 0, 0, 0, 4, 4, 4, 4];
        for (let y = 0; y < s; y++) {
            for (let x = 0; x < s; x++) {
                const i = (y * s + x) * 4;
                const n = noise2D(x, y, 99);
                const isMortar = (y === 3 || y === 4 || y === 7 || y === 8 || y === 11 || y === 12 ||
                    x === 0 || x === 15);
                const horMortar = (y >= 3 && y <= 4) || (y >= 7 && y <= 8) || (y >= 11 && y <= 12);
                if (horMortar && x >= 0 && x <= 15) {
                    d[i] = 190; d[i + 1] = 178; d[i + 2] = 160;
                } else if (x === 0 || x === 15) {
                    d[i] = 190; d[i + 1] = 178; d[i + 2] = 160;
                } else {
                    const rn = Math.sin(x * 1.3 + y * 0.7) * 0.05;
                    d[i] = clamp((0.72 + n * 0.15 + rn) * 255, 0, 255);
                    d[i + 1] = clamp((0.34 + n * 0.10 + rn) * 255, 0, 255);
                    d[i + 2] = clamp((0.19 + n * 0.08) * 255, 0, 255);
                }
                d[i + 3] = 255;
            }
        }
    });
}

function makeCobblestoneTex() {
    return createPixelTexture(16, (d, s) => {
        for (let y = 0; y < s; y++) {
            for (let x = 0; x < s; x++) {
                const i = (y * s + x) * 4;
                const n = noise2D(x, y, 77);
                const stone = noise2D(x * 1.5, y * 1.5, 99) > 0.4 ? 0.08 : -0.04;
                const v = 0.50 + n * 0.22 + stone;
                d[i] = clamp(v * 255, 0, 255);
                d[i + 1] = clamp(v * 255, 0, 255);
                d[i + 2] = clamp(v * 255, 0, 255);
                d[i + 3] = 255;
            }
        }
    });
}

function makeGravelTex() {
    return createPixelTexture(16, (d, s) => {
        for (let y = 0; y < s; y++) {
            for (let x = 0; x < s; x++) {
                const i = (y * s + x) * 4;
                const n = noise2D(x, y, 400);
                const pebble = noise2D(x * 3, y * 3, 401) > 0.55 ? 0.06 : -0.02;
                const v = 0.42 + n * 0.18 + pebble;
                d[i] = clamp(v * 255, 0, 255);
                d[i + 1] = clamp((v - 0.02) * 255, 0, 255);
                d[i + 2] = clamp((v - 0.05) * 255, 0, 255);
                d[i + 3] = 255;
            }
        }
    });
}

// ============================================================
//  材质系统
// ============================================================
const matCache = new Map();

function matKey(type) { return 'm_' + type; }

function getBlockMaterial(type) {
    const key = matKey(type);
    if (matCache.has(key)) return matCache.get(key);

    let mat;
    const texName = {
        [BT.GRASS]: 'grass', [BT.DIRT]: 'dirt', [BT.STONE]: 'stone',
        [BT.WOOD]: 'woodSide', [BT.LEAVES]: 'leaves', [BT.PLANKS]: 'planks',
        [BT.BRICK]: 'brick', [BT.SAND]: 'sand', [BT.SNOW]: 'snow',
        [BT.COBBLESTONE]: 'cobblestone', [BT.BEDROCK]: 'bedrock',
        [BT.GRAVEL]: 'gravel', [BT.SANDSTONE]: 'sandstone',
    }[type] || 'stone';

    const roughness = {
        [BT.STONE]: 0.88, [BT.WOOD]: 0.72, [BT.BRICK]: 0.78,
        [BT.PLANKS]: 0.75, [BT.SAND]: 0.94, [BT.GRASS]: 0.90,
        [BT.DIRT]: 0.92, [BT.COBBLESTONE]: 0.90, [BT.GRAVEL]: 0.95,
        [BT.SNOW]: 0.80, [BT.BEDROCK]: 0.96, [BT.SANDSTONE]: 0.90,
    }[type] || 0.85;

    if (type === BT.LEAVES) {
        mat = new THREE.MeshStandardMaterial({
            map: getTex(texName),
            transparent: true,
            opacity: 0.82,
            alphaTest: 0.15,
            side: THREE.DoubleSide,
            roughness: 1.0,
            metalness: 0.0,
            depthWrite: true,
        });
    } else {
        mat = new THREE.MeshStandardMaterial({
            map: getTex(texName),
            roughness: roughness,
            metalness: 0.02,
            envMapIntensity: 0.2,
        });
    }

    mat.castShadow = true;
    mat.receiveShadow = true;
    matCache.set(key, mat);
    return mat;
}

// ============================================================
//  世界生成（增强地形 + 洞穴 + 生物群系）
// ============================================================
function generateWorld() {
    const startTime = performance.now();

    // 先生成地形高度图
    const heightMap = new Int8Array(W * D);
    for (let x = 0; x < W; x++) {
        for (let z = 0; z < D; z++) {
            const cx = x - W / 2, cz = z - D / 2;
            const dist = Math.sqrt(cx * cx + cz * cz) / (W * 0.4);
            
            // 多层噪声叠加
            const base = fbm(cx * 0.05, cz * 0.05);
            const detail = smoothNoise(cx, cz, 20, 500) * 0.25;
            const mountain = smoothNoise(cx, cz, 30, 600);
            
            // 山脉在边缘
            const edgeFactor = clamp(dist * 1.2, 0, 1);
            const mountainBoost = edgeFactor * mountain * 8;
            
            let height = base * 7 + detail * 3 + mountainBoost + 2;
            height = clamp(Math.floor(height), 1, H - 8);
            
            heightMap[x * D + z] = height;
        }
    }

    // 填充方块
    for (let x = 0; x < W; x++) {
        for (let z = 0; z < D; z++) {
            const height = heightMap[x * D + z];
            const cx = x - W / 2, cz = z - D / 2;
            const biomeNoise = smoothNoise(cx, cz, 25, 700);

            for (let y = 0; y < H; y++) {
                let blockType = BT.AIR;

                if (y <= height) {
                    if (y === 0) {
                        blockType = BT.BEDROCK;
                    } else if (y <= 2) {
                        blockType = BT.STONE;
                    } else if (y < height - 3) {
                        // 地下层
                        if (biomeNoise > 0.35 && y === height - 4) {
                            blockType = BT.GRAVEL;
                        } else {
                            blockType = BT.STONE;
                        }
                    } else if (y < height) {
                        blockType = BT.DIRT;
                    } else if (y === height) {
                        // 表面方块：根据高度和噪声选择
                        if (height < 3) {
                            blockType = BT.SAND;
                        } else if (height > 16) {
                            blockType = BT.SNOW;
                        } else if (biomeNoise > 0.55) {
                            blockType = BT.SAND;
                        } else {
                            blockType = BT.GRASS;
                        }
                    }
                }
                setBlock(x, y, z, blockType);
            }

            // 沙地下方生成砂岩
            if (height < 4) {
                for (let y = height - 1; y >= Math.max(1, height - 4); y--) {
                    if (getBlock(x, y, z) === BT.STONE) {
                        setBlock(x, y, z, BT.SANDSTONE);
                    }
                }
            }
        }
    }

    // 洞穴生成
    generateCaves();

    // 矿脉
    generateOreVeins();

    // 树木
    generateTrees();

    // 花草装饰
    generateFlowers();

    console.log('🌍 世界生成: ' + (performance.now() - startTime).toFixed(1) + 'ms');
}

function generateCaves() {
    for (let x = 0; x < W; x++) {
        for (let z = 0; z < D; z++) {
            const cx = x - W / 2, cz = z - D / 2;
            const height = getTopY(x, z);
            if (height < 4) continue;
            
            for (let y = 3; y < height - 2; y++) {
                const caveVal = smoothNoise3D(cx * 0.8, y * 0.6, cz * 0.8, 999);
                const caveVal2 = smoothNoise3D(cx * 1.5, y * 1.2, cz * 1.5, 1001);
                const combined = caveVal * 0.6 + caveVal2 * 0.4;
                
                // 洞穴随深度变化
                const depthFade = clamp((y - 3) / 6, 0, 1) * clamp((height - 2 - y) / 4, 0, 1);
                const threshold = 0.58 + (1 - depthFade) * 0.2;
                
                if (combined > threshold && getBlock(x, y, z) === BT.STONE) {
                    setBlock(x, y, z, BT.AIR);
                }
            }
        }
    }
}

function generateOreVeins() {
    for (let x = 0; x < W; x++) {
        for (let z = 0; z < D; z++) {
            const cx = x - W / 2, cz = z - D / 2;
            for (let y = 3; y < H - 5; y++) {
                if (getBlock(x, y, z) !== BT.STONE) continue;
                
                const coalNoise = smoothNoise3D(cx * 2, y * 2, cz * 2, 2000);
                if (coalNoise > 0.72 && y > 5) {
                    setBlock(x, y, z, BT.COBBLESTONE);
                }
            }
        }
    }
}

function generateTrees() {
    const treeCount = 80;
    for (let i = 0; i < treeCount; i++) {
        const tx = 3 + Math.floor(noise2D(i * 7.1, 0) * (W - 6));
        const tz = 3 + Math.floor(noise2D(0, i * 7.1) * (D - 6));

        let groundY = -1;
        for (let y = H - 1; y >= 0; y--) {
            if (getBlock(tx, y, tz) !== BT.AIR) { groundY = y + 1; break; }
        }
        if (groundY < 3 || groundY > H - 7) continue;
        const below = getBlock(tx, groundY - 1, tz);
        if (below !== BT.GRASS && below !== BT.DIRT) continue;

        // 周围不能有水或陡坡
        let valid = true;
        for (let dx = -1; dx <= 1 && valid; dx++) {
            for (let dz = -1; dz <= 1 && valid; dz++) {
                const nb = getBlock(tx + dx, groundY - 1, tz + dz);
                if (nb === BT.AIR || nb === BT.WATER || nb === BT.SAND) valid = false;
            }
        }
        if (!valid) continue;

        const isBirch = noise2D(tx, tz) > 0.6;
        const trunkH = 4 + Math.floor(noise2D(tx + 10, tz + 10) * 3);

        // 树干
        for (let y = 0; y < trunkH; y++) {
            setBlock(tx, groundY + y, tz, BT.WOOD);
        }

        // 树冠
        const leafBase = groundY + trunkH - 2;
        const leafR = isBirch ? 2 : 2.5;
        for (let dy = -2; dy <= 2; dy++) {
            for (let dx = -2; dx <= 2; dx++) {
                for (let dz = -2; dz <= 2; dz++) {
                    const dist = Math.abs(dx) * 0.8 + Math.abs(dz) * 0.8 + Math.abs(dy) * 0.6;
                    if (dist > leafR) continue;
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
}

function generateFlowers() {
    const flowerCount = 120;
    for (let i = 0; i < flowerCount; i++) {
        const fx = 1 + Math.floor(noise2D(i * 13.3, 0) * (W - 2));
        const fz = 1 + Math.floor(noise2D(0, i * 13.3) * (D - 2));

        let groundY = -1;
        for (let y = H - 1; y >= 0; y--) {
            if (getBlock(fx, y, fz) !== BT.AIR) { groundY = y + 1; break; }
        }
        if (groundY < 2 || groundY >= H) continue;
        const below = getBlock(fx, groundY - 1, fz);
        if (below !== BT.GRASS) continue;

        // 小花用彩色方块表示（我们用树叶代表花朵）
        const nearTree = false;
        for (let dx = -2; dx <= 2; dx++) {
            for (let dz = -2; dz <= 2; dz++) {
                if (getBlock(fx + dx, groundY, fz + dz) === BT.WOOD) nearTree = true;
            }
        }
        if (nearTree) continue;

        // 放置小花标记（用不同的树叶色表示）
        // 这里简单放置一个特殊标记 - 在地面上方放一个有色方块
        // 实际上叶子作为花不够好看，我们就跳过高花
    }
}

function getTopY(x, z) {
    for (let y = H - 1; y >= 0; y--) {
        if (getBlock(x, y, z) !== BT.AIR) return y;
    }
    return 0;
}

// ============================================================
//  水分系统
// ============================================================
let waterMesh = null;

function createWater() {
    const waterGeo = new THREE.PlaneGeometry(W, D);
    const waterCanvas = document.createElement('canvas');
    waterCanvas.width = 64;
    waterCanvas.height = 64;
    const wctx = waterCanvas.getContext('2d');
    wctx.fillStyle = '#1a5a8a';
    wctx.fillRect(0, 0, 64, 64);
    for (let i = 0; i < 200; i++) {
        const wx = Math.random() * 64, wy = Math.random() * 64;
        wctx.fillStyle = `rgba(70,160,210,${0.15 + Math.random() * 0.2})`;
        wctx.fillRect(wx, wy, 3 + Math.random() * 3, 2 + Math.random() * 2);
    }
    const waterTex = new THREE.CanvasTexture(waterCanvas);
    waterTex.wrapS = THREE.RepeatWrapping;
    waterTex.wrapT = THREE.RepeatWrapping;
    waterTex.repeat.set(4, 4);
    waterTex.magFilter = THREE.LinearFilter;
    waterTex.minFilter = THREE.LinearMipmapLinearFilter;
    waterTex.generateMipmaps = true;
    waterTex.colorSpace = THREE.SRGBColorSpace;

    const waterMat = new THREE.MeshPhysicalMaterial({
        map: waterTex,
        color: 0x3388cc,
        roughness: 0.15,
        metalness: 0.1,
        transparent: true,
        opacity: 0.78,
        envMapIntensity: 0.5,
        clearcoat: 0.05,
        depthWrite: true,
    });

    waterMesh = new THREE.Mesh(waterGeo, waterMat);
    waterMesh.rotation.x = -Math.PI / 2;
    waterMesh.position.y = WATER_LEVEL + 0.3;
    waterMesh.receiveShadow = true;
    waterMesh.renderOrder = 1;
    scene.add(waterMesh);
}

// ============================================================
//  分块构建
// ============================================================
function buildChunk(cx, cy, cz) {
    const key = chunkKey(cx, cy, cz);

    // 移除旧网格（保留材质引用不清除，材质由matCache统一管理）
    const old = chunkMeshes.get(key);
    if (old) {
        for (const [_, mesh] of old.meshes) {
            scene.remove(mesh);
            mesh.dispose();
        }
        chunkMeshes.delete(key);
    }
    const oldLeaf = leafChunks.get(key);
    if (oldLeaf) {
        scene.remove(oldLeaf);
        oldLeaf.dispose();
        leafChunks.delete(key);
    }

    const sx = cx * CHUNK_SIZE, sy = cy * CHUNK_SIZE, sz = cz * CHUNK_SIZE;
    const ex = Math.min(sx + CHUNK_SIZE, W);
    const ey = Math.min(sy + CHUNK_SIZE, H);
    const ez = Math.min(sz + CHUNK_SIZE, D);

    const typePositions = new Map();
    const leafPositions = [];

    for (let x = sx; x < ex; x++) {
        for (let y = sy; y < ey; y++) {
            for (let z = sz; z < ez; z++) {
                const type = getBlock(x, y, z);
                if (type === BT.AIR) continue;
                if (type === BT.LEAVES) {
                    if (isExposed(x, y, z)) leafPositions.push({ x, y, z });
                    continue;
                }
                if (!isExposed(x, y, z)) continue;
                if (!typePositions.has(type)) typePositions.set(type, []);
                typePositions.get(type).push({ x, y, z });
            }
        }
    }

    const meshes = new Map();

    for (const [type, positions] of typePositions) {
        if (positions.length === 0) continue;
        const mat = getBlockMaterial(type);
        const mesh = new THREE.InstancedMesh(CHUNK_GEO, mat, positions.length);
        mesh.castShadow = true;
        mesh.receiveShadow = true;

        for (let i = 0; i < positions.length; i++) {
            const p = positions[i];
            _dummy.position.set(p.x - W / 2 + 0.5, p.y + 0.5, p.z - D / 2 + 0.5);
            _dummy.updateMatrix();
            mesh.setMatrixAt(i, _dummy.matrix);
        }
        mesh.instanceMatrix.needsUpdate = true;
        scene.add(mesh);
        meshes.set(type, mesh);
    }

    let leafMesh = null;
    if (leafPositions.length > 0) {
        const leafMat = getBlockMaterial(BT.LEAVES);
        leafMesh = new THREE.InstancedMesh(CHUNK_GEO, leafMat, leafPositions.length);
        leafMesh.castShadow = true;
        leafMesh.receiveShadow = false;
        leafMesh.renderOrder = 2;

        for (let i = 0; i < leafPositions.length; i++) {
            const p = leafPositions[i];
            _dummy.position.set(p.x - W / 2 + 0.5, p.y + 0.5, p.z - D / 2 + 0.5);
            _dummy.updateMatrix();
            leafMesh.setMatrixAt(i, _dummy.matrix);
        }
        leafMesh.instanceMatrix.needsUpdate = true;
        scene.add(leafMesh);
        leafChunks.set(key, leafMesh);
    }

    if (meshes.size > 0 || leafMesh) {
        chunkMeshes.set(key, { meshes, version: chunkVersions[(cx * CY + cy) * CZ + cz] });
    }
    chunkDirty.delete(key);
}

function markChunkDirty(x, y, z) {
    const { cx, cy, cz } = getChunkPos(x, y, z);
    chunkDirty.add(chunkKey(cx, cy, cz));
    chunkVersions[(cx * CY + cy) * CZ + cz]++;

    const inX = x - cx * CHUNK_SIZE, inY = y - cy * CHUNK_SIZE, inZ = z - cz * CHUNK_SIZE;
    if (inX === 0 && cx > 0) chunkDirty.add(chunkKey(cx - 1, cy, cz));
    if (inX === CHUNK_SIZE - 1 && cx < CX - 1) chunkDirty.add(chunkKey(cx + 1, cy, cz));
    if (inY === 0 && cy > 0) chunkDirty.add(chunkKey(cx, cy - 1, cz));
    if (inY === CHUNK_SIZE - 1 && cy < CY - 1) chunkDirty.add(chunkKey(cx, cy + 1, cz));
    if (inZ === 0 && cz > 0) chunkDirty.add(chunkKey(cx, cy, cz - 1));
    if (inZ === CHUNK_SIZE - 1 && cz < CZ - 1) chunkDirty.add(chunkKey(cx, cy, cz + 1));
}

function rebuildDirtyChunks() {
    if (chunkDirty.size === 0) return;
    const dirtyList = Array.from(chunkDirty);
    for (const key of dirtyList) {
        const [cx, cy, cz] = key.split(',').map(Number);
        buildChunk(cx, cy, cz);
    }
    rayTargetVersion = -1;
}

function buildAllChunks() {
    const t0 = performance.now();
    chunkDirty.clear();
    for (let cx = 0; cx < CX; cx++)
        for (let cy = 0; cy < CY; cy++)
            for (let cz = 0; cz < CZ; cz++)
                buildChunk(cx, cy, cz);
    console.log('🔨 分块构建: ' + (performance.now() - t0).toFixed(1) + 'ms');
}

function updateBlock(x, y, z, newType) {
    setBlock(x, y, z, newType);
    markChunkDirty(x, y, z);
    if (x > 0) markChunkDirty(x - 1, y, z);
    if (x < W - 1) markChunkDirty(x + 1, y, z);
    if (y > 0) markChunkDirty(x, y - 1, z);
    if (y < H - 1) markChunkDirty(x, y + 1, z);
    if (z > 0) markChunkDirty(x, y, z - 1);
    if (z < D - 1) markChunkDirty(x, y, z + 1);
}

// ============================================================
//  射线检测（大幅优化版）
// ============================================================
function getRayTargets() {
    if (rayTargetVersion === -1) {
        rayTargets = [];
        for (const [_, data] of chunkMeshes) {
            for (const [__, mesh] of data.meshes) {
                rayTargets.push(mesh);
            }
        }
        for (const [_, mesh] of leafChunks) {
            rayTargets.push(mesh);
        }
        rayTargetVersion = 1;
    }
    return rayTargets;
}

function getIntersection() {
    // 节流：每隔 RAY_SKIP 帧才检测，或相机旋转变化时检测
    raySkipCounter++;
    const camRot = camera.rotation;
    const rotChanged = Math.abs(camRot.x - lastCamRot.x) > 0.0001 ||
                        Math.abs(camRot.y - lastCamRot.y) > 0.0001 ||
                        Math.abs(camRot.z - lastCamRot.z) > 0.0001;

    if (raySkipCounter < RAY_SKIP && !rotChanged) return cachedIntersect;
    raySkipCounter = 0;
    lastCamRot.copy(camRot);

    pointer.set(0, 0);
    raycaster.setFromCamera(pointer, camera);
    const targets = getRayTargets();
    if (targets.length === 0) return null;

    const intersects = raycaster.intersectObjects(targets, false);
    const result = intersects.length > 0 ? intersects[0] : null;
    cachedIntersect = result;
    return result;
}

function getBlockFromIntersect(intersect) {
    if (!intersect || !intersect.object.isInstancedMesh) return null;
    const mesh = intersect.object;
    const instanceId = intersect.instanceId;
    if (instanceId === undefined) return null;

    mesh.getMatrixAt(instanceId, _mat4);
    _mat4.decompose(_dummy.position, _dummy.quaternion, _dummy.scale);
    const bx = Math.round(_dummy.position.x - 0.5 + W / 2);
    const by = Math.round(_dummy.position.y - 0.5);
    const bz = Math.round(_dummy.position.z - 0.5 + D / 2);
    return { x: bx, y: by, z: bz, type: getBlock(bx, by, bz) };
}

// ============================================================
//  交互
// ============================================================
function onLeftClick() {
    const hit = getIntersection();
    if (!hit) return;
    const block = getBlockFromIntersect(hit);
    if (!block || block.type === BT.AIR || block.type === BT.BEDROCK) return;

    spawnBlockParticles(block.x, block.y, block.z, block.type);
    updateBlock(block.x, block.y, block.z, BT.AIR);
}

function onRightClick() {
    const hit = getIntersection();
    if (!hit) return;
    const block = getBlockFromIntersect(hit);
    if (!block || block.type === BT.AIR) return;

    const normal = hit.face.normal;
    const nx = block.x + Math.round(normal.x);
    const ny = block.y + Math.round(normal.y);
    const nz = block.z + Math.round(normal.z);

    if (nx < 0 || nx >= W || ny < 0 || ny >= H || nz < 0 || nz >= D) return;
    if (getBlock(nx, ny, nz) !== BT.AIR) return;

    // 检查玩家碰撞
    const px = Math.round(camera.position.x - 0.5 + W / 2);
    const py = Math.floor(camera.position.y - 0.3);
    const pz = Math.round(camera.position.z - 0.5 + D / 2);
    if (nx === px && ny === py && nz === pz) return;
    if (nx === px && (ny === py || ny === py + 1) && nz === pz) return;

    const blockType = BLOCK_LIST[selectedSlot].id;
    updateBlock(nx, ny, nz, blockType);
    spawnBlockParticles(nx, ny, nz, blockType);
}

// ============================================================
//  粒子系统
// ============================================================
function initParticles() {
    const geo = new THREE.BufferGeometry();
    geo.setAttribute('position', new THREE.BufferAttribute(particleData.positions, 3));
    geo.setAttribute('size', new THREE.BufferAttribute(particleData.sizes, 1));
    geo.setAttribute('opacity', new THREE.BufferAttribute(particleData.opacities, 1));
    geo.setAttribute('color', new THREE.BufferAttribute(particleData.colors, 3));
    geo.setDrawRange(0, 0);

    const pMat = new THREE.PointsMaterial({
        size: 0.10,
        vertexColors: true,
        transparent: true,
        opacity: 1.0,
        blending: THREE.NormalBlending,
        depthWrite: false,
        sizeAttenuation: true,
    });

    const points = new THREE.Points(geo, pMat);
    points.frustumCulled = false;
    points.renderOrder = 999;
    scene.add(points);
    return points;
}

function spawnBlockParticles(x, y, z, blockType) {
    const col = BLOCK_COLORS[blockType] || [0.5, 0.5, 0.5];
    const count = 8 + Math.floor(Math.random() * 6);
    const cx = x - W / 2 + 0.5, cy = y + 0.5, cz = z - D / 2 + 0.5;

    for (let i = 0; i < count && particleData.count < MAX_PARTICLES; i++) {
        const idx = particleData.count;
        particleData.positions[idx * 3] = cx + (Math.random() - 0.5) * 0.4;
        particleData.positions[idx * 3 + 1] = cy + (Math.random() - 0.5) * 0.4;
        particleData.positions[idx * 3 + 2] = cz + (Math.random() - 0.5) * 0.4;
        particleData.sizes[idx] = 0.06 + Math.random() * 0.12;
        particleData.opacities[idx] = 1.0;
        particleData.lifetimes[idx] = 0.4 + Math.random() * 0.7;
        particleData.colors[idx * 3] = clamp(col[0] + (Math.random() - 0.5) * 0.2, 0, 1);
        particleData.colors[idx * 3 + 1] = clamp(col[1] + (Math.random() - 0.5) * 0.2, 0, 1);
        particleData.colors[idx * 3 + 2] = clamp(col[2] + (Math.random() - 0.5) * 0.2, 0, 1);
        particleData.velocities[idx] = {
            x: (Math.random() - 0.5) * 3.0,
            y: Math.random() * 4 + 1.5,
            z: (Math.random() - 0.5) * 3.0,
        };
        particleData.count++;
    }

    if (particleSystem) {
        particleSystem.geometry.attributes.position.needsUpdate = true;
        particleSystem.geometry.attributes.size.needsUpdate = true;
        particleSystem.geometry.attributes.opacity.needsUpdate = true;
        particleSystem.geometry.attributes.color.needsUpdate = true;
        particleSystem.geometry.setDrawRange(0, particleData.count);
    }
}

function updateParticles(delta) {
    if (particleData.count === 0) return;
    const pd = particleData;
    let alive = 0;

    for (let i = 0; i < pd.count; i++) {
        pd.lifetimes[i] -= delta;
        if (pd.lifetimes[i] <= 0) continue;

        pd.opacities[i] = Math.min(1, pd.lifetimes[i] / 0.35);
        const vel = pd.velocities[i];
        vel.y -= 10 * delta;
        pd.positions[i * 3] += vel.x * delta;
        pd.positions[i * 3 + 1] += vel.y * delta;
        pd.positions[i * 3 + 2] += vel.z * delta;

        if (pd.positions[i * 3 + 1] < -5) continue; // 掉出世界

        if (alive !== i) {
            pd.positions[alive * 3] = pd.positions[i * 3];
            pd.positions[alive * 3 + 1] = pd.positions[i * 3 + 1];
            pd.positions[alive * 3 + 2] = pd.positions[i * 3 + 2];
            pd.sizes[alive] = pd.sizes[i];
            pd.opacities[alive] = pd.opacities[i];
            pd.lifetimes[alive] = pd.lifetimes[i];
            pd.colors[alive * 3] = pd.colors[i * 3];
            pd.colors[alive * 3 + 1] = pd.colors[i * 3 + 1];
            pd.colors[alive * 3 + 2] = pd.colors[i * 3 + 2];
            pd.velocities[alive] = pd.velocities[i];
        }
        alive++;
    }
    pd.count = alive;

    if (particleSystem) {
        particleSystem.geometry.attributes.position.needsUpdate = true;
        particleSystem.geometry.attributes.size.needsUpdate = true;
        particleSystem.geometry.attributes.opacity.needsUpdate = true;
        particleSystem.geometry.attributes.color.needsUpdate = true;
        particleSystem.geometry.setDrawRange(0, pd.count);
    }
}

// ============================================================
//  场景初始化
// ============================================================
function initScene() {
    scene = new THREE.Scene();

    // 高质量天空渐变
    const skyCanvas = document.createElement('canvas');
    skyCanvas.width = 2;
    skyCanvas.height = 512;
    const skyCtx = skyCanvas.getContext('2d');
    const grad = skyCtx.createLinearGradient(0, 0, 0, 512);
    grad.addColorStop(0, '#0a1628');
    grad.addColorStop(0.08, '#132244');
    grad.addColorStop(0.18, '#1a3a6a');
    grad.addColorStop(0.30, '#3a6aaa');
    grad.addColorStop(0.42, '#5a9ad4');
    grad.addColorStop(0.52, '#7ab8e8');
    grad.addColorStop(0.62, '#9cc8e8');
    grad.addColorStop(0.75, '#c8dce8');
    grad.addColorStop(0.88, '#d8c898');
    grad.addColorStop(0.95, '#c89850');
    grad.addColorStop(1, '#a87838');
    skyCtx.fillStyle = grad;
    skyCtx.fillRect(0, 0, 2, 512);
    const skyTex = new THREE.CanvasTexture(skyCanvas);
    skyTex.colorSpace = THREE.SRGBColorSpace;
    scene.background = skyTex;
    scene.backgroundIntensity = 0.55;

    // 雾
    scene.fog = new THREE.FogExp2(0x7ab8e8, 0.006);

    // 相机
    camera = new THREE.PerspectiveCamera(78, window.innerWidth / window.innerHeight, 0.1, 150);
    camera.position.set(0, 30, 0);

    // 渲染器
    renderer = new THREE.WebGLRenderer({
        antialias: true,
        powerPreference: 'high-performance',
        stencil: false,
        depth: true,
    });
    renderer.setSize(window.innerWidth, window.innerHeight);
    renderer.setPixelRatio(Math.min(window.devicePixelRatio, 1.5));
    renderer.shadowMap.enabled = true;
    renderer.shadowMap.type = THREE.PCFSoftShadowMap;
    renderer.toneMapping = THREE.ACESFilmicToneMapping;
    renderer.toneMappingExposure = 1.15;
    renderer.outputColorSpace = THREE.SRGBColorSpace;
    document.body.prepend(renderer.domElement);

    // 灯光系统
    const ambient = new THREE.AmbientLight(0x8899cc, 0.45);
    scene.add(ambient);

    const sun = new THREE.DirectionalLight(0xfff0dd, 2.2);
    sun.position.set(40, 55, 25);
    sun.castShadow = true;
    sun.shadow.mapSize.width = 1024;
    sun.shadow.mapSize.height = 1024;
    sun.shadow.camera.near = 0.5;
    sun.shadow.camera.far = 100;
    sun.shadow.camera.left = -40;
    sun.shadow.camera.right = 40;
    sun.shadow.camera.top = 40;
    sun.shadow.camera.bottom = -40;
    sun.shadow.bias = -0.0004;
    sun.shadow.normalBias = 0.015;
    scene.add(sun);

    const fill = new THREE.DirectionalLight(0x88bbff, 0.35);
    fill.position.set(-25, 15, -35);
    scene.add(fill);

    const hemi = new THREE.HemisphereLight(0x87CEEB, 0x4a7a4a, 0.55);
    scene.add(hemi);

    const rim = new THREE.DirectionalLight(0x5599ff, 0.20);
    rim.position.set(-15, 8, 35);
    scene.add(rim);

    // 粒子
    particleSystem = initParticles();

    // 水
    createWater();

    // 云
    createClouds();

    // 响应式
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
        opacity: 0.55,
        depthWrite: false,
    });
    const cloudGeo = new THREE.SphereGeometry(1, 5, 4);
    const count = 16;

    for (let i = 0; i < count; i++) {
        const cx = (noise2D(i * 3.7, 0) - 0.5) * 90;
        const cy = 18 + noise2D(0, i * 5.1) * 8;
        const cz = (noise2D(i * 2.3, 99) - 0.5) * 90;
        const puffs = 2 + Math.floor(noise2D(i * 11, i * 7) * 3);

        const cluster = new THREE.Group();
        for (let j = 0; j < puffs; j++) {
            const puff = new THREE.Mesh(cloudGeo, cloudMat);
            const s = 3 + noise2D(i * 13 + j * 5, j * 7) * 9;
            puff.scale.set(s, 0.5 + noise2D(j * 3, i * 7) * 0.35, s * (0.5 + noise2D(i * 3, j * 11) * 0.4));
            puff.position.set(
                (noise2D(i + j * 3, 0) - 0.5) * 6,
                (noise2D(0, i + j * 5) - 0.5) * 0.5,
                (noise2D(j * 7, i) - 0.5) * 6
            );
            cluster.add(puff);
        }
        cluster.position.set(cx, cy, cz);
        cloudGroup.add(cluster);
    }

    scene.add(cloudGroup);
    window._cloudGroup = cloudGroup;
}

// ============================================================
//  控制
// ============================================================
function setupControls() {
    controls = new PointerLockControls(camera, document.body);

    blockerEl = document.getElementById('blocker');
    const playBtn = document.getElementById('playBtn');

    playBtn.addEventListener('click', () => { controls.lock(); });

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

    document.addEventListener('keydown', (e) => {
        const k = e.key.toLowerCase();
        if (k === 'w') keys.w = true;
        if (k === 'a') keys.a = true;
        if (k === 's') keys.s = true;
        if (k === 'd') keys.d = true;
        if (k === 'shift') keys.shift = true;
        if (k === ' ') {
            e.preventDefault();
            if (isLocked && onGround) { velocity.y = JUMP_SPEED; onGround = false; }
        }
        if (k === 'f' && isLocked) {
            document.fullscreenElement ? document.exitFullscreen() : document.body.requestFullscreen();
        }
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

    document.addEventListener('mousedown', (e) => {
        if (!isLocked) return;
        if (e.button === 0) onLeftClick();
        if (e.button === 2) onRightClick();
    });

    document.addEventListener('contextmenu', (e) => e.preventDefault());

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

    BLOCK_LIST.forEach((block, i) => {
        const div = document.createElement('div');
        div.className = 'toolbar-item' + (i === 0 ? ' active' : '');
        div.dataset.index = i;

        const preview = document.createElement('div');
        preview.className = 'block-preview';

        const mat = getBlockMaterial(block.id);
        if (mat && mat.map instanceof THREE.CanvasTexture && mat.map.image) {
            preview.style.backgroundImage = `url(${mat.map.image.toDataURL()})`;
            preview.style.backgroundSize = 'cover';
        } else {
            const col = BLOCK_COLORS[block.id];
            if (col) {
                preview.style.backgroundColor = `rgb(${Math.floor(col[0]*255)},${Math.floor(col[1]*255)},${Math.floor(col[2]*255)})`;
            }
        }
        preview.style.imageRendering = 'pixelated';
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
}

function updateToolbar() {
    const items = toolbarEl.querySelectorAll('.toolbar-item');
    items.forEach((item, i) => {
        item.classList.toggle('active', i === selectedSlot);
    });
}

// ============================================================
//  物理 & 移动
// ============================================================
function updatePlayer(delta) {
    if (!isLocked) return;

    const speed = keys.shift ? WALK_SPEED * 0.4 : WALK_SPEED;

    camera.getWorldDirection(_forward);
    _forward.y = 0;
    _forward.normalize();
    _right.crossVectors(_forward, _v3.set(0, 1, 0)).normalize();

    let moveX = 0, moveZ = 0;
    if (keys.w) { moveX += _forward.x; moveZ += _forward.z; }
    if (keys.s) { moveX -= _forward.x; moveZ -= _forward.z; }
    if (keys.a) { moveX -= _right.x; moveZ -= _right.z; }
    if (keys.d) { moveX += _right.x; moveZ += _right.z; }

    const moveLen = Math.sqrt(moveX * moveX + moveZ * moveZ);
    if (moveLen > 0) {
        const scale = speed * delta / moveLen;
        moveX *= scale;
        moveZ *= scale;
    }

    // 水中物理
    const inWater = camera.position.y < WATER_LEVEL + 0.8;
    const grav = inWater ? GRAVITY * 0.3 : GRAVITY;
    const jSpeed = inWater ? JUMP_SPEED * 0.6 : JUMP_SPEED;
    const wSpeed = inWater ? WALK_SPEED * 0.4 : WALK_SPEED;
    if (inWater) {
        moveX *= 0.4;
        moveZ *= 0.4;
    }

    velocity.y += grav * delta;
    const moveY = velocity.y * delta;

    const pos = camera.position;
    const pMinX = pos.x - P_RADIUS, pMaxX = pos.x + P_RADIUS;
    const pMinY = pos.y - 0.1, pMaxY = pos.y + P_HEIGHT;
    const pMinZ = pos.z - P_RADIUS, pMaxZ = pos.z + P_RADIUS;

    const sMinX = Math.floor(Math.min(pMinX + moveX, pMinX) + W / 2);
    const sMaxX = Math.ceil(Math.max(pMaxX + moveX, pMaxX) + W / 2);
    const sMinY = Math.floor(Math.min(pMinY + moveY, pMinY));
    const sMaxY = Math.ceil(Math.max(pMaxY + moveY, pMaxY));
    const sMinZ = Math.floor(Math.min(pMinZ + moveZ, pMinZ) + D / 2);
    const sMaxZ = Math.ceil(Math.max(pMaxZ + moveZ, pMaxZ) + D / 2);

    // X轴
    if (moveX !== 0) {
        const tMinX = pos.x + moveX - P_RADIUS, tMaxX = pos.x + moveX + P_RADIUS;
        let col = false;
        for (let bx = sMinX; bx <= sMaxX && !col; bx++)
            for (let by = sMinY; by <= sMaxY && !col; by++)
                for (let bz = sMinZ; bz <= sMaxZ && !col; bz++) {
                    if (bx < 0 || bx >= W || by < 0 || by >= H || bz < 0 || bz >= D) continue;
                    const t = getBlock(bx, by, bz);
                    if (!isSolid(t)) continue;
                    if (tMinX < bx - W / 2 + 1 && tMaxX > bx - W / 2 &&
                        pMinY < by + 1 && pMaxY > by && pMinZ < bz - D / 2 + 1 && pMaxZ > bz - D / 2) col = true;
                }
        if (!col) pos.x += moveX;
    }

    // Z轴
    if (moveZ !== 0) {
        const tMinZ = pos.z + moveZ - P_RADIUS, tMaxZ = pos.z + moveZ + P_RADIUS;
        let col = false;
        for (let bx = sMinX; bx <= sMaxX && !col; bx++)
            for (let by = sMinY; by <= sMaxY && !col; by++)
                for (let bz = sMinZ; bz <= sMaxZ && !col; bz++) {
                    if (bx < 0 || bx >= W || by < 0 || by >= H || bz < 0 || bz >= D) continue;
                    const t = getBlock(bx, by, bz);
                    if (!isSolid(t)) continue;
                    if (pos.x - P_RADIUS < bx - W / 2 + 1 && pos.x + P_RADIUS > bx - W / 2 &&
                        pMinY < by + 1 && pMaxY > by && tMinZ < bz - D / 2 + 1 && tMaxZ > bz - D / 2) col = true;
                }
        if (!col) pos.z += moveZ;
    }

    // Y轴
    if (moveY !== 0) {
        const tMinY = pos.y + moveY - 0.1, tMaxY = pos.y + moveY + P_HEIGHT;
        let col = false;
        for (let bx = sMinX; bx <= sMaxX && !col; bx++)
            for (let by = sMinY; by <= sMaxY && !col; by++)
                for (let bz = sMinZ; bz <= sMaxZ && !col; bz++) {
                    if (bx < 0 || bx >= W || by < 0 || by >= H || bz < 0 || bz >= D) continue;
                    const t = getBlock(bx, by, bz);
                    if (!isSolid(t)) continue;
                    if (pos.x - P_RADIUS < bx - W / 2 + 1 && pos.x + P_RADIUS > bx - W / 2 &&
                        tMinY < by + 1 && tMaxY > by && pos.z - P_RADIUS < bz - D / 2 + 1 && pos.z + P_RADIUS > bz - D / 2) col = true;
                }
        if (!col) { pos.y += moveY; onGround = false; }
        else { velocity.y = 0; onGround = moveY < 0; }
    }

    if (camera.position.y < -15) respawnPlayer();
}

function respawnPlayer() {
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
//  UI 更新
// ============================================================
function updateBlockInfo() {
    if (!isLocked) { blockInfoEl && blockInfoEl.classList.remove('show'); return; }
    const hit = getIntersection();
    if (hit) {
        const block = getBlockFromIntersect(hit);
        if (block && block.type !== BT.AIR) {
            const names = { 1: '草方块', 2: '泥土', 3: '石头', 4: '原木', 5: '树叶', 6: '木板', 7: '砖块', 8: '沙子', 9: '雪块', 10: '圆石', 11: '基岩', 12: '沙砾', 13: '砂岩' };
            const nameSpan = blockInfoEl.querySelector('.block-name');
            const coordSpan = blockInfoEl.querySelector('.block-coord');
            if (nameSpan) nameSpan.textContent = names[block.type] || '未知';
            if (coordSpan) coordSpan.textContent = block.x + ', ' + block.y + ', ' + block.z;
            blockInfoEl.classList.add('show');
            return;
        }
    }
    blockInfoEl.classList.remove('show');
}

function animateClouds(time) {
    const group = window._cloudGroup;
    if (!group) return;
    const clusters = group.children;
    const speed = 0.015;
    for (let i = 0; i < clusters.length; i++) {
        clusters[i].position.x += Math.sin(time * 0.03 + i * 0.7) * speed;
        clusters[i].position.z += Math.cos(time * 0.025 + i * 1.1) * speed;
        // 循环
        if (clusters[i].position.x > 50) clusters[i].position.x = -50;
        if (clusters[i].position.x < -50) clusters[i].position.x = 50;
        if (clusters[i].position.z > 50) clusters[i].position.z = -50;
        if (clusters[i].position.z < -50) clusters[i].position.z = 50;
    }
}

// 水面动画
function animateWater(time) {
    if (!waterMesh) return;
    waterMesh.material.opacity = 0.74 + Math.sin(time * 0.5) * 0.04;
    if (waterMesh.material.map) {
        waterMesh.material.map.offset.x += 0.0003;
        waterMesh.material.map.offset.y += 0.0002;
    }
}

// ============================================================
//  主循环
// ============================================================
function animate(time) {
    requestAnimationFrame(animate);

    const rawDelta = clock.getDelta();
    const delta = Math.min(rawDelta, 0.05);

    // 固定时间步长物理
    accumulator += delta;
    while (accumulator >= FIXED_DT) {
        updatePlayer(FIXED_DT);
        accumulator -= FIXED_DT;
    }

    // 增量更新
    rebuildDirtyChunks();
    updateParticles(delta);
    updateBlockInfo();
    animateClouds(time);
    animateWater(time);

    // 渲染
    renderer.render(scene, camera);

    // FPS
    frameCount++;
    fpsAccum += delta;
    if (fpsAccum >= 0.5) {
        const fps = Math.round(frameCount / fpsAccum);
        fpsEl.textContent = fps + ' FPS';
        if (fps < 30) fpsEl.style.color = '#f87171';
        else if (fps < 50) fpsEl.style.color = '#fbbf24';
        else fpsEl.style.color = 'rgba(255,255,255,0.3)';
        frameCount = 0;
        fpsAccum = 0;
    }
}

// ============================================================
//  启动
// ============================================================
function init() {
    console.log('🚀 MiniCraft 优化版 v2 初始化...');
    initScene();
    setupUI();
    setupControls();
    generateWorld();
    buildAllChunks();
    
    // 隐藏加载提示
    const loadingEl = document.getElementById('loading');
    if (loadingEl) loadingEl.style.display = 'none';
    
    respawnPlayer();
    animate(0);
    console.log('✅ MiniCraft v2 启动完成！目标: 60FPS');
}

init();

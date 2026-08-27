"use strict";

/* =========================================================================
   Math expression parser
   Tokenizes -> shunting-yard (with implicit multiplication) -> compiles
   to a fast evaluator fn(vars) => number, where vars = {x, y, ans, ...params}.
   Any identifier that isn't x, y, ans, a known constant, or a known
   function name is treated as a user parameter, resolved from `vars`.
   ========================================================================= */

const FUNCS = {
  sin: Math.sin, cos: Math.cos, tan: Math.tan,
  asin: Math.asin, acos: Math.acos, atan: Math.atan,
  sinh: Math.sinh, cosh: Math.cosh, tanh: Math.tanh,
  sqrt: Math.sqrt, cbrt: Math.cbrt, abs: Math.abs,
  log: Math.log10, log2: Math.log2, ln: Math.log,
  exp: Math.exp, floor: Math.floor, ceil: Math.ceil,
  round: Math.round, sign: Math.sign,
};

const CONSTS = { pi: Math.PI, e: Math.E };
const RESERVED_VARS = new Set(["x", "y", "t", "ans"]);

// Multi-letter names (functions, constants, "ans") are matched greedily,
// longest first, so "asin(x)" reads as arcsine rather than a*sin(x).
// Anything else is a single-character identifier: a variable (x, y) or a
// user parameter (a, b, k, ...) that gets its own slider automatically.
// This keeps "3xy^2" unambiguous as 3*x*y^2 via implicit multiplication.
const KNOWN_NAMES = [...Object.keys(FUNCS), ...Object.keys(CONSTS), "ans"]
  .sort((a, b) => b.length - a.length);

class MathError extends Error {}

function tokenize(src) {
  const tokens = [];
  let i = 0;
  const n = src.length;
  while (i < n) {
    const c = src[i];
    if (c === " " || c === "\t") { i++; continue; }
    if (/[0-9.]/.test(c)) {
      let j = i + 1;
      while (j < n && /[0-9.]/.test(src[j])) j++;
      if (j < n && (src[j] === "e" || src[j] === "E") && /[0-9+\-]/.test(src[j + 1] || "")) {
        j += 2;
        while (j < n && /[0-9]/.test(src[j])) j++;
      }
      const raw = src.slice(i, j);
      const val = parseFloat(raw);
      if (Number.isNaN(val)) throw new MathError(`Invalid number "${raw}"`);
      tokens.push({ type: "num", value: val });
      i = j;
      continue;
    }
    if (/[a-zA-Z]/.test(c)) {
      let matched = null;
      for (const name of KNOWN_NAMES) {
        if (src.slice(i, i + name.length).toLowerCase() === name) { matched = name; break; }
      }
      if (matched) {
        if (FUNCS[matched]) tokens.push({ type: "ident", kind: "func", name: matched });
        else if (matched === "ans") tokens.push({ type: "ident", kind: "value", name: "ans", reserved: true });
        else tokens.push({ type: "ident", kind: "value", name: matched });
        i += matched.length;
      } else {
        const name = c.toLowerCase();
        if (RESERVED_VARS.has(name)) tokens.push({ type: "ident", kind: "value", name, reserved: true });
        else tokens.push({ type: "ident", kind: "value", name, param: true });
        i += 1;
      }
      continue;
    }
    if ("+-*/^%(),".includes(c)) {
      const map = { "(": "(", ")": ")", ",": "," };
      if (map[c]) tokens.push({ type: c });
      else tokens.push({ type: "op", op: c });
      i++;
      continue;
    }
    throw new MathError(`Unexpected character "${c}"`);
  }
  return tokens;
}

function insertImplicitMultiplication(tokens) {
  const out = [];
  for (let k = 0; k < tokens.length; k++) {
    const t = tokens[k];
    if (out.length) {
      const prev = out[out.length - 1];
      const prevIsValue =
        prev.type === "num" ||
        prev.type === ")" ||
        (prev.type === "ident" && prev.kind === "value");
      const curStartsValue =
        t.type === "num" ||
        t.type === "(" ||
        t.type === "ident";
      if (prevIsValue && curStartsValue) {
        out.push({ type: "op", op: "*" });
      }
    }
    out.push(t);
  }
  return out;
}

const PRECEDENCE = { u: 4, "^": 5, "*": 3, "/": 3, "%": 3, "+": 2, "-": 2 };
const RIGHT_ASSOC = { "^": true, u: true };

function toRPN(tokens) {
  const output = [];
  const stack = [];

  const isValueEnd = (pt) =>
    pt && (pt.type === "num" || pt.type === ")" || (pt.type === "ident" && pt.kind === "value"));

  for (let k = 0; k < tokens.length; k++) {
    const t = tokens[k];
    if (t.type === "num") {
      output.push(t);
    } else if (t.type === "ident" && t.kind === "value") {
      output.push(t);
    } else if (t.type === "ident" && t.kind === "func") {
      stack.push(t);
    } else if (t.type === "(") {
      stack.push(t);
    } else if (t.type === ")") {
      while (stack.length && stack[stack.length - 1].type !== "(") {
        output.push(stack.pop());
      }
      if (!stack.length) throw new MathError("Mismatched parentheses");
      stack.pop();
      if (stack.length && stack[stack.length - 1].type === "ident" && stack[stack.length - 1].kind === "func") {
        output.push(stack.pop());
      }
    } else if (t.type === "op") {
      let op = t.op;
      if (op === "-" && !isValueEnd(tokens[k - 1])) {
        op = "u";
      } else if (op === "+" && !isValueEnd(tokens[k - 1])) {
        continue;
      }
      while (
        stack.length &&
        stack[stack.length - 1].type === "op" &&
        (
          PRECEDENCE[stack[stack.length - 1].op] > PRECEDENCE[op] ||
          (PRECEDENCE[stack[stack.length - 1].op] === PRECEDENCE[op] && !RIGHT_ASSOC[op])
        )
      ) {
        output.push(stack.pop());
      }
      stack.push({ type: "op", op });
    } else {
      throw new MathError("Unexpected token");
    }
  }
  while (stack.length) {
    const top = stack.pop();
    if (top.type === "(" || top.type === ")") throw new MathError("Mismatched parentheses");
    output.push(top);
  }
  return output;
}

function compileRPN(rpn) {
  return function evaluate(vars) {
    const stack = [];
    for (const t of rpn) {
      if (t.type === "num") {
        stack.push(t.value);
      } else if (t.type === "ident") {
        if (CONSTS[t.name] !== undefined) {
          stack.push(CONSTS[t.name]);
        } else if (FUNCS[t.name]) {
          if (stack.length < 1) throw new MathError("Invalid expression");
          const a = stack.pop();
          stack.push(FUNCS[t.name](a));
        } else {
          stack.push(vars[t.name]);
        }
      } else if (t.type === "op") {
        if (t.op === "u") {
          if (stack.length < 1) throw new MathError("Invalid expression");
          const a = stack.pop();
          stack.push(-a);
        } else {
          if (stack.length < 2) throw new MathError("Invalid expression");
          const b = stack.pop();
          const a = stack.pop();
          switch (t.op) {
            case "+": stack.push(a + b); break;
            case "-": stack.push(a - b); break;
            case "*": stack.push(a * b); break;
            case "/": stack.push(a / b); break;
            case "%": stack.push(a % b); break;
            case "^": stack.push(Math.pow(a, b)); break;
            default: throw new MathError(`Unknown operator "${t.op}"`);
          }
        }
      }
    }
    if (stack.length !== 1) throw new MathError("Invalid expression");
    return stack[0];
  };
}

/**
 * Parses a math expression into a fast evaluator fn(vars) => number.
 * @param {string} src
 * @param {string[]} allowVars - reserved variable names permitted here, e.g. ['x'] or ['x','y']
 * @returns {{fn: (vars:object)=>number, params: Set<string>}}
 */
function compileExpression(src, allowVars) {
  if (!src || !src.trim()) throw new MathError("Empty expression");
  const allow = new Set(allowVars || []);
  const tokens = insertImplicitMultiplication(tokenize(src));
  const params = new Set();
  let usesTime = false;
  for (const t of tokens) {
    if (t.type !== "ident" || t.kind !== "value") continue;
    if (t.reserved) {
      if (t.name === "t") usesTime = true;
      if (t.name !== "ans" && !allow.has(t.name)) {
        const hint = t.name === "y" ? " (z = f(x, y))" : "";
        throw new MathError(`"${t.name}" is not available here${hint}`);
      }
    } else if (t.param) {
      params.add(t.name);
    }
  }
  const rpn = toRPN(tokens);
  const fn = compileRPN(rpn);
  const smokeVars = { x: 1, y: 1, t: 0, ans: 0 };
  for (const p of params) smokeVars[p] = 1;
  fn(smokeVars);
  return { fn, params, usesTime };
}

/* =========================================================================
   Small vector / color helpers (used by the 3D engine)
   ========================================================================= */

const vSub = (a, b) => [a[0] - b[0], a[1] - b[1], a[2] - b[2]];
const vDot = (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
const vCross = (a, b) => [
  a[1] * b[2] - a[2] * b[1],
  a[2] * b[0] - a[0] * b[2],
  a[0] * b[1] - a[1] * b[0],
];
const vLen = (a) => Math.sqrt(vDot(a, a));
const vNorm = (a) => { const l = vLen(a) || 1e-9; return [a[0] / l, a[1] / l, a[2] / l]; };
const clamp = (v, lo, hi) => Math.min(hi, Math.max(lo, v));

function hexToRgb(hex) {
  const m = /^#?([0-9a-f]{2})([0-9a-f]{2})([0-9a-f]{2})$/i.exec(hex);
  if (!m) return [128, 128, 128];
  return [parseInt(m[1], 16), parseInt(m[2], 16), parseInt(m[3], 16)];
}
function shadeColor(hex, shade) {
  const [r, g, b] = hexToRgb(hex);
  return `rgb(${Math.round(r * shade)},${Math.round(g * shade)},${Math.round(b * shade)})`;
}

const LIGHT_DIR = vNorm([0.45, -0.35, 0.82]);

// A classic elevation-map palette (water -> lowland -> highland -> snow),
// used by the 3D "Topo view" so multivariable surfaces read like the
// topographic maps used in geology/geography.
const TOPO_STOPS = [
  [0.00, [40, 76, 130]],
  [0.22, [58, 120, 96]],
  [0.45, [138, 168, 74]],
  [0.68, [191, 156, 90]],
  [0.86, [140, 96, 66]],
  [1.00, [248, 248, 244]],
];
function elevationColor(t) {
  t = clamp(t, 0, 1);
  for (let i = 0; i < TOPO_STOPS.length - 1; i++) {
    const [t0, c0] = TOPO_STOPS[i];
    const [t1, c1] = TOPO_STOPS[i + 1];
    if (t <= t1 || i === TOPO_STOPS.length - 2) {
      const f = t1 > t0 ? (t - t0) / (t1 - t0) : 0;
      const r = c0[0] + (c1[0] - c0[0]) * f;
      const g = c0[1] + (c1[1] - c0[1]) * f;
      const b = c0[2] + (c1[2] - c0[2]) * f;
      return [r, g, b];
    }
  }
  return TOPO_STOPS[TOPO_STOPS.length - 1][1];
}

/* =========================================================================
   2D Graph engine
   ========================================================================= */

const PALETTE = [
  "#4f6df5", "#e5484d", "#12b886", "#f2994a",
  "#9b5de5", "#00b8d9", "#ff7ab6", "#8d6e63",
];

class Graph {
  constructor(canvas) {
    this.canvas = canvas;
    this.ctx = canvas.getContext("2d");
    this.centerX = 0;
    this.centerY = 0;
    this.scale = 60;
    this.dpr = Math.max(1, window.devicePixelRatio || 1);
    this.width = 0;
    this.height = 0;
    this.functions = [];
    this._resizeObserver = new ResizeObserver(() => this.resize());
    this._resizeObserver.observe(canvas);
    this.resize();
  }

  resize() {
    const rect = this.canvas.parentElement.getBoundingClientRect();
    this.width = Math.max(1, Math.floor(rect.width));
    this.height = Math.max(1, Math.floor(rect.height));
    this.dpr = Math.max(1, window.devicePixelRatio || 1);
    this.canvas.width = Math.floor(this.width * this.dpr);
    this.canvas.height = Math.floor(this.height * this.dpr);
    this.canvas.style.width = this.width + "px";
    this.canvas.style.height = this.height + "px";
    this.draw();
  }

  pxToWorldX(px) { return this.centerX + (px - this.width / 2) / this.scale; }
  pxToWorldY(py) { return this.centerY - (py - this.height / 2) / this.scale; }
  worldToPxX(wx) { return this.width / 2 + (wx - this.centerX) * this.scale; }
  worldToPxY(wy) { return this.height / 2 - (wy - this.centerY) * this.scale; }

  panByPixels(dx, dy) {
    this.centerX -= dx / this.scale;
    this.centerY += dy / this.scale;
    this.draw();
  }

  zoomAt(px, py, factor) {
    const wx = this.pxToWorldX(px);
    const wy = this.pxToWorldY(py);
    this.scale = Math.min(200000, Math.max(0.5, this.scale * factor));
    const newPxX = this.worldToPxX(wx);
    const newPxY = this.worldToPxY(wy);
    this.centerX += (newPxX - px) / this.scale;
    this.centerY -= (newPxY - py) / this.scale;
    this.draw();
  }

  resetView() {
    this.centerX = 0;
    this.centerY = 0;
    this.scale = 60;
    this.draw();
  }

  static niceStep(target) {
    const exp = Math.floor(Math.log10(target));
    const base = Math.pow(10, exp);
    const fraction = target / base;
    let niceFraction;
    if (fraction < 1.5) niceFraction = 1;
    else if (fraction < 3.5) niceFraction = 2;
    else if (fraction < 7.5) niceFraction = 5;
    else niceFraction = 10;
    return niceFraction * base;
  }

  draw() {
    const { ctx, width, height, dpr } = this;
    ctx.save();
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, width, height);

    const styles = getComputedStyle(document.body);
    const gridMinor = styles.getPropertyValue("--grid-minor").trim();
    const gridMajor = styles.getPropertyValue("--grid-major").trim();
    const axisColor = styles.getPropertyValue("--axis").trim();
    const textColor = styles.getPropertyValue("--text-dim").trim();

    const stepMajor = Graph.niceStep(90 / this.scale);
    const stepMinor = stepMajor / 5;

    ctx.strokeStyle = gridMinor;
    ctx.lineWidth = 1;
    this._drawGridLines(stepMinor);

    ctx.strokeStyle = gridMajor;
    ctx.lineWidth = 1;
    this._drawGridLines(stepMajor);

    const axisXpx = this.worldToPxX(0);
    const axisYpx = this.worldToPxY(0);
    ctx.strokeStyle = axisColor;
    ctx.lineWidth = 1.6;
    ctx.beginPath();
    if (axisYpx >= -5 && axisYpx <= height + 5) {
      ctx.moveTo(0, axisYpx); ctx.lineTo(width, axisYpx);
    }
    if (axisXpx >= -5 && axisXpx <= width + 5) {
      ctx.moveTo(axisXpx, 0); ctx.lineTo(axisXpx, height);
    }
    ctx.stroke();

    ctx.fillStyle = textColor;
    ctx.font = "11px -apple-system, sans-serif";
    ctx.textBaseline = "top";
    const labelY = Math.min(Math.max(axisYpx + 4, 2), height - 14);
    for (let v = Math.ceil(this.pxToWorldX(0) / stepMajor) * stepMajor; v <= this.pxToWorldX(width); v += stepMajor) {
      if (Math.abs(v) < stepMajor / 1000) continue;
      const px = this.worldToPxX(v);
      if (px < 0 || px > width) continue;
      ctx.fillText(formatTick(v), px + 3, labelY);
    }
    ctx.textBaseline = "middle";
    const labelX = Math.min(Math.max(axisXpx + 4, 2), width - 30);
    for (let v = Math.ceil(this.pxToWorldY(height) / stepMajor) * stepMajor; v <= this.pxToWorldY(0); v += stepMajor) {
      if (Math.abs(v) < stepMajor / 1000) continue;
      const py = this.worldToPxY(v);
      if (py < 0 || py > height) continue;
      ctx.fillText(formatTick(v), labelX, py);
    }

    for (const f of this.functions) {
      if (!f.enabled || !f.fn) continue;
      this._drawFunction(f);
    }

    ctx.restore();
  }

  _drawGridLines(step) {
    if (!isFinite(step) || step <= 0) return;
    const { ctx, width, height } = this;
    const xMin = this.pxToWorldX(0);
    const xMax = this.pxToWorldX(width);
    const yMin = this.pxToWorldY(height);
    const yMax = this.pxToWorldY(0);
    ctx.beginPath();
    let start = Math.floor(xMin / step) * step;
    for (let v = start; v <= xMax; v += step) {
      const px = Math.round(this.worldToPxX(v)) + 0.5;
      ctx.moveTo(px, 0);
      ctx.lineTo(px, height);
    }
    start = Math.floor(yMin / step) * step;
    for (let v = start; v <= yMax; v += step) {
      const py = Math.round(this.worldToPxY(v)) + 0.5;
      ctx.moveTo(0, py);
      ctx.lineTo(width, py);
    }
    ctx.stroke();
  }

  _drawFunction(f) {
    const { ctx, width, height } = this;
    ctx.save();
    ctx.strokeStyle = f.color;
    ctx.lineWidth = 2.4;
    ctx.lineJoin = "round";
    ctx.lineCap = "round";
    ctx.beginPath();

    let started = false;
    let prevY = null;
    const jumpThreshold = height * 4;

    for (let px = 0; px <= width; px++) {
      const wx = this.pxToWorldX(px);
      let wy;
      try {
        wy = f.fn(buildVars(wx, undefined));
      } catch (e) {
        wy = NaN;
      }
      if (!isFinite(wy)) {
        started = false;
        prevY = null;
        continue;
      }
      const py = this.worldToPxY(wy);

      if (prevY !== null && Math.abs(py - prevY) > jumpThreshold) {
        started = false;
      }

      if (!started) {
        ctx.moveTo(px, py);
        started = true;
      } else {
        ctx.lineTo(px, py);
      }
      prevY = py;
    }
    ctx.stroke();
    ctx.restore();
  }

  findNearest(px, py) {
    let best = null;
    for (const f of this.functions) {
      if (!f.enabled || !f.fn) continue;
      const wx = this.pxToWorldX(px);
      let wy;
      try { wy = f.fn(buildVars(wx, undefined)); } catch (e) { continue; }
      if (!isFinite(wy)) continue;
      const fpy = this.worldToPxY(wy);
      const d = Math.abs(fpy - py);
      if (!best || d < best.dist) {
        best = { wx, wy, dist: d, color: f.color, expr: f.expr };
      }
    }
    return best;
  }
}

function formatTick(v) {
  const rounded = Math.round(v * 1e9) / 1e9;
  if (Math.abs(rounded) >= 10000 || (Math.abs(rounded) < 0.001 && rounded !== 0)) {
    return rounded.toExponential(1);
  }
  return String(rounded);
}

/* =========================================================================
   3D Graph engine
   Orbit camera, painter's-algorithm depth sort, no external libraries.
   ========================================================================= */

class Graph3D {
  constructor(canvas) {
    this.canvas = canvas;
    this.ctx = canvas.getContext("2d");
    this.azimuth = -0.7;
    this.elevation = 0.55;
    this.distance = 16;
    this.domain = 5;
    this.focal = 2.4;
    this.dpr = Math.max(1, window.devicePixelRatio || 1);
    this.width = 0;
    this.height = 0;
    this.functions = [];
    this._quality = "high";
    this._cachedGrids = [];
    this._zScale = 1;
    this._zMin = 0;
    this._zMax = 0;
    this.topo = false;
    this._preTopoView = null;
    this._resizeObserver = new ResizeObserver(() => this.resize());
    this._resizeObserver.observe(canvas);
    this.resize();
  }

  resize() {
    const rect = this.canvas.parentElement.getBoundingClientRect();
    this.width = Math.max(1, Math.floor(rect.width));
    this.height = Math.max(1, Math.floor(rect.height));
    this.dpr = Math.max(1, window.devicePixelRatio || 1);
    this.canvas.width = Math.floor(this.width * this.dpr);
    this.canvas.height = Math.floor(this.height * this.dpr);
    this.canvas.style.width = this.width + "px";
    this.canvas.style.height = this.height + "px";
    this.recompute();
    this.render();
  }

  setQuality(q) { this._quality = q; }
  divisions() { return this._quality === "low" ? 18 : 42; }

  resetView() {
    this.azimuth = -0.7;
    this.elevation = 0.55;
    this.distance = 16;
    this.render();
  }

  /** Resamples every visible surface over the current domain. Call when
   *  expressions, parameters, domain, or visibility change (not on orbit).
   *  Pass {rescale:false} (e.g. while dragging a parameter slider) to keep
   *  the current vertical scale fixed, so amplitude changes are visible
   *  instead of being normalized away. */
  recompute(opts = {}) {
    const rescale = opts.rescale !== false;
    const N = this.divisions();
    const domain = this.domain;
    let zMin = Infinity, zMax = -Infinity;
    const grids = [];
    for (const f of this.functions) {
      if (!f.enabled || !f.fn) continue;
      const pts = [];
      for (let i = 0; i <= N; i++) {
        const wx = -domain + (2 * domain * i) / N;
        const row = [];
        for (let j = 0; j <= N; j++) {
          const wy = -domain + (2 * domain * j) / N;
          let wz;
          try { wz = f.fn(buildVars(wx, wy)); } catch (e) { wz = NaN; }
          const valid = isFinite(wz);
          if (valid) {
            if (wz < zMin) zMin = wz;
            if (wz > zMax) zMax = wz;
          }
          row.push({ x: wx, y: wy, z: wz, valid });
        }
        pts.push(row);
      }
      grids.push({ f, pts });
    }
    this._cachedGrids = grids;
    if (isFinite(zMin) && isFinite(zMax)) {
      this._zMin = zMin;
      this._zMax = zMax;
    }
    if (rescale || !isFinite(this._zScale)) {
      const maxAbsZ = Math.max(Math.abs(zMin), Math.abs(zMax), 1e-6);
      let zScale = domain / maxAbsZ;
      if (!isFinite(zScale) || zScale <= 0) zScale = 1;
      this._zScale = Math.min(zScale, 1000);
    }
  }

  /** Toggles the elevation-map coloring + a near-top-down camera. Remembers
   *  the orbit angle you were at so turning it off restores your view. */
  setTopo(on) {
    if (on === this.topo) return;
    this.topo = on;
    if (on) {
      this._preTopoView = { azimuth: this.azimuth, elevation: this.elevation };
      this.azimuth = -Math.PI / 2;
      this.elevation = 1.5;
    } else if (this._preTopoView) {
      this.azimuth = this._preTopoView.azimuth;
      this.elevation = this._preTopoView.elevation;
    }
    this.render();
  }

  _camera() {
    const theta = this.azimuth, phi = this.elevation, r = this.distance;
    const pos = [
      r * Math.cos(phi) * Math.cos(theta),
      r * Math.cos(phi) * Math.sin(theta),
      r * Math.sin(phi),
    ];
    const forward = vNorm([-pos[0], -pos[1], -pos[2]]);
    const worldUp = [0, 0, 1];
    let right = vNorm(vCross(forward, worldUp));
    if (!isFinite(right[0]) || vLen(right) < 1e-6) right = [1, 0, 0];
    const up = vCross(right, forward);
    return { pos, right, up, forward };
  }

  _project(p, cam) {
    const rel = vSub(p, cam.pos);
    const vz = vDot(rel, cam.forward);
    if (vz <= 0.05) return null;
    const scale = (this.height / 2) * this.focal / vz;
    const vx = vDot(rel, cam.right);
    const vy = vDot(rel, cam.up);
    return { x: this.width / 2 + vx * scale, y: this.height / 2 - vy * scale, depth: vz };
  }

  render() {
    const { ctx, width, height, dpr } = this;
    ctx.save();
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, width, height);

    const styles = getComputedStyle(document.body);
    const gridColor = styles.getPropertyValue("--grid-major").trim();
    const axisColor = styles.getPropertyValue("--axis").trim();
    const textColor = styles.getPropertyValue("--text-dim").trim();

    const cam = this._camera();
    const domain = this.domain;
    const reach = domain * 1.18;
    const drawables = [];

    // Floor grid (z = 0 plane)
    const step = Graph.niceStep(domain / 4.5);
    for (let v = -Math.floor(domain / step) * step; v <= domain + 1e-9; v += step) {
      drawables.push({ type: "line", pts: [[v, -domain, 0], [v, domain, 0]], color: gridColor, width: 1 });
      drawables.push({ type: "line", pts: [[-domain, v, 0], [domain, v, 0]], color: gridColor, width: 1 });
    }

    // Axes
    drawables.push({ type: "line", pts: [[-reach, 0, 0], [reach, 0, 0]], color: axisColor, width: 1.6 });
    drawables.push({ type: "line", pts: [[0, -reach, 0], [0, reach, 0]], color: axisColor, width: 1.6 });
    drawables.push({ type: "line", pts: [[0, 0, -reach], [0, 0, reach]], color: axisColor, width: 1.6 });

    // Surfaces
    const zRange = Math.max(this._zMax - this._zMin, 1e-6);
    for (const { f, pts } of this._cachedGrids) {
      const N = pts.length - 1;
      for (let i = 0; i < N; i++) {
        for (let j = 0; j < N; j++) {
          const p00 = pts[i][j], p10 = pts[i + 1][j], p11 = pts[i + 1][j + 1], p01 = pts[i][j + 1];
          if (!p00.valid || !p10.valid || !p11.valid || !p01.valid) continue;
          const c0 = [p00.x, p00.y, p00.z * this._zScale];
          const c1 = [p10.x, p10.y, p10.z * this._zScale];
          const c2 = [p11.x, p11.y, p11.z * this._zScale];
          const c3 = [p01.x, p01.y, p01.z * this._zScale];
          const normal = vNorm(vCross(vSub(c1, c0), vSub(c3, c0)));
          const light = Math.max(0, vDot(normal, LIGHT_DIR));
          let color, strokeColor;
          if (this.topo) {
            const avgZ = (p00.z + p10.z + p11.z + p01.z) / 4;
            const t = (avgZ - this._zMin) / zRange;
            const [r, g, b] = elevationColor(t);
            const shade = clamp(0.75 + 0.35 * light, 0.7, 1.15);
            color = `rgb(${Math.min(255, r * shade) | 0},${Math.min(255, g * shade) | 0},${Math.min(255, b * shade) | 0})`;
            strokeColor = `rgba(0,0,0,0.12)`;
          } else {
            const shade = clamp(0.4 + 0.6 * light, 0.35, 1.0);
            color = shadeColor(f.color, shade);
            strokeColor = shadeColor(f.color, shade * 0.55);
          }
          drawables.push({ type: "quad", pts: [c0, c1, c2, c3], color, strokeColor });
        }
      }
    }

    const projected = [];
    for (const d of drawables) {
      const screen = [];
      let depthSum = 0;
      let ok = true;
      for (const p of d.pts) {
        const s = this._project(p, cam);
        if (!s) { ok = false; break; }
        screen.push(s);
        depthSum += s.depth;
      }
      if (!ok) continue;
      projected.push({ ...d, screen, depth: depthSum / d.pts.length });
    }
    projected.sort((a, b) => b.depth - a.depth);

    for (const d of projected) {
      if (d.type === "quad") {
        ctx.beginPath();
        ctx.moveTo(d.screen[0].x, d.screen[0].y);
        for (let k = 1; k < d.screen.length; k++) ctx.lineTo(d.screen[k].x, d.screen[k].y);
        ctx.closePath();
        ctx.fillStyle = d.color;
        ctx.fill();
        ctx.strokeStyle = d.strokeColor;
        ctx.lineWidth = 0.6;
        ctx.stroke();
      } else {
        ctx.beginPath();
        ctx.moveTo(d.screen[0].x, d.screen[0].y);
        ctx.lineTo(d.screen[1].x, d.screen[1].y);
        ctx.strokeStyle = d.color;
        ctx.lineWidth = d.width;
        ctx.stroke();
      }
    }

    // Axis labels, drawn last so they stay legible
    ctx.font = "12px -apple-system, sans-serif";
    ctx.fillStyle = textColor;
    const labelDefs = [
      { p: [reach * 1.04, 0, 0], text: "x" },
      { p: [0, reach * 1.04, 0], text: "y" },
      { p: [0, 0, reach * 1.04], text: "z" },
    ];
    for (const l of labelDefs) {
      const s = this._project(l.p, cam);
      if (s) ctx.fillText(l.text, s.x - 3, s.y - 3);
    }

    ctx.restore();
  }
}

/* =========================================================================
   Parametric curve engine (2D)
   Reuses Graph's pan/zoom/grid math; draws x(t), y(t) traced paths instead
   of y = f(x). Each curve also shows a live tracing dot driven by the
   shared animation clock, so the curve's own t-range is independent of
   the global "t" used as a live parameter in 2D/3D formulas.
   ========================================================================= */

class ParametricGraph extends Graph {
  constructor(canvas) {
    // Graph's constructor calls this.resize() -> this.draw() before we can
    // set fields here, so draw() must tolerate this.curves being unset yet.
    super(canvas);
    this.curves = [];
    this.draw();
  }

  draw() {
    const { ctx, width, height, dpr } = this;
    ctx.save();
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, width, height);

    const styles = getComputedStyle(document.body);
    const gridMinor = styles.getPropertyValue("--grid-minor").trim();
    const gridMajor = styles.getPropertyValue("--grid-major").trim();
    const axisColor = styles.getPropertyValue("--axis").trim();
    const textColor = styles.getPropertyValue("--text-dim").trim();

    const stepMajor = Graph.niceStep(90 / this.scale);
    const stepMinor = stepMajor / 5;
    ctx.strokeStyle = gridMinor;
    ctx.lineWidth = 1;
    this._drawGridLines(stepMinor);
    ctx.strokeStyle = gridMajor;
    ctx.lineWidth = 1;
    this._drawGridLines(stepMajor);

    const axisXpx = this.worldToPxX(0);
    const axisYpx = this.worldToPxY(0);
    ctx.strokeStyle = axisColor;
    ctx.lineWidth = 1.6;
    ctx.beginPath();
    if (axisYpx >= -5 && axisYpx <= height + 5) { ctx.moveTo(0, axisYpx); ctx.lineTo(width, axisYpx); }
    if (axisXpx >= -5 && axisXpx <= width + 5) { ctx.moveTo(axisXpx, 0); ctx.lineTo(axisXpx, height); }
    ctx.stroke();

    ctx.fillStyle = textColor;
    ctx.font = "11px -apple-system, sans-serif";
    ctx.textBaseline = "top";
    const labelY = Math.min(Math.max(axisYpx + 4, 2), height - 14);
    for (let v = Math.ceil(this.pxToWorldX(0) / stepMajor) * stepMajor; v <= this.pxToWorldX(width); v += stepMajor) {
      if (Math.abs(v) < stepMajor / 1000) continue;
      const px = this.worldToPxX(v);
      if (px < 0 || px > width) continue;
      ctx.fillText(formatTick(v), px + 3, labelY);
    }
    ctx.textBaseline = "middle";
    const labelX = Math.min(Math.max(axisXpx + 4, 2), width - 30);
    for (let v = Math.ceil(this.pxToWorldY(height) / stepMajor) * stepMajor; v <= this.pxToWorldY(0); v += stepMajor) {
      if (Math.abs(v) < stepMajor / 1000) continue;
      const py = this.worldToPxY(v);
      if (py < 0 || py > height) continue;
      ctx.fillText(formatTick(v), labelX, py);
    }

    for (const c of this.curves || []) {
      if (!c.enabled || !c.fnX || !c.fnY) continue;
      this._drawCurve(c);
    }

    ctx.restore();
  }

  _drawCurve(c) {
    const { ctx } = this;
    const N = 500;
    const tMin = c.tMin, tMax = c.tMax;
    ctx.save();
    ctx.strokeStyle = c.color;
    ctx.lineWidth = 2.4;
    ctx.lineJoin = "round";
    ctx.lineCap = "round";
    ctx.beginPath();
    let started = false;
    for (let i = 0; i <= N; i++) {
      const t = tMin + (tMax - tMin) * (i / N);
      let wx, wy;
      try {
        const vars = buildVars(undefined, undefined, t);
        wx = c.fnX(vars);
        wy = c.fnY(vars);
      } catch (e) { wx = NaN; wy = NaN; }
      if (!isFinite(wx) || !isFinite(wy)) { started = false; continue; }
      const px = this.worldToPxX(wx);
      const py = this.worldToPxY(wy);
      if (!started) { ctx.moveTo(px, py); started = true; }
      else ctx.lineTo(px, py);
    }
    ctx.stroke();

    const span = tMax - tMin;
    if (span > 0) {
      const frac = (((animT * animSpeed) % span) + span) % span;
      const t = tMin + frac;
      try {
        const vars = buildVars(undefined, undefined, t);
        const wx = c.fnX(vars);
        const wy = c.fnY(vars);
        if (isFinite(wx) && isFinite(wy)) {
          const px = this.worldToPxX(wx);
          const py = this.worldToPxY(wy);
          ctx.fillStyle = c.color;
          ctx.beginPath();
          ctx.arc(px, py, 5, 0, Math.PI * 2);
          ctx.fill();
          ctx.strokeStyle = "#ffffff";
          ctx.lineWidth = 1.5;
          ctx.stroke();
        }
      } catch (e) {}
    }
    ctx.restore();
  }
}

/* =========================================================================
   4D engine — a tesseract (hypercube), the 4D analog of a cube.
   16 vertices rotated through two independent 4D rotation planes (driven
   by the shared animation clock), perspective-projected 4D -> 3D, then
   run through the same camera/orbit/projection math as Graph3D.
   ========================================================================= */

class Graph4D {
  constructor(canvas) {
    this.canvas = canvas;
    this.ctx = canvas.getContext("2d");
    this.azimuth = -0.7;
    this.elevation = 0.4;
    this.distance = 9;
    this.focal = 2.4;
    this.rotSpeedXW = 0.3;
    this.rotSpeedYZ = 0.18;
    this.dpr = Math.max(1, window.devicePixelRatio || 1);
    this.width = 0;
    this.height = 0;
    this._resizeObserver = new ResizeObserver(() => this.resize());
    this._resizeObserver.observe(canvas);
    this.resize();
  }

  resize() {
    const rect = this.canvas.parentElement.getBoundingClientRect();
    this.width = Math.max(1, Math.floor(rect.width));
    this.height = Math.max(1, Math.floor(rect.height));
    this.dpr = Math.max(1, window.devicePixelRatio || 1);
    this.canvas.width = Math.floor(this.width * this.dpr);
    this.canvas.height = Math.floor(this.height * this.dpr);
    this.canvas.style.width = this.width + "px";
    this.canvas.style.height = this.height + "px";
    this.render();
  }

  resetView() {
    this.azimuth = -0.7;
    this.elevation = 0.4;
    this.distance = 9;
    this.render();
  }

  _camera() {
    const theta = this.azimuth, phi = this.elevation, r = this.distance;
    const pos = [
      r * Math.cos(phi) * Math.cos(theta),
      r * Math.cos(phi) * Math.sin(theta),
      r * Math.sin(phi),
    ];
    const forward = vNorm([-pos[0], -pos[1], -pos[2]]);
    const worldUp = [0, 0, 1];
    let right = vNorm(vCross(forward, worldUp));
    if (!isFinite(right[0]) || vLen(right) < 1e-6) right = [1, 0, 0];
    const up = vCross(right, forward);
    return { pos, right, up, forward };
  }

  _project(p, cam) {
    const rel = vSub(p, cam.pos);
    const vz = vDot(rel, cam.forward);
    if (vz <= 0.05) return null;
    const scale = (this.height / 2) * this.focal / vz;
    const vx = vDot(rel, cam.right);
    const vy = vDot(rel, cam.up);
    return { x: this.width / 2 + vx * scale, y: this.height / 2 - vy * scale, depth: vz };
  }

  render() {
    const { ctx, width, height, dpr } = this;
    ctx.save();
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, width, height);

    const styles = getComputedStyle(document.body);
    const accentHex = styles.getPropertyValue("--accent").trim();
    const [ar, ag, ab] = hexToRgb(accentHex);

    const verts4 = [];
    for (let i = 0; i < 16; i++) {
      verts4.push([(i & 1) ? 1 : -1, (i & 2) ? 1 : -1, (i & 4) ? 1 : -1, (i & 8) ? 1 : -1]);
    }
    const edges = [];
    for (let i = 0; i < 16; i++) {
      for (let bit = 0; bit < 4; bit++) {
        const j = i ^ (1 << bit);
        if (j > i) edges.push([i, j]);
      }
    }

    const angleXW = animT * this.rotSpeedXW;
    const angleYZ = animT * this.rotSpeedYZ;
    const cosXW = Math.cos(angleXW), sinXW = Math.sin(angleXW);
    const cosYZ = Math.cos(angleYZ), sinYZ = Math.sin(angleYZ);
    const scale4 = 1.1;
    const wDist = 3;

    const pts3 = verts4.map(([x, y, z, w]) => {
      const x1 = x * cosXW - w * sinXW;
      const w1 = x * sinXW + w * cosXW;
      const y1 = y * cosYZ - z * sinYZ;
      const z1 = y * sinYZ + z * cosYZ;
      const wScale = wDist / (wDist - w1);
      return [x1 * wScale * scale4, y1 * wScale * scale4, z1 * wScale * scale4];
    });

    const cam = this._camera();
    const projectedEdges = [];
    for (const [i, j] of edges) {
      const s0 = this._project(pts3[i], cam);
      const s1 = this._project(pts3[j], cam);
      if (!s0 || !s1) continue;
      projectedEdges.push({ s0, s1, depth: (s0.depth + s1.depth) / 2 });
    }
    projectedEdges.sort((a, b) => b.depth - a.depth);

    const n = Math.max(1, projectedEdges.length);
    projectedEdges.forEach((d, idx) => {
      const t = idx / n;
      const alpha = 0.3 + 0.6 * t;
      ctx.beginPath();
      ctx.moveTo(d.s0.x, d.s0.y);
      ctx.lineTo(d.s1.x, d.s1.y);
      ctx.strokeStyle = `rgba(${ar},${ag},${ab},${alpha})`;
      ctx.lineWidth = 1.1 + 1.6 * t;
      ctx.stroke();
    });

    for (const p of pts3) {
      const s = this._project(p, cam);
      if (!s) continue;
      ctx.beginPath();
      ctx.arc(s.x, s.y, 3, 0, Math.PI * 2);
      ctx.fillStyle = `rgb(${ar},${ag},${ab})`;
      ctx.fill();
    }

    ctx.restore();
  }
}

/* =========================================================================
   Shared parameter state
   Any identifier in an expression that isn't x, y, ans, a known constant,
   or a known function becomes a live slider automatically.
   ========================================================================= */

let paramValues = {};
let paramRanges = {};
let lastAns = 0;

/* ---- Global animation clock ----
   "t" is a reserved variable usable in any 2D/3D formula or parametric
   curve. Play/Pause drives it forward in real time; it can also be
   scrubbed by hand at any time, playing or not. */
let animT = 0;
let animPlaying = false;
let animSpeed = 1;
let animMaxT = 20;
let animRafId = null;
let animLastTs = null;

function buildVars(x, y, t) {
  return Object.assign({ x, y, t: t === undefined ? animT : t, ans: lastAns }, paramValues);
}

/* =========================================================================
   UI wiring
   ========================================================================= */

const $ = (sel) => document.querySelector(sel);

const canvas2d = $("#graph");
const canvas3d = $("#graph3d");
const canvasParam = $("#graph-param");
const canvas4d = $("#graph-4d");
const graph2d = new Graph(canvas2d);
const graph3d = new Graph3D(canvas3d);
const graphParam = new ParametricGraph(canvasParam);
const graph4d = new Graph4D(canvas4d);

let mode = "2d";
let fnIdCounter = 0;

function activeGraph() {
  if (mode === "3d") return graph3d;
  if (mode === "param") return graphParam;
  if (mode === "4d") return graph4d;
  return graph2d;
}
function activeAllowVars() { return mode === "3d" ? ["x", "y", "t"] : ["x", "t"]; }
function redrawActive() {
  if (mode === "3d") graph3d.render();
  else if (mode === "2d") graph2d.draw();
  else if (mode === "param") graphParam.draw();
  else if (mode === "4d") graph4d.render();
}

function nextColor(fns) {
  const used = fns.map((f) => f.color);
  for (const c of PALETTE) if (!used.includes(c)) return c;
  return PALETTE[fns.length % PALETTE.length];
}

function addFunction(expr = "", color = null, enabled = true) {
  const g = activeGraph();
  const f = {
    id: ++fnIdCounter,
    expr,
    color: color || nextColor(g.functions),
    enabled,
    fn: null,
    error: null,
    params: new Set(),
  };
  g.functions.push(f);
  recompile(f);
  renderFnList();
  if (mode === "3d") graph3d.recompute();
  redrawActive();
  return f;
}

function recompile(f) {
  if (!f.expr.trim()) {
    f.fn = null;
    f.error = null;
    f.params = new Set();
    f.usesTime = false;
    return;
  }
  try {
    const result = compileExpression(f.expr, activeAllowVars());
    f.fn = result.fn;
    f.params = result.params;
    f.usesTime = result.usesTime;
    f.error = null;
  } catch (e) {
    f.fn = null;
    f.params = new Set();
    f.usesTime = false;
    f.error = e.message || "Invalid expression";
  }
}

function removeFunction(id) {
  const g = activeGraph();
  g.functions = g.functions.filter((f) => f.id !== id);
  renderFnList();
  recomputeParams();
  if (mode === "3d") graph3d.recompute();
  redrawActive();
  persist();
}

function renderFnList() {
  const list = $("#fn-list");
  list.innerHTML = "";
  const g = activeGraph();
  const placeholder = mode === "3d" ? "e.g. x^2 - y^2" : "e.g. sin(x) + x/2";

  g.functions.forEach((f, idx) => {
    const row = document.createElement("div");
    row.className = "fn-row" + (f.enabled ? "" : " disabled");

    const swatch = document.createElement("button");
    swatch.className = "fn-swatch";
    swatch.style.background = f.color;
    swatch.title = "Toggle visibility";
    swatch.addEventListener("click", () => {
      f.enabled = !f.enabled;
      row.classList.toggle("disabled", !f.enabled);
      if (mode === "3d") graph3d.recompute();
      redrawActive();
      persist();
    });

    const prefixEl = document.createElement("span");
    prefixEl.className = "fn-prefix";
    prefixEl.textContent = mode === "3d" ? `z${idx + 1}=` : `y${idx + 1}=`;

    const input = document.createElement("input");
    input.className = "fn-input" + (f.error ? " error" : "");
    input.type = "text";
    input.spellcheck = false;
    input.autocomplete = "off";
    input.value = f.expr;
    input.placeholder = placeholder;
    if (f.error) input.title = f.error;
    input.addEventListener("input", () => {
      f.expr = input.value;
      recompile(f);
      input.classList.toggle("error", !!f.error);
      input.title = f.error || "";
      recomputeParams();
      if (mode === "3d") graph3d.recompute();
      redrawActive();
      persist();
    });
    input.addEventListener("keydown", (e) => {
      if (e.key === "Enter") {
        e.preventDefault();
        if (idx === g.functions.length - 1) {
          const nf = addFunction();
          focusFnInput(nf.id);
        } else {
          focusFnInput(g.functions[idx + 1].id);
        }
      } else if (e.key === "Backspace" && input.value === "" && g.functions.length > 1) {
        e.preventDefault();
        removeFunction(f.id);
        const prevIdx = Math.max(0, idx - 1);
        if (g.functions[prevIdx]) focusFnInput(g.functions[prevIdx].id);
      }
    });

    const del = document.createElement("button");
    del.className = "fn-del";
    del.textContent = "✕";
    del.title = "Delete";
    del.addEventListener("click", () => removeFunction(f.id));

    row.append(swatch, prefixEl, input, del);
    row.dataset.fnId = f.id;
    list.appendChild(row);
  });
}

function focusFnInput(id) {
  requestAnimationFrame(() => {
    const row = document.querySelector(`.fn-row[data-fn-id="${id}"]`);
    if (row) row.querySelector(".fn-input").focus();
  });
}

/* ---- Parameters (auto sliders) ---- */

let lastParamSignature = "";

function recomputeParams() {
  const used = new Set();
  const g = activeGraph();
  const items = mode === "param" ? g.curves : (g.functions || []);
  for (const f of items) {
    for (const p of f.params || []) used.add(p);
  }
  for (const name of Object.keys(paramValues)) {
    if (!used.has(name)) {
      delete paramValues[name];
      delete paramRanges[name];
    }
  }
  for (const name of used) {
    if (!(name in paramValues)) {
      paramValues[name] = 1;
      paramRanges[name] = { min: -10, max: 10, step: 0.1 };
    }
  }
  renderParamsPanel(used);
  updateAnimBar();
}

function renderParamsPanel(used) {
  const panel = $("#params-panel");
  const names = Array.from(used).sort();
  const signature = names.join(",");
  panel.classList.toggle("hidden", names.length === 0);
  if (signature === lastParamSignature) return;
  lastParamSignature = signature;

  panel.innerHTML = "";
  if (!names.length) return;

  const heading = document.createElement("h2");
  heading.textContent = "Parameters";
  panel.appendChild(heading);

  for (const name of names) {
    const range = paramRanges[name];
    const row = document.createElement("div");
    row.className = "param-row";

    const label = document.createElement("span");
    label.className = "param-name";
    label.textContent = name;

    const valueInput = document.createElement("input");
    valueInput.type = "number";
    valueInput.className = "param-value";
    valueInput.step = range.step;
    valueInput.value = paramValues[name];

    const slider = document.createElement("input");
    slider.type = "range";
    slider.className = "param-slider";
    slider.min = range.min;
    slider.max = range.max;
    slider.step = range.step;
    slider.value = paramValues[name];

    const minInput = document.createElement("input");
    minInput.type = "number";
    minInput.className = "param-bound";
    minInput.value = range.min;
    minInput.title = "Minimum";

    const maxInput = document.createElement("input");
    maxInput.type = "number";
    maxInput.className = "param-bound";
    maxInput.value = range.max;
    maxInput.title = "Maximum";

    const applyValue = (v) => {
      paramValues[name] = v;
      slider.value = v;
      valueInput.value = v;
      if (mode === "3d") graph3d.recompute({ rescale: false });
      redrawActive();
      persist();
    };

    slider.addEventListener("input", () => applyValue(parseFloat(slider.value)));
    valueInput.addEventListener("change", () => {
      const v = parseFloat(valueInput.value);
      if (isFinite(v)) applyValue(v);
    });
    minInput.addEventListener("change", () => {
      const v = parseFloat(minInput.value);
      if (isFinite(v)) { range.min = v; slider.min = v; persist(); }
    });
    maxInput.addEventListener("change", () => {
      const v = parseFloat(maxInput.value);
      if (isFinite(v)) { range.max = v; slider.max = v; persist(); }
    });

    row.append(label, minInput, slider, maxInput, valueInput);
    panel.appendChild(row);
  }
}

/* ---- Mode switching ---- */

const MODES = ["2d", "3d", "param", "4d"];

const HINTS = {
  "2d": 'Tip: use <code>x</code> as the variable. Implicit multiplication works: <code>2x</code>, <code>2sin(x)</code>. Type <code>t</code> for a live, animatable time variable.',
  "3d": 'Tip: use <code>x</code> and <code>y</code> as variables. Any other letter (a, b, k…) becomes a slider automatically. Type <code>t</code> for a live time variable.',
  param: 'Tip: define <code>x(t)</code> and <code>y(t)</code> — any other letter becomes a slider. Drag the scrubber below to trace the curve, or press play.',
  "4d": "Tip: drag to orbit, scroll to zoom. Press play to set it spinning, or drag the speed control to change the rate.",
};

function setMode(next) {
  if (mode === next) return;
  mode = next;
  for (const m of MODES) $(`#tab-${m}`).classList.toggle("active", mode === m);

  canvas2d.classList.toggle("hidden", mode !== "2d");
  canvas3d.classList.toggle("hidden", mode !== "3d");
  canvasParam.classList.toggle("hidden", mode !== "param");
  canvas4d.classList.toggle("hidden", mode !== "4d");

  $("#presets-3d").classList.toggle("hidden", mode !== "3d");
  $("#presets-param").classList.toggle("hidden", mode !== "param");
  $("#domain-control").classList.toggle("hidden", mode !== "3d");
  $("#btn-topo").classList.toggle("hidden", mode !== "3d");
  $("#coord-readout").classList.add("hidden");
  $("#btn-add-fn").classList.toggle("hidden", mode === "4d");
  $("#fn-list").classList.toggle("hidden", mode === "4d");
  $("#four-d-info").classList.toggle("hidden", mode !== "4d");
  $("#hint-text").innerHTML = HINTS[mode];

  if (mode === "param") renderCurveList();
  else if (mode !== "4d") renderFnList();
  lastParamSignature = " "; // force panel rebuild across mode switch
  recomputeParams();
  updateAnimBar();

  if (mode === "3d") graph3d.resize();
  else if (mode === "2d") graph2d.resize();
  else if (mode === "param") graphParam.resize();
  else if (mode === "4d") {
    graph4d.resize();
    if (!animPlaying) playAnimation();
  }
  persist();
}

for (const m of MODES) $(`#tab-${m}`).addEventListener("click", () => setMode(m));

/* ---- 3D presets ---- */

// Each preset's parameter hints give amplitude/frequency-style sliders a
// sensible range out of the box (e.g. a frequency slider that goes too high
// for the sample grid just looks like noise) rather than the generic -10..10.
const PRESETS_3D = {
  paraboloid: {
    expr: "a*x^2 + b*y^2",
    hints: {
      a: { min: 0.1, max: 3, step: 0.1, value: 1 },
      b: { min: 0.1, max: 3, step: 0.1, value: 1 },
    },
  },
  saddle: {
    expr: "a*x^2 - b*y^2",
    hints: {
      a: { min: 0.1, max: 3, step: 0.1, value: 1 },
      b: { min: 0.1, max: 3, step: 0.1, value: 1 },
    },
  },
  monkey: {
    expr: "a*(x^3 - 3xy^2)",
    hints: { a: { min: -3, max: 3, step: 0.1, value: 1 } },
  },
  cone: {
    expr: "a*sqrt(x^2 + y^2)",
    hints: { a: { min: 0.2, max: 3, step: 0.1, value: 1 } },
  },
  dome: {
    expr: "sqrt(a^2 - x^2 - y^2)",
    hints: { a: { min: 1, max: 5, step: 0.1, value: 4 } },
  },
  volcano: {
    expr: "b*(x^2 + y^2)*exp(-(x^2 + y^2)/a)",
    hints: {
      a: { min: 0.5, max: 15, step: 0.5, value: 4 },
      b: { min: -3, max: 3, step: 0.1, value: 1 },
    },
  },
  ripple: {
    expr: "a*sin(b*sqrt(x^2 + y^2))",
    hints: {
      a: { min: -3, max: 3, step: 0.1, value: 1 },
      b: { min: 0.2, max: 3, step: 0.1, value: 1 },
    },
  },
  bump: {
    expr: "a*exp(-(x^2 + y^2)/b)",
    hints: {
      a: { min: -5, max: 5, step: 0.1, value: 2 },
      b: { min: 0.2, max: 8, step: 0.1, value: 1 },
    },
  },
  eggcarton: {
    expr: "a*sin(b*x)*cos(b*y)",
    hints: {
      a: { min: -3, max: 3, step: 0.1, value: 1 },
      b: { min: 0.3, max: 3, step: 0.1, value: 1 },
    },
  },
};

$("#presets-3d").addEventListener("click", (e) => {
  const btn = e.target.closest("button[data-preset]");
  if (!btn) return;
  const preset = PRESETS_3D[btn.dataset.preset];
  if (!preset) return;
  graph3d.functions = [];
  addFunction(preset.expr);
  recomputeParams();
  for (const [name, hint] of Object.entries(preset.hints || {})) {
    if (!(name in paramValues)) continue;
    paramRanges[name] = { min: hint.min, max: hint.max, step: hint.step };
    paramValues[name] = hint.value;
  }
  lastParamSignature = " "; // force the panel to rebuild with the new ranges
  recomputeParams();
  graph3d.recompute();
  graph3d.render();
  persist();
});

/* ---- Parametric curves: x(t), y(t) ---- */

function addCurve(exprX = "", exprY = "", color = null, enabled = true, tMin = 0, tMax = 2 * Math.PI) {
  const c = {
    id: ++fnIdCounter,
    exprX, exprY,
    color: color || nextColor(graphParam.curves),
    enabled,
    fnX: null, fnY: null,
    errorX: null, errorY: null,
    params: new Set(),
    tMin, tMax,
  };
  graphParam.curves.push(c);
  recompileCurve(c);
  renderCurveList();
  graphParam.draw();
  return c;
}

function recompileCurve(c) {
  c.params = new Set();
  c.errorX = null;
  c.errorY = null;
  if (c.exprX && c.exprX.trim()) {
    try {
      const r = compileExpression(c.exprX, ["t"]);
      c.fnX = r.fn;
      for (const p of r.params) c.params.add(p);
    } catch (e) {
      c.fnX = null;
      c.errorX = e.message || "Invalid expression";
    }
  } else {
    c.fnX = null;
  }
  if (c.exprY && c.exprY.trim()) {
    try {
      const r = compileExpression(c.exprY, ["t"]);
      c.fnY = r.fn;
      for (const p of r.params) c.params.add(p);
    } catch (e) {
      c.fnY = null;
      c.errorY = e.message || "Invalid expression";
    }
  } else {
    c.fnY = null;
  }
}

function removeCurve(id) {
  graphParam.curves = graphParam.curves.filter((c) => c.id !== id);
  renderCurveList();
  recomputeParams();
  graphParam.draw();
  persist();
}

function renderCurveList() {
  const list = $("#fn-list");
  list.innerHTML = "";
  graphParam.curves.forEach((c, idx) => {
    const row = document.createElement("div");
    row.className = "curve-row" + (c.enabled ? "" : " disabled");

    const head = document.createElement("div");
    head.className = "curve-row-head";
    const swatch = document.createElement("button");
    swatch.className = "fn-swatch";
    swatch.style.background = c.color;
    swatch.title = "Toggle visibility";
    swatch.addEventListener("click", () => {
      c.enabled = !c.enabled;
      row.classList.toggle("disabled", !c.enabled);
      graphParam.draw();
      persist();
    });
    const label = document.createElement("span");
    label.className = "curve-label";
    label.textContent = `Curve ${idx + 1}`;
    const del = document.createElement("button");
    del.className = "fn-del";
    del.textContent = "✕";
    del.title = "Delete";
    del.addEventListener("click", () => removeCurve(c.id));
    head.append(swatch, label, del);
    row.appendChild(head);

    const makeInput = (prefixText, key, errKey, placeholder) => {
      const wrap = document.createElement("div");
      wrap.className = "curve-input-row";
      const prefixEl = document.createElement("span");
      prefixEl.className = "fn-prefix";
      prefixEl.textContent = prefixText;
      const input = document.createElement("input");
      input.className = "fn-input" + (c[errKey] ? " error" : "");
      input.type = "text";
      input.spellcheck = false;
      input.autocomplete = "off";
      input.value = c[key];
      input.placeholder = placeholder;
      if (c[errKey]) input.title = c[errKey];
      input.addEventListener("input", () => {
        c[key] = input.value;
        recompileCurve(c);
        input.classList.toggle("error", !!c[errKey]);
        input.title = c[errKey] || "";
        recomputeParams();
        graphParam.draw();
        persist();
      });
      wrap.append(prefixEl, input);
      return wrap;
    };

    row.appendChild(makeInput("x(t) =", "exprX", "errorX", "e.g. cos(t)"));
    row.appendChild(makeInput("y(t) =", "exprY", "errorY", "e.g. sin(t)"));

    const rangeRow = document.createElement("div");
    rangeRow.className = "curve-range-row";
    const tLabel = document.createElement("span");
    tLabel.className = "curve-range-label";
    tLabel.textContent = "t:";
    const tMinInput = document.createElement("input");
    tMinInput.type = "number";
    tMinInput.step = "0.1";
    tMinInput.className = "param-bound";
    tMinInput.value = c.tMin;
    tMinInput.addEventListener("change", () => {
      const v = parseFloat(tMinInput.value);
      if (isFinite(v)) { c.tMin = v; graphParam.draw(); persist(); }
    });
    const arrow = document.createElement("span");
    arrow.className = "curve-range-arrow";
    arrow.textContent = "→";
    const tMaxInput = document.createElement("input");
    tMaxInput.type = "number";
    tMaxInput.step = "0.1";
    tMaxInput.className = "param-bound";
    tMaxInput.value = c.tMax;
    tMaxInput.addEventListener("change", () => {
      const v = parseFloat(tMaxInput.value);
      if (isFinite(v)) { c.tMax = v; graphParam.draw(); persist(); }
    });
    rangeRow.append(tLabel, tMinInput, arrow, tMaxInput);
    row.appendChild(rangeRow);

    row.dataset.fnId = c.id;
    list.appendChild(row);
  });
}

function focusCurveInput(id) {
  requestAnimationFrame(() => {
    const row = document.querySelector(`.curve-row[data-fn-id="${id}"]`);
    if (row) row.querySelector(".fn-input").focus();
  });
}

// Classic and physics-flavored parametric curves — the "cool equations"
// list: circles, Lissajous figures, a spirograph, a rose curve, an
// astroid, a heart curve, plus projectile motion and a pendulum.
const PRESETS_PARAM = {
  circle: {
    x: "a*cos(t)", y: "a*sin(t)", tMin: 0, tMax: 2 * Math.PI,
    hints: { a: { min: 0.5, max: 5, step: 0.1, value: 2 } },
  },
  lissajous: {
    x: "a*sin(b*t + c)", y: "a*sin(d*t)", tMin: 0, tMax: 2 * Math.PI,
    hints: {
      a: { min: 0.5, max: 4, step: 0.1, value: 2 },
      b: { min: 1, max: 6, step: 1, value: 3 },
      c: { min: 0, max: 6.3, step: 0.1, value: 1.6 },
      d: { min: 1, max: 6, step: 1, value: 2 },
    },
  },
  spirograph: {
    x: "(a-b)*cos(t) + c*cos((a-b)/b*t)", y: "(a-b)*sin(t) - c*sin((a-b)/b*t)", tMin: 0, tMax: 12 * Math.PI,
    hints: {
      a: { min: 2, max: 12, step: 1, value: 5 },
      b: { min: 1, max: 6, step: 1, value: 3 },
      c: { min: 0.2, max: 4, step: 0.1, value: 2 },
    },
  },
  rose: {
    x: "cos(k*t)*cos(t)", y: "cos(k*t)*sin(t)", tMin: 0, tMax: 2 * Math.PI,
    hints: { k: { min: 1, max: 9, step: 1, value: 5 } },
  },
  astroid: {
    x: "a*cos(t)^3", y: "a*sin(t)^3", tMin: 0, tMax: 2 * Math.PI,
    hints: { a: { min: 0.5, max: 5, step: 0.1, value: 3 } },
  },
  heart: {
    x: "a*16*sin(t)^3", y: "a*(13*cos(t) - 5*cos(2t) - 2*cos(3t) - cos(4t))", tMin: 0, tMax: 2 * Math.PI,
    hints: { a: { min: 0.05, max: 0.4, step: 0.01, value: 0.15 } },
  },
  projectile: {
    x: "v*cos(a)*t", y: "v*sin(a)*t - 0.5*g*t^2", tMin: 0, tMax: 4,
    hints: {
      v: { min: 2, max: 20, step: 0.5, value: 10 },
      a: { min: 0.1, max: 1.5, step: 0.05, value: 0.8 },
      g: { min: 1, max: 20, step: 0.5, value: 9.8 },
    },
  },
  pendulum: {
    x: "l*sin(a*cos(w*t))", y: "-l*cos(a*cos(w*t))", tMin: 0, tMax: 12,
    hints: {
      l: { min: 0.5, max: 4, step: 0.1, value: 2 },
      a: { min: 0.1, max: 1.5, step: 0.05, value: 0.9 },
      w: { min: 0.5, max: 4, step: 0.1, value: 2 },
    },
  },
};

$("#presets-param").addEventListener("click", (e) => {
  const btn = e.target.closest("button[data-preset]");
  if (!btn) return;
  const preset = PRESETS_PARAM[btn.dataset.preset];
  if (!preset) return;
  graphParam.curves = [];
  addCurve(preset.x, preset.y, null, true, preset.tMin, preset.tMax);
  recomputeParams();
  for (const [name, hint] of Object.entries(preset.hints || {})) {
    if (!(name in paramValues)) continue;
    paramRanges[name] = { min: hint.min, max: hint.max, step: hint.step };
    paramValues[name] = hint.value;
  }
  lastParamSignature = " ";
  recomputeParams();
  graphParam.draw();
  persist();
});

/* ---- Panning / zooming (2D) ---- */

let isDragging = false;
let dragLast = null;
let dragMoved = false;

canvas2d.addEventListener("mousedown", (e) => {
  isDragging = true;
  dragMoved = false;
  dragLast = { x: e.clientX, y: e.clientY };
  canvas2d.style.cursor = "grabbing";
});

window.addEventListener("mousemove", (e) => {
  if (mode !== "2d") return;
  if (isDragging) {
    const dx = e.clientX - dragLast.x;
    const dy = e.clientY - dragLast.y;
    if (Math.abs(dx) > 1 || Math.abs(dy) > 1) dragMoved = true;
    dragLast = { x: e.clientX, y: e.clientY };
    graph2d.panByPixels(dx, dy);
  } else {
    handleHover(e);
  }
});

window.addEventListener("mouseup", () => {
  if (isDragging) {
    isDragging = false;
    canvas2d.style.cursor = "crosshair";
    if (dragMoved) persist();
  }
});

canvas2d.addEventListener("mouseleave", () => {
  $("#coord-readout").classList.add("hidden");
});

canvas2d.addEventListener("wheel", (e) => {
  e.preventDefault();
  const rect = canvas2d.getBoundingClientRect();
  const px = e.clientX - rect.left;
  const py = e.clientY - rect.top;
  const factor = Math.pow(1.0016, -e.deltaY);
  graph2d.zoomAt(px, py, factor);
}, { passive: false });

function handleHover(e) {
  const rect = canvas2d.getBoundingClientRect();
  const px = e.clientX - rect.left;
  const py = e.clientY - rect.top;
  const readout = $("#coord-readout");
  if (px < 0 || py < 0 || px > rect.width || py > rect.height) {
    readout.classList.add("hidden");
    return;
  }
  const nearest = graph2d.findNearest(px, py);
  const wx = graph2d.pxToWorldX(px);
  const wy = graph2d.pxToWorldY(py);
  if (nearest && nearest.dist < 25) {
    readout.innerHTML = `<span style="color:${nearest.color}">●</span> x = ${fmt(nearest.wx)}, y = ${fmt(nearest.wy)}`;
  } else {
    readout.textContent = `x = ${fmt(wx)}, y = ${fmt(wy)}`;
  }
  readout.classList.remove("hidden");
}

function fmt(v) {
  if (!isFinite(v)) return "—";
  const r = Math.round(v * 1000) / 1000;
  return String(r);
}

let touchState = null;

canvas2d.addEventListener("touchstart", (e) => {
  if (e.touches.length === 1) {
    touchState = { mode: "pan", x: e.touches[0].clientX, y: e.touches[0].clientY };
  } else if (e.touches.length === 2) {
    const [a, b] = e.touches;
    touchState = {
      mode: "pinch",
      dist: Math.hypot(a.clientX - b.clientX, a.clientY - b.clientY),
    };
  }
}, { passive: true });

canvas2d.addEventListener("touchmove", (e) => {
  e.preventDefault();
  const rect = canvas2d.getBoundingClientRect();
  if (e.touches.length === 1 && touchState && touchState.mode === "pan") {
    const dx = e.touches[0].clientX - touchState.x;
    const dy = e.touches[0].clientY - touchState.y;
    touchState.x = e.touches[0].clientX;
    touchState.y = e.touches[0].clientY;
    graph2d.panByPixels(dx, dy);
  } else if (e.touches.length === 2 && touchState && touchState.mode === "pinch") {
    const [a, b] = e.touches;
    const dist = Math.hypot(a.clientX - b.clientX, a.clientY - b.clientY);
    const midX = (a.clientX + b.clientX) / 2 - rect.left;
    const midY = (a.clientY + b.clientY) / 2 - rect.top;
    graph2d.zoomAt(midX, midY, dist / touchState.dist);
    touchState.dist = dist;
  }
}, { passive: false });

canvas2d.addEventListener("touchend", (e) => {
  if (e.touches.length === 0) {
    touchState = null;
    persist();
  }
});

/* ---- Orbit / zoom (3D) ---- */

let isOrbiting = false;
let orbitLast = null;
let orbitMoved = false;

canvas3d.addEventListener("mousedown", (e) => {
  isOrbiting = true;
  orbitMoved = false;
  orbitLast = { x: e.clientX, y: e.clientY };
  canvas3d.style.cursor = "grabbing";
  graph3d.setQuality("low");
});

window.addEventListener("mousemove", (e) => {
  if (mode !== "3d" || !isOrbiting) return;
  const dx = e.clientX - orbitLast.x;
  const dy = e.clientY - orbitLast.y;
  if (Math.abs(dx) > 1 || Math.abs(dy) > 1) orbitMoved = true;
  orbitLast = { x: e.clientX, y: e.clientY };
  graph3d.azimuth -= dx * 0.006;
  graph3d.elevation = clamp(graph3d.elevation + dy * 0.006, -1.45, 1.45);
  graph3d.render();
});

window.addEventListener("mouseup", () => {
  if (isOrbiting) {
    isOrbiting = false;
    canvas3d.style.cursor = "grab";
    graph3d.setQuality("high");
    graph3d.recompute();
    graph3d.render();
    if (orbitMoved) persist();
  }
});

canvas3d.addEventListener("wheel", (e) => {
  e.preventDefault();
  graph3d.distance = clamp(graph3d.distance * Math.pow(1.0015, e.deltaY), 4, 60);
  graph3d.render();
}, { passive: false });

let touch3d = null;

canvas3d.addEventListener("touchstart", (e) => {
  graph3d.setQuality("low");
  if (e.touches.length === 1) {
    touch3d = { mode: "orbit", x: e.touches[0].clientX, y: e.touches[0].clientY };
  } else if (e.touches.length === 2) {
    const [a, b] = e.touches;
    touch3d = { mode: "pinch", dist: Math.hypot(a.clientX - b.clientX, a.clientY - b.clientY) };
  }
}, { passive: true });

canvas3d.addEventListener("touchmove", (e) => {
  e.preventDefault();
  if (e.touches.length === 1 && touch3d && touch3d.mode === "orbit") {
    const dx = e.touches[0].clientX - touch3d.x;
    const dy = e.touches[0].clientY - touch3d.y;
    touch3d.x = e.touches[0].clientX;
    touch3d.y = e.touches[0].clientY;
    graph3d.azimuth -= dx * 0.006;
    graph3d.elevation = clamp(graph3d.elevation + dy * 0.006, -1.45, 1.45);
    graph3d.render();
  } else if (e.touches.length === 2 && touch3d && touch3d.mode === "pinch") {
    const [a, b] = e.touches;
    const dist = Math.hypot(a.clientX - b.clientX, a.clientY - b.clientY);
    graph3d.distance = clamp(graph3d.distance * (touch3d.dist / dist), 4, 60);
    touch3d.dist = dist;
    graph3d.render();
  }
}, { passive: false });

canvas3d.addEventListener("touchend", (e) => {
  if (e.touches.length === 0) {
    touch3d = null;
    graph3d.setQuality("high");
    graph3d.recompute();
    graph3d.render();
    persist();
  }
});

/* ---- Panning / zooming (Parametric) ---- */

let isDraggingParam = false;
let dragLastParam = null;
let dragMovedParam = false;

canvasParam.addEventListener("mousedown", (e) => {
  isDraggingParam = true;
  dragMovedParam = false;
  dragLastParam = { x: e.clientX, y: e.clientY };
  canvasParam.style.cursor = "grabbing";
});

window.addEventListener("mousemove", (e) => {
  if (mode !== "param" || !isDraggingParam) return;
  const dx = e.clientX - dragLastParam.x;
  const dy = e.clientY - dragLastParam.y;
  if (Math.abs(dx) > 1 || Math.abs(dy) > 1) dragMovedParam = true;
  dragLastParam = { x: e.clientX, y: e.clientY };
  graphParam.panByPixels(dx, dy);
});

window.addEventListener("mouseup", () => {
  if (isDraggingParam) {
    isDraggingParam = false;
    canvasParam.style.cursor = "grab";
    if (dragMovedParam) persist();
  }
});

canvasParam.addEventListener("wheel", (e) => {
  e.preventDefault();
  const rect = canvasParam.getBoundingClientRect();
  const factor = Math.pow(1.0016, -e.deltaY);
  graphParam.zoomAt(e.clientX - rect.left, e.clientY - rect.top, factor);
}, { passive: false });

let touchParam = null;

canvasParam.addEventListener("touchstart", (e) => {
  if (e.touches.length === 1) {
    touchParam = { mode: "pan", x: e.touches[0].clientX, y: e.touches[0].clientY };
  } else if (e.touches.length === 2) {
    const [a, b] = e.touches;
    touchParam = { mode: "pinch", dist: Math.hypot(a.clientX - b.clientX, a.clientY - b.clientY) };
  }
}, { passive: true });

canvasParam.addEventListener("touchmove", (e) => {
  e.preventDefault();
  const rect = canvasParam.getBoundingClientRect();
  if (e.touches.length === 1 && touchParam && touchParam.mode === "pan") {
    const dx = e.touches[0].clientX - touchParam.x;
    const dy = e.touches[0].clientY - touchParam.y;
    touchParam.x = e.touches[0].clientX;
    touchParam.y = e.touches[0].clientY;
    graphParam.panByPixels(dx, dy);
  } else if (e.touches.length === 2 && touchParam && touchParam.mode === "pinch") {
    const [a, b] = e.touches;
    const dist = Math.hypot(a.clientX - b.clientX, a.clientY - b.clientY);
    const midX = (a.clientX + b.clientX) / 2 - rect.left;
    const midY = (a.clientY + b.clientY) / 2 - rect.top;
    graphParam.zoomAt(midX, midY, dist / touchParam.dist);
    touchParam.dist = dist;
  }
}, { passive: false });

canvasParam.addEventListener("touchend", (e) => {
  if (e.touches.length === 0) { touchParam = null; persist(); }
});

/* ---- Orbit / zoom (4D) ---- */

let isOrbiting4d = false;
let orbitLast4d = null;
let orbitMoved4d = false;

canvas4d.addEventListener("mousedown", (e) => {
  isOrbiting4d = true;
  orbitMoved4d = false;
  orbitLast4d = { x: e.clientX, y: e.clientY };
  canvas4d.style.cursor = "grabbing";
});

window.addEventListener("mousemove", (e) => {
  if (mode !== "4d" || !isOrbiting4d) return;
  const dx = e.clientX - orbitLast4d.x;
  const dy = e.clientY - orbitLast4d.y;
  if (Math.abs(dx) > 1 || Math.abs(dy) > 1) orbitMoved4d = true;
  orbitLast4d = { x: e.clientX, y: e.clientY };
  graph4d.azimuth -= dx * 0.006;
  graph4d.elevation = clamp(graph4d.elevation + dy * 0.006, -1.45, 1.45);
  graph4d.render();
});

window.addEventListener("mouseup", () => {
  if (isOrbiting4d) {
    isOrbiting4d = false;
    canvas4d.style.cursor = "grab";
    if (orbitMoved4d) persist();
  }
});

canvas4d.addEventListener("wheel", (e) => {
  e.preventDefault();
  graph4d.distance = clamp(graph4d.distance * Math.pow(1.0015, e.deltaY), 2, 30);
  graph4d.render();
}, { passive: false });

let touch4d = null;

canvas4d.addEventListener("touchstart", (e) => {
  if (e.touches.length === 1) {
    touch4d = { mode: "orbit", x: e.touches[0].clientX, y: e.touches[0].clientY };
  } else if (e.touches.length === 2) {
    const [a, b] = e.touches;
    touch4d = { mode: "pinch", dist: Math.hypot(a.clientX - b.clientX, a.clientY - b.clientY) };
  }
}, { passive: true });

canvas4d.addEventListener("touchmove", (e) => {
  e.preventDefault();
  if (e.touches.length === 1 && touch4d && touch4d.mode === "orbit") {
    const dx = e.touches[0].clientX - touch4d.x;
    const dy = e.touches[0].clientY - touch4d.y;
    touch4d.x = e.touches[0].clientX;
    touch4d.y = e.touches[0].clientY;
    graph4d.azimuth -= dx * 0.006;
    graph4d.elevation = clamp(graph4d.elevation + dy * 0.006, -1.45, 1.45);
    graph4d.render();
  } else if (e.touches.length === 2 && touch4d && touch4d.mode === "pinch") {
    const [a, b] = e.touches;
    const dist = Math.hypot(a.clientX - b.clientX, a.clientY - b.clientY);
    graph4d.distance = clamp(graph4d.distance * (touch4d.dist / dist), 2, 30);
    touch4d.dist = dist;
    graph4d.render();
  }
}, { passive: false });

canvas4d.addEventListener("touchend", (e) => {
  if (e.touches.length === 0) touch4d = null;
});

/* ---- Zoom controls (shared, routes by mode) ---- */

$("#btn-zoom-in").addEventListener("click", () => {
  if (mode === "3d") { graph3d.distance = clamp(graph3d.distance / 1.35, 4, 60); graph3d.render(); }
  else if (mode === "4d") { graph4d.distance = clamp(graph4d.distance / 1.35, 2, 30); graph4d.render(); }
  else if (mode === "param") graphParam.zoomAt(graphParam.width / 2, graphParam.height / 2, 1.4);
  else graph2d.zoomAt(graph2d.width / 2, graph2d.height / 2, 1.4);
});
$("#btn-zoom-out").addEventListener("click", () => {
  if (mode === "3d") { graph3d.distance = clamp(graph3d.distance * 1.35, 4, 60); graph3d.render(); }
  else if (mode === "4d") { graph4d.distance = clamp(graph4d.distance * 1.35, 2, 30); graph4d.render(); }
  else if (mode === "param") graphParam.zoomAt(graphParam.width / 2, graphParam.height / 2, 1 / 1.4);
  else graph2d.zoomAt(graph2d.width / 2, graph2d.height / 2, 1 / 1.4);
});
$("#btn-reset-view").addEventListener("click", () => {
  if (mode === "3d") graph3d.resetView();
  else if (mode === "4d") graph4d.resetView();
  else if (mode === "param") graphParam.resetView();
  else graph2d.resetView();
});

/* ---- Domain control (3D) ---- */

$("#domain-input").addEventListener("change", (e) => {
  const v = clamp(parseFloat(e.target.value) || 5, 1, 50);
  e.target.value = v;
  graph3d.domain = v;
  graph3d.recompute();
  graph3d.render();
  persist();
});

/* ---- Topo view (3D) ---- */

$("#btn-topo").addEventListener("click", () => {
  graph3d.setTopo(!graph3d.topo);
  $("#btn-topo").classList.toggle("active", graph3d.topo);
  persist();
});

/* ---- Quick calc ---- */

const qcInput = $("#quickcalc-input");
const qcResult = $("#quickcalc-result");

function runQuickCalc() {
  const src = qcInput.value.trim();
  if (!src) { qcResult.textContent = ""; return; }
  try {
    const { fn } = compileExpression(src, ["t"]);
    const val = fn(buildVars(undefined, undefined));
    lastAns = val;
    qcResult.textContent = "= " + fmt(val);
    qcResult.classList.remove("err");
  } catch (e) {
    qcResult.textContent = e.message || "Error";
    qcResult.classList.add("err");
  }
}
$("#quickcalc-eval").addEventListener("click", runQuickCalc);
qcInput.addEventListener("keydown", (e) => { if (e.key === "Enter") runQuickCalc(); });

/* ---- Keypad ---- */

let activeInputEl = null;
document.addEventListener("focusin", (e) => {
  if (e.target.matches(".fn-input, #quickcalc-input")) activeInputEl = e.target;
});

$("#keypad").addEventListener("click", (e) => {
  const btn = e.target.closest("button[data-insert]");
  if (!btn) return;
  const target = activeInputEl || qcInput;
  const insert = btn.dataset.insert;
  const start = target.selectionStart ?? target.value.length;
  const end = target.selectionEnd ?? target.value.length;
  target.value = target.value.slice(0, start) + insert + target.value.slice(end);
  const caret = start + insert.length;
  target.focus();
  target.setSelectionRange(caret, caret);
  target.dispatchEvent(new Event("input"));
});

/* ---- Animation clock ----
   "t" is usable in any 2D/3D formula (a live parameter) and is the
   sweep variable for parametric curves; in 4D mode it drives the
   tesseract's rotation. One shared Play/Pause/scrub/speed control
   works across all four modes. */

function shouldShowAnimBar() {
  if (mode === "param" || mode === "4d") return true;
  if (mode === "2d") return graph2d.functions.some((f) => f.enabled && f.usesTime);
  if (mode === "3d") return graph3d.functions.some((f) => f.enabled && f.usesTime);
  return false;
}

function updateAnimBar() {
  const show = shouldShowAnimBar();
  $("#anim-bar").classList.toggle("hidden", !show);
  $("#anim-scrub-group").classList.toggle("hidden", !show || mode === "4d");
  if (!show && animPlaying) pauseAnimation();
}

function animLoop(ts) {
  if (!animPlaying) return;
  if (animLastTs === null) animLastTs = ts;
  const dt = Math.min(0.1, (ts - animLastTs) / 1000);
  animLastTs = ts;
  animT += dt * animSpeed;
  if (mode !== "4d" && animT > animMaxT) animT -= animMaxT * Math.floor(animT / animMaxT);
  $("#anim-t-slider").value = Math.min(animT, animMaxT);
  $("#anim-t-readout").textContent = "t = " + fmt(animT);
  redrawActive();
  animRafId = requestAnimationFrame(animLoop);
}

function playAnimation() {
  if (animPlaying) return;
  animPlaying = true;
  animLastTs = null;
  $("#btn-anim-play").textContent = "⏸";
  $("#btn-anim-play").title = "Pause";
  animRafId = requestAnimationFrame(animLoop);
}

function pauseAnimation() {
  animPlaying = false;
  if (animRafId) cancelAnimationFrame(animRafId);
  animRafId = null;
  $("#btn-anim-play").textContent = "▶";
  $("#btn-anim-play").title = "Play";
}

$("#btn-anim-play").addEventListener("click", () => {
  if (animPlaying) pauseAnimation();
  else playAnimation();
  persist();
});

$("#anim-t-slider").addEventListener("input", (e) => {
  animT = parseFloat(e.target.value) || 0;
  $("#anim-t-readout").textContent = "t = " + fmt(animT);
  redrawActive();
});
$("#anim-t-slider").addEventListener("change", persist);

$("#anim-speed").addEventListener("change", (e) => {
  animSpeed = parseFloat(e.target.value) || 1;
  persist();
});

$("#anim-max-t").addEventListener("change", (e) => {
  const v = parseFloat(e.target.value);
  if (isFinite(v) && v > 0) {
    animMaxT = v;
    $("#anim-t-slider").max = v;
    persist();
  }
});

/* ---- Theme ---- */

function applyTheme(theme) {
  if (theme === "dark") document.documentElement.setAttribute("data-theme", "dark");
  else document.documentElement.setAttribute("data-theme", "light");
  redrawActive();
}

$("#btn-theme").addEventListener("click", () => {
  const cur = document.documentElement.getAttribute("data-theme") || "light";
  const next = cur === "dark" ? "light" : "dark";
  applyTheme(next);
  try { localStorage.setItem("graphit-theme", next); } catch (e) {}
});

/* ---- Mobile sidebar toggle ---- */

$("#btn-menu").addEventListener("click", () => {
  $("#sidebar").classList.toggle("open");
});
document.addEventListener("click", (e) => {
  const sidebar = $("#sidebar");
  if (!sidebar.classList.contains("open")) return;
  if (sidebar.contains(e.target) || e.target.closest("#btn-menu")) return;
  sidebar.classList.remove("open");
});

/* ---- Add function button ---- */

$("#btn-add-fn").addEventListener("click", () => {
  if (mode === "param") {
    const c = addCurve();
    focusCurveInput(c.id);
  } else {
    const f = addFunction();
    focusFnInput(f.id);
  }
  recomputeParams();
  persist();
});

/* ---- Persistence + sharing via URL hash ---- */

function serializeFns(fns) {
  return fns.map((f) => ({ expr: f.expr, color: f.color, enabled: f.enabled }));
}

function serializeCurves(curves) {
  return curves.map((c) => ({
    exprX: c.exprX, exprY: c.exprY, color: c.color, enabled: c.enabled, tMin: c.tMin, tMax: c.tMax,
  }));
}

function snapshotState() {
  return {
    mode,
    fns2d: serializeFns(graph2d.functions),
    fns3d: serializeFns(graph3d.functions),
    curvesParam: serializeCurves(graphParam.curves),
    view2d: { cx: graph2d.centerX, cy: graph2d.centerY, s: graph2d.scale },
    view3d: {
      az: graph3d.azimuth, el: graph3d.elevation, dist: graph3d.distance,
      domain: graph3d.domain, topo: graph3d.topo,
    },
    view4d: { az: graph4d.azimuth, el: graph4d.elevation, dist: graph4d.distance },
    params: paramValues,
    paramRanges,
    anim: { maxT: animMaxT, speed: animSpeed, t: animT },
  };
}

function persist() {
  try {
    localStorage.setItem("graphit-state", JSON.stringify(snapshotState()));
  } catch (e) {}
}

function shareUrl() {
  const state = snapshotState();
  state.fns2d = state.fns2d.filter((f) => f.expr.trim());
  state.fns3d = state.fns3d.filter((f) => f.expr.trim());
  state.curvesParam = state.curvesParam.filter((c) => (c.exprX || "").trim() || (c.exprY || "").trim());
  const encoded = btoa(encodeURIComponent(JSON.stringify(state)));
  const url = `${location.origin}${location.pathname}#d=${encoded}`;
  history.replaceState(null, "", url);
  return url;
}

$("#btn-share").addEventListener("click", async () => {
  const url = shareUrl();
  try {
    await navigator.clipboard.writeText(url);
    flashShareButton("Copied!");
  } catch (e) {
    flashShareButton("Link ready");
  }
});

function flashShareButton(msg) {
  const btn = $("#btn-share");
  const orig = btn.textContent;
  btn.textContent = "✅";
  btn.title = msg;
  setTimeout(() => { btn.textContent = orig; btn.title = "Copy shareable link"; }, 1200);
}

function loadFromHash() {
  if (!location.hash.startsWith("#d=")) return false;
  try {
    const encoded = location.hash.slice(3);
    const state = JSON.parse(decodeURIComponent(atob(encoded)));
    applyState(state);
    return true;
  } catch (e) {
    return false;
  }
}

function loadFromStorage() {
  try {
    const raw = localStorage.getItem("graphit-state");
    if (!raw) return false;
    applyState(JSON.parse(raw));
    return true;
  } catch (e) {
    return false;
  }
}

function applyState(state) {
  if (state.params) paramValues = state.params;
  if (state.paramRanges) paramRanges = state.paramRanges;
  if (state.anim) {
    animMaxT = state.anim.maxT ?? 20;
    animSpeed = state.anim.speed ?? 1;
    animT = state.anim.t ?? 0;
  }

  graph2d.functions = [];
  (state.fns2d || []).forEach((f) => {
    const nf = { id: ++fnIdCounter, expr: f.expr, color: f.color, enabled: f.enabled !== false, fn: null, error: null, params: new Set(), usesTime: false };
    graph2d.functions.push(nf);
    recompileWithAllowVars(nf, ["x", "t"]);
  });
  if (state.view2d) {
    graph2d.centerX = state.view2d.cx ?? 0;
    graph2d.centerY = state.view2d.cy ?? 0;
    graph2d.scale = state.view2d.s ?? 60;
  }

  graph3d.functions = [];
  (state.fns3d || []).forEach((f) => {
    const nf = { id: ++fnIdCounter, expr: f.expr, color: f.color, enabled: f.enabled !== false, fn: null, error: null, params: new Set(), usesTime: false };
    graph3d.functions.push(nf);
    recompileWithAllowVars(nf, ["x", "y", "t"]);
  });
  if (state.view3d) {
    graph3d.azimuth = state.view3d.az ?? -0.7;
    graph3d.elevation = state.view3d.el ?? 0.55;
    graph3d.distance = state.view3d.dist ?? 16;
    graph3d.domain = state.view3d.domain ?? 5;
    graph3d.topo = !!state.view3d.topo;
  }

  graphParam.curves = [];
  (state.curvesParam || []).forEach((c) => {
    const nc = {
      id: ++fnIdCounter, exprX: c.exprX || "", exprY: c.exprY || "", color: c.color,
      enabled: c.enabled !== false, fnX: null, fnY: null, errorX: null, errorY: null,
      params: new Set(), tMin: c.tMin ?? 0, tMax: c.tMax ?? 2 * Math.PI,
    };
    graphParam.curves.push(nc);
    recompileCurve(nc);
  });

  if (state.view4d) {
    graph4d.azimuth = state.view4d.az ?? -0.7;
    graph4d.elevation = state.view4d.el ?? 0.4;
    graph4d.distance = state.view4d.dist ?? 7;
  }

  mode = MODES.includes(state.mode) ? state.mode : "2d";
}

function recompileWithAllowVars(f, allowVars) {
  if (!f.expr.trim()) return;
  try {
    const result = compileExpression(f.expr, allowVars);
    f.fn = result.fn;
    f.params = result.params;
    f.usesTime = result.usesTime;
    f.error = null;
  } catch (e) {
    f.fn = null;
    f.params = new Set();
    f.usesTime = false;
    f.error = e.message || "Invalid expression";
  }
}

/* ---- Init ---- */

let savedTheme = "light";
try {
  savedTheme = localStorage.getItem("graphit-theme") ||
    (window.matchMedia && window.matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light");
} catch (e) {
  savedTheme = (window.matchMedia && window.matchMedia("(prefers-color-scheme: dark)").matches) ? "dark" : "light";
}
document.documentElement.setAttribute("data-theme", savedTheme === "dark" ? "dark" : "light");

let loaded = false;
try { loaded = loadFromHash() || loadFromStorage(); } catch (e) { loaded = false; }
if (!loaded) {
  graph2d.functions = [];
  addFunction("sin(x)");
  addFunction("x^2/4 - 2");

  graph3d.functions = [];
  const savedMode = mode;
  mode = "3d";
  addFunction("x^2 - y^2");
  mode = savedMode;

  graphParam.curves = [];
  addCurve("a*sin(b*t + c)", "a*sin(d*t)", null, true, 0, 2 * Math.PI);
}

$("#domain-input").value = graph3d.domain;
$("#anim-max-t").value = animMaxT;
$("#anim-speed").value = animSpeed;
$("#anim-t-slider").max = animMaxT;
$("#anim-t-slider").value = Math.min(animT, animMaxT);
$("#anim-t-readout").textContent = "t = " + fmt(animT);
for (const m of MODES) $(`#tab-${m}`).classList.toggle("active", mode === m);
canvas2d.classList.toggle("hidden", mode !== "2d");
canvas3d.classList.toggle("hidden", mode !== "3d");
canvasParam.classList.toggle("hidden", mode !== "param");
canvas4d.classList.toggle("hidden", mode !== "4d");
$("#presets-3d").classList.toggle("hidden", mode !== "3d");
$("#presets-param").classList.toggle("hidden", mode !== "param");
$("#domain-control").classList.toggle("hidden", mode !== "3d");
$("#btn-topo").classList.toggle("hidden", mode !== "3d");
$("#btn-topo").classList.toggle("active", graph3d.topo);
$("#btn-add-fn").classList.toggle("hidden", mode === "4d");
$("#fn-list").classList.toggle("hidden", mode === "4d");
$("#four-d-info").classList.toggle("hidden", mode !== "4d");
$("#hint-text").innerHTML = HINTS[mode];

if (mode === "param") renderCurveList();
else if (mode !== "4d") renderFnList();
recomputeParams();
updateAnimBar();

graph2d.resize();
graph3d.recompute();
graph3d.resize();
graphParam.resize();
graph4d.resize();
if (mode === "4d") playAnimation();

window.addEventListener("resize", () => {
  graph2d.resize();
  graph3d.resize();
  graphParam.resize();
  graph4d.resize();
});

setInterval(persist, 4000);

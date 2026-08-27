"use strict";

/* =========================================================================
   Math expression parser
   Tokenizes -> shunting-yard (with implicit multiplication) -> compiles
   to a fast closure evaluator fn(x) => number.
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
    if (/[a-zA-Z_]/.test(c)) {
      let j = i + 1;
      while (j < n && /[a-zA-Z_0-9]/.test(src[j])) j++;
      const name = src.slice(i, j).toLowerCase();
      if (FUNCS[name]) {
        tokens.push({ type: "ident", kind: "func", name });
      } else if (CONSTS[name] !== undefined) {
        tokens.push({ type: "ident", kind: "value", name });
      } else if (name === "x") {
        tokens.push({ type: "ident", kind: "value", name: "x" });
      } else if (name === "ans") {
        tokens.push({ type: "ident", kind: "value", name: "ans" });
      } else {
        // Unknown identifier: treat each letter as implicit-multiplied variable
        // is overkill; instead treat whole run as a single unknown value (will
        // error at eval time unless it's x-like). Safer: throw clear error.
        throw new MathError(`Unknown symbol "${name}"`);
      }
      i = j;
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
  let prevType = null; // for detecting unary minus

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
      stack.pop(); // discard "("
      if (stack.length && stack[stack.length - 1].type === "ident" && stack[stack.length - 1].kind === "func") {
        output.push(stack.pop());
      }
    } else if (t.type === "op") {
      let op = t.op;
      if (op === "-" && !isValueEnd(tokens[k - 1])) {
        op = "u"; // unary minus
      } else if (op === "+" && !isValueEnd(tokens[k - 1])) {
        prevType = t;
        continue; // unary plus is a no-op
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
    prevType = t;
  }
  while (stack.length) {
    const top = stack.pop();
    if (top.type === "(" || top.type === ")") throw new MathError("Mismatched parentheses");
    output.push(top);
  }
  return output;
}

function compileRPN(rpn) {
  return function evaluate(x, ans) {
    const stack = [];
    for (const t of rpn) {
      if (t.type === "num") {
        stack.push(t.value);
      } else if (t.type === "ident") {
        if (t.name === "x") stack.push(x);
        else if (t.name === "ans") stack.push(ans === undefined ? 0 : ans);
        else if (CONSTS[t.name] !== undefined) stack.push(CONSTS[t.name]);
        else if (FUNCS[t.name]) {
          if (stack.length < 1) throw new MathError("Invalid expression");
          const a = stack.pop();
          stack.push(FUNCS[t.name](a));
        } else {
          throw new MathError(`Unknown identifier "${t.name}"`);
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
 * Parses a math expression string into a fast evaluator function.
 * @param {string} src
 * @returns {(x:number, ans?:number)=>number}
 */
function compileExpression(src) {
  if (!src || !src.trim()) throw new MathError("Empty expression");
  const tokens = insertImplicitMultiplication(tokenize(src));
  const rpn = toRPN(tokens);
  const fn = compileRPN(rpn);
  // Smoke-test compile at x=1 to surface structural errors immediately.
  fn(1, 0);
  return fn;
}

/* =========================================================================
   Graph engine
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
    this.scale = 60; // pixels per unit
    this.dpr = Math.max(1, window.devicePixelRatio || 1);
    this.width = 0;
    this.height = 0;
    this.functions = []; // {id, expr, color, enabled, fn, error}
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

    // Minor grid
    ctx.strokeStyle = gridMinor;
    ctx.lineWidth = 1;
    this._drawGridLines(stepMinor);

    // Major grid
    ctx.strokeStyle = gridMajor;
    ctx.lineWidth = 1;
    this._drawGridLines(stepMajor);

    // Axes
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

    // Axis labels
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

    // Functions
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
        wy = f.fn(wx);
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

  /** Finds the closest plotted point (across enabled functions) to a pixel coord. */
  findNearest(px, py) {
    let best = null;
    for (const f of this.functions) {
      if (!f.enabled || !f.fn) continue;
      const wx = this.pxToWorldX(px);
      let wy;
      try { wy = f.fn(wx); } catch (e) { continue; }
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
   UI wiring
   ========================================================================= */

const $ = (sel) => document.querySelector(sel);

const canvas = $("#graph");
const graph = new Graph(canvas);

let fnIdCounter = 0;
let lastAns = 0;

function nextColor() {
  const used = graph.functions.map((f) => f.color);
  for (const c of PALETTE) if (!used.includes(c)) return c;
  return PALETTE[graph.functions.length % PALETTE.length];
}

function addFunction(expr = "", color = null, enabled = true) {
  const f = {
    id: ++fnIdCounter,
    expr,
    color: color || nextColor(),
    enabled,
    fn: null,
    error: null,
  };
  graph.functions.push(f);
  recompile(f);
  renderFnList();
  graph.draw();
  return f;
}

function recompile(f) {
  if (!f.expr.trim()) {
    f.fn = null;
    f.error = null;
    return;
  }
  try {
    f.fn = compileExpression(f.expr);
    f.error = null;
  } catch (e) {
    f.fn = null;
    f.error = e.message || "Invalid expression";
  }
}

function removeFunction(id) {
  graph.functions = graph.functions.filter((f) => f.id !== id);
  renderFnList();
  graph.draw();
  persist();
}

function renderFnList() {
  const list = $("#fn-list");
  list.innerHTML = "";
  graph.functions.forEach((f, idx) => {
    const row = document.createElement("div");
    row.className = "fn-row" + (f.enabled ? "" : " disabled");

    const swatch = document.createElement("button");
    swatch.className = "fn-swatch";
    swatch.style.background = f.color;
    swatch.title = "Toggle visibility";
    swatch.addEventListener("click", () => {
      f.enabled = !f.enabled;
      row.classList.toggle("disabled", !f.enabled);
      graph.draw();
      persist();
    });

    const prefix = document.createElement("span");
    prefix.className = "fn-prefix";
    prefix.textContent = `y${idx + 1}=`;

    const input = document.createElement("input");
    input.className = "fn-input" + (f.error ? " error" : "");
    input.type = "text";
    input.spellcheck = false;
    input.autocomplete = "off";
    input.value = f.expr;
    input.placeholder = "e.g. sin(x) + x/2";
    if (f.error) input.title = f.error;
    input.addEventListener("input", () => {
      f.expr = input.value;
      recompile(f);
      input.classList.toggle("error", !!f.error);
      input.title = f.error || "";
      graph.draw();
      persist();
    });
    input.addEventListener("keydown", (e) => {
      if (e.key === "Enter") {
        e.preventDefault();
        if (idx === graph.functions.length - 1) {
          const nf = addFunction();
          focusFnInput(nf.id);
        } else {
          focusFnInput(graph.functions[idx + 1].id);
        }
      } else if (e.key === "Backspace" && input.value === "" && graph.functions.length > 1) {
        e.preventDefault();
        removeFunction(f.id);
        const prevIdx = Math.max(0, idx - 1);
        if (graph.functions[prevIdx]) focusFnInput(graph.functions[prevIdx].id);
      }
    });

    const del = document.createElement("button");
    del.className = "fn-del";
    del.textContent = "✕";
    del.title = "Delete";
    del.addEventListener("click", () => removeFunction(f.id));

    row.append(swatch, prefix, input, del);
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

/* ---- Panning / zooming ---- */

let isDragging = false;
let dragLast = null;
let dragMoved = false;

canvas.addEventListener("mousedown", (e) => {
  isDragging = true;
  dragMoved = false;
  dragLast = { x: e.clientX, y: e.clientY };
  canvas.style.cursor = "grabbing";
});

window.addEventListener("mousemove", (e) => {
  if (isDragging) {
    const dx = e.clientX - dragLast.x;
    const dy = e.clientY - dragLast.y;
    if (Math.abs(dx) > 1 || Math.abs(dy) > 1) dragMoved = true;
    dragLast = { x: e.clientX, y: e.clientY };
    graph.panByPixels(dx, dy);
  } else {
    handleHover(e);
  }
});

window.addEventListener("mouseup", () => {
  isDragging = false;
  canvas.style.cursor = "crosshair";
});

canvas.addEventListener("mouseleave", () => {
  $("#coord-readout").classList.add("hidden");
});

canvas.addEventListener("wheel", (e) => {
  e.preventDefault();
  const rect = canvas.getBoundingClientRect();
  const px = e.clientX - rect.left;
  const py = e.clientY - rect.top;
  const factor = Math.pow(1.0016, -e.deltaY);
  graph.zoomAt(px, py, factor);
}, { passive: false });

function handleHover(e) {
  const rect = canvas.getBoundingClientRect();
  const px = e.clientX - rect.left;
  const py = e.clientY - rect.top;
  const readout = $("#coord-readout");
  if (px < 0 || py < 0 || px > rect.width || py > rect.height) {
    readout.classList.add("hidden");
    return;
  }
  const nearest = graph.findNearest(px, py);
  const wx = graph.pxToWorldX(px);
  const wy = graph.pxToWorldY(py);
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

// Touch support: 1-finger pan, 2-finger pinch zoom.
let touchState = null;

canvas.addEventListener("touchstart", (e) => {
  if (e.touches.length === 1) {
    touchState = { mode: "pan", x: e.touches[0].clientX, y: e.touches[0].clientY };
  } else if (e.touches.length === 2) {
    const [a, b] = e.touches;
    touchState = {
      mode: "pinch",
      dist: Math.hypot(a.clientX - b.clientX, a.clientY - b.clientY),
      midX: (a.clientX + b.clientX) / 2,
      midY: (a.clientY + b.clientY) / 2,
    };
  }
}, { passive: true });

canvas.addEventListener("touchmove", (e) => {
  e.preventDefault();
  const rect = canvas.getBoundingClientRect();
  if (e.touches.length === 1 && touchState && touchState.mode === "pan") {
    const dx = e.touches[0].clientX - touchState.x;
    const dy = e.touches[0].clientY - touchState.y;
    touchState.x = e.touches[0].clientX;
    touchState.y = e.touches[0].clientY;
    graph.panByPixels(dx, dy);
  } else if (e.touches.length === 2 && touchState && touchState.mode === "pinch") {
    const [a, b] = e.touches;
    const dist = Math.hypot(a.clientX - b.clientX, a.clientY - b.clientY);
    const midX = (a.clientX + b.clientX) / 2 - rect.left;
    const midY = (a.clientY + b.clientY) / 2 - rect.top;
    const factor = dist / touchState.dist;
    graph.zoomAt(midX, midY, factor);
    touchState.dist = dist;
  }
}, { passive: false });

canvas.addEventListener("touchend", (e) => {
  if (e.touches.length === 0) {
    touchState = null;
    persist();
  }
});

$("#btn-zoom-in").addEventListener("click", () => graph.zoomAt(graph.width / 2, graph.height / 2, 1.4));
$("#btn-zoom-out").addEventListener("click", () => graph.zoomAt(graph.width / 2, graph.height / 2, 1 / 1.4));
$("#btn-reset-view").addEventListener("click", () => graph.resetView());

window.addEventListener("mouseup", () => { if (dragMoved) persist(); });

/* ---- Quick calc ---- */

const qcInput = $("#quickcalc-input");
const qcResult = $("#quickcalc-result");

function runQuickCalc() {
  const src = qcInput.value.trim();
  if (!src) { qcResult.textContent = ""; return; }
  try {
    const fn = compileExpression(src);
    const val = fn(NaN, lastAns);
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

/* ---- Theme ---- */

function applyTheme(theme) {
  if (theme === "dark") document.documentElement.setAttribute("data-theme", "dark");
  else document.documentElement.setAttribute("data-theme", "light");
  graph.draw();
}

$("#btn-theme").addEventListener("click", () => {
  const cur = document.documentElement.getAttribute("data-theme") || "light";
  const next = cur === "dark" ? "light" : "dark";
  applyTheme(next);
  localStorage.setItem("graphit-theme", next);
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
  const f = addFunction();
  focusFnInput(f.id);
  persist();
});

/* ---- Persistence + sharing via URL hash ---- */

function persist() {
  const state = {
    fns: graph.functions.map((f) => ({ expr: f.expr, color: f.color, enabled: f.enabled })),
    view: { cx: graph.centerX, cy: graph.centerY, s: graph.scale },
  };
  localStorage.setItem("graphit-state", JSON.stringify(state));
}

function shareUrl() {
  const state = {
    fns: graph.functions.filter((f) => f.expr.trim()).map((f) => ({ expr: f.expr, color: f.color, enabled: f.enabled })),
    view: { cx: graph.centerX, cy: graph.centerY, s: graph.scale },
  };
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
  graph.functions = [];
  (state.fns || []).forEach((f) => addFunction(f.expr, f.color, f.enabled !== false));
  if (state.view) {
    graph.centerX = state.view.cx ?? 0;
    graph.centerY = state.view.cy ?? 0;
    graph.scale = state.view.s ?? 60;
  }
}

/* ---- Init ---- */

const savedTheme = localStorage.getItem("graphit-theme") ||
  (window.matchMedia && window.matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light");
applyTheme(savedTheme);

const loaded = loadFromHash() || loadFromStorage();
if (!loaded) {
  addFunction("sin(x)");
  addFunction("x^2/4 - 2");
}
renderFnList();
graph.draw();

window.addEventListener("resize", () => graph.resize());

// Periodic autosave of view state while idle (covers pan/zoom without a
// discrete "end" event on some input paths).
setInterval(persist, 4000);

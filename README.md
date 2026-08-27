# GraphIt — Fast, Free Graphing Calculator

A zero-dependency, zero-build graphing calculator that runs entirely in the
browser. No frameworks, no bundler, no server — just `index.html`,
`styles.css`, and `app.js`. Open it locally or host it anywhere static files
are served, for free.

## Features

- **Plot multiple functions** of `x` at once, each with its own color, with
  toggle-visibility and delete controls.
- **Custom expression parser** (tokenizer → shunting-yard → compiled
  evaluator) supporting `+ - * / % ^`, parentheses, implicit multiplication
  (`2x`, `2sin(x)`, `(x+1)(x-1)`), and functions: `sin cos tan asin acos atan
  sinh cosh tanh sqrt cbrt abs log log2 ln exp floor ceil round sign`, plus
  constants `pi` and `e`.
- **Smooth pan & zoom**: drag to pan, scroll to zoom (desktop), one-finger
  pan / pinch-to-zoom (touch), or use the on-screen +/−/reset controls.
- **Live trace**: hover the graph to see coordinates, with cursor-snapping to
  the nearest plotted curve.
- **Quick calculator** bar for one-off numeric expressions.
- **On-screen scientific keypad** for fast entry of functions/symbols.
- **Light/dark theme**, auto-detected from system preference, toggleable.
- **Shareable links** — encodes your functions and viewport into the URL
  hash so you can copy/paste a link that reproduces the exact graph.
- **Autosave** to `localStorage` so your graph survives a page reload.
- **Responsive** layout with a collapsible functions drawer on mobile.

## Running it

No build step. Just open `index.html` in a browser, or serve the folder:

```bash
python3 -m http.server 8000
# then visit http://localhost:8000
```

## Deploying for free

Any static host works — e.g. GitHub Pages:

1. Push this repo to GitHub.
2. Repo Settings → Pages → Deploy from branch → select the branch/root.
3. Your calculator is live at `https://<user>.github.io/<repo>/`.

## Project structure

```
index.html   Page structure/layout
styles.css   Theming (light/dark) and responsive layout
app.js       Expression parser + canvas graphing engine + UI wiring
```

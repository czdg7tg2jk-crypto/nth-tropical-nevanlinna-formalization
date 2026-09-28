#!/usr/bin/env python3
"""Generate the whole-project Lean import graph.

The graph is derived from the actual ``import`` commands in every project
Lean file.  Mathlib imports are collapsed to one external node so that the
project architecture remains readable.
"""

from __future__ import annotations

import argparse
import html
import json
import re
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parents[1]
OUTPUT = PROJECT_ROOT / "home_page" / "nth_tropical_nevanlinna_lean_structure.html"
PREFIX = "NthTropicalNevanlinna"
IMPORT_RE = re.compile(r"^\s*import\s+(.+?)\s*$")

GROUP_ORDER = {
    "External": 0,
    "Function": 1,
    "PoissonJensen": 2,
    "Nevanlinna": 3,
    "LogDerivative": 4,
    "Curves": 5,
    "Truncated": 6,
    "Cross-project": 7,
    "Paper": 8,
    "Entry point": 9,
}


def module_name(path: Path) -> str:
    relative = path.relative_to(PROJECT_ROOT).with_suffix("")
    return ".".join(relative.parts)


def group_name(module: str) -> str:
    if module == PREFIX:
        return "Entry point"
    suffix = module.removeprefix(PREFIX + ".")
    first = suffix.split(".", 1)[0]
    if first == "Counterexamples":
        return "Cross-project"
    return first


def short_label(module: str) -> str:
    if module == PREFIX:
        return "NthTropicalNevanlinna.lean"
    return module.removeprefix(PREFIX + ".")


def imports_of(path: Path) -> list[str]:
    imports: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = IMPORT_RE.match(line)
        if match:
            imports.extend(match.group(1).split())
    return imports


def collect_graph() -> tuple[list[dict[str, object]], int]:
    lean_files = [PROJECT_ROOT / f"{PREFIX}.lean"]
    lean_files.extend(sorted((PROJECT_ROOT / PREFIX).rglob("*.lean")))
    modules = {module_name(path): path for path in lean_files}

    nodes: list[dict[str, object]] = [
        {
            "id": "Mathlib",
            "label": "Mathlib",
            "group": "External",
            "path": "https://github.com/leanprover-community/mathlib4",
            "deps": [],
        }
    ]
    edge_count = 0
    for module, path in modules.items():
        deps: list[str] = []
        has_mathlib = False
        for imported in imports_of(path):
            if imported in modules:
                deps.append(imported)
                edge_count += 1
            elif imported == "Mathlib" or imported.startswith("Mathlib."):
                has_mathlib = True
        if has_mathlib:
            deps.append("Mathlib")
        nodes.append(
            {
                "id": module,
                "label": short_label(module),
                "group": group_name(module),
                "path": "../" + path.relative_to(PROJECT_ROOT).as_posix(),
                "deps": sorted(set(deps)),
            }
        )

    nodes.sort(key=lambda node: (GROUP_ORDER.get(str(node["group"]), 99), str(node["label"])))
    return nodes, edge_count


def render(nodes: list[dict[str, object]], edge_count: int) -> str:
    node_json = json.dumps(nodes, ensure_ascii=False).replace("</", "<\\/")
    internal_count = len(nodes) - 1
    colors = {
        "External": "#7b8790",
        "Function": "#3f7f6b",
        "PoissonJensen": "#9a6d32",
        "Nevanlinna": "#39739d",
        "LogDerivative": "#7656a5",
        "Curves": "#a9536f",
        "Truncated": "#a34f3d",
        "Cross-project": "#626f3a",
        "Paper": "#2f6f55",
        "Entry point": "#183f59",
    }
    by_id = {str(node["id"]): node for node in nodes}
    levels: dict[str, int] = {}

    def level_of(node_id: str) -> int:
        if node_id in levels:
            return levels[node_id]
        deps = [str(dep) for dep in by_id[node_id]["deps"] if str(dep) in by_id]
        levels[node_id] = 0 if not deps else 1 + max(level_of(dep) for dep in deps)
        return levels[node_id]

    for node in nodes:
        level_of(str(node["id"]))
    columns: dict[int, list[dict[str, object]]] = {}
    for node in nodes:
        columns.setdefault(levels[str(node["id"])], []).append(node)
    for column in columns.values():
        column.sort(key=lambda node: (GROUP_ORDER.get(str(node["group"]), 99), str(node["label"])))

    node_width, node_height, column_gap, row_gap, padding = 218, 78, 88, 22, 28
    max_level = max(columns)
    max_rows = max(len(column) for column in columns.values())
    width = padding * 2 + (max_level + 1) * node_width + max_level * column_gap
    height = max(760, padding * 2 + max_rows * node_height + (max_rows - 1) * row_gap)
    positions: dict[str, tuple[float, float]] = {}
    static_nodes: list[str] = []
    for level in range(max_level + 1):
        column = columns.get(level, [])
        column_height = len(column) * node_height + max(0, len(column) - 1) * row_gap
        start_y = (height - column_height) / 2
        for row, node in enumerate(column):
            node_id = str(node["id"])
            x = padding + level * (node_width + column_gap)
            y = start_y + row * (node_height + row_gap)
            positions[node_id] = (x, y)
            group = str(node["group"])
            static_nodes.append(
                f'<button type="button" class="module" data-id="{html.escape(node_id)}" '
                f'style="left:{x}px;top:{y:.1f}px;--group-color:{colors.get(group, colors["External"])}">'
                f'<span class="module-name">{html.escape(str(node["label"]))}</span>'
                f'<span class="module-group">{html.escape(group)}</span></button>'
            )
    static_edges: list[str] = []
    for target in nodes:
        target_id = str(target["id"])
        tx, ty0 = positions[target_id]
        ty = ty0 + node_height / 2
        for source_value in target["deps"]:
            source_id = str(source_value)
            if source_id not in positions:
                continue
            sx0, sy0 = positions[source_id]
            sx, sy = sx0 + node_width, sy0 + node_height / 2
            bend = max(34, (tx - sx) * 0.44)
            static_edges.append(
                f'<path class="dep-edge" data-source="{html.escape(source_id)}" '
                f'data-target="{html.escape(target_id)}" '
                f'd="M {sx:.1f} {sy:.1f} C {sx+bend:.1f} {sy:.1f}, {tx-bend:.1f} {ty:.1f}, {tx:.1f} {ty:.1f}"></path>'
            )
    static_legend = "".join(
        f'<span style="--group-color:{colors[group]}"><i class="swatch"></i>{html.escape(group)}</span>'
        for group in GROUP_ORDER
    )
    template = r'''<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Whole-project Lean dependency graph - n-th Tropical Nevanlinna Theory</title>
  <style>
    :root {
      color-scheme: light dark;
      --paper:#f5f6f7; --surface:#fff; --ink:#17212b; --muted:#65717d;
      --rule:#d8dee4; --accent:#245c7c; --edge:#8796a0;
      --edge-active:#245c7c; --verified:#2f6f55; --shadow:0 10px 30px rgba(23,33,43,.08);
    }
    * { box-sizing:border-box; }
    body { margin:0; background:var(--paper); color:var(--ink); font-family:Inter,ui-sans-serif,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif; line-height:1.45; }
    main { max-width:1760px; margin:0 auto; padding:42px 24px 60px; }
    h1,h2,p { margin-top:0; }
    h1,h2,.module-name,.detail-title { font-family:"STIX Two Text","Libertinus Serif",Georgia,serif; }
    h1 { margin-bottom:9px; font-size:clamp(2rem,4vw,3rem); line-height:1.08; font-weight:600; }
    h2 { margin-bottom:5px; font-size:1.42rem; }
    a { color:var(--accent); text-underline-offset:3px; }
    .eyebrow { margin-bottom:10px; color:var(--accent); font-size:.74rem; font-weight:700; letter-spacing:.11em; text-transform:uppercase; }
    .lede { max-width:86ch; margin-bottom:0; color:var(--muted); }
    .toolbar { display:flex; flex-wrap:wrap; gap:9px; margin:22px 0; }
    .toolbar a,.toolbar button { padding:7px 11px; border:1px solid var(--rule); border-radius:999px; background:var(--surface); color:var(--accent); font:inherit; font-size:.84rem; text-decoration:none; cursor:pointer; }
    .toolbar a:hover,.toolbar button:hover,.toolbar a:focus-visible,.toolbar button:focus-visible { border-color:var(--accent); }
    .summary,.graph-panel,.detail-panel,.note { border:1px solid var(--rule); border-radius:14px; background:var(--surface); box-shadow:var(--shadow); }
    .summary { display:flex; flex-wrap:wrap; align-items:center; gap:12px 24px; padding:15px 18px; color:var(--muted); font-size:.86rem; }
    .summary strong { color:var(--ink); }
    .status { margin-left:auto; color:var(--verified); font-weight:650; }
    .status::before { content:"✓"; margin-right:6px; }
    .legend { display:flex; flex-wrap:wrap; gap:7px 14px; margin:18px 0; color:var(--muted); font-size:.76rem; }
    .legend span { display:inline-flex; align-items:center; gap:6px; }
    .swatch { width:11px; height:11px; border-radius:50%; background:var(--group-color); }
    .graph-panel { padding:18px; overflow:hidden; }
    .graph-heading { display:flex; justify-content:space-between; align-items:start; gap:24px; }
    .graph-heading p { max-width:80ch; margin-bottom:0; color:var(--muted); }
    .view-tools { display:grid; justify-items:end; gap:9px; }
    .view-controls { display:flex; gap:7px; }
    .view-controls button { padding:6px 9px; border:1px solid var(--rule); border-radius:8px; background:var(--paper); color:var(--accent); font:inherit; font-size:.75rem; cursor:pointer; }
    .view-controls button:hover,.view-controls button:focus-visible { border-color:var(--accent); }
    .search { min-width:260px; padding:8px 10px; border:1px solid var(--rule); border-radius:9px; background:var(--paper); color:var(--ink); font:inherit; }
    .graph-scroll { margin-top:18px; overflow:auto; border-top:1px solid var(--rule); }
    .graph-stage { position:relative; }
    .graph-board { position:relative; min-height:760px; margin:20px 0; }
    .edge-layer { position:absolute; inset:0; z-index:0; width:100%; height:100%; overflow:visible; pointer-events:none; }
    .module-layer { position:absolute; inset:0; z-index:1; }
    .dep-edge { fill:none; stroke:var(--edge); stroke-width:1.35; stroke-opacity:.50; marker-end:url(#arrow); transition:opacity 140ms ease,stroke 140ms ease,stroke-width 140ms ease; }
    .dep-edge.is-active { stroke:var(--edge-active); stroke-width:2.4; stroke-opacity:1; marker-end:url(#arrow-active); }
    .dep-edge.is-dim { opacity:.055; }
    .module { position:absolute; width:218px; min-height:78px; padding:10px 11px 9px 14px; border:1px solid var(--rule); border-left:5px solid var(--group-color); border-radius:10px; background:var(--surface); color:var(--ink); font:inherit; text-align:left; cursor:pointer; box-shadow:0 4px 12px rgba(23,33,43,.06); transition:opacity 140ms ease,border-color 140ms ease,box-shadow 140ms ease; }
    .module:hover,.module:focus-visible { border-color:var(--accent); }
    .module.is-selected { border-color:var(--accent); box-shadow:0 0 0 2px var(--accent); }
    .module.is-related { border-color:var(--edge-active); }
    .module.is-dim { opacity:.18; }
    .module-name { display:block; font-size:.88rem; font-weight:600; line-height:1.16; overflow-wrap:anywhere; }
    .module-group { display:block; margin-top:7px; color:var(--muted); font-size:.63rem; letter-spacing:.06em; text-transform:uppercase; }
    .detail-panel { display:grid; grid-template-columns:minmax(230px,.8fr) minmax(360px,1.5fr); gap:22px 34px; margin-top:20px; padding:21px; }
    .detail-label { margin-bottom:4px; color:var(--muted); font-size:.67rem; letter-spacing:.07em; text-transform:uppercase; }
    .detail-title { margin-bottom:7px; font-size:1.08rem; font-weight:600; overflow-wrap:anywhere; }
    .detail-source { font-family:ui-monospace,SFMono-Regular,Menlo,monospace; font-size:.76rem; overflow-wrap:anywhere; }
    .detail-list { margin:0; padding-left:1.1rem; columns:2; column-gap:30px; }
    .detail-list li { break-inside:avoid; margin:2px 0; font-size:.8rem; overflow-wrap:anywhere; }
    .note { margin-top:20px; padding:16px 19px; color:var(--muted); font-size:.88rem; }
    .note strong { color:var(--ink); }
    @media (prefers-color-scheme:dark) {
      :root { --paper:#11171c; --surface:#182128; --ink:#edf1f4; --muted:#aab4bd; --rule:#35434e; --accent:#8fc9e9; --edge:#748894; --edge-active:#8fc9e9; --verified:#83c9aa; --shadow:none; }
    }
    @media (max-width:780px) { main{padding:28px 14px 44px}.graph-heading{display:block}.view-tools{justify-items:stretch;margin-top:14px}.search{width:100%;min-width:0}.detail-panel{grid-template-columns:1fr}.detail-list{columns:1}.status{margin-left:0}.graph-panel{padding:13px} }
  </style>
</head>
<body>
<main>
  <div class="eyebrow">Implementation architecture</div>
  <h1>Whole-project Lean dependency graph</h1>
  <p class="lede">Every project module is displayed in one directed acyclic graph. An arrow A → B means that B directly imports A. Paper-order interfaces, implementation modules, cross-project assemblies, and the top-level entry point remain visible together.</p>

  <nav class="toolbar" aria-label="Related resources">
    <a href="../blueprint/web/index.html">Web Blueprint</a>
    <a href="../blueprint/web/dep_graph_document.html">Formal proof graph</a>
    <a href="nth_tropical_nevanlinna_dependency_graph.html">Mathematical dependency graph</a>
    <a href="../NthTropicalNevanlinna/Paper.lean">Paper-order Lean entry</a>
    <button id="reset" type="button">Show complete graph</button>
  </nav>

  <section class="summary" aria-label="Graph coverage">
    <span><strong>__INTERNAL_COUNT__</strong> project Lean files</span>
    <span><strong>__EDGE_COUNT__</strong> direct internal imports</span>
    <span><strong>1</strong> collapsed external dependency</span>
    <span class="status">Generated from current imports</span>
  </section>
  <div class="legend" id="legend" aria-label="Module groups">__STATIC_LEGEND__</div>

  <section class="graph-panel" aria-labelledby="graph-title">
    <div class="graph-heading">
      <div>
        <h2 id="graph-title">From Mathlib foundations to the public library entry</h2>
        <p>The graph is topologically ordered from left to right. Select a module to isolate its direct imports and direct downstream consumers.</p>
      </div>
      <div class="view-tools">
        <input class="search" id="search" type="search" placeholder="Find a module…" aria-label="Find a module">
        <div class="view-controls" aria-label="Graph zoom controls">
          <button id="fit-width" type="button">Fit whole graph</button>
          <button id="zoom-out" type="button">−</button>
          <button id="zoom-reset" type="button">100%</button>
          <button id="zoom-in" type="button">+</button>
        </div>
      </div>
    </div>
    <div class="graph-scroll">
      <div class="graph-stage" id="graph-stage" style="width:__WIDTH__px;height:__STAGE_HEIGHT__px">
        <div class="graph-board" id="graph-board" style="width:__WIDTH__px;height:__HEIGHT__px">
          <svg class="edge-layer" id="edge-layer" aria-hidden="true" viewBox="0 0 __WIDTH__ __HEIGHT__" width="__WIDTH__" height="__HEIGHT__">
            <defs>
              <marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto">
                <path d="M 0 0 L 10 5 L 0 10 z" fill="var(--edge)"></path>
              </marker>
              <marker id="arrow-active" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto">
                <path d="M 0 0 L 10 5 L 0 10 z" fill="var(--edge-active)"></path>
              </marker>
            </defs>
            <g id="edge-paths">__STATIC_EDGES__</g>
          </svg>
          <div class="module-layer" id="module-layer">__STATIC_NODES__</div>
        </div>
      </div>
    </div>
  </section>

  <section class="detail-panel" aria-live="polite">
    <div>
      <div class="detail-label">Selected module</div>
      <div class="detail-title" id="detail-title">Complete project</div>
      <a class="detail-source" id="detail-source"></a>
      <div class="detail-label" style="margin-top:14px">Module group</div>
      <div id="detail-group"></div>
    </div>
    <div>
      <div class="detail-label">Direct imports</div>
      <ul class="detail-list" id="detail-inputs"></ul>
      <div class="detail-label" style="margin-top:13px">Direct downstream modules</div>
      <ul class="detail-list" id="detail-outputs"></ul>
    </div>
  </section>

  <aside class="note"><strong>Scope.</strong> This is the engineering graph of Lean files and direct imports. The mathematical dependency graph records theorem-level use instead. The two graphs intentionally answer different questions.</aside>
</main>

<script>
(() => {
  "use strict";
  const nodes = __NODES__;
  const colors = {
    "External":"#7b8790", "Function":"#3f7f6b", "PoissonJensen":"#9a6d32",
    "Nevanlinna":"#39739d", "LogDerivative":"#7656a5", "Curves":"#a9536f",
    "Truncated":"#a34f3d", "Cross-project":"#626f3a", "Paper":"#2f6f55", "Entry point":"#183f59"
  };
  const groupOrder = ["External","Function","PoissonJensen","Nevanlinna","LogDerivative","Curves","Truncated","Cross-project","Paper","Entry point"];
  const byId = new Map(nodes.map(node => [node.id,node]));
  const outputs = new Map(nodes.map(node => [node.id,[]]));
  nodes.forEach(node => node.deps.forEach(dep => { if(outputs.has(dep)) outputs.get(dep).push(node.id); }));

  const board = document.getElementById("graph-board");
  const stage = document.getElementById("graph-stage");
  const graphScroll = document.querySelector(".graph-scroll");
  const layer = document.getElementById("module-layer");
  const svg = document.getElementById("edge-layer");
  const edgePaths = document.getElementById("edge-paths");
  const detailTitle = document.getElementById("detail-title");
  const detailSource = document.getElementById("detail-source");
  const detailGroup = document.getElementById("detail-group");
  const detailInputs = document.getElementById("detail-inputs");
  const detailOutputs = document.getElementById("detail-outputs");
  const search = document.getElementById("search");

  const levelMemo = new Map();
  const levelOf = (id,stack=new Set()) => {
    if(levelMemo.has(id)) return levelMemo.get(id);
    if(stack.has(id)) return 0;
    const node = byId.get(id);
    const internalDeps = node.deps.filter(dep => byId.has(dep));
    const level = internalDeps.length===0 ? 0 : 1+Math.max(...internalDeps.map(dep=>levelOf(dep,new Set(stack).add(id))));
    levelMemo.set(id,level);
    return level;
  };
  nodes.forEach(node => levelOf(node.id));
  const columns = new Map();
  nodes.forEach(node => {
    const level=levelMemo.get(node.id);
    if(!columns.has(level)) columns.set(level,[]);
    columns.get(level).push(node);
  });
  columns.forEach(column => column.sort((a,b) => groupOrder.indexOf(a.group)-groupOrder.indexOf(b.group) || a.label.localeCompare(b.label)));

  const nodeWidth=218, nodeHeight=78, columnGap=88, rowGap=22, padding=28;
  const maxLevel=Math.max(...columns.keys());
  const maxRows=Math.max(...[...columns.values()].map(column=>column.length));
  const width=padding*2+(maxLevel+1)*nodeWidth+maxLevel*columnGap;
  const height=Math.max(760,padding*2+maxRows*nodeHeight+(maxRows-1)*rowGap);
  board.style.width=`${width}px`;
  board.style.height=`${height}px`;
  svg.setAttribute("viewBox",`0 0 ${width} ${height}`);
  svg.setAttribute("width",String(width));
  svg.setAttribute("height",String(height));
  let zoom=1;
  const setZoom=value => {
    zoom=Math.max(.2,Math.min(1.4,value));
    board.style.transformOrigin="top left";
    board.style.transform=`scale(${zoom})`;
    stage.style.width=`${width*zoom}px`;
    stage.style.height=`${height*zoom+40}px`;
    document.getElementById("zoom-reset").textContent=`${Math.round(zoom*100)}%`;
  };

  const positions=new Map();
  for(let level=0;level<=maxLevel;level+=1){
    const column=columns.get(level)||[];
    const columnHeight=column.length*nodeHeight+Math.max(0,column.length-1)*rowGap;
    const startY=(height-columnHeight)/2;
    column.forEach((node,row) => {
      const x=padding+level*(nodeWidth+columnGap);
      const y=startY+row*(nodeHeight+rowGap);
      positions.set(node.id,{x,y});
    });
  }
  layer.querySelectorAll(".module").forEach(element=>element.addEventListener("click",()=>selectNode(element.dataset.id)));

  const setList=(element,items,emptyText) => {
    element.replaceChildren();
    const values=items.length?items:[emptyText];
    values.forEach(value=>{ const li=document.createElement("li"); li.textContent=value; element.appendChild(li); });
  };
  const reset=() => {
    layer.querySelectorAll(".module").forEach(node=>node.classList.remove("is-selected","is-related","is-dim"));
    edgePaths.querySelectorAll(".dep-edge").forEach(edge=>edge.classList.remove("is-active","is-dim"));
    detailTitle.textContent="Complete project";
    detailSource.removeAttribute("href"); detailSource.textContent="";
    detailGroup.textContent="All module groups";
    setList(detailInputs,[],"Select a module to inspect its imports");
    setList(detailOutputs,[],"Select a module to inspect its consumers");
    search.value="";
  };
  const selectNode=id => {
    const node=byId.get(id);
    const related=new Set([id,...node.deps,...(outputs.get(id)||[])]);
    layer.querySelectorAll(".module").forEach(element=>{
      const nodeId=element.dataset.id;
      element.classList.toggle("is-selected",nodeId===id);
      element.classList.toggle("is-related",related.has(nodeId)&&nodeId!==id);
      element.classList.toggle("is-dim",!related.has(nodeId));
    });
    edgePaths.querySelectorAll(".dep-edge").forEach(edge=>{
      const active=edge.dataset.source===id||edge.dataset.target===id;
      edge.classList.toggle("is-active",active);
      edge.classList.toggle("is-dim",!active);
    });
    detailTitle.textContent=node.id;
    detailSource.href=node.path;
    detailSource.textContent=node.path;
    detailGroup.textContent=node.group;
    setList(detailInputs,node.deps,"No project dependency");
    setList(detailOutputs,outputs.get(id)||[],"No direct downstream module");
  };

  document.getElementById("reset").addEventListener("click",reset);
  document.getElementById("zoom-out").addEventListener("click",()=>setZoom(zoom-.1));
  document.getElementById("zoom-in").addEventListener("click",()=>setZoom(zoom+.1));
  document.getElementById("zoom-reset").addEventListener("click",()=>setZoom(1));
  document.getElementById("fit-width").addEventListener("click",()=>setZoom((graphScroll.clientWidth-24)/width));
  search.addEventListener("input",() => {
    const query=search.value.trim().toLowerCase();
    if(!query){ reset(); return; }
    layer.querySelectorAll(".module").forEach(element=>element.classList.toggle("is-dim",!element.dataset.id.toLowerCase().includes(query)));
    edgePaths.querySelectorAll(".dep-edge").forEach(edge=>edge.classList.add("is-dim"));
  });
  setZoom(.75);
  reset();
})();
</script>
</body>
</html>
'''
    return (
        template.replace("__NODES__", node_json)
        .replace("__INTERNAL_COUNT__", str(internal_count))
        .replace("__EDGE_COUNT__", str(edge_count))
        .replace("__STATIC_LEGEND__", static_legend)
        .replace("__STATIC_NODES__", "\n".join(static_nodes))
        .replace("__STATIC_EDGES__", "\n".join(static_edges))
        .replace("__WIDTH__", str(width))
        .replace("__HEIGHT__", str(height))
        .replace("__STAGE_HEIGHT__", str(height + 40))
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="fail if the generated graph is stale")
    args = parser.parse_args()
    nodes, edge_count = collect_graph()
    generated = render(nodes, edge_count)
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text(encoding="utf-8") != generated:
            print(f"stale generated graph: {OUTPUT.relative_to(PROJECT_ROOT)}")
            return 1
        print(f"whole-project module graph is current ({len(nodes)-1} modules, {edge_count} internal imports)")
        return 0
    OUTPUT.write_text(generated, encoding="utf-8")
    print(f"wrote {OUTPUT.relative_to(PROJECT_ROOT)} ({len(nodes)-1} modules, {edge_count} internal imports)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

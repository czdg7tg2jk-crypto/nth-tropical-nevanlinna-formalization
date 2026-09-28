#!/usr/bin/env python3
"""Embed a no-JavaScript rendering in the mathematical dependency graph."""

from __future__ import annotations

import argparse
import html
import re
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parents[1]
TARGET = PROJECT_ROOT / "home_page" / "nth_tropical_nevanlinna_dependency_graph.html"
NODE_RE = re.compile(
    r'\{\s*id:"(?P<id>[^"]+)",\s*code:"(?P<code>[^"]+)",\s*section:"(?P<section>[^"]+)",'
    r'\s*title:"(?P<title>[^"]+)",\s*description:"(?P<description>[^"]+)",'
    r'\s*path:"(?P<path>[^"]+)",\s*kind:"(?P<kind>[^"]+)",\s*deps:\[(?P<deps>[^]]*)\]\s*\}'
)
EDGE_BLOCK_RE = re.compile(
    r'(?P<open><g id="dag-edge-layer">).*?(?P<close></g>)', re.DOTALL
)
NODE_BLOCK_RE = re.compile(
    r'(?P<open><div class="dag-levels" id="dag-levels">).*?(?P<close></div>)'
    r'(?=\s*</div>\s*</div>\s*<div class="node-detail")',
    re.DOTALL,
)


def parse_nodes(source: str) -> list[dict[str, object]]:
    nodes: list[dict[str, object]] = []
    for match in NODE_RE.finditer(source):
        deps = re.findall(r'"([^"]+)"', match.group("deps"))
        node: dict[str, object] = match.groupdict()
        node["deps"] = deps
        nodes.append(node)
    if not nodes:
        raise RuntimeError("could not find the mathematical graph node data")
    return nodes


def static_render(nodes: list[dict[str, object]]) -> tuple[str, str, int]:
    by_id = {str(node["id"]): node for node in nodes}
    levels: dict[str, int] = {}

    def level_of(node_id: str) -> int:
        if node_id in levels:
            return levels[node_id]
        deps = [str(dep) for dep in by_id[node_id]["deps"]]
        levels[node_id] = 0 if not deps else 1 + max(level_of(dep) for dep in deps)
        return levels[node_id]

    for node in nodes:
        level_of(str(node["id"]))
    rows: dict[int, list[dict[str, object]]] = {}
    for node in nodes:
        rows.setdefault(levels[str(node["id"])], []).append(node)

    dag_width, horizontal_padding = 1460, 12
    node_width, node_height, node_gap, level_gap, vertical_padding = 188, 108, 22, 72, 20
    max_level = max(rows)
    dag_height = vertical_padding * 2 + (max_level + 1) * node_height + max_level * level_gap
    content_width = dag_width - 2 * horizontal_padding
    positions: dict[str, tuple[float, float]] = {}
    node_rows: list[str] = []
    for level in range(max_level + 1):
        row = rows.get(level, [])
        row_width = len(row) * node_width + max(0, len(row) - 1) * node_gap
        start_x = horizontal_padding + (content_width - row_width) / 2
        y = vertical_padding + level * (node_height + level_gap)
        cards: list[str] = []
        for index, node in enumerate(row):
            node_id = str(node["id"])
            x = start_x + index * (node_width + node_gap)
            positions[node_id] = (x, y)
            kind_label = "Definition" if node["kind"] == "definition" else "Result"
            cards.append(
                f'<button type="button" class="node" data-id="{html.escape(node_id)}" '
                f'data-kind="{html.escape(str(node["kind"]))}" data-section="{html.escape(str(node["section"]))}" '
                f'aria-pressed="false" title="{html.escape(str(node["description"]))}">'
                f'<span class="node-meta"><span class="node-code">{html.escape(str(node["code"]))}</span>'
                f'<span class="node-section">Section {html.escape(str(node["section"]))}</span></span>'
                f'<span class="node-title">{html.escape(str(node["title"]))}</span>'
                f'<span class="node-kind">{kind_label}</span></button>'
            )
        node_rows.append(f'<div class="dag-level">{"".join(cards)}</div>')

    edges: list[str] = []
    for target in nodes:
        target_id = str(target["id"])
        tx0, ty = positions[target_id]
        tx = tx0 + node_width / 2
        for source_value in target["deps"]:
            source_id = str(source_value)
            sx0, sy0 = positions[source_id]
            sx, sy = sx0 + node_width / 2, sy0 + node_height
            bend = max(24, (ty - sy) * 0.5)
            edges.append(
                f'<path class="dep-edge" data-source="{html.escape(source_id)}" '
                f'data-target="{html.escape(target_id)}" '
                f'd="M {sx:.1f} {sy:.1f} C {sx:.1f} {sy+bend:.1f}, {tx:.1f} {ty-bend:.1f}, {tx:.1f} {ty:.1f}"></path>'
            )
    return "\n".join(node_rows), "\n".join(edges), dag_height


def generate(source: str) -> str:
    nodes = parse_nodes(source)
    node_markup, edge_markup, dag_height = static_render(nodes)
    source = re.sub(
        r'<div class="dag" id="dag"(?: style="[^"]*")?>',
        f'<div class="dag" id="dag" style="height:{dag_height}px">',
        source,
        count=1,
    )
    source = re.sub(
        r'<svg class="dag-svg" id="dag-svg" aria-hidden="true"(?: viewBox="[^"]*")?(?: width="[^"]*")?(?: height="[^"]*")?>',
        f'<svg class="dag-svg" id="dag-svg" aria-hidden="true" viewBox="0 0 1460 {dag_height}" width="1460" height="{dag_height}">',
        source,
        count=1,
    )
    source = EDGE_BLOCK_RE.sub(lambda match: match.group("open") + edge_markup + match.group("close"), source, count=1)
    source = NODE_BLOCK_RE.sub(lambda match: match.group("open") + node_markup + match.group("close"), source, count=1)
    return source


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    source = TARGET.read_text(encoding="utf-8")
    generated = generate(source)
    if args.check:
        if generated != source:
            print(f"stale standalone mathematical graph: {TARGET.relative_to(PROJECT_ROOT)}")
            return 1
        print("standalone mathematical graph is current")
        return 0
    TARGET.write_text(generated, encoding="utf-8")
    print(f"embedded static mathematical graph in {TARGET.relative_to(PROJECT_ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

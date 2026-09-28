#!/usr/bin/env python3
"""Check Lean source coverage, reading links, graphs, and generated webpages."""

import argparse
import json
import re
import subprocess
import sys
from functools import lru_cache
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]

def anchors(text):
    result = set()
    counts = {}
    for heading in re.findall(r"^#{1,6}\s+(.+)$", text, flags=re.M):
        slug = re.sub(r"[^\w\- ]", "", heading.lower()).replace(" ", "-")
        count = counts.get(slug, 0)
        result.add(slug if not count else f"{slug}-{count}")
        counts[slug] = count + 1
    return result


def check_reading_links(strict=False):
    errors = []
    checked = 0
    tracked = set(subprocess.check_output(
        ["git", "-C", str(ROOT), "ls-files", "-z"], text=True
    ).split("\0")) if strict else None
    for name in ("README.md",):
        file = ROOT / name
        text = file.read_text()
        for link in re.findall(r"\[[^\]]*\]\(([^)]+)\)", text):
            url = urlsplit(link)
            if url.scheme or url.netloc:
                continue
            target = (file.parent / unquote(url.path)).resolve() if url.path else file
            checked += 1
            if ROOT not in target.parents and target != ROOT:
                errors.append(f"{name}: link leaves repository: {link}")
            elif not target.exists():
                errors.append(f"{name}: missing target: {link}")
            elif strict and target.is_file() and target.relative_to(ROOT).as_posix() not in tracked:
                errors.append(f"{name}: target is not tracked by Git: {link}")
            elif strict and target.is_dir() and not any(
                item.startswith(target.relative_to(ROOT).as_posix().rstrip("/") + "/")
                and (ROOT / item).is_file() for item in tracked
            ):
                errors.append(f"{name}: directory has no tracked files: {link}")
            elif url.fragment and target.suffix == ".md" and unquote(url.fragment) not in anchors(target.read_text()):
                errors.append(f"{name}: missing heading: {link}")
    if errors:
        raise SystemExit("\n".join(errors))
    print(f"Checked {checked} repository reading links" + (" (Git tracking verified)." if strict else "."))


def check_lean():
    PREFIX = "NthTropicalNevanlinna"
    files = [ROOT / f"{PREFIX}.lean", *sorted((ROOT / PREFIX).rglob("*.lean"))]
    modules = {".".join(p.relative_to(ROOT).with_suffix("").parts): p for p in files}
    seen = set()
    pending = [PREFIX]
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        if name not in modules:
            raise SystemExit(f"Missing project module: {name}")
        seen.add(name)
        for line in modules[name].read_text().splitlines():
            match = re.match(r"^\s*(?:public\s+)?import\s+(.+?)(?:\s*--.*)?$", line)
            if match:
                pending.extend(m for m in match[1].split() if m == PREFIX or m.startswith(PREFIX + "."))
    missing = sorted(modules.keys() - seen)
    if missing:
        raise SystemExit("Modules not imported by the library entry: " + ", ".join(missing))
    print(f"All {len(seen)} project Lean modules are reachable from the library entry.")
    for path in files:
        if re.search(r"\b(sorry|admit|axiom)\b", path.read_text()):
            raise SystemExit(f"Forbidden proof placeholder or project axiom: {path}")
    print("No sorry, admit, or project axiom tokens found.")


class Page(HTMLParser):
    def __init__(self, text):
        super().__init__()
        self.links = []
        self.anchors = set()
        self.upstream = False
        self.feed(text)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag == "meta" and attrs.get("name") == "docgen-upstream" and attrs.get("content") == "mathlib":
            self.upstream = True
        for key in ("id", "name" if tag == "a" else "id"):
            if attrs.get(key):
                self.anchors.add(attrs[key])
        for key in ("href", "src", "xlink:href"):
            if attrs.get(key):
                self.links.append(attrs[key])


def check_site(site):
    root = Path(site).resolve()
    required = ["index.html", "blueprint/index.html", "blueprint/dep_graph_document.html",
                "blueprint.pdf", "LICENSE", "home_page/arxiv-2602.03500v1.pdf", "docs/index.html",
                "docs/search.html", "docs/declarations/declaration-data.bmp",
                "home_page/nth_tropical_nevanlinna_dependency_graph.html",
                "home_page/nth_tropical_nevanlinna_lean_structure.html"]
    errors = [f"Missing reading asset: {name}" for name in required if not (root / name).is_file()]
    for name in ("LICENSE", "home_page/arxiv-2602.03500v1.pdf"):
        if (root / name).is_file() and (root / name).read_bytes() != (ROOT / name).read_bytes():
            errors.append(f"Website asset differs from source: {name}")
    for name in ("nth_tropical_nevanlinna_dependency_graph.html", "nth_tropical_nevanlinna_lean_structure.html"):
        expected = (ROOT / "home_page" / name).read_text()
        expected = expected.replace("../blueprint/web/", "../blueprint/")
        expected = expected.replace("../blueprint/print/print.pdf", "../blueprint.pdf")
        target = root / "home_page" / name
        if target.is_file() and target.read_text() != expected:
            errors.append(f"Website dependency map differs from source: {name}")
    pages = {root / name for name in required if name.endswith(".html")}
    pages.update((root / "blueprint").rglob("*.html"))
    pages.update((root / "docs/NthTropicalNevanlinna").rglob("*.html"))
    pages.add(root / "docs/NthTropicalNevanlinna.html")

    @lru_cache(maxsize=None)
    def page(path):
        return Page(path.read_text())

    checked = 0
    external = set()
    upstream_fragments = 0
    if errors:
        raise SystemExit("\n".join(errors))
    declarations = json.loads((root / "docs/declarations/declaration-data.bmp").read_text())["declarations"]
    for source in sorted(pages):
        if not source.is_file():
            errors.append(f"Missing page: {source.relative_to(root)}")
            continue
        if re.search(r"\\(?:begin|end)\s*\{bgroup\}", source.read_text()):
            errors.append(f"{source.relative_to(root)}: unsupported TeX bgroup environment in generated mathematics")
        for link in page(source).links:
            url = urlsplit(link)
            if url.scheme or url.netloc:
                external.add(link)
                continue
            path = unquote(url.path)
            target = ((root / path.lstrip("/")) if path.startswith("/") else
                      (source.parent / path if path else source)).resolve()
            checked += 1
            if target != root and root not in target.parents:
                errors.append(f"{source.relative_to(root)}: link escapes site: {link}")
                continue
            if target.is_dir():
                target /= "index.html"
            if not target.is_file():
                errors.append(f"{source.relative_to(root)}: missing target: {link}")
            elif url.fragment and target.suffix in (".html", ".svg"):
                fragment = unquote(url.fragment)
                if target == root / "docs/find/index.html" and fragment.startswith("doc/"):
                    name = fragment[4:]
                    entry = declarations.get(name)
                    if not entry:
                        errors.append(f"{source.relative_to(root)}: declaration absent from search index: {name}")
                        continue
                    destination = urlsplit(entry["docLink"])
                    target = (root / "docs" / unquote(destination.path).lstrip("/")).resolve()
                    fragment = unquote(destination.fragment)
                    if root not in target.parents or not target.is_file():
                        errors.append(f"{source.relative_to(root)}: declaration destination missing: {name}")
                        continue
                # HTML defines #top as navigation to the top of the document.
                if fragment.lower() == "top":
                    continue
                if page(target).upstream:
                    upstream_fragments += 1
                    continue
                if fragment not in page(target).anchors:
                    errors.append(f"{source.relative_to(root)}: missing anchor: {link}")
    if errors:
        raise SystemExit("\n".join(sorted(set(errors))))
    print(f"Checked {len(pages)} pages and {checked} local links/anchors; all targets exist.")
    print(f"Skipped {len(external)} distinct external/editor links; browser interaction not tested.")
    if upstream_fragments:
        print(f"{upstream_fragments} Mathlib anchor links are forwarded upstream; remote anchors not checked.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--site", type=Path, help="Also check a generated website")
    parser.add_argument("--tracked", action="store_true", help="Require reading targets to be Git-tracked")
    args = parser.parse_args()
    check_lean()
    check_reading_links(args.tracked)
    for name in ("generate_lean_module_graph.py", "make_mathematical_graph_standalone.py"):
        subprocess.run([sys.executable, str(ROOT / "scripts" / name), "--check"], check=True)
    if args.site:
        check_site(args.site)


if __name__ == "__main__":
    main()

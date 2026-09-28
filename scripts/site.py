#!/usr/bin/env python3
"""Build, assemble, and serve the same static reading site locally or in CI."""

import argparse
import functools
import html
import http.server
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from urllib.parse import quote, unquote, urlsplit, urlunsplit

ROOT = Path(__file__).resolve().parents[1]
MAPS = ("nth_tropical_nevanlinna_dependency_graph.html", "nth_tropical_nevanlinna_lean_structure.html")

def dependency_packages(project):
    packages = {}
    for name in ("lake-manifest.json", "docbuild/lake-manifest.json"):
        for package in json.loads((project / name).read_text())["packages"]:
            if package.get("url") and package.get("rev"):
                packages[package["name"].strip("«»")] = package
    return packages


def collect_blueprint_licenses(blueprint):
    """Run with the Blueprint Python environment before assembling the site."""
    from importlib.metadata import distribution
    target = blueprint / "dependency-licenses"
    for name in ("leanblueprint", "plasTeX"):
        package = distribution(name)
        found = []
        for entry in package.files or []:
            if entry.name.upper().startswith(("LICENSE", "COPYING", "NOTICE")):
                destination = target / name / entry.name
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(package.locate_file(entry), destination)
                found.append(entry.name)
        if not found:
            raise SystemExit(f"Missing installed license notices for {name}")
    print("Collected Blueprint dependency licenses.")


def copy_dependency_licenses(project, blueprint, output):
    target = output / "dependency-licenses"
    for name in dependency_packages(project):
        for source in sorted((project / ".lake/packages" / name).glob("*")):
            if source.is_file() and source.name.upper().startswith(("LICENSE", "COPYING", "NOTICE")):
                destination = target / name / source.name
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, destination)
    supplied = blueprint / "dependency-licenses"
    if not supplied.is_dir():
        raise SystemExit("Collect Blueprint licenses with its Python environment before assembly.")
    shutil.copytree(supplied, target, dirs_exist_ok=True)
    for name in ("mathlib/LICENSE", "doc-gen4/LICENSE", "leanblueprint/LICENSE", "plasTeX/LICENSE"):
        if not (target / name).is_file():
            raise SystemExit(f"Missing dependency license: {name}")
    links = "\n".join(
        f'<li><a href="{quote(p.relative_to(target).as_posix())}">{html.escape(p.relative_to(target).as_posix())}</a></li>'
        for p in sorted(target.rglob("*")) if p.is_file()
    )
    (target / "index.html").write_text(
        '<!doctype html><html lang="en"><meta charset="utf-8">'
        '<title>Third-party licenses</title><h1>Third-party licenses</h1>'
        '<p>Dependency licenses and notices accompany the generated documentation. '
        'Additional notices embedded in distributed assets are preserved.</p><ul>' + links + '</ul></html>\n'
    )


def github_source_links(site, project):
    """Convert local documentation source URLs to pinned GitHub URLs."""
    def git(*args):
        return subprocess.check_output(["git", "-C", str(ROOT), *args], text=True).strip()
    remote = git("remote", "get-url", "origin").removesuffix(".git")
    remote = remote.replace("git@github.com:", "https://github.com/")
    if not re.fullmatch(r"https://github.com/[\w.-]+/[\w.-]+", remote):
        raise SystemExit("Hosted source links require a GitHub origin.")
    revision = git("rev-parse", "HEAD")
    packages = dependency_packages(project)
    count = 0

    def replace(match):
        nonlocal count
        parsed = re.fullmatch(r"(.*?\.lean)(?::(\d+)(?::\d+)?)?", html.unescape(match[1]))
        if not parsed:
            raise SystemExit("Unrecognized local source URL in API documentation.")
        relative = Path("/" + parsed[1].lstrip("/")).resolve().relative_to(project.resolve())
        parts = relative.parts
        if parts[:2] == (".lake", "packages"):
            package = packages[parts[2]]
            url = package["url"].removesuffix(".git") + "/blob/" + package["rev"] + "/"
            url += quote(Path(*parts[3:]).as_posix())
        elif parts[0] in ("NthTropicalNevanlinna", "NthTropicalNevanlinna.lean"):
            url = remote + "/blob/" + revision + "/" + quote(relative.as_posix())
        else:
            raise SystemExit("Unrecognized local source location in API documentation.")
        if parsed[2]:
            url += "#L" + parsed[2]
        count += 1
        return 'href="' + html.escape(url, quote=True) + '"'

    for source in sorted((site / "docs").rglob("*.html")):
        original = source.read_text()
        updated = re.sub(r'href="vscode://file/([^"]+)"', replace, original)
        if updated != original:
            source.write_text(updated)
    print(f"Converted {count} local source links to pinned GitHub links.")

def verify_api_source(project):
    """Allow cached API reuse only for identical Lean sources and build inputs."""
    names = {"NthTropicalNevanlinna.lean", "lean-toolchain", "lakefile.toml", "lake-manifest.json",
             "docbuild/lean-toolchain", "docbuild/lakefile.toml", "docbuild/lake-manifest.json"}
    for base in (ROOT, project):
        names.update(p.relative_to(base).as_posix() for p in (base / "NthTropicalNevanlinna").rglob("*.lean"))
    for name in sorted(names):
        current, cached = ROOT / name, project / name
        if not current.is_file() or not cached.is_file() or current.read_bytes() != cached.read_bytes():
            raise SystemExit(f"API source does not match candidate: {name}")


def repair_api_links(site):
    docs = Path(site).resolve() / "docs"
    count = 0
    for source in sorted((docs / "NthTropicalNevanlinna").rglob("*.html")):
        original = source.read_text()

        def replace(match):
            nonlocal count
            url = urlsplit(match.group(1))
            if url.scheme or url.netloc or not url.path.endswith(".html"):
                return match.group(0)
            target = (source.parent / unquote(url.path)).resolve()
            if target.exists() or docs not in target.parents:
                return match.group(0)
            corrected = docs / "NthTropicalNevanlinna" / target.relative_to(docs)
            if not corrected.is_file():
                return match.group(0)
            path = Path(os.path.relpath(corrected, source.parent)).as_posix()
            count += 1
            return 'href="' + urlunsplit(("", "", path, url.query, url.fragment)) + '"'

        updated = re.sub(r'href="([^"]+)"', replace, original)
        if updated != original:
            source.write_text(updated)
    print(f"Repaired {count} shortened project-module links in generated API pages.")


def copy_api(source, destination, compact):
    """Optionally replace Mathlib HTML with upstream links, keeping its index."""
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    pinned = mathlib["url"].removesuffix(".git") + "/blob/" + mathlib["rev"] + "/"
    redirected = 0
    for file in sorted(source.rglob("*")):
        if file.is_symlink():
            raise SystemExit(f"Unexpected API symlink: {file}")
        if not file.is_file():
            continue
        relative = file.relative_to(source)
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        is_mathlib = relative.parts[0] == "Mathlib" or relative.as_posix() == "Mathlib.html"
        if compact and is_mathlib and file.suffix == ".html":
            upstream = "https://leanprover-community.github.io/mathlib4_docs/" + quote(relative.as_posix())
            exact = pinned + quote(relative.with_suffix(".lean").as_posix())
            target.write_text(
                '<!doctype html><html lang="en"><meta charset="utf-8">'
                '<meta name="viewport" content="width=device-width,initial-scale=1">'
                '<meta name="docgen-upstream" content="mathlib">'
                '<title>Mathlib reference</title><h1>Mathlib reference</h1>'
                '<p>Opening current upstream documentation. The proof uses the pinned revision below.</p>'
                f'<p><a id="upstream" href="{html.escape(upstream)}">Documentation</a> · '
                f'<a href="{html.escape(exact)}">Exact source revision</a></p>'
                '<script>const target=' + json.dumps(upstream) + '+location.hash;'
                'document.getElementById("upstream").href=target;location.replace(target);</script></html>\n'
            )
            redirected += 1
        else:
            shutil.copyfile(file, target)
    print(f"Copied API documentation; {redirected} Mathlib pages link upstream.")


def assemble(output, project, blueprint, pdf, compact=False, source_links="local"):
    if output.exists():
        raise SystemExit(f"Output already exists; preserve it or choose a new path: {output}")
    verify_api_source(project)
    api = project / "docbuild/.lake/build/doc"
    required = [blueprint / "index.html", blueprint / "dep_graph_document.html", pdf,
                api / "index.html", api / "search.html", api / "declarations/declaration-data.bmp",
                ROOT / "home_page/index.html", ROOT / "home_page/arxiv-2602.03500v1.pdf",
                ROOT / "LICENSE"]
    required.extend(ROOT / "home_page" / name for name in MAPS)
    for path in required:
        if not path.is_file():
            raise SystemExit(f"Missing reading asset: {path}")
    for source in (blueprint, api, ROOT / "NthTropicalNevanlinna"):
        if source == output or source in output.parents:
            raise SystemExit("Output must be outside source directories")
    output.mkdir(parents=True)
    shutil.copytree(blueprint, output / "blueprint")
    copy_api(api, output / "docs", compact)
    repair_api_links(output)
    copy_dependency_licenses(project, blueprint, output)
    if source_links == "github":
        github_source_links(output, project)
    shutil.copyfile(ROOT / "home_page/index.html", output / "index.html")
    shutil.copyfile(ROOT / "LICENSE", output / "LICENSE")
    shutil.copyfile(pdf, output / "blueprint.pdf")
    (output / ".nojekyll").touch()
    assets = output / "home_page"
    assets.mkdir()
    shutil.copyfile(ROOT / "home_page/arxiv-2602.03500v1.pdf", assets / "arxiv-2602.03500v1.pdf")
    for name in MAPS:
        text = (ROOT / "home_page" / name).read_text()
        text = text.replace("../blueprint/web/", "../blueprint/")
        text = text.replace("../blueprint/print/print.pdf", "../blueprint.pdf")
        (assets / name).write_text(text)
    shutil.copytree(ROOT / "NthTropicalNevanlinna", output / "NthTropicalNevanlinna",
                    ignore=shutil.ignore_patterns(".DS_Store", "__pycache__"))
    shutil.copyfile(ROOT / "NthTropicalNevanlinna.lean", output / "NthTropicalNevanlinna.lean")
    from check import check_site
    check_site(output, hosted=source_links == "github")
    size = sum(p.stat().st_size for p in output.rglob("*") if p.is_file())
    if compact and size >= 1_000_000_000:
        raise SystemExit(f"Compact website exceeds 1 GB: {size:,} bytes")
    print(f"Website: {output} ({size:,} bytes)")


def build_api():
    env = os.environ.copy()
    env["DOCGEN_SRC"] = "vscode"
    # The pinned doc-gen4 can reuse old HTML after updating its database.
    # Build the documentation data, then explicitly render pages and search.
    subprocess.run(["lake", "build", "NthTropicalNevanlinna:docInfo"],
                   cwd=ROOT / "docbuild", env=env, check=True)
    subprocess.run(["lake", "exe", "doc-gen4", "fromDb", "--build", ".lake/build",
                    "--manifest", ".lake/build/doc-manifest.json", ".lake/build/api-docs.db",
                    "NthTropicalNevanlinna", "Init", "Std", "Lake", "Lean"],
                   cwd=ROOT / "docbuild", env=env, check=True)


def build(args):
    if args.output.exists():
        raise SystemExit(f"Output already exists: {args.output}")
    env = os.environ.copy()
    env["PATH"] = str(ROOT / ".blueprint-venv/bin") + os.pathsep + env["PATH"]
    if not shutil.which("leanblueprint", path=env["PATH"]):
        raise SystemExit("Install the Blueprint dependencies listed in README.md first.")
    for command in (["lake", "build"], ["leanblueprint", "pdf"], ["leanblueprint", "web"],
                    ["lake", "exe", "checkdecls", "blueprint/lean_decls"]):
        subprocess.run(command, cwd=ROOT, env=env, check=True)
    blueprint_python = Path(shutil.which("leanblueprint", path=env["PATH"])).parent / "python"
    subprocess.run([str(blueprint_python), str(Path(__file__).resolve()), "licenses"],
                   cwd=ROOT, env=env, check=True)
    build_api()
    assemble(args.output.resolve(), ROOT, ROOT / "blueprint/web", ROOT / "blueprint/print/print.pdf",
             args.compact, args.source_links)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("build", "assemble"):
        command = commands.add_parser(name)
        command.add_argument("--output", type=Path, required=True, help="New output directory; never overwritten")
        command.add_argument("--compact", action="store_true", help="Link Mathlib reference pages upstream")
        command.add_argument("--source-links", choices=("local", "github"), default="local")
        if name == "assemble":
            command.add_argument("--api-project", type=Path, default=ROOT)
            command.add_argument("--blueprint-dir", type=Path, default=ROOT / "blueprint/web")
            command.add_argument("--pdf", type=Path, default=ROOT / "blueprint/print/print.pdf")
    commands.add_parser("licenses", help="Collect licenses using the Blueprint Python environment")
    commands.add_parser("api", help="Build API documentation and refresh its pages and search index")
    serve = commands.add_parser("serve")
    serve.add_argument("directory", type=Path)
    serve.add_argument("--port", type=int, default=8000)
    args = parser.parse_args()
    if args.command == "build":
        build(args)
    elif args.command == "assemble":
        assemble(args.output.resolve(), args.api_project.resolve(), args.blueprint_dir.resolve(),
                 args.pdf.resolve(), args.compact, args.source_links)
    elif args.command == "licenses":
        collect_blueprint_licenses(ROOT / "blueprint/web")
    elif args.command == "api":
        build_api()
    else:
        if not (args.directory / "index.html").is_file():
            parser.error("directory must contain a built website")
        handler = functools.partial(http.server.SimpleHTTPRequestHandler, directory=str(args.directory.resolve()))
        with http.server.ThreadingHTTPServer(("127.0.0.1", args.port), handler) as server:
            print(f"Local preview: http://127.0.0.1:{args.port}/", flush=True)
            try:
                server.serve_forever()
            except KeyboardInterrupt:
                pass


if __name__ == "__main__":
    main()

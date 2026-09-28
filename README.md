# n-th Tropical Nevanlinna Theory in Lean

Lean 4 formalization of *n-th Tropical Nevanlinna Theory* by Risto Korhonen
and Chengliang Tan ([arXiv:2602.03500v1](https://arxiv.org/abs/2602.03500v1)).

## Read

- [Blueprint — PDF](blueprint/blueprint.pdf)
- [Original paper — PDF](home_page/arxiv-2602.03500v1.pdf)
- [Lean proofs in paper order](NthTropicalNevanlinna/Paper.lean)

The Blueprint website has not been deployed. HTML files opened in GitHub's
file viewer display source code, not the rendered website.
A [downloadable website preview](https://github.com/czdg7tg2jk-crypto/nth-tropical-nevanlinna-formalization/releases/tag/private-review-20260928-r2)
is available; extract it and run `python3 preview.py` to open it locally.

<details>
<summary>Build instructions and repository structure</summary>

## Repository structure

```text
NthTropicalNevanlinna/     Lean proofs; start with Paper/ for paper order
NthTropicalNevanlinna.lean Library entry point
blueprint/                Mathematical exposition: src/ and blueprint.pdf
home_page/                Homepage, original paper PDF, and two dependency maps
docbuild/                 Three pinned configuration files for Lean API generation
scripts/                  Four build, check, and graph-generation tools
lakefile.toml             Lean project configuration
lake-manifest.json        Exact dependency revisions
lean-toolchain            Lean version
.github/workflows/        Build checks; deployment is a separate opt-in job
```

Within `NthTropicalNevanlinna/`, `Paper/` provides the paper-order interface;
`Function/`, `PoissonJensen/`, `Nevanlinna/`, `LogDerivative/`, `Curves/`, and
`Truncated/` contain the implementation. All 49 Lean modules belong to the
proof library.

## Build and check

With the pinned Lean toolchain installed:

```bash
lake build
python3 scripts/check.py
```

`check.py` checks proof-placeholder tokens, module coverage, repository reading
links, and both dependency maps. Add `--tracked` to verify that reading targets
are included in Git. Compilation checks Lean proofs; mathematical review must
also compare their statements with the paper.

To build the reading website, install a TeX distribution (including XeLaTeX
and latexmk), Graphviz with its development headers, and the Python dependencies:

```bash
python3 -m venv .blueprint-venv
.blueprint-venv/bin/pip install -r blueprint/requirements.txt
python3 scripts/site.py build --output ../nth-tropical-site
python3 scripts/site.py serve ../nth-tropical-site
```

Open <http://127.0.0.1:8000/> for the Blueprint, expandable proofs, three
dependency views, searchable Lean API, and the two PDFs. The server binds only
to this computer. The output is kept outside the source repository and must
be a new directory. Choose another output path for a fresh build.

Local API `Source` links open the matching file in VS Code. For a hosted build,
use `--source-links github`; this requires a committed Git repository with a
valid origin. Add `--compact` to redirect Mathlib reference pages to upstream
documentation while keeping project API pages and search. Those redirects also
link to the exact pinned Mathlib source; upstream documentation can change.

The four tools in `scripts/` have distinct roles:

| Tool | Purpose |
| --- | --- |
| `site.py` | Build, assemble, or serve the website |
| `check.py` | Check source structure, reading links, and optionally `--site PATH` |
| `generate_lean_module_graph.py` | Regenerate the Lean import graph |
| `make_mathematical_graph_standalone.py` | Refresh the mathematical graph's static rendering |

`blueprint/web/` and `blueprint/print/` are ignored build output. The tracked
`blueprint/blueprint.pdf` is a reading snapshot; after changing the exposition,
review the regenerated PDF before refreshing that snapshot. Website builds
use the newly generated PDF.

</details>

<details>
<summary>Mathematical scope, reading order, and verification status</summary>

The target list covers 26 numbered or section-level results, seven explicit
examples, and two unnumbered counterexamples.

## Mathematical reading order

| Paper section | Main objects and results | Reader-facing Lean file |
| --- | --- | --- |
| 2 | Tropicalization, meromorphic functions, multiplicities, entire functions, Propositions 2.2-2.3 | [`Paper/Section2.lean`](NthTropicalNevanlinna/Paper/Section2.lean) |
| 3 | Lemmas 3.1-3.2, Poisson-Jensen formula, counting functions, Jensen identity, Proposition 3.8 | [`Paper/Section3.lean`](NthTropicalNevanlinna/Paper/Section3.lean) |
| 4 | Well-defined functions, Lemmas 4.3-4.6, Theorem 4.7, Corollary 4.8 | [`Paper/Section4.lean`](NthTropicalNevanlinna/Paper/Section4.lean) |
| 5 | Tropical holomorphic curves, characteristics, homogeneous polynomials, Theorems 5.6 and 5.8, Examples 5.9-5.10 | [`Paper/Section5.lean`](NthTropicalNevanlinna/Paper/Section5.lean) |
| 6 | Shifts, Casoratian, finite-root identity, Lemma 6.1, Theorem 6.2, Corollary 6.3 | [`Paper/Section6.lean`](NthTropicalNevanlinna/Paper/Section6.lean) |
| Examples | Explicit examples and counterexamples from Sections 2-6 | [`Paper/Examples.lean`](NthTropicalNevanlinna/Paper/Examples.lean) |

The corrected sequential numbering 4.3-4.8 is used in this project.  The
source paper labels the same chain as Lemma 4.3.0, Lemmas 4.3-4.5, Theorem
4.6, and Corollary 4.7.

## Formalization status

- `lake build` succeeds with the pinned toolchain.  Remaining linter and
  deprecation messages are warnings, not compilation errors.
- The source tree contains no `sorry`, `admit`, or project-defined `axiom`.
- All 83 distinct Lean declarations referenced by the Blueprint pass
  `lake exe checkdecls blueprint/lean_decls`.
- The paper convention `n in {1,2,...}` is represented explicitly by `1 <= n`.
- Growth invariants use `EReal`; local polynomial germs and multiplicities are
  independent of the chosen presentation.
- The shift-growth, power-step Borel, and Casoratian common-factor results used
  by the project are proved internally rather than introduced as axioms.

The scope is the target list described above. Compilation checks the Lean
proofs; agreement with the paper also requires mathematical review of the
statements and definitions.

Changes must preserve definitions, hypotheses, quantifiers, and conclusions.
Do not add `sorry`, `admit`, or project-specific axioms. Update the Blueprint
when a paper-level statement changes, and rerun the build and declaration checks.

</details>

## License

The project-authored Lean code, Python tools, and build configuration are
licensed under the [Apache License 2.0](LICENSE). Third-party code and
dependencies retain their own licenses and attribution notices.

The original paper by Risto Korhonen and Chengliang Tan,
*n-th Tropical Nevanlinna Theory*, arXiv:2602.03500v1, is distributed under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
See [paper attribution](#original-paper-and-dependency-maps) for the version and source.

The software license does not apply to the paper, the Blueprint's mathematical
exposition, or the mathematical content of the dependency maps. Material
reproduced or adapted from the paper remains subject to its applicable license
and attribution requirements. No separate license is currently specified for
the project's original mathematical exposition and dependency-map content.

<details>
<summary>Paper attribution and dependency maps</summary>

## Original paper and dependency maps

**Paper:** Risto Korhonen and Chengliang Tan, *n-th Tropical Nevanlinna
Theory*, [arXiv:2602.03500v1](https://arxiv.org/abs/2602.03500v1),
3 February 2026.

The [paper PDF](home_page/arxiv-2602.03500v1.pdf) reproduces the arXiv v1
preprint without modification. It is not a publisher's version.
The arXiv version record links to the
[Creative Commons Attribution 4.0 license](https://creativecommons.org/licenses/by/4.0/).
This attribution concerns the paper; the software license is specified above.

The homepage assets also include two dependency maps:

- [Mathematical dependencies](home_page/nth_tropical_nevanlinna_dependency_graph.html):
  a curated overview of the relationships between the paper's results.
- [Lean module imports](home_page/nth_tropical_nevanlinna_lean_structure.html):
  generated from the project's Lean imports.

GitHub's file viewer displays HTML source. Download and open these maps in a
browser, or use the local website described above. Website builds use these
same files, adjusting only the links to the generated Blueprint pages.

</details>

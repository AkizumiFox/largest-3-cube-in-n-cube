# Largest three-dimensional cubes in higher-dimensional unit cubes

**K.-C. Chang**  
**Preliminary working manuscript — 25 November 2026. Not peer reviewed.**

This repository contains a mathematical manuscript and a Lean 4 formalization
concerning the maximal side length of a three-dimensional cube contained
isometrically in the unit n-dimensional cube. It studies static containment,
not Prince Rupert's passage problem.

## Main result

Write `f(3,n)` for the maximal side length and `F_3(n) = f(3,n)^2`.
The manuscript gives the following exact values for every integer `n >= 3`:

| Dimension | `F_3(n)` |
| --- | --- |
| `n=3m`, `m>=1` | `m` |
| `n=4` | `1+delta_1` |
| `n=7` | `2+delta_2` |
| `n=3m+1`, `m>=3` | `m+15-4*sqrt(14)` |
| `n=3m+2`, `m>=1` | `m+10-4*sqrt(6)` |

The two exceptional constants are defined algebraically in the paper, with
`delta_1 ~ 0.014925` and `delta_2 ~ 0.030276`.
The formula gives `F_3(n+3) = F_3(n) + 1` for all `n >= 8`.

The cases with `3 | n` and the exact values for `n=4` and `n=5` were known
previously; see the manuscript's bibliography. Research priority for the entire
family is not independently established, particularly in relation to unpublished
work by Huber and Ligocki.

## Manuscript

- `paper/manuscript.pdf`: current 30-page working draft.
- `paper/manuscript.tex`: LaTeX source; compile from `paper/` with `latexmk -pdf manuscript.tex`.
- `paper/pair_support_graph.pdf`: figure used in the manuscript.

## Lean 4 formalization

The formalization uses Lean 4.19.0 and a pinned Mathlib dependency. From the
repository root, on Linux, macOS, or WSL2 with Lean and Lake installed:

```bash
lake exe cache get
lake build
bash scripts/verify.sh
```

The script checks source hashes, builds the project, runs `CompleteAudit.lean`,
`KeyTheorems.lean`, `AuxiliaryAudit.lean` and `PaperWitnesses.lean`, and checks
1,195 theorem type/axiom records. It accepts only `propext`,
`Classical.choice`, and `Quot.sound` as theorem dependencies. Reproducibility
logs are saved locally in the ignored `verification_runs/` directory.
`PaperWitnesses.lean` checks the existence and prints types of selected Lean
witness declarations. A successful Lean build does not by itself establish the
fidelity of every natural-language statement to its formal specification.

## Status, licensing, and citation

The paper is a preliminary working draft; a full author-side review and peer
review remain outstanding. Its AI-assistance disclosure appears in the paper.

- Lean source, build and verification scripts, and this repository README:
  Apache License 2.0 (`LICENSE`, `NOTICE`).
- Mathematical manuscript, LaTeX, and figure in `paper/`:
  Copyright (c) 2026 K.-C. Chang, all rights reserved (`paper/LICENSE`).
  The repository-level Apache license does not extend to `paper/`.
- Third-party dependencies retain their respective licenses.

For citations, see `CITATION.cff`. No DOI has yet been assigned to this version.

# Core

- Project root: `/Users/Spare/Documents/code/riemann/publications/hgt`.
- Mission: speculative research program for HGT / multi-`q` difference Galois theory around L-functions and RH/DSS. Native object: one prime-indexed dilation `σ_p` per prime in Bohr coordinates `x_p = p^{-s}`.
- Required session-orientation docs before research work: `docs/drafts/00-core-vision.md`, `docs/drafts/00-charter-wall-and-door.md`, `docs/drafts/door/00-index.md`.
- Research state source of truth: `docs/drafts/door/00-status.md`. Concept buckets live in `docs/drafts/door/`; active work queue lives in `docs/drafts/pipeline/`.
- Pipeline stages: `0-backlog`, `1-in-progress`, `2-fully-proven`, `3-formalized`, `4-publication-ready`, `5-failed`. Use `docs/drafts/pipeline/_card-template.md` for new cards.
- Formalization project: `formal/`, Lean library `GaloisForLFunctions`; root import file `formal/GaloisForLFunctions.lean` imports all modules.
- Computations are exceptional; archive any run results under `computations/`. Working logs belong under `logs/`, which is git-ignored.
- Current high-level research invariant: branchhood is proto-branch; C1/C2/C4 met, C6 met at bridge level, C5 and C7 not met; C3 reduced/coupled to C5. First native/C5 theorem remains open.
- Current live C5 lead: bounded-degree finite-free/Hankel carrier; fixed-`d` edge is Baker-load-bearing bridge, `d → ∞` uniform edge control is the native crux.
- See `mem:tech_stack` for build/tool pins, `mem:conventions` for research/Lean discipline, `mem:task_completion` for verification gates, and `mem:suggested_commands` for useful commands.
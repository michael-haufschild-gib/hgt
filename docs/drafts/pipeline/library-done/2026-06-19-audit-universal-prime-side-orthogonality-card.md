# Library ticket — new backlog card: universal-prime-side-orthogonality

- **Filed:** 2026-06-19
- **Kind:** index/status update request (do not edit the door files from a worker; Librarian applies)

## What happened
Audited every card in `pipeline/2-fully-proven/` (35 cards) for references to future/open research and
checked each open core is logged as a backlog ticket. Result: 34/35 already route their open cores to existing
tickets (`baker-for-stieltjes`, `g2-dss-lower-bound`, `weil-positivity-operator`, `compute-omega-h2-gl`,
`combination-mode-baker-reducibility`, `finite-free-convolution-flow`, `corank-seam-invariant`,
`c7-autonomy-foundational-core`, `archimedean-prime-cross-term`, `gamma-module-construction`). One gap found.

## The gap (now fixed)
`2-fully-proven/orthogonality-meta-theorem.md` §6 carves out, explicitly **not banked**, the **universal
orthogonality conjecture** ("no positive-definite polarization on any object of `𝓜` whose positivity is
equivalent to RH"). It was not logged as a pipeline ticket. Created:
`pipeline/0-backlog/universal-prime-side-orthogonality.md` (CONJECTURE, FOUNDATIONAL). Cross-reference added
back from the meta-theorem §6 + its Cross-references section.

## Requested door updates
- `door/00-status.md §C`: add a row for the new conjecture (universal orthogonality, the #137 residual), Type
  CONJECTURE, Priority FOUNDATIONAL, bucket realization-and-fake-family / seam.
- `door/00-index.md`: optional — note under [[bucket-realization-and-fake-family]] / the orthogonality
  meta-theorem (#137) that the universal residual is now carded at `universal-prime-side-orthogonality`.

## Note (out of audit scope, flagged for cleanup)
Several `2-fully-proven` cards carry **stale cross-reference paths** to open-core homes that have since moved
(e.g. `../1-in-progress/finite-free-convolution-flow.md` and `.../combination-mode-baker-reducibility.md` are
now in `0-backlog`; `../0-backlog/archimedean-prime-cross-term.md` is now in `2-fully-proven`;
`../0-backlog/fields-medal-after-future-tickets/...` subdir paths no longer exist). The tickets themselves all
exist, so no research is orphaned — only the paths are wrong. Not fixed here.

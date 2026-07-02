# The m-step window branch: independence over the certified-viable region

- **ID:** m-step-window-branch
- **Stage:** 3-formalized (reduction + geometric core banked; branch construction = located open core)
- **Type:** THEOREM (Lean, conditional) + [OPEN CORE] - grade **BRIDGE**
- **Source:** the far end of the critical-curve program; generalizes the sharp window pass
  (`u0-phib-window-independence`) from `‖b‖ > 2+√2` to the full viability region.
- **Statement:** For a viable parameter (`K_b ∩ D̄(0,1) = ∅`), the algebraic independence
  `NoRelation ℂ(z) (window branch) (u₀)` holds on a `b`-dependent annulus crossing `|z| = 1`,
  REDUCED to the single analytic input "an analytic branch on the window ball, transcendental over
  ℂ(z)".  The natural-boundary engine, the descent, and the capstone assembly are all discharged
  generically; the uniform-clearance geometry is unconditional.

## What is banked (axiom-clean `[propext, Classical.choice, Quot.sound]`)

- **Uniform clearance from viability** (`U0UniformClearance.exists_uniform_clearance`): for
  `2 < ‖b‖`, viability ⟹ `∃ r > 1, ∃ N, ∀ ‖z‖ ≤ r, xStar ‖b‖ < ‖f^[N] z‖`.  The load-bearing
  bridge: a disk `D̄(0,r)` crossing `|z| = 1` escapes past the escape fixed point in a UNIFORM
  number of steps.  Proof: pointwise escape (`exists_orbit_gt`) + persistence of the far field
  (`farB_iterate`) makes the escape sets `Aₙ` increasing & open; compactness of `D̄(0,1)`
  collapses the cover to one `A_{N₀}`; `exists_thickening_subset_open` fattens it to `r > 1`.
  Card `FullyProvenNewTargets.uniform_clearance_card`.
- **The m-step carrier** (`U0MStepBranch.annMB r = ball 0 r ∩ Ext`, `1 < r`) with its full
  topology interface (open, preconnected via `isPreconnected_annulus_of_one_lt`, nonempty,
  infinite, `⊆ Ext`).
- **The branch-conditional capstone** (`U0MStepBranch.u0_mstep_independence_of_branch`): given ANY
  analytic `φ` on `ball 0 r` with germ on `annMB r` and transcendence over ℂ(z), produces
  `NoRelation ℂ(z) φ u₀`.  The natural-boundary engine
  (`U0WindowNormalization.u0_windowed_no_relation_nondegenerate`, GENERIC in the branch) and the
  carrier-generic assembly (`u0_window_independence_of_transcendental_engine`) are discharged
  automatically.
- **Non-vacuity** (`U0MStepBranch.mstep_interface_realized_above_sharp`): above `2+√2`, `phiB`
  realizes the interface (its carrier `annWB b` is defeq `annMB (rB b)`), so the conditional
  capstone recovers the full sharp `u0_phiB_independence`.  The interface is exactly right — the
  m-step generalization changes ONLY the branch, not the assembly.

## The located open core (the sole remaining analytic input)

Construct `phiB_m` : an analytic branch on the window ball `ball 0 r` (`r` from clearance),
transcendental over ℂ(z).  The one-step branch `phiB` uses the normalization
`log(1 + z²/b)` valid on `ball 0 (rB b)` only for `‖b‖ > 2+√2` (`ratio_re_ge`).  The N-step
generalization pulls the far Böttcher log back `N` steps (each step `×2⁻¹` + a log-correction).

**The precise obstruction.**  The per-step log-corrections `log(1 + (f^[k] z)²/·)` must each stay
in the right half-plane along the clearance chain, but the INTERMEDIATE points `f^[k] z`
(`k < N`) are not small — they can sit anywhere in the disk before escaping, so the naive per-step
normalization can cross the branch cut.  Equivalently: analytically continue the Böttcher
coordinate across `|z| = 1` into a window disk that does not encircle `K_b` (single-valued), for
viable `b` where `K_b` is strictly inside the unit disk.  `exists_uniform_clearance` guarantees the
chain reaches the far field; the open piece is the branch-cut bookkeeping of the continuation.

## Lean surface

- Files: `formal/GaloisForLFunctions/U0/U0UniformClearance.lean`, `U0MStepBranch.lean`.
- Cards: `FullyProvenNewTargets.uniform_clearance_card`.
- Consumes: `U0PhiLargeWindow` (farB, isPreconnected_annulus), `U0MonotoneEscape` (xStar),
  `U0WindowNormalization` (generic engine), `U0PhiLargeCapstone` (generic assembly).

## Open

- Build `phiB_m` (the located open core above); then `u0_mstep_independence` unconditional over the
  viable region follows by feeding it to `u0_mstep_independence_of_branch`, with instances at the
  6 certified-viable parameters (`b = 3`, the 5 slice points) — the first independence theorems
  strictly below the sharp threshold `2+√2`.
- Kummer layers for `phiB_m` (the ψ-route deliberately skips root extraction; the 2^k-th-root
  transfer meets a winding obstruction on the annulus — assess once the branch exists).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (the banked reduction + clearance are proven; branch is open core)
- [~] 2 → 3  formalized: clearance + carrier + conditional capstone axiom-clean, build + lint
  green; the UNCONDITIONAL capstone awaits the branch construction
- [ ] 3 → 4  publication-ready

## Log
- 2026-07-02 — carded from the critical-curve program ([ρ.10]).
- 2026-07-02 — uniform clearance + carrier + branch-conditional capstone + non-vacuity banked
  (#45–#50); the natural-boundary engine found to be GENERIC in the branch, so the m-step reduces
  to the single branch-construction input; obstruction located (intermediate-point branch-cut
  validity in the N-step normalization).  Promoted 0-backlog → 3-formalized.

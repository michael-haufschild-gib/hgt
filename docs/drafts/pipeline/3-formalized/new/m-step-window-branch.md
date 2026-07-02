# The m-step window branch: independence over the certified-viable region

- **ID:** m-step-window-branch
- **Stage:** 3-formalized (FULLY UNCONDITIONAL — the ψ-transcendence gap is closed)
- **Type:** THEOREM (Lean, unconditional) - grade **BRIDGE**
- **Source:** the far end of the critical-curve program; generalizes the sharp window pass
  (`u0-phib-window-independence`) from `‖b‖ > 2+√2` to the full viability region.
- **Statement:** For EVERY viable parameter (`K_b ∩ D̄(0,1) = ∅`), the algebraic independence
  `NoRelation ℂ(z) ψ u₀` holds on a `b`-dependent window disk crossing `|z| = 1`, where
  `ψ = bottcherCoord ∘ f_b^[N]` (`U0PhiMStepFar.u0_mstep_independence`, `MStepIndependence b`).  NO
  assumed transcendence, NO `‖b‖ > 2+√2`: the natural-boundary engine, the descent, the capstone
  assembly, the uniform-clearance geometry, AND `ψ`'s transcendence are all discharged.

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

## The branch is now BUILT: `ψ = bottcherCoord ∘ f^[N]` (`U0PhiMStep`)

The naive per-step log-normalization (`phiB_m` with corrections `log(1 + (f^[k] z)²/·)`) crosses
the branch cut at intermediate orbit points — a dead route.  The CLEAN branch avoids it entirely:

  **`ψ(z) = bottcherCoord b (f_b^[N] z)`** — the genuine Böttcher coordinate `N` steps ahead, no
  root extraction, no per-step normalization.

Banked (axiom-clean):
- `U0PhiMStep.exists_clearance_escapeOpen` — viability ⟹ `∃ r>1, N`, `f^[N](D̄(0,r)) ⊆ escapeOpen b`
  (clearance past `max 2 ‖b‖`, elementary persistence `escapeOpen_persist` + the compactness of
  `exists_uniform_clearance`).  Card `mstep_branch_built_card`.
- `psiN` (def), `psiN_ne_zero`, `psiN_analyticOnNhd` — ψ analytic on the window ball via
  `analyticAt_iterate` (polynomial iterate) composed with the slit-free
  `Bottcher.analyticOnNhd_bottcherCoord_full`.
- `u0_psiN_independence` — feeds the CONCRETE ψ to `u0_mstep_independence_of_branch`: `u₀ ⟂ ψ` for
  every viable parameter, with the branch built in, modulo one hypothesis: ψ's transcendence.

## The ψ-transcendence gap — CLOSED (`U0PhiMStepFar`)

`ψ = bottcherCoord ∘ f^[N] = bottcherCoord ∘ pMapB b (N−1)` is exactly the object
`phiB_transcendental` descends (there `phiB^{2^{m+1}} = bottcherCoord ∘ pMapB`; here ψ IS
`bottcherCoord ∘ pMapB`, no `2^k` power).  ψ's transcendence is
`Bottcher.bottcher_transcendental_far` transported along `f^[N]` by `descend_algebraicP` — the SAME
descent, on carrier `annMB r` instead of `annWB b` (`U0PhiMStepFar.psiN_transcendental`).

**The key that closed it:** the sharp descent used `‖b‖ > 2+√2` at exactly ONE point —
`pMapB_deriv_ne_zero` → openness of the far image `f^[N] '' annMB r`.  That derivative hypothesis
is UNNECESSARY.  A positive-degree polynomial map is an OPEN map on all of `ℂ`
(`Polynomial.isOpenQuotientMap_eval` applied to `pPolyB b (N−1)`, `natDegree = 2^N ≠ 0`), regardless
of where its derivative vanishes.  So the far image is open with no orbit-avoids-`0` condition — no
puncturing, no genericity, no `IsPreconnected (open ∖ finite)` topology lemma.  `pPolyB`/`pullAn`/
`kappaP`/`Φ` transfer verbatim (all carrier-generic, none needs `pMapB` injective).

Banked (axiom-clean `[propext, Classical.choice, Quot.sound]`, `U0PhiMStepFar`):
- `zero_not_mem_of_viable`, `persist_past_M`, `exists_clearance_farBound` (uniform clearance past
  `bottcherFarBound b hc`, one compactness argument at threshold `max (bottcherFarBound) (max 2‖b‖)`);
- `isOpen_pMapB_image_annMB` (the deriv-free far-image openness, open mapping theorem);
- `psiN_transcendental` (ψ transcendental over ℂ(z) on `annMB r`, every viable `b`);
- `u0_mstep_independence : viable b → MStepIndependence b` (UNCONDITIONAL);
- six sub-threshold instances (`U0MStepInstances`): `b = 3` and five slice points at
  `arg b ≈ 105°…155°`, all `‖b‖ ≈ 3.00 < 2+√2` — the first `u₀`–Böttcher independence theorems
  strictly below the direction-independent threshold.

## Lean surface

- Files: `formal/GaloisForLFunctions/U0/U0UniformClearance.lean`, `U0MStepBranch.lean`.
- Cards: `FullyProvenNewTargets.uniform_clearance_card`.
- Consumes: `U0PhiLargeWindow` (farB, isPreconnected_annulus), `U0MonotoneEscape` (xStar),
  `U0WindowNormalization` (generic engine), `U0PhiLargeCapstone` (generic assembly).

## What this OPENS (next generative moves)

- **Kummer for ψ (root-level independence):** the ψ-route targets the FULL Böttcher coordinate, so
  independence of `u₀` from `2^k`-th ROOTS of ψ (the `U0PhiKummerLayers` refinement) is now a
  downstream question resting on the SAME (discharged) transcendence — a concrete next construction.
- **The whole viable region, not just witnesses:** `u0_mstep_independence` holds for every viable
  `b`; the natural next object is the map `b ↦ (r, N)` (window radius / clearance depth) as a
  function on the viable set, and whether it extends continuously to the critical curve `ρ`.
- **The exact independence locus:** independence now holds on ALL of `Viable = 𝒪ᶜ`; pairing this
  with `ObstructedEqClosurePattern` (the `∂𝒱 = closure(pattern)` conjecture, `dV-pattern-closure`)
  would pin the boundary of the independence region exactly.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: the FULL unconditional capstone is axiom-clean, build + lint green
  (`U0PhiMStepFar`, `U0MStepInstances`); `#print axioms = [propext, Classical.choice, Quot.sound]`
- [ ] 3 → 4  publication-ready

## Log
- 2026-07-02 — carded from the critical-curve program ([ρ.10]).
- 2026-07-02 — uniform clearance + carrier + branch-conditional capstone + non-vacuity banked
  (#45–#50); the natural-boundary engine found to be GENERIC in the branch, so the m-step reduces
  to the single branch-construction input; obstruction located (intermediate-point branch-cut
  validity in the N-step normalization).  Promoted 0-backlog → 3-formalized.
- 2026-07-02 — **ψ-transcendence gap CLOSED, capstone now fully unconditional.**  The located
  residual (`pMapB_deriv_ne_zero` on `annMB`) dissolved: `deriv ≠ 0` was only ever needed for
  openness of the far image, and a positive-degree polynomial is an open map unconditionally
  (`Polynomial.isOpenQuotientMap_eval`) — no puncturing, no `IsPreconnected (open ∖ finite)` lemma.
  Descent ported verbatim to the unpunctured `annMB` (`U0PhiMStepFar`); `u0_mstep_independence`
  unconditional over the viable region; six sub-threshold instances banked (`U0MStepInstances`).

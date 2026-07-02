# The critical curve ρ(arg b): closed-form sectors and a formalized slice at modulus 3

- **ID:** critical-curve-slice
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) - grade **BRIDGE**
- **Source:** the critical-curve program over the dichotomy ring; builds on the obstruction
  patterns, the disk-escape kit, and the sharp window threshold.
- **Statement:** For the viability set `𝒱 = {b : K_b ∩ D̄(0,1) = ∅}` (the region where the
  window geometry exists) with critical curve `ρ(arg b) = ∂𝒱` in the ring `2 < ‖b‖ ≤ 2+√2`:
  (i) `ρ(π) = 2+√2` two-sided; (ii) closed-form viable and obstructed regions bound the curve;
  (iii) on the modulus-3 circle the transition angle is bracketed inside `(155.43°, 155.94°)`
  by machine-checked verdicts at genuinely `arg`-ordered parameters.

## Goal

Maps the boundary of the region where the window route (a Böttcher branch across `u₀`'s
natural-boundary circle) can exist at all.  The obstructed side is a union of explicit
preperiodic pattern regions — P1 (fixed point, exact Cassini form `‖s−3‖·‖s+1‖ ≤ 4` in
`b = (1−s²)/4`), P2 (2-cycle), and deeper lobes (period-3 and beyond, mapped numerically) —
the viable side is certified by square-tree disk-arithmetic escape.  `[CONJECTURE]` the
complement of `𝒱` in the Cantor regime is exactly the closure of the union of pattern regions;
the curve is the outer boundary of a parameter-space "disk-avoidance" analog of `M`.

## Lean surface

- `U0CurveSectors.rho_pi_pinned` — `ρ(π) = 2+√2` two-sided (`viable_of_gt_sharp`: EVERY
  direction above the sharp threshold is viable; the obstruction endpoint witness meets it).
- `U0CurveSectors.viable_modulus_three` (`Re b ≥ −3/50` at `‖b‖ = 3`), `viable_sector_ring_re`,
  `obstructed_of_s`, `obstructed_real_segment` — the closed-form sectors.
- `U0DichotomySlice.critical_curve_bracket` — the bracket pair (`arg`-ordered via
  `arg_lt_arg_Q2`); grid verdicts `slice_viable_105/125/140/150/155` (square-tree certificates,
  45–461 nodes) and `slice_obstructed_156/161/165/169/176/180` (exact-rational P1 instances).
- Kit: `U0DiskEscape` (escape past `xStar`, chain steps, square subdivision, coordinate forms);
  patterns: `U0ObstructionPatterns` (P1/P2, generic complex form).
- Cards: `FullyProvenNewTargets.rho_pi_pinned_card`, `curve_sectors_card`,
  `obstruction_patterns_card`, `disk_escape_viability_card`, `critical_curve_slice_card`.
- Files: `formal/GaloisForLFunctions/U0/U0ObstructionPatterns.lean`, `U0DiskEscape.lean`,
  `U0CurveSectors.lean`, `U0SliceViableA.lean`, `U0SliceViableB.lean`,
  `U0DichotomySliceObstructed.lean`, `U0CriticalCurveSlice.lean` (+ generator
  `computations/rho_curve_recon/gen_slice.py`).

## Proof shape

Obstruction: preperiodic witnesses — `x₀ ↦ −β ↦ β ↦ β` (P1) and `x ↦ γ ↦ γ' ↦ γ` (P2) with
membership by finite-orbit boundedness; the `s`-parameterization `b = (1−s²)/4` turns the P1
condition into exact rational arithmetic (`(1+s)/2 + b = −(s−3)(s+1)/4`).  Viability: square
subdivision of `[−1,1]²` (exact splits, outside-unit pruning), leaf squares enclosed in disks,
disk chains `f(D(c,r)) ⊆ D(c²+b, r(2‖c‖+r))` with rounded rational centers and drift bounds,
terminating past the escape fixed point `xStar ‖b‖` (monotone escape, no rate).  All conditions
are rational inequalities in coordinate form; certificates are machine-generated.  The `arg`
ordering of the bracket uses `arcsin` monotonicity in the second quadrant with a
cross-multiplied tangent comparison certified through squared rationals.

## Open

- The exact transition angle `θ*(3)` (bracketed within 0.51°); tightening is generator-budget.
- The mid-angle lobe (period-3 and deeper patterns, `arg ≈ 75°–130°` at `‖b‖ ≈ 2.0–2.5`):
  mapped numerically, no Lean instances yet.
- `[CONJECTURE]` `∂𝒱` = closure of pattern-region boundaries; the m-step window branch over
  certified-viable parameters (see `0-backlog/m-step-window-branch.md`).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (proofs carried directly in Lean)
- [x] 2 → 3  formalized: axiom set `[propext, Classical.choice, Quot.sound]`; build + lint green
- [ ] 3 → 4  publication-ready

## Log
- 2026-07-02 — sectors + patterns + kit + slice + bracket banked; ρ(π) pinned two-sided.

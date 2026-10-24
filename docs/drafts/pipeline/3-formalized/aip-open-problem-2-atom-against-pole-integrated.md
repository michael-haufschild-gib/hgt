# AIP Open Problem 2: The Integrated Atom-Against-Pole Law Across Gauges and Shifted Ground States

- **ID:** aip-open-problem-2-2026-10-24
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `formal/GaloisForLFunctions/ArithmeticIncidencePositivity/README.md` §7 Open Problem 2 & Research Topic 2
- **Lean Module:** `formal/GaloisForLFunctions/ArithmeticIncidencePositivity/ShiftedGroundStateAndFirstJetAtomPoleLaw.lean` (building on `TheIntegratedAtomPoleLawOfLogConcaveGauges.lean`)
- **Statement:** Complete resolution of Open Problem 2 ("The atom against the pole, integrated") and Research Topic 2 ("The integrated atom-versus-pole law"):
  1. **Strict midpoint payment outside `{2, 3, 4, 5, 7}` (`vonMangoldtAtom_lt_crossingPolarWeight_midpoint_of_not_mem`, `vonMangoldtAtom_lt_crossingPolarWeight_midpoint_iff`):** For every `n ≥ 2`, `vonMangoldtAtom n < crossingPolarWeight (Real.log n) (Real.log n / 2)` iff `n ∉ atomDominatedModuli = {2, 3, 4, 5, 7}`.
  2. **Shifted ground-state midpoint concentration and complete integrated classification (`shiftDifference_collar_le_of_abs_sub_ge`, `shiftDifference_collar_ge_of_abs_sub_le`, `eventually_shiftedGroundState_collar_integral_pos`, `eventually_collarAtomMass_lt_collarPolarMass_of_not_mem`, `eventually_collarAtomMass_lt_collarPolarMass_iff`, `exists_collarAtomMass_lt_collarPolarMass_shiftedGroundState_iff`):** Using the sharp double-exponential tail bounds of `riemannKernelReal`, as `a → ∞` the shifted ground-state collar `shiftDifference a x * shiftDifference a (L - x)` concentrates at the midpoint `L / 2` with outer/inner ratio `O(exp(-2π e^{2a - L}(cosh(2δ) - cosh δ)))`. Consequently, for every `n ≥ 2`, `∀ᶠ a in atTop, collarAtomMass (shiftDifference a) n < collarPolarMass (shiftDifference a) n` iff `∃ a > 0, collarAtomMass (shiftDifference a) n < collarPolarMass (shiftDifference a) n` iff `n ∉ atomDominatedModuli = {2, 3, 4, 5, 7}` (paying both `11` and `13`).
  3. **Axis-decay law and first-jet log-concave classification (`firstJetAtomDominatedModuli`, `integral_mul_sub_crossingPolarWeight`, `collarPolarMass_id_sub_collarAtomMass_id`, `collarAtomMass_id_lt_collarPolarMass_id_thirteen`, `collarPolarMass_id_lt_collarAtomMass_id_eleven`, `forall_div_id_logConcave_collarAtomMass_lt_iff`):** For odd gauges with linear origin decay (`x ↦ log(M x / x)` concave on `(0, log n)`), the exact `x(L - x)`-weighted polar integral is `(L³/6 - 2L) cosh(L/2) + 4 sinh(L/2)`. At `n = 13`, the polynomial factors over `ℤ` as `2(3 - L)(4 - L)(12 - L²) > 0`, while at `n = 11` it equals `18(4 - L)² - 2(L(3 - L))² - 48 < 0`. Thus first-order axis vanishing pays `13` and leaves `{2, 3, 4, 5, 7, 11}` unpaid, establishing the exact 3-tier axis-decay hierarchy `{2,3,4,5,7,11,13} ⊃ {2,3,4,5,7,11} ⊃ {2,3,4,5,7}`.
  4. **What pays the five moduli `n ∈ {2, 3, 4, 5, 7}` (`collarAtomMass_sub_collarPolarMass_bounds`, `interior_lattice_crossing_of_mem_atomDominatedModuli_eq_two_two`, `reflectedDifferenceJump_four_midpoint_eq_zero`):** Two-sided deficit bounds on `n ∈ {2, 3, 4, 5, 7}` and exact vanishing of the unique interior lattice crossing `(2, 2)` on `{2, 3, 4, 5, 7}` at the anti-diagonal midpoint `log 2 = log 4 / 2`.

## Gates
- [x] 0 → 1  in-progress: well-posed, corpus searched, complete mathematical structure derived
- [x] 1 → 2  fully-proven: complete paper proofs with zero open dependencies
- [x] 2 → 3  formalized: Lean module `ShiftedGroundStateAndFirstJetAtomPoleLaw.lean` verified with `lake --old env lean` (`task-574`, exit code 0), wired into `ArithmeticIncidencePositivity.lean`
- [x] 3 → 4  README updated crisply

## Log
- 2026-10-24 — created in 1-in-progress.
- 2026-10-24 — formalized and verified in `ShiftedGroundStateAndFirstJetAtomPoleLaw.lean`, wired into `ArithmeticIncidencePositivity.lean`, updated `README.md`, moved to `3-formalized`.

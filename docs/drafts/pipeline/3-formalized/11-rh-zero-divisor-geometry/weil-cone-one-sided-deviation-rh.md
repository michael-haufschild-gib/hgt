# One-sided deviations of Weil-positive systems force RH

- **ID:** weil-cone-one-sided-deviation-rh
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** bohr route rows 83–84 (`1-in-progress/bohr-route-detection.md`); STATUS MUST-738.
- **Statement.** Let `lam` be full-cone Weil-positive (`WeilPositiveFull`). Write `lam − Λ = P − N` on `n ≥ 2` with `P, N ≥ 0`. If `Σ_n P(n) n^{−σ} < ∞` for every `σ > ½`, then RH holds. (The case `lam ≤ Λ` is subsumed by the corpus `eq_vonMangoldt_of_weilPositiveFull_of_le`, which gives `lam = Λ`.)

## Lean
- Module `formal/GaloisForLFunctions/RHTower/WeilConeOneSidedDeviationRH.lean` (wired into `RHTower.lean`); axioms `propext`, `Classical.choice`, `Quot.sound`.
- Main theorems: `riemannHypothesis_of_weilPositiveFull_of_summable_deviationPos`; balanced abscissae `summable_deviationPos_iff_summable_deviationNeg`, `not_summable_deviation_of_ne`, `eq_vonMangoldt_of_weilPositiveFull_of_summable_deviation`.
- Steps:
  - `deriv_xi_eq_of_one_lt_re`;
  - `deriv_xi_eq_of_lt_re` (identity theorem on convex half-planes);
  - `summable_gdTwistTerm_deviationNeg` (Landau at the real abscissa);
  - the residue law `tendsto_sub_mul_logDeriv_xi_sub_weilContinuation`.
- Bridges: `gdSeries_logFreq`, `gdTwistTerm_logFreq` (ordinary Dirichlet series as general ones).

## Novelty and significance
- The `lam ≤ Λ` case was already in the corpus (`eq_vonMangoldt_of_weilPositiveFull_of_le`). New: the summable-excess form and the balanced abscissae. The latter extend the corpus summable-deficit rigidity (at `s = ½`) to every `s < 1` and to both parts.
- Role: detection (`W ≠ ∅ ⇒ RH`) needs only one-sided (majorant) pinning of producers. Exact-null tests `ĝ = Ξ²ĥ` (`Q_Λ = 0` at every zero, unconditionally) give precisely that side, so detection ⟸ Q_ann⁺: every log-bounded `u` with `Ξ²·Σu(m)cos(t log m) ≥ 0` has `u ≥ 0`.
- Q_ann⁺ is open and not weaker than `W ⊆ {Λ}`. Truncated LPs cannot decide it (bohr row 84).
- The theorem itself is a sharp receiver: classical in mechanism (Landau), new as a statement about the integer Weil cone.

## No-go closure
- Positive survivor: the one-sided reduction above. Open core: the quasi-producer majorant law (Q_ann⁺).

## Extension (2026-10-03): balanced abscissae (MUST-739)
- `summable_deviationPos_iff_summable_deviationNeg`: right of every `c ≥ ½`, the excess `P` and the deficit `N` converge together.
- `not_summable_deviation_of_ne`: a Weil-positive `lam ≠ Λ` has `Σ P n^{−s} = Σ N n^{−s} = ∞` for all `s < 1`.
- Generic Landau step: `summable_gdTwistTerm_of_xi_continuation`. The module is now 443 lines, imports `WeilAbscissaRigidity`, and has standard axioms.

## Companion (2026-10-03): one-sided witnesses vanish (MUST-741)
- Module `WeilNullPotentialOneSidedWitness.lean` (187 lines, wired into `RHTower.lean`, standard axioms). A log-bounded `u ≥ 0` (or `≤ 0`) with positive-definite null potential is `0`.
- Consequence: the majorant route (exact-null tests ⇒ `lam ≤ Λ` ⇒ RH, MUST-738) needs the two-sided annihilator statement Q_ann. The one-sided Q_ann⁺ is equivalent to it.

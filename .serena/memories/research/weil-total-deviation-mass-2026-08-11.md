# Attempt 15: RH as the vanishing of one convergent series (Lean-proved)

Module: `formal/GaloisForLFunctions/RHTower/GaussHodgeWeilTotalDeviationMass.lean` (wired,
umbrella green 18910 jobs, all 5 key theorems `[propext, Classical.choice, Quot.sound]`).

## Headline
`xiTotalDeviationMass := Σ'_q (Im α_q)²/‖α_q‖²` over the multiplicity-exact centered divisor:
- Converges UNCONDITIONALLY (`xiDeviationMassDensity_summable`): strip bound (im² ≤ 1/4)
  dominates by (1/4)·(1/‖α‖²), summable by corpus `xiSpectralPoint_inv_sq_summable`
  (XiCanonicalProduct.lean, genus-one Hadamard over copies).
- 0 ≤ mass ≤ (1/4)·Σ' 1/‖α_q‖² (`xiTotalDeviationMass_le_quarter`).
- **`riemannHypothesis_iff_totalDeviationMass_eq_zero`: RH ⟺ mass = 0.** Converse via
  le_tsum term extraction; the ‖α‖ = 0 edge case (α = 0 ⇒ im = 0) handled without needing
  ξ(1/2) ≠ 0.

## All-heights arithmetic ceiling
`xiArithmeticDeviationCeiling δ A q := if |Re α_q| ≤ 3 then 1/4 − δ else 1/4 − A/(2·log⁹|Re α_q|)`.
`exists_arithmetic_weighted_moment_bound`: ∃ δ A with (i) every squared deviation ≤ ceiling,
(ii) ceiling < 1/4 at EVERY copy, (iii) unrestricted weighted deviation-moment lower bound
Re W(F,F) ≥ Σ‖even‖² − Σ ceiling·‖ΔF‖² for all square-summable F with summable ΔF².
`xiTotalDeviationMass_le_arithmetic_ceiling`: mass ≤ Σ ceiling·(1/‖α‖²).

## Final shape of the wall (attempts 11–15)
Known mathematics traps: 0 ≤ xiTotalDeviationMass ≤ Σ ceiling/‖α‖², ceiling < 1/4 everywhere
(Euler product via PNTPlus zero-free region). RH ⟺ mass at the left endpoint. 

## Caveats / notes
- Divisor NONEMPTINESS is not formalized (first zero γ ≈ 14 needs computation or Hardy-type
  argument): avoid strict tsum inequalities; everything stated with ≤.
- δ is min-ed with 1/8 to keep the low ceiling nonneg (needed for summability domination).
- Pattern for a/c ≤ b/c with possibly-zero c: rewrite via div_eq_mul_inv twice +
  mul_le_mul_of_nonneg_right (inv_nonneg).

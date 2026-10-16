# CHMD: odd-cone sign law of prime cross terms (2026-10-16)

STATUS MUST-1562. Card: 3-formalized/chmd-odd-window-cross-sign-2026-10-16.md. Module `RHTower/CHMDOddWindowCrossSign`
(ns RHTower.CHMDPolar), 11 decls, wired. Follows MUST-1561 (`CHMDSinglePrimeWindow`).

## Results
- `phiDoobPrimeCross_nonpos_of_odd_oneSigned`: odd v ≥ 0 on [0,∞), supp ⊆ (−L/2, L/2), L ≤ 2 log n ⇒ cross n ≤ 0 pointwise.
- `tsum_cross_nonpos_of_odd_oneSigned` (L ≤ 2 log 2); **`levy_le_sourceEnergy_of_odd_oneSigned`** (E(v) ≥ weilLevyForm(Θv)).
- `sq_abs_sub_abs_le`, `integral_sq_abs_sub_le`, `jumpEnergy_abs_le`, **`weilLevyForm_abs_le`** (diamagnetic), `abs_phiDoobTest`,
  **`levy_abs_le_sourceEnergy_of_odd_oneSigned`** (E(v) ≥ weilLevyForm(Θ|v|)), `sourceEnergy_nonneg_of_levy_abs_nonneg`.

## Lesson
Fixed-prime-power domination is automatic on the one-signed odd cone (lag crosses the origin). Arithmetic positivity on
the cone with window ≤ 2 log 2 (primes 2, 3 active) ⟸ prime-free Λ_∞ ≥ 0 on nonneg even tests of support ≤ 2 log 2
(stronger than corpus weilArchRe ≥ 0 at 12/25, which keeps the pole mass). Next: exact cross-sign bonus identity
Λ_∞(Θv) = Λ_∞(Θ|v|) + 4∫∫_{s,t>0} g(s)g(t)ω(s+t).

## Lean traps
- `lintegral_mono_ae` + `ae_restrict_of_forall_mem measurableSet_Ioi` avoids measurability of the jump integrand;
  `archLevyDensity_pos` needs `0 < x` (density negative for x < 0).
- `mul_nonpos_iff.mpr (Or.inl ⟨_, _⟩ / Or.inr ⟨_, _⟩)` for sign products; `abs_abs_sub_abs_le_abs_sub` + `pow_le_pow_left₀` + `sq_abs`.

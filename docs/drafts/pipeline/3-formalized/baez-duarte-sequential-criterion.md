# Báez-Duarte sequential criterion and exponent law

- **ID:** baez-duarte-sequential
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** RH goal loop cycles 269–270 (MUST-771, MUST-772)
- **Statement:** RH ⟺ `c_{k+1} = O(k^{−3/4+ε})` ∀ε, `c_k = Σ_{j≤k}(−1)^jC(k,j)/ζ(2j+2)`; exactly `Θ = 2·inf{b : c_k = O((k+1)^{b−1})}`.

## Goal
Close the missing converse half of the corpus Báez-Duarte lane (forward half: weighted-moment scale
law, `bdCoeff_decay_of_weightedMoments`) and give the exact exponent law.

## Gates
- [x] 0 → 1, 1 → 2
- [x] 2 → 3: `RHTower.riemannHypothesis_iff_bdCoeff_decay` (BaezDuarteRieszPoissonCriterion),
  `zetaZeroAbscissa_eq_two_mul_sInf_bdReal_exponents` (BaezDuarteExponentLaw); axioms clean.
- [ ] 3 → 4 (no manuscripts by directive)

## Approach
- Poissonization: `R(x) = Σμ(n)n^{−2}e^{−x/n²} = e^{−x}Σ_k c_k x^k/k!`.
- Poisson power decay: `Σ e^{−x}x^k/k!(k+1)^{−β} ≤ 2x^{−β}` via `t^{−β} ≤ 1 + t^{−1}`.
- Lower half by the Riesz Mellin obstruction (riesz-function-criterion card); upper half by the
  generic Abel transfer with weight increments `≤ 9·128^θ k^{−2θ} n^{4θ−3}`.

## Log
- 2026-10-05 — created and formalized.
- 2026-10-05 — Ω± and one-sided boundary (MUST-773, BaezDuarteQuarterPowerOmega).

# First-power prime injections with coprime periods are equidistributed under ×4

- **ID:** first-power-coprime-injection
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** parity-drift-pi card (1-in-progress), cycle 66 (log row 89)
- **Statement:** Let q_j be the j-th prime ≥ 5 and p_j the least prime factor of (4^{q_j} − 1)/3
  (so p_j ∤ 6, p_j ∣ 4^{q_j} − 1, the p_j are distinct). If e is strictly increasing with
  (J+1)(e_J + 2 q_0⋯q_{J+1}) ≤ e_{J+1}, then x_e = Σ_j p_j^{−1} 4^{−e_j} has Weyl sums o(N) at every
  nonzero frequency under ×4; hence {4ⁿx_e} is equidistributed and its parity drift is o(N).
- **Escape bound (new ingredient):** for every prime p ∤ 6b with p ∣ 4^q − 1,
  ‖Σ_{t<q} e(b4ᵗ/p)‖ ≤ q − 1/72 — no Gauss sum, valid for every order of 4 mod p (the cubes of a
  fourth-power cycle near 1 double their distance to 1, so the cycle leaves every disc of radius 1/6).

## Goal
Reach-table rung inside the **first-power regime** that blocks π (log row 84): every denominator is a
prime entering at the first power, where complete subgroup sums are Gauss sums of size √p rather than 0.
The Gauss-sum loss is bypassed by (i) the escape bound 1 − 1/(72q) per prime and (ii) pairwise coprime
periods, which make the mean over a common period the product of the individual means (CRT); Σ 1/q = ∞
then drives the product to 0.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper proof = the Lean development)
- [x] 2 → 3  formalized: `FirstPowerInjection.not_parityDriftHypothesis_injNumber_injExp`
  (hypothesis-free instance), `FirstPowerInjection.tendsto_weylSum_injNumber`,
  `StonehamParityDrift.norm_sum_ephase_orbit_le`; axioms propext, Classical.choice, Quot.sound
- [ ] 3 → 4  publication-ready

## Lean
- `HTGeometry/FourthPowerCycleEscape`: `norm_pow_sub_one_le`, `two_mul_le_norm_pow_four_sub_one`,
  `exists_le_norm_sub`, `norm_sum_le_sub`, `norm_sum_ephase_orbit_le`.
- `HTGeometry/CoprimePeriodInjectionNormality`: periodic block sums (`norm_sum_block_le`), CRT for
  means (`sum_range_mul_coprime`), repunit primes (`injPrime_dvd`, `injPrime_ne_two/three`,
  `injPrime_injective`), `tendsto_prod_meanFactor` (via `Nat.Primes.not_summable_one_div`), block
  decomposition `weylPhase_eq`, `norm_weylSum_le`, `tendsto_weylSum_injNumber`.

## Why π is still out of reach
π's BBP denominators 8k+j have orders of 16 that share factors (no CRT factorisation of means) and
enter at every step (the common period is never completed: the logarithmic-length barrier). The rung
removes the per-prime √p obstruction only for sparse injections with coprime periods.

## Novelty audit
Classical explicit normals (Stoneham α_{b,c}; Korobov β_{b,c,d}; Bailey–Crandall Σ 1/(b^{m_i}c^{n_i}))
use powers of one modulus. Distinct first-power prime denominators with an elementary escape bound in
place of primitive-root / Gauss-sum input: not found in the literature checked; significance is that of
a model rung, not of a result about π.

## Log
- 2026-10-03 — created directly in 3-formalized (cycle 66 of the PDH-π goal).

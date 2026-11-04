# An explicit gauge point with Möbius exponent one half

- **ID:** F0311-Q3-4.3
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0311/fable.md` §4.3; loop card `1-in-progress/fable-0311-q3-breakthrough-questions.md`
- **Statement:** The gauge point `halfPoint` — the Liouville twin of `χ₄` with quarter phases `±i` on
  the first `2^k` primes of each octave `(4^k, 2·4^k]` — has Möbius exponent exactly `½`, its sums
  reach `√(N/2)` along `N_k = 2·4^k`, and it agrees with no point `dirichletGauge ψ + verticalShift t`
  (Tate line of `0` included) at all but finitely many primes.

## Answer to §4.3

Yes. The half-power law is reached at an explicit point outside the special locus without the pole:
the cancellation comes from the periodicity of `χ₄` (through `μ² = Σ_{d²|n} μ(d)`), the lower bound
from prime blocks above `N_k/2`, which are the only squarefree multiples of themselves below `N_k`.

## Paper proof

Notation: `S_x(N) = Σ_{n≤N} μ(n)χ_x(n)`, `A_x(N)` the same sum over `n` prime to `p`.

1. **One prime, sharp form.** If `x, x'` agree off a prime `p`, splitting off `p` gives
   `S_{x'}(N) = S_x(N) − (χ_{x'}(p) − χ_x(p)) A_x(⌊N/p⌋)`. Inversion `A_x(M) = Σ_k χ_x(p)^k S_x(⌊M/p^k⌋)`
   bounds `|A_x(M)| ≤ C 2^θ (1 − p^{−θ})^{−1} (M+1)^θ` under `|S_x(M)| ≤ C(M+1)^θ`. `A_x(0) = 0`, and for
   `⌊N/p⌋ ≥ 1`, `⌊N/p⌋ + 1 ≤ 2(N+1)/p`. Hence `|S_{x'}(N)| ≤ C(1 + K_θ p^{−θ})(N+1)^θ`,
   `K_θ = 2·4^θ/(1 − 2^{−θ})`.
2. **Sparse sets.** By induction the factors multiply over a finite set. The sum up to `N` reads only
   primes `≤ N`, so if every finite part of `P` has `Σ p^{−θ} ≤ B`, agreement off `P` transports the
   bound with factor `∏(1 + K_θ p^{−θ}) ≤ exp(K_θ B)`. Consequently, if `P` is sparse at every
   `θ > θ₀`, `θ_μ(x') ≤ max(θ₀, θ_μ(x))`.
3. **Blocks.** `P_k` = first `2^k` primes of `(4^k, 2·4^k]`; disjoint; `p ∈ P_k ⇒ k < p`. Each
   `p ∈ P_k` has `p^{−θ} ≤ (4^{−θ})^k`, so `Σ_{P_k} p^{−θ} ≤ (2·4^{−θ})^k`, a geometric series with
   ratio `< 1` for `θ > ½`.
4. **Upper bound.** The twin of `χ₄` has exponent `≤ ½` (twin inequality with the constant source at a
   nonprincipal Dirichlet point). `halfPoint` agrees with it off `⋃P_k`; by 2–3 its exponent is `≤ ½`.
5. **One block step.** For `n ≤ N_k = 2·4^k` and `p ∈ P_k`, `p ∣ n ⇒ n = p` (`p > N_k/2`). So setting
   `P_k` to the phase `u` changes `S(N_k)` from `S_z(N_k)` to
   `blockCharge z k − #P_k·u`, `blockCharge z k = S_z(N_k) + Σ_{p∈P_k} χ_z(p)`.
6. **Signs.** Stages set the blocks in order, with `u_k = i` if `Im(blockCharge) < 0`, else `−i`.
   Then `|Im S(N_k)| ≥ #P_k`. The limit point agrees with stage `k+1` at all primes `≤ N_k`
   (later blocks lie above `4^{k+1} > N_k`), so `|S_{halfPoint}(N_k)| ≥ #P_k`.
7. **Lower bound.** By the PNT window count, `(4^k, 2·4^k]` holds `≥ 4^k/(2k log 4) ≥ 2^k` primes for
   large `k` (`2k log 4 < 3k ≤ 2^k`), so `#P_k = 2^k` and `|S(N_k)| ≥ 2^k = √(N_k/2)`. A bound
   `C(N+1)^θ`, `0 ≤ θ < ½`, would give `(2/4^θ)^k ≤ C 3^θ` for all large `k`: impossible. So the
   exponent is `≥ ½`.
8. **Outside the special locus.** For `p ≡ 1 (mod 4)` the point takes `−1` (twin value `−χ₄(p)`) or
   `±i`: `χ^4 = 1`, `χ ≠ 1`. For `p ≡ 1 (mod 4q)`, `dirichletGauge ψ + verticalShift t` takes
   `ψ(p)p^{it} = p^{it}`. If they agreed at two such primes `p₁ ≠ p₂`, then `4t log p_j ∈ 2πℤ`; for
   `t ≠ 0` this gives `|n₂| log p₁ = |n₁| log p₂`, `p₁^{|n₂|} = p₂^{|n₁|}`, contradiction; so `t = 0`
   and the value would be `1`. Infinitely many primes `≡ 1 (mod 4q)` exist, so agreement fails at
   infinitely many primes.

## Lean

`formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheExponentIsInvariantOnSparsePrimeSets.lean`:
`moebiusGaugeSum_eq_sub_of_agree_off`, `primeTransferConst`, `norm_moebiusGaugeSum_le_of_agree_off`,
`norm_moebiusGaugeSum_le_of_agree_off_finset`, `moebiusGaugeSum_congr_of_le`,
`gaugePowerBound_moebius_of_agree_off_sparse`, `gaugeExponent_moebius_le_of_agree_off_sparse`.

`formal/GaloisForLFunctions/ArithmeticGaugeTheory/AnExplicitPointHasExponentOneHalf.lean`:
`halfBlock`, `halfPrimes`, `sum_rpow_le_of_subset_halfPrimes`, `twinPoint`,
`gaugeExponent_twinPoint_le`, `moebiusGaugeSum_setBlock`, `halfStage`, `halfPoint`,
`card_halfBlock_le_norm`, `eventually_card_halfBlock`, `eventually_two_pow_le_norm_halfPoint`,
`not_gaugePowerBound_halfPoint`, **`gaugeExponent_halfPoint`**, `twist_halfPoint_of_mod_four`,
`eq_zero_of_exp_four_mul_log`, **`halfPoint_not_special`**.

Both modules checked with `lake --old env lean`; transitive axioms of `gaugeExponent_halfPoint`,
`halfPoint_not_special`, `eventually_two_pow_le_norm_halfPoint`,
`gaugeExponent_moebius_le_of_agree_off_sparse`: `propext`, `Classical.choice`, `Quot.sound`.
Wired into `ArithmeticGaugeTheory.lean`.

## Consequences

- The half-power law at a single point does not need the pole: `halfPoint` has no pole, no Euler
  product of an `L`-function, and exponent `½`.
- Sparse invariance: the exponent is a `θ`-sparse tail invariant above `½` (finite flips were the
  previous invariance).
- Square-root size is attained, not only approached: `|S(N_k)| ≥ √(N_k/2)` infinitely often.

## Log
- 2026-11-03 — paper proof and Lean formalization completed

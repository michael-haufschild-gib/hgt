# Margins of zero-density prime-set twins

- **ID:** rit-zero-density-margin
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) + open converse
- **Programme:** RenormalizedIntersectionTheory, open topic 3
- **Statement (target classification):** for a prime set `P` with zero Euler density
  (`Σ_{p∈P} 1/p = ∞`), with conductor weights `w_P(m) = (μ * ω_P)(m)²/φ(m)` and energies
  `E_m − γ = log m + Σ_{p|m} log p/(p − 1)`:
  `HodgeSeparates ω_P ⇔ ∃ s ∈ (0, 2 log 2), Σ_{m≥2} w_P(m)/(E_m − γ − s) > 1/s` (divergence included).

## Status of the two directions
- **⇐ (separation)**: from `ArithmeticCountingPositivity.primeSet_partial_secular_le_of_gap`
  (a gap above `s` bounds every finite packet sum by `1/s`, no density assumption).
- **⇒ (maximal margin when the series stays ≤ 1/s)**: open at zero density (ACP open question 2);
  proved at positive density (`primeSetFlip_hasHyperplaneGap_iff_secular`).

## Proof of divergence for lower logarithmic density ≥ 1/4
Hypothesis: `Σ_{p∈P, p≤n} log p/p ≥ (1/4) log n − C` for all `n ≥ 1`.
1. Squarefree `P`-supported `m = ∏_{p∈T} p`: `w_P(m) = ∏_{p∈T} 4/(p−1)` (multiplicativity,
   `(μ*ω)(p) = −2`), `e(m) := E_m − γ = Σ_{p∈T} p log p/(p−1)`.
2. Laplace: `1/e ≥ Σ_{j<J} 2^{−j−1} e^{−2^{−j} e}` (`(e^{−ae} − e^{−be})/e ≥ (b−a)e^{−be}`, telescoping).
3. `Σ_{T⊆F} ∏_{p∈T} x_p = ∏_{p∈F}(1 + x_p)`, `x_p = (4/(p−1)) e^{−σ p log p/(p−1)} ≥ 4 p^{−1−2σ}`.
4. `log(1+x) ≥ x − x²`; `Σ x_p² ≤ 32`: `∏(1 + x_p) ≥ exp(Σ x_p − 32)`.
5. Abel summation with `g(t) = t^{−2σ}/log t` decreasing: `Σ_{p∈P,p≤X} (log p/p) g(p) ≥
   (1/4) Σ_{k≤X} (Δ log k) g(k) − C g(2)`.
6. `e^{−2σ log k} ≥ 1 − 2σ log k`; `Δlog k/log k ≥ Δ log log k − (Δ log k)²/(log k log(k−1))`:
   with `X = e^{1/(2σ)}`, `Σ x_p ≥ log(1/σ) − C'`.
7. `Z(σ) = ∏(1 + x_p) ≥ e^{−C''}/σ`; `Σ w/e ≥ Σ_{j<J} 2^{−j−1}(Z(2^{−j}) − 1) ≥ c J − 1 → ∞`.

## Gates
- [x] 1 → 2  fully-proven (separation side)
- [x] 2 → 3  formalized: `RenormalizedIntersectionTheory/TheConductorSeriesSeparatesTheZeroDensityTwins.lean`

## Lean declarations
`hodgeSeparates_primeSetFlip_of_packet`, `hodgeSeparates_primeSetFlip_iff_secular_pos`,
`primeSetSpectralWeight_prod_primes`, `ramanujanAdjunctionEnergy_prod_primes`,
`sum_dyadic_exp_le_inv`, `sum_dyadic_euler_le_packet`, `exp_sub_le_prod_one_add`,
`sum_Icc_two_mul_eq_abel`, `exists_sum_inv_primeSetCutoff_ge`, `exists_flipPrime_euler_ge`,
`exists_packet_gt_of_lowerLogDensity`, `hodgeSeparates_primeSetFlip_of_lowerLogDensity`,
`hodgeSeparates_residueClassFlip_of_totient_le_four`, `hodgeSeparates_primeSetFlip_one_mod_five`.

## Converse (open)
Needs `R_N(s)/c_N² → −1/s + W_P(s)` for the actual resolvent at zero density: the spectral mass of
the horizon vector above bounded energies must sit at energies `≫ c_N^{−2}`.
- Exact reformulation: `L − γ − P_N(x) = D(y) − Σ err_n y_n²/n`, `y_n = √n x_n`,
  `D(y) = Σ_{m,t} Λ(t)/(mt) (y_m − y_{mt})²`, `err_n = Σ_{t≤N/n} Λ(t)/t − log(N/n) + γ`. With
  `u = α·1 + z`, `z ⊥ 1`, the gap `s` is `⟨ŵ_⊥, (G − s)^{−1} ŵ_⊥⟩ ≤ c_N²/s (1 + o(1))`, `G = D − M_err`
  on `1^⊥`; the `err` cross terms are `O(1/(c_N √log N))`, negligible exactly when `S_N² ≫ log N`.
- Variationally the packet part is exact (quasimode inner products, as in the inheritance proof); the
  missing input is `⟨ŵ_h, G_h^{−1} ŵ_h⟩ = o(c_N²)` on the complement of a finite packet. Bounded-window
  tools give only `≤ 1/T`. Upper bounds would follow from Thomson flows of energy `o(c_N²)` for the
  twisted charge `(ω(n) − c_N)/n` on the multiplicative graph.
- Heuristic size of the bulk: the incoherent part of `ŵ` has energy `≍ κ log N` and contributes
  `≍ (log log N)/log N ≪ c_N²` when `κ < 1/4`.

## Log
- 2026-11-01 — card created; separation side formalized; converse open

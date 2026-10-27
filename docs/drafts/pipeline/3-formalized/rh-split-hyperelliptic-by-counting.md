# RH for split odd-degree hyperelliptic curves by counting

- **ID:** aet-rh-split-hyperelliptic
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** AET README §10 (calibration: unitarity of curve data), fable §5.7.1, §5.8.12
- **Statement:** `p` odd prime, `f ∈ 𝔽_p[X]` squarefree of odd degree `m`, split over `𝔽_p`. There
  are `ω_1, …, ω_{m−1} ∈ ℂ` with `|ω_i| = √p` and, for every finite extension `E/𝔽_p` of degree
  `n`, `Σ_{x∈E} χ_E(f(x)) = −Σ_i ω_i^n`; hence `|#{(x,y) ∈ E² : y² = f(x)} − |E|| ≤ (m−1)√|E|`.

## Goal
The function-field calibration of AET with counts as the only positivity: Stepanov's section count
(`RHTower.Stepanov`) gives `|ω_i| ≤ √p`; the Gauss-sum modulus `|τ|² = p` gives
`|Π ω_i| = p^{(m−1)/2}`; together unitarity, hence (ACS/AET) Hodge index, naive heights and
effectivity functions for an actual family of curves of every genus.

## Approach (paper proof)
1. *Weight.* `w(P) = χ(Res(P, f))` on monic `P`; multiplicative (`resultant_mul_left`).
2. *Extensions.* For `x ∈ E`, `P = minpoly x`, `d = deg P`: `χ_E(y) = χ_F(N_{E/F} y)` (Euler,
   `algebraMap_norm_eq_pow`); `N_{E/F}(x − α) = ((−1)^d P(α))^{n/d}` (`norm_eq_norm_adjoin`,
   `minpoly.sub_algebraMap`); with `f = c Π(X − α_i)`: `N(f(x)) = Res(P, f)^{n/d}`
   (`resultant_comm`, `resultant_eq_prod_eval`). Grouping by minimal polynomial
   (`card_minpoly_fiber`): `Σ_{x∈E} χ_E(f(x)) = c_n := Σ_{d∣n} Σ_{P irr, deg d} d w(P)^{n/d}`.
3. *Degree sums.* `s_k = Σ_{deg h = k} w(h) = χ(±c^k) Σ_h Π_i χ(h(α_i))`; for `k ≥ m` the evaluation
   vector is uniform on `𝔽^m` (Vandermonde), so `s_k = 0`.
4. *Newton.* `k s_k = Σ_j c_j s_{k−j}` (`newton_identity`) and Newton for the roots `ω_i` of
   `Σ_{k<m} s_k X^{m−1−k}` give `c_n = −Σ ω_i^n`.
5. *Upper bound.* Stepanov over `E` with `|E| = p^{2k}` (`abs_sum_quadraticChar_le`) gives
   `|Σ (ω_i²)^k| ≤ C p^k`, so `|ω_i|² ≤ p` (`norm_le_of_power_sums_bound`).
6. *Functional equation.* `s_{m−1} = Σ_{v : Σ v_i/d_i = 1} Π χ(v_i)` (Lagrange,
   `d_i = Π_{j≠i}(α_i − α_j)`); additive orthogonality and Gauss sums give
   `|s_{m−1}| = |τ|^{m+1}/p = p^{(m−1)/2}`.
7. *Unitarity.* `|Π ω_i| = |s_{m−1}|`, `m − 1` factors each `≤ √p`: all `|ω_i| = √p`.

## Lean
- `RHTower/HyperellipticLFunction.lean`: `hypW`, `hypW_mul`, `quadraticChar_norm`,
  `norm_sub_algebraMap`, `norm_aeval_eq_resultant_pow`, `extHyp_eq_powerSumW` (steps 1–2).
- `RHTower/HyperellipticDegreeSums.lean`: `hypW_eq_prod`, `degSumW_eq_zero`,
  `sum_monicDeg_pred_eq` (steps 3, 6).
- `RHTower/HyperellipticRiemannHypothesis.lean`: `esymm_lRoots`, `powerSumW_eq_neg_rootPowerSum`,
  `norm_prod_lRoots`, `norm_rootEnum_le`, `riemannHypothesis_splitHyperelliptic`,
  `abs_card_points_sub_le_splitHyperelliptic` (steps 4, 5, 7). Axioms: propext, choice, Quot.sound.

## Log
- 2026-10-27 — created; corpus inputs located (RHTower.Stepanov*, RHTower.WeilKloosterman*,
  HTGeometry.MultisetNewton).
- 2026-10-27 — formalized (all seven steps).
- 2026-10-27 — generalized to every finite base field and every squarefree odd-degree `f`: card
  `rh-odd-hyperelliptic-curves-all-finite-fields.md`.

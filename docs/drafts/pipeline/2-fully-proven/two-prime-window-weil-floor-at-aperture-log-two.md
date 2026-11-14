# Positive Weil floor on the first full two-prime window at aperture `log 2`

- **ID:** A140-two-prime-aperture-log-two
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/review-1411/obstacles-summary.md` §2.21, §2.4
- **Statement:** Every real or complex compact `C²` test supported in `[-log 2, log 2]` satisfies `(1 / 10^13) ∫ |f|² ≤ Re W(f, f)` (`1 / 10^10` on odd real tests), while an explicit smooth polynomial test `F_* ∈ C²_c([-log 2, log 2])` satisfies `weilQuad F_* < (1 / 10^9) ∫ F_*²` and makes the degree-14 Gamma lower form strictly negative. Consequently `1 / 10^13 ≤ ccmRestrictedWeilGroundEnergy ⟨log 2, _⟩ < 1 / 10^9`, every step packet and neutral window `(R, R + J]` of ratio `(R + J) / R < 4` (`Q ≥ 3`, `R ≥ 1`) has uniform gap `1 / 10^13` and (for `R ≤ J`) `hermNegIndex = 1`, every ratio-three window (`R ≤ J ≤ 2 R`, `Q ≥ 2`, `R ≥ 1`) has gap `1 / 10^13` and `hermNegIndex = 1`, `levelAt Q 4 = 0` for `Q ≥ 3`, `levelAt 2 3 = 0`, and `globalTowerLevel k = 0` for `k ≤ 3`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorems checked with `lake --old env lean`, standard axioms only

## Proof `[PROVED HERE]`

### 1. Arithmetic enclosures at `A = log 2`

For `t ∈ (0, 1)` and `N ≥ 1`, integrating `2 / (1 - x²) = 2 ∑_{k=0}^{N-1} x^{2k} + 2 x^{2N} / (1 - x²)` over `[0, t]` yields
`∑_{k=0}^{N-1} (2 / (2k + 1)) t^{2k+1} ≤ log((1 + t)/(1 - t)) ≤ ∑_{k=0}^{N-1} (2 / (2k + 1)) t^{2k+1} + (2 / (2N + 1)) t^{2N+1} / (1 - t²)`.
Evaluating at `t = 1/5` (`N = 18`, giving `log(3/2)`) and `t = 1/7` (`N = 15`, giving `log(4/3)`) gives 26-digit rational enclosures for `log 2 = log(3/2) + log(4/3)` and `log 3 = 2 log(3/2) + log(4/3)`. Squaring rational brackets gives 26-digit enclosures for `√2` and `√3`. Combining `Real.pi_gt_d20` and `Real.pi_lt_d20` with `t = (π - 3)/(π + 3)` (`N = 8`) encloses `log π = log 3 + log(π/3)` to 20 digits.

For Euler's constant `γ`, define for `m ≥ 1`:
`u(m) = H_m - log m - 1/(2m) + 1/(12m²) - 1/(120m⁴) + 1/(252m⁶) - 1/(240m⁸) + 1/(132m¹⁰)`,
`l(m) = u(m) - 691 / (32760 m¹²)`.
Applying the `N = 7` bound on `log((m + 1)/m) = log((1 + t)/(1 - t))` at `t = 1/(2m + 1)` and substituting `m = 24 + x` (`x ≥ 0`) shows `u(m + 1) ≤ u(m)` and `l(m) ≤ l(m + 1)` for all `m ≥ 24`. Passing to the `m → ∞` limit (`H_m - log m → γ`) gives `l(24) ≤ γ ≤ u(24)`, enclosing `γ` to 18 digits via `log 24 = 3 log 2 + log 3`.

At `y = 2 log 2`, `e^{-y/2} = 1/2`, so `2 archLevyAntideriv(2 log 2) = log 3 + 2 arctan(1/2)`. Integrating `1 / (1 + x²) = ∑_{k=0}^{31} (-1)^k x^{2k} + x^{64} / (1 + x²)` over `[0, 1/2]` encloses `2 archLevyAntideriv(2 log 2)` to 20 digits, hence encloses `EF.gammaBracket 0`, `w₂ = log 2 / √2`, `w₃ = log 3 / √3`, `d₃ = log 3 / log 2`, `a = d₃ - 1`, and `L₄ = (1 - a)/2` to `≥ 18` digits.

### 2. Exact two-prime decomposition and Gamma kernel comparison on `(0, 7/5]`

Let `F ∈ C²_c(ℝ)` satisfy `tsupport F ⊆ [-A, A]` with `A = log 2`. Continuity forces `F(x) = 0` for `|x| ≥ A`. For every integer `n ≥ 4` and `u ∈ ℝ`, `log n ≥ log 4 = 2A`, so either `u ≤ -A` (`F(u) = 0`) or `u + log n > A` (`F(u + log n) = 0`). Thus `weil_eq_markovForm_add_pole` at `N = 3` gives the exact identity
`weilQuad F = EF.gammaBracket 0 ∫ F² + biScaleLevyEnergy F - 2 w₂ autocorr F (log 2) - 2 w₃ autocorr F (log 3) + coshPairing F² / 2 - sinhPairing F² / 2`.

On `(0, 7/5]` (containing `(0, 2 log 2]`), `archLevySinhWeight t = 1/(2 sinh(t/2)) + 1/(2 cosh(t/2))`. Truncating the reciprocal power series of `z / sinh z` at `z²²` gives `gammaSinhPolynomial22 z ≤ z / sinh z` on `(0, 1]` by multiplying against the degree-23 Taylor upper bound for `sinh z`. On `s = z² ∈ [0, 49/100]`, a degree-11 rational polynomial `Q_cosh(s) = ∑_{q=0}^{11} β_q s^q > 0` satisfies `Q_cosh(z²) coshTaylor24(z) ≤ 1` via a factored positive polynomial plus homogeneous Bernstein certificate on `[0, 49/100]`, proving `Q_cosh((t/2)²) ≤ 1 / cosh(t/2)`. Bounding the odd polynomial tail `∑_{k=5}^{11} c_{2k} (t/2)^{2k} / t ≥ P_corr(t²) = ∑_{q=0}^{11} γ_q t^{2q}` on `[0, 7/5]` by a second homogeneous Bernstein certificate yields
`retainedGammaRemainderWeight t ≥ (7/5760) t³ - (31/967680) t⁵ + (127/154828800) t⁷ + ∑_{q=0}^{11} α_q t^{2q} =: K_rem(t)`
for all `t ∈ (0, 7/5]` (pointwise gap `< 2.2 × 10⁻¹⁴`), and `autocorr_sub_nonneg` propagates `K_rem` under the lag integral.

### 3. Moment expansion, odd lag primitives, and regional harmonic gap

Put `G(u) = F(A u)` on `[-1, 1]`, `M = ∫₀¹ G(u)² du` (`∫ F² = 2 A M`), and let `m_k = ∫₀¹ G(u) legP(d_k, u) du` for `k = 0, ..., K - 1`, where `(K, M_cut, d_k) = (12, 24, 2k)` for even `F` and `(11, 23, 2k + 1)` for odd `F`. Let `P_K = lowProjection G M_cut = ∑_{k=0}^{K-1} (2 d_k + 1) m_k legP(d_k, ·)` on `[-1, 1]` and `R_K = G - P_K`, so `∫_{-1}^1 R_K² = 2 M_res` with `M_res = M - ∑_{k=0}^{K-1} (2 d_k + 1) m_k² ≥ 0`.

1. **Logarithmic lag and regional gap:** `logarithmic_lag_and_boundary` and parity folding give `(1/(2A)) ∫₀^{2A} (autocorr F 0 - autocorr F t)/t dt = regionalLogEnergy G / 4 + ∫₀¹ G(u)² V(u) du` with `V(u) = log 2 - log(1 - u²)/2`. By `regionalLogEnergy_ge_gap_sub_low_moments` at `M_cut`, `regionalLogEnergy G / 4 ≥ H_{M_cut} M - ∑_{k=0}^{K-1} (H_{M_cut} - H_{d_k})(2 d_k + 1) m_k²`.
2. **Even lag powers:** For `0 ≤ q ≤ 11`, Fubini and binomial expansion of `(y - x)^{2q}` express `∫₀² t^{2q} autocorr G t dt` as `2 ∑_{r=0}^q C(2q, 2r) μ_{q-r} μ_r` (even `G`) or `-2 ∑_{r=0}^{q-1} C(2q, 2r + 1) μ_{q-1-r} μ_r` (odd `G`), where each monomial moment `μ_j = ∫₀¹ u^{d_j} G(u) du` is a fixed rational combination of `m_0, ..., m_j`.
3. **Odd lag powers (`q = 0, 1, 2, 3`):** Let `I_1 h(x) = ∫_{-1}^x h` and `I_{r+1} h(x) = ∫_{-1}^x I_r h`. Integrating by parts `2q + 2` times on `y ∈ [x, 1]` and `q + 1` times on `x ∈ [-1, 1]` gives
   `∫₀² t^{2q+1} autocorr G t dt = ∫_{-1}^1 G Φ_{2q+1}(G) + (2q+1)! ∑_{r=0}^q (-1)^r I_{r+1} G(1) I_{2q+2-r} G(1) + (-1)^{q+1} (2q+1)! ∫_{-1}^1 (I_{q+1} G)²`.
   Because `R_K ⊥ span{1, ..., x^{M_cut - 1}}` and `2q + 1 ≤ 7 < M_cut`, `I_{r+1} R_K(1) = 0` for `0 ≤ r ≤ 7` and `∫_{-1}^1 R_K Φ_{2q+1}(P_K) = 0`. Thus
   `∫₀² t^{2q+1} autocorr G t dt = B_q(P_K, P_K) + 2(2q+1)! ∫_{-1}^1 (I_{2q+2} P_K - Q_q) R_K + (-1)^{q+1}(2q+1)! ∫_{-1}^1 (I_{q+1} R_K)²`,
   where `Q_q` is the projection of `I_{2q+2} P_K` below `M_cut`. Multiplying by `((-1)^q c_{odd,q} / 2) A^{2q+2}` makes every `(I_{q+1} R_K)²` coefficient `-w_{odd,q} < 0`. Applying Dirichlet–Wirtinger on `[-1, 1]` `q + 1` times (`I_r R_K(±1) = 0` for `1 ≤ r ≤ q + 1`) gives `∫_{-1}^1 (I_{q+1} R_K)² ≤ (4/π²)^{q+1} (2 M_res)`, and Young's inequality bounds the cross term by `(2 w_{odd,q}² / ε_q) ∫_{-1}^1 (I_{2q+2} P_K - Q_q)² + ε_q M_res`. Since `∑_{q=0}^3 (2 w_{odd,q}(4/π²)^{q+1} + ε_q) < δ_{res}`, the orthogonal remainder `M_res` retains a strictly positive net coefficient `> 2 × 10⁻⁴`.
4. **Pole pairings:** Taylor approximation of `cosh(A u / 2)` at degree 22 (even) and `sinh(A u / 2)` at degree 21 (odd) expresses the pole pairings as rank-1 quadratic forms in `m_0, ..., m_{K-1}` up to `< 10⁻²⁴ M`.

### 4. Six-interval fiber partition and exact rational Schur–Bernstein certificate

Because `0 < L₄ < 1 - a < 1/2 < a < 1 - L₄ < 1` with `L₄ = (1 - a)/2`, `[0, 1]` partitions up to measure zero into six intervals parametrized by:
- 4-vertex path fiber `s ∈ [0, L₄]`: `(x₁, x₂, x₃, x₄) = (s, 1 - s, a + s, 1 - a - s)` covering `[0, L₄] ⊔ [1 - L₄, 1] ⊔ [a, 1 - L₄] ⊔ [L₄, 1 - a]`;
- 2-vertex pair fiber `u ∈ [1 - a, 1/2]`: `(y₁, y₂) = (u, 1 - u)` covering `[1 - a, 1/2] ⊔ [1/2, a]`.

Under parity folding and change of variables, the prime-2 and prime-3 correlations combine with `∫₀¹ (c₀ + V(x)) G(x)² dx` into the exact fiber integrals
`∫₀^{L₄} g₄(s)ᵀ M₄(s) g₄(s) ds + ∫_{1-a}^{1/2} g₂(u)ᵀ M₂(u) g₂(u) du`,
where `M₄(s)` is the `4 × 4` tridiagonal matrix with diagonal `c₀ + V(x_i(s))` and off-diagonal `(e₂, e₃, e₂)` (`e_p = ∓w_p`), and `M₂(u)` is `2 × 2` with off-diagonal `e₂`. Absorbing `|e_2 - e_{2,0}| + |e_3 - e_{3,0}|` into `c_{0,rat}` via Young's inequality and bounding `V(x) ≥ base + ∑_{m=1}^{r_{ord}} ((x² - t₀)/(1 - t₀))^m / (2m)` around `{2, 3}`-smooth points `1 - t₀ = 2^p 3^q` (using `a ≥ a_{lo}` on `V(a + s)` and `a ≤ a_{hi}` on `V(1 - a - s)`) yields pure rational polynomial lower matrices `M_{4,rat}(ξ) ⪯ M₄(s)` and `M_{2,rat}(ξ) ⪯ M₂(u)` on 10 subintervals of `[0, L_{4,lo}]` and 2 subintervals of `[u_{2,hi}, 1/2]`, plus constant lower bounds on the two endpoint slivers `[L_{4,lo}, L₄]` and `[1 - a, u_{2,hi}]` of width `< 3 × 10⁻²⁴`.

On every subinterval and sliver, exact rational `L D Lᵀ` pivots certify `M_{rat}(ξ) - (17/16) I ⪰ 0` (`17/16 = 1/16 + 1`). For any symmetric `M ⪰ (17/16) I`, `v = v₀ + δv`, and rational polynomial witness `w`, setting `u = g - w` and `r = M w - v₀` gives the algebraic identity
`gᵀ M g - 2 gᵀ v = uᵀ(M - (17/16)I)u + (1/16)‖g - 16 δv‖² + ‖u + r‖² - (2 v₀ᵀ w - wᵀ M w + ‖r‖²) - 16 ‖δv‖² ≥ -(2 v₀ᵀ w - wᵀ M w + ‖r‖²) - 16 ‖δv‖²`.
Choosing `v(x) = ∑_{j,k} legP(d_j, x) Λ_{jk} m_k` (`∫₀¹ G(x) v(x) dx = mᵀ Λ m`), bounding `∫₀¹ r(ξ)² dξ ≤ (1/(N + 1)) ∑_{q=0}^N b_q²` in the Bernstein basis by Jensen's inequality, bounding `16 ∫ δv²` on `a - a₀` via `|legP'_n| ≤ n(n+1)/2`, and setting `w = 0` on the two slivers reduces positivity to the pure rational `K × K` matrix `Cert = 2 Λ - Q_{bern} - B_{mom} - diag(pert)`. Exact rational `L D Lᵀ + E` decomposition with strictly diagonally dominant `E` (`E_{ii} - ∑_{j≠i} |E_{ij}| ≥ 10⁻¹⁵ > 0`) proves `Cert ⪰ 0`, yielding `(1 / 10^10) ∫ F² ≤ weilQuad F` for odd `F` and `(1 / 10^13) ∫ F² ≤ weilQuad F` for even `F`.

### 5. Sharp upper bound and degree-14 Gamma lower-form negativity

Define `G_*(u) = (1 - u²)³ ∑_{k=0}^6 c_k legP(2k, u)` on `[-1, 1]` (`0` outside `[-1, 1]`) with explicit 6-digit rational coefficients `c_0, ..., c_6`, and `F_*(x) = G_*(x / log 2)`. Because `(1 - u²)³` vanishes to order 3 at `±1`, `F_* ∈ C²_c([-log 2, log 2])`. All moments, `regionalLogEnergy G_*`, the exterior integral `∫₀¹ u^{2m} V(u) du = (1/(2m + 1)) ∑_{k=0}^m 1/(2k + 1)`, and the polynomial `autocorr G_*(τ)` on `[0, 2]` evaluate in closed rational form.
1. Replacing `archLevySinhWeight t` on `(0, 2 log 2]` by `gammaSinhPolynomial14(t/2)/t + gammaCoshPolynomial14(t/2)/2` defines the degree-14 Gamma lower two-prime form `twoPrimeDegree14GammaForm F ≤ weilQuad F`; exact rational interval evaluation proves `twoPrimeDegree14GammaForm F_* < 0` (`≈ -9.12 × 10⁻⁸ ∫ F_*²`).
2. Extending `1 / cosh z` to `gammaCoshPolynomial26 z` bounds `archLevySinhWeight t` from above on `(0, 7/5]` within `4 / 10¹⁰`, proving `weilQuad F_* < (1 / 10^9) ∫ F_*²` (`< (3 / 10^8) ∫ F_*²`).

### 6. Continuum, window, and ratio-three ladder corollaries

1. **Continuum & ratio-four windows:** Orthogonal parity splitting (`WeilFloor.of_even_of_odd`), complexification (`zetaZeroConfig_re_W_ge_of_window`), and `WeilFloor.le_groundEnergy` yield `WeilFloor (log 2) (1 / 10^13)`, the complex floor, and `1 / 10^13 ≤ ccmRestrictedWeilGroundEnergy ⟨log 2, _⟩ < 1 / 10^9`. Since `log((R + J)/R) < log 4 = 2 log 2` iff `R + J < 4 R`, `groundEnergy_mul_le_packetForm_stepPacket`, `neutralWindow_floor_of_le_groundEnergy`, `hasGap_neutralWindow_of_le_groundEnergy`, `hermNegIndex_neutralWindow_eq_one_of_groundEnergy_nonneg`, `greenForm_add_excess_le_of_floor`, `hermNegIndex_neutralWindow_eq_dressedMiddle`, `groundEnergy_nonneg_iff_forall_weilSchur_nonneg`, and `exists_stepPacket_lt_of_groundEnergy_lt` establish all window, Green, Schur, and upper-bound corollaries for `R + J < 4 R` (`Q ≥ 3`, `R ≥ 1`).
2. **Ratio-three windows (`§2.4`) & excess ladder:** For `J ≤ 2 R` and `Q ≥ 2`, `neutralWindow Q R J = neutralWindow 3 R J` (`neutralWindow_eq_two_of_le_two_mul`) and `R + J ≤ 3 R < 4 R`, giving `neutralWindow` floor `1 / 10^13`, `HasGap (neutralWindow Q R J) (1 / 10^13)`, and (for `R ≤ J`) `hermNegIndex ((neutralWindow Q R J).map (↑)) = 1` unconditionally for all `Q ≥ 2`, `R ≥ 1`. Finally, `schurStepExcess_eq_zero_of_le_groundEnergy` at `A = log 2` proves `schurStepExcess Q ρ C = 0` whenever `ρ²/2 < 4`, `ρ²/2 < Q + 1`, and `-1 / 10^13 ≤ C < -neutralBlock 1 1 1`. Since `iteratedRatio 3 < 3 < iteratedRatio 4 < 4` and `towerCutoff k ≥ 4` (`k ≤ 2`), `towerCutoff 3 = 5`, this gives `levelAt 2 k = 0` (`k ≤ 3`), `levelAt Q k = 0` (`Q ≥ 3`, `k ≤ 4`), and `globalTowerLevel k = 0` (`k ≤ 3`).

## Log
- 2026-11-14 — created in 1-in-progress
- 2026-11-14 — complete dependency-closed paper proof recorded; promoted to 2-fully-proven

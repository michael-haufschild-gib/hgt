# The bilinear (`ε₁ε₂`) response of the semilocal Jacobi data to two cosine modes

**Stage:** 3 (formalized), 2026-09-04.  Closes MUST-171 (structure); the quantitative bound is
MUST-173.  Two new modules (`SemilocalTwoModeBilinearResponse`, `SemilocalTwoModeRadiusResponse`),
wired into `RHTower.lean`, axioms `[propext, Classical.choice, Quot.sound]`, lint clean.

**Setting.**  Multiply the archimedean Gamma measure `μ` by `(1 + 2ε₁ cos(δ₁ s))(1 + 2ε₂ cos(δ₂ s))`.
In the orthonormal archimedean Jacobi basis the Gram matrix is (`twoModeGram_eq`, product-to-sum)

    G(ε₁, ε₂) = 1 + ε₁ T(δ₁) + ε₂ T(δ₂) + ε₁ε₂ (T(δ₁+δ₂) + T(δ₁−δ₂)),   T(δ)_{ij} = 2∫ p_i p_j cos(δs) dμ.

**Theorem 1** (`RHTower.CosineModeResponse.deriv_deriv_log_twoModeDeterminant`).  With
`D_n(ε₁,ε₂) = det G` (indices `0..n`) and `J_δ(n) = tr T(δ) = 2Σ_{j≤n} m_j(δ)` the first-order jet,

    ∂₁∂₂ log D_n |₀ = J_{δ₁+δ₂}(n) + J_{δ₁−δ₂}(n) − tr(T(δ₁) T(δ₂))     (= `bilinearDeterminantJet`).

**Theorem 2** (`deriv_deriv_twoModeSquaredRadius`).  Through the Hankel quotient
`a_n² = r_n² Δ_{n−1}Δ_{n+1}/Δ_n²`,

    ∂₁∂₂ a_n² |₀ = r_n² (B_{n−1} + B_{n+1} − 2B_n) + [ε₁]a_n² · [ε₂]a_n² / r_n²,   B_m = bilinearDeterminantJet δ₁ δ₂ m,

with `[ε]a_n² = 2r_n²(m_{n+1}(δ) − m_n(δ))` the owned first-order jets.  Both are iterated
`deriv`s of genuine two-parameter Gram-determinant families, proved with the corpus's Jacobi
formula `hasDerivAt_matrixDet`, `detFirstJet_eq_det_mul_trace_inv_mul` and `hasDerivAt_matrix_inv`
(inner derivative `tr((1+ε₂T₂)⁻¹(T₁ + ε₂T₁₂))` on a neighbourhood, then its derivative at `0`).

**What it says about the two-prime cross term.**  Theorem 1 is the covariance of the two linear
statistics in the `(n+1)`-point archimedean Jacobi ensemble, `tr(K f₁ (1−K) f₂ K)`: the first-order
response to the *product* mode `f₁f₂ = 2cos((δ₁+δ₂)s) + 2cos((δ₁−δ₂)s)` is cancelled exactly by
the diagonal part of the second-order term, and what survives is the off-diagonal block pairing
of the two boost matrices `M(δ_a)_{ij} = ∫ p_i p_j e^{iδ_a s} dμ`.  Written as above, the
`ε₁ε₂` jet is: (beat-mode first-order jet) + (sum-mode first-order jet) − (truncation defect
`tr(T(δ₁)T(δ₂)) = 4Σ_{i,j≤n} Re M_{ij}(δ₁) Re M_{ij}(δ₂)`).

**Numerics** (`computations/routej-semilocal-scale/bilinear_response.py`, `.log`; `(p₁,p₂) = (211, 421)`,
`δ_a = log p_a`, `ε = (p₁p₂)^{-1/2}`):
- Theorem 1 against a symmetric finite-difference mixed derivative of `log det`: agreement `10⁻⁶`.
- At the log-determinant level the defect is **not** small: 9 % of the beat term at `n = 10`,
  17 % at `n = 20`, 92 % at `n = 150` (it grows like `εn`, `|M_{00}(δ)| = (cosh δ)^{-1/2}` is
  attained); the sum-mode term is `7·10⁻³`.
- At the radius level the defect is smooth in `n`, so its second difference is `O(ε)`:
  `∂₁∂₂ log a_n²` agrees with the beat-mode radius jet `2(m_{n+1}(δ₁−δ₂) − m_n(δ₁−δ₂))` to 1–3 %
  for `n ≤ 150`; the discrepancy tracks `ΔΔ tr(T₁T₂)` (`2–6·10⁻³`), the product of first-order jets
  is `≤ 10⁻³`.  This is the mechanism behind report §3.5 ("the cross-prime term is the linear
  response to the beat mode"): true at the radius level, false at the determinant level.

**Status of the bound.**  The obvious sharp estimate `|M_{ij}(t)| ≤ (cosh t)^{-1/2} c_i c_j` is
false (at `t → 0` the entries are `δ_{ij}`), and the naive coefficient majorant of the generating
function `(1 − wz − i tanh t (w+z))^{-1/2}` is exponential; the correct statement is a
large-rapidity estimate (`tanh t = 1` factorizes the kernel as `(1−iw)^{-1/2}(1−iz)^{-1/2}`, the
correction is a series in `1 − tanh t ≈ 2e^{−2t}`), valid for `i + j ≪ e^{t}`.  Proving it, and
hence `|ΔΔ tr(T(δ₁)T(δ₂))| ≤ C (cosh δ₁ cosh δ₂)^{-1/2}·(explicit in n)`, is MUST-173.

| module | content |
|---|---|
| `SemilocalTwoModeBilinearResponse` | `twoModeGram`, `twoModeMatrix`, `twoModeGram_eq`; `twoModeDeterminant`; `bilinearDeterminantJet`; entrywise derivatives, `hasDerivAt_det_twoModeMatrix`, `deriv_log_det_twoModeMatrix`, `hasDerivAt_inv_one_add_smul`, `hasDerivAt_traceInvMul`; **`deriv_deriv_log_twoModeDeterminant`** |
| `SemilocalTwoModeRadiusResponse` | `bilinearTraceFunction` and its derivative/value at `0`, the formal predecessor (`twoModePrevDeterminant`, `prevTraceFunction`), `twoModeSquaredRadius`, `innerRadiusSlope`, `deriv_twoModeSquaredRadius_left`, `bilinearSquaredRadiusJet`; **`deriv_deriv_twoModeSquaredRadius`** |

**Literature.**  The covariance identity `Cov(Σf₁, Σf₂) = tr(Kf₁(1−K)f₂K)` for orthogonal-polynomial
ensembles is classical (Diaconis–Shahshahani, Johansson); its instance for the Connes–Consani–Moscovici
semilocal measure, the identification of the two-prime cross term with the beat-mode response *plus
an explicit truncation defect*, and the formal proof through two-parameter Gram determinants are new.

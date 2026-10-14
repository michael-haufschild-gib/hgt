import GaloisForLFunctions.RHTower.ModularArcDyadicBilinearProductLaplacianSectorWronskian

/-!
# Division-free Liouville–Gauss logarithmic harmonicity of complex Mellin moduli, full-strip partial derivatives and Jacobian determinant of the sector modulus imbalance and origin–infinity sector Wronskian, and critical-line zero-locus anti-conformality

In `ModularArcDyadicHarmonicLaplacianSubharmonicModulus`,
`ModularArcDyadicOriginInfinitySectorHolomorphy`, and
`ModularArcDyadicBilinearProductLaplacianSectorWronskian`, we established the five-point
subharmonicity of the full-line complex Mellin modulus squared
`|F_k(l, τ)|² = M_k(l, τ)² + N_k(l, τ)²`, the origin–infinity imbalance modulus squared
`|Δ_k(l, τ)|² = Δ_k^{\cos}(l, τ)² + Δ_k^{\sin}(l, τ)²`, and the one-sided sector moduli squared
`|F_k^+(l, τ)|²` and `|F_k^-(l, τ)|²`, together with the sector modulus imbalance
`H_k(l, τ) = |F_k^+(l, τ)|² − |F_k^-(l, τ)|² = M_k(l, τ) Δ_k^{\cos}(l, τ) + N_k(l, τ) Δ_k^{\sin}(l, τ)`
and the origin–infinity sector Wronskian
`W_k(l, τ) = M_k(l, τ) Δ_k^{\sin}(l, τ) − N_k(l, τ) Δ_k^{\cos}(l, τ) = −2 (C_k^+(l, τ) S_k^-(l, τ) − C_k^-(l, τ) S_k^+(l, τ))`.

In this module we develop the **division-free Liouville–Gauss logarithmic harmonicity calculus**
and the **full-strip Jacobian and critical-line anti-conformal geometry** of `(H_k, W_k)`:

1. **Section 1 — Universal first-order partial derivatives of squared moduli, self-Wronskian
   phase-velocity calculus, and the division-free Liouville–Gauss logarithmic harmonicity theorem:**
   - Universal punctured-neighborhood chain rules for squares and 2D squared moduli
     (`tendsto_div_sq_sub_nhdsWithin_zero`, `tendsto_div_modulusSq_sub_nhdsWithin_zero`).
   - Universal polynomial Liouville–Gauss identity (`liouville_gauss_modulusSq_identity`):
     `(U₀² + V₀²) · (4 (D_l_U² + D_l_V²)) − ((2 (U₀ D_l_U + V₀ D_l_V))² + (−2 (U₀ D_l_V − V₀ D_l_U))²) = 0`.
   - Universal division-free Liouville–Gauss logarithmic harmonicity limit theorem
     (`tendsto_liouville_gauss_modulusSq_nhdsWithin_zero`): for any Cauchy–Riemann pair `(U, V)`
     with five-point subharmonic modulus squared `U² + V²`,
     `(U₀² + V₀²) · ((Δ_l² (U² + V²) + Δ_τ² (U² + V²)) / h²) − (((Δ_l (U² + V²)) / h)² + ((Δ_τ (U² + V²)) / h)²) → 0`
     globally without any non-vanishing hypothesis `U₀² + V₀² ≠ 0`.
   - Universal conjugate-gradient sum-of-squares and Jacobian determinant identities for
     `H = u x + v y` and `W = u y − v x` under Cauchy–Riemann
     (`hermitian_wronskian_gradient_sum_sq_eq`, `hermitian_wronskian_jacobian_det_eq`).

2. **Section 2 — Off-line radial-logarithmic and phase-velocity partial derivatives and
   division-free Liouville–Gauss logarithmic harmonicity for `|F_k(l, τ)|²` and `|Δ_k(l, τ)|²`:**
   - Full-strip (`|l| < 1/8`, `τ ∈ ℝ`) horizontal and vertical partial derivatives of
     `|F_k(l, τ)|² = M_k(l, τ)² + N_k(l, τ)²` and `|Δ_k(l, τ)|² = Δ_k^{\cos}(l, τ)² + Δ_k^{\sin}(l, τ)²`,
     identifying `∂_l (|F_k|²) = 2 (M_k ∂_l M_k + N_k ∂_l N_k) = 2 (M_k ∂_τ N_k − N_k ∂_τ M_k)`
     (twice the vertical phase-velocity self-Wronskian) and
     `∂_τ (|F_k|²) = 2 (M_k ∂_τ M_k + N_k ∂_τ N_k) = −2 (M_k ∂_l N_k − N_k ∂_l M_k)`
     (minus twice the horizontal phase-velocity self-Wronskian).
   - Global division-free Liouville–Gauss logarithmic harmonicity for both `|F_k(l, τ)|²` and
     `|Δ_k(l, τ)|²` across `|l| < 1/8`, `τ ∈ ℝ` (`tendsto_complexModulusSq_liouville_gauss_nhds_zero`,
     `tendsto_imbalanceModulusSq_liouville_gauss_nhds_zero`).

3. **Section 3 — Full-strip partial derivatives, conjugate gradient decomposition, and exact
   Jacobian determinant of the sector modulus imbalance `H_k` and sector Wronskian `W_k`:**
   - Full-strip (`|l| < 1/8`, `τ ∈ ℝ`) horizontal and vertical partial derivatives of
     `H_k = |F_k^+|² − |F_k^-|²` and `W_k = M_k Δ_k^{\sin} − N_k Δ_k^{\cos}`.
   - Exact finite-difference Jacobian determinant limit across `|l| < 1/8`, `τ ∈ ℝ`:
     `∂_l H_k · ∂_τ W_k − ∂_τ H_k · ∂_l W_k = |F_k(l, τ)|² · |Δ_k'(l, τ)|² − |Δ_k(l, τ)|² · |F_k'(l, τ)|²`
     (`tendsto_hermitian_wronskian_jacobian_det_nhds_zero`), and its non-positivity `≤ 0` at every
     zero `M_k(l, τ)² + N_k(l, τ)² = 0` in `|l| < 1/8`
     (`tendsto_sectorModulusSq_sub_wronskian_jacobian_det_at_zero_locus`).

4. **Section 4 — Critical-line reduction, even/odd symmetry, and critical-line zero-locus
   anti-conformality of the origin–infinity sector Wronskian `W_k`:**
   - Even horizontal symmetry `W_k(−l, τ) = W_k(l, τ)` and odd vertical antisymmetry
     `W_k(l, −τ) = −W_k(l, τ)`, critical-line factorization
     `W_k(0, τ) = M_k(0, τ) · (2 ∫_{v > 0} sin(τv) Φ_k(v) dv)`, and vanishing `W_k(0, τ₀) = 0` at
     every critical-line zero `M_k(0, τ₀) = 0`.
   - Critical-line horizontal stationarity `∂_l W_k(0, τ) = 0`, vertical derivative `∂_τ W_k(0, τ)`,
     and exact anti-conformal duality `∂_τ W_k(0, τ₀) = −∂_l H_k(0, τ₀)` at every critical-line zero
     `M_k(0, τ₀) = 0` (`exists_dyadic_logarithmicSubharmonicity_wronskianJacobian_arcWitness`).
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ## Section 1: Universal First-Order Partial Derivatives of Squared Moduli, Self-Wronskian Phase-Velocity Calculus, and the Division-Free Liouville–Gauss Logarithmic Harmonicity Theorem -/

/-- **Universal punctured-neighborhood chain rule for squares:**
If `(U h − U₀) / h → D_U` as `h → 0` (`h ≠ 0`), then
`(U h ^ 2 − U₀ ^ 2) / h → 2 * U₀ * D_U`. -/
theorem tendsto_div_sq_sub_nhdsWithin_zero
    {U : ℝ → ℝ} {U₀ D_U : ℝ}
    (hU : Tendsto (fun h : ℝ => (U h - U₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_U)) :
    Tendsto (fun h : ℝ => (U h ^ 2 - U₀ ^ 2) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * U₀ * D_U)) := by
  have hprod := tendsto_div_mul_sub_nhdsWithin_zero hU hU
  have hlim : U₀ * D_U + U₀ * D_U = 2 * U₀ * D_U := by ring
  rw [hlim] at hprod
  refine hprod.congr (fun h => ?_)
  ring

/-- **Universal first-order directional derivative of a 2D modulus squared:**
If `(U h − U₀) / h → D_U` and `(V h − V₀) / h → D_V` as `h → 0` (`h ≠ 0`), then
`((U h ^ 2 + V h ^ 2) − (U₀ ^ 2 + V₀ ^ 2)) / h → 2 * (U₀ * D_U + V₀ * D_V)`. -/
theorem tendsto_div_modulusSq_sub_nhdsWithin_zero
    {U V : ℝ → ℝ} {U₀ V₀ D_U D_V : ℝ}
    (hU : Tendsto (fun h : ℝ => (U h - U₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_U))
    (hV : Tendsto (fun h : ℝ => (V h - V₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_V)) :
    Tendsto (fun h : ℝ => ((U h ^ 2 + V h ^ 2) - (U₀ ^ 2 + V₀ ^ 2)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * (U₀ * D_U + V₀ * D_V))) := by
  have hcomb := (tendsto_div_sq_sub_nhdsWithin_zero hU).add (tendsto_div_sq_sub_nhdsWithin_zero hV)
  have hlim : 2 * U₀ * D_U + 2 * V₀ * D_V = 2 * (U₀ * D_U + V₀ * D_V) := by ring
  rw [hlim] at hcomb
  refine hcomb.congr (fun h => ?_)
  ring

/-- **Universal polynomial Liouville–Gauss logarithmic harmonicity identity:**
For any `U₀, V₀, D_l_U, D_l_V : ℝ`,
`(U₀ ^ 2 + V₀ ^ 2) * (4 * (D_l_U ^ 2 + D_l_V ^ 2)) −
  ((2 * (U₀ * D_l_U + V₀ * D_l_V)) ^ 2 + (2 * (U₀ * (-D_l_V) + V₀ * D_l_U)) ^ 2) = 0`. -/
theorem liouville_gauss_modulusSq_identity (U₀ V₀ D_l_U D_l_V : ℝ) :
    (U₀ ^ 2 + V₀ ^ 2) * (4 * (D_l_U ^ 2 + D_l_V ^ 2)) -
      ((2 * (U₀ * D_l_U + V₀ * D_l_V)) ^ 2 +
        (2 * (U₀ * (-D_l_V) + V₀ * D_l_U)) ^ 2) = 0 := by
  ring

/-- **Universal division-free Liouville–Gauss logarithmic harmonicity limit theorem:**
If `(U_l, V_l)` and `(U_t, V_t)` are the horizontal and vertical shifts of a Cauchy–Riemann pair
around `(U₀, V₀)` (`D_t_U = −D_l_V`, `D_t_V = D_l_U`) and the five-point Laplacian of `U² + V²`
converges to `4 (D_l_U² + D_l_V²)`, then
`(U₀² + V₀²) · Δ_5(U² + V²)(h) − ((∂_l^h(U² + V²))² + (∂_τ^h(U² + V²))²) → 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_liouville_gauss_modulusSq_nhdsWithin_zero
    {U_l U_t V_l V_t L_mod : ℝ → ℝ} {U₀ V₀ D_l_U D_l_V : ℝ}
    (hUl : Tendsto (fun h : ℝ => (U_l h - U₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_l_U))
    (hUt : Tendsto (fun h : ℝ => (U_t h - U₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (-D_l_V)))
    (hVl : Tendsto (fun h : ℝ => (V_l h - V₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_l_V))
    (hVt : Tendsto (fun h : ℝ => (V_t h - V₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_l_U))
    (hLap : Tendsto L_mod (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * (D_l_U ^ 2 + D_l_V ^ 2)))) :
    Tendsto
      (fun h : ℝ =>
        (U₀ ^ 2 + V₀ ^ 2) * L_mod h -
          ((((U_l h ^ 2 + V_l h ^ 2) - (U₀ ^ 2 + V₀ ^ 2)) / h) ^ 2 +
            (((U_t h ^ 2 + V_t h ^ 2) - (U₀ ^ 2 + V₀ ^ 2)) / h) ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have hdl := tendsto_div_modulusSq_sub_nhdsWithin_zero hUl hVl
  have hdt := tendsto_div_modulusSq_sub_nhdsWithin_zero hUt hVt
  have hcomb :=
    (hLap.const_mul (U₀ ^ 2 + V₀ ^ 2)).sub ((hdl.pow 2).add (hdt.pow 2))
  rw [liouville_gauss_modulusSq_identity U₀ V₀ D_l_U D_l_V] at hcomb
  exact hcomb

/-- **Universal conjugate-gradient sum-of-squares identity for the Hermitian/Wronskian pair
`(H, W) = (u x + v y, u y − v x)` under Cauchy–Riemann (`u_t = −v_l`, `v_t = u_l`,
`x_t = −y_l`, `y_t = x_l`):**
`(H_l² + H_t²) + (W_l² + W_t²) = 2 ((u² + v²)(x_l² + y_l²) + (x² + y²)(u_l² + v_l²))`. -/
theorem hermitian_wronskian_gradient_sum_sq_eq (u v x y u_l v_l x_l y_l : ℝ) :
    ((u_l * x + u * x_l + v_l * y + v * y_l) ^ 2 +
        ((-v_l) * x + u * (-y_l) + u_l * y + v * x_l) ^ 2) +
      ((u_l * y + u * y_l - (v_l * x + v * x_l)) ^ 2 +
        ((-v_l) * y + u * x_l - (u_l * x + v * (-y_l))) ^ 2) =
    2 * ((u ^ 2 + v ^ 2) * (x_l ^ 2 + y_l ^ 2) +
      (x ^ 2 + y ^ 2) * (u_l ^ 2 + v_l ^ 2)) := by
  ring

/-- **Universal Jacobian determinant identity for the Hermitian/Wronskian pair
`(H, W) = (u x + v y, u y − v x)` under Cauchy–Riemann (`u_t = −v_l`, `v_t = u_l`,
`x_t = −y_l`, `y_t = x_l`):**
`H_l * W_t − H_t * W_l = (u² + v²)(x_l² + y_l²) − (x² + y²)(u_l² + v_l²)`. -/
theorem hermitian_wronskian_jacobian_det_eq (u v x y u_l v_l x_l y_l : ℝ) :
    (u_l * x + u * x_l + v_l * y + v * y_l) *
        ((-v_l) * y + u * x_l - (u_l * x + v * (-y_l))) -
      ((-v_l) * x + u * (-y_l) + u_l * y + v * x_l) *
        (u_l * y + u * y_l - (v_l * x + v * x_l)) =
    (u ^ 2 + v ^ 2) * (x_l ^ 2 + y_l ^ 2) -
      (x ^ 2 + y ^ 2) * (u_l ^ 2 + v_l ^ 2) := by
  ring


/-! ## Section 2: Off-Line Radial-Logarithmic and Phase-Velocity Partial Derivatives and Division-Free Liouville–Gauss Logarithmic Harmonicity for `|F_k(l, τ)|²` and `|Δ_k(l, τ)|²` -/

/-- **Full-strip horizontal partial derivative `∂_l (|F_k(l, τ)|²)` of the complex Mellin modulus
squared across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((M_k(l + h, τ)² + N_k(l + h, τ)²) − (M_k(l, τ)² + N_k(l, τ)²)) / h →
  2 (M_k(l, τ) ∂_l M_k(l, τ) + N_k(l, τ) ∂_l N_k(l, τ))`
as `h → 0` (`h ≠ 0`), which by Cauchy–Riemann (`∂_l M_k = ∂_τ N_k`, `∂_l N_k = −∂_τ M_k`) equals
twice the vertical phase-velocity self-Wronskian `2 (M_k ∂_τ N_k − N_k ∂_τ M_k)`. -/
theorem tendsto_div_complexModulusSq_horiz_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (0 : ℝ),
              x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (0 : ℝ),
              x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
          ((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (2 * ((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
            (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) :=
  tendsto_div_modulusSq_sub_nhdsWithin_zero
    (tendsto_div_oscillatoryMellin_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sineMellin_horiz_shift_nhds_zero hk hν hl τ)

/-- **Full-strip vertical partial derivative `∂_τ (|F_k(l, τ)|²)` of the complex Mellin modulus
squared across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((M_k(l, τ + h)² + N_k(l, τ + h)²) − (M_k(l, τ)² + N_k(l, τ)²)) / h →
  2 (M_k(l, τ) ∂_τ M_k(l, τ) + N_k(l, τ) ∂_τ N_k(l, τ))`
as `h → 0` (`h ≠ 0`), which by Cauchy–Riemann equals minus twice the horizontal phase-velocity
self-Wronskian `−2 (M_k ∂_l N_k − N_k ∂_l M_k)`. -/
theorem tendsto_div_complexModulusSq_vert_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
          ((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (2 * ((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (-(∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
            (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) :=
  tendsto_div_modulusSq_sub_nhdsWithin_zero
    (tendsto_div_oscillatoryMellin_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sineMellin_vert_shift_nhds_zero hk hν hl τ)

/-- **Critical-line (`l = 0`) vertical derivative of the complex Mellin modulus squared
(`k ≥ 2`, `τ ∈ ℝ`):**
`((M_k(0, τ + h)² + N_k(0, τ + h)²) − M_k(0, τ)²) / h →
  −2 M_k(0, τ) ∫_ℝ v sin(τv) Φ_k(v) dv` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_complexModulusSq_vert_shift_at_criticalLine_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (0 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (0 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (∫ x in Ioi (0 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (-2 * (∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          (∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) := by
  have hk1 : 1 ≤ k := by omega
  have h := tendsto_div_complexModulusSq_vert_shift_nhds_zero
    hk hν (by norm_num : |(0 : ℝ)| < 1 / 8) τ
  have hl0 : (0 : ℝ) - 1 / 2 = -(1 / 2 : ℝ) := by ring
  have hN0 := setIntegral_Ioi_rpow_neg_half_mul_sin_log_eq_zero hk1 ν τ
  have hcosh0 :
      (∫ v : ℝ, v * Real.cosh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
        ∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    dsimp only; rw [zero_mul, Real.cosh_zero, mul_one]
  have hlim :
      2 * ((∫ x in Ioi (0 : ℝ),
              x ^ ((0 : ℝ) - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (-(∫ v : ℝ, v * Real.cosh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
          (∫ x in Ioi (0 : ℝ),
              x ^ ((0 : ℝ) - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v : ℝ, v * Real.sinh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) =
      -2 * (∫ x in Ioi (0 : ℝ),
          x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
        (∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
    rw [hl0, hN0, hcosh0]
    ring
  rw [hlim] at h
  refine h.congr (fun h' => ?_)
  rw [hl0, hN0]
  ring

/-- **Global Division-Free Liouville–Gauss Logarithmic Harmonicity for the Complex Mellin Modulus
Squared `|F_k(l, τ)|² = M_k(l, τ)² + N_k(l, τ)²` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
At every point `(l, τ)` in `|l| < 1/8, τ ∈ ℝ` (including zeros where `|F_k(l, τ)|² = 0`),
`|F_k(l, τ)|² · ((Δ_l² |F_k|² + Δ_τ² |F_k|²) / h²) −
  (((|F_k(l + h, τ)|² − |F_k(l, τ)|²) / h)² + ((|F_k(l, τ + h)|² − |F_k(l, τ)|²) / h)²) → 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_complexModulusSq_liouville_gauss_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
          (((((∫ x in Ioi (0 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                ((∫ x in Ioi (0 : ℝ),
                    x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                2 * ((∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
              (((∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                ((∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                2 * ((∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h ^ 2) -
          (((((∫ x in Ioi (0 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                ((∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h) ^ 2 +
            ((((∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                ((∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h) ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) :=
  tendsto_liouville_gauss_modulusSq_nhdsWithin_zero
    (tendsto_div_oscillatoryMellin_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_oscillatoryMellin_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sineMellin_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sineMellin_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sq_complexModulusSq_fivePoint_laplacian_nhds_zero hk hν hl τ)

/-- **Full-strip horizontal partial derivative `∂_l (|Δ_k(l, τ)|²)` of the origin–infinity
imbalance modulus squared across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((Δ_k^{\cos}(l + h, τ)² + Δ_k^{\sin}(l + h, τ)²) − (Δ_k^{\cos}(l, τ)² + Δ_k^{\sin}(l, τ)²)) / h →
  2 (Δ_k^{\cos}(l, τ) ∂_l Δ_k^{\cos}(l, τ) + Δ_k^{\sin}(l, τ) ∂_l Δ_k^{\sin}(l, τ))`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_imbalanceModulusSq_horiz_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (1 : ℝ),
                x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            ((∫ x in Ioi (1 : ℝ),
                x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (2 * (((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
            ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) :=
  tendsto_div_modulusSq_sub_nhdsWithin_zero
    (tendsto_div_imbalanceCos_sub_left_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceSin_sub_left_nhds_zero hk hν hl τ)

/-- **Full-strip vertical partial derivative `∂_τ (|Δ_k(l, τ)|²)` of the origin–infinity
imbalance modulus squared across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((Δ_k^{\cos}(l, τ + h)² + Δ_k^{\sin}(l, τ + h)²) − (Δ_k^{\cos}(l, τ)² + Δ_k^{\sin}(l, τ)²)) / h →
  2 (Δ_k^{\cos}(l, τ) ∂_τ Δ_k^{\cos}(l, τ) + Δ_k^{\sin}(l, τ) ∂_τ Δ_k^{\sin}(l, τ))`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_imbalanceModulusSq_vert_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (2 * (((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (-(∫ v in Ioi (0 : ℝ),
                2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
            ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) :=
  tendsto_div_modulusSq_sub_nhdsWithin_zero
    (tendsto_div_imbalanceCos_sub_right_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceSin_sub_right_nhds_zero hk hν hl τ)

/-- **Global Division-Free Liouville–Gauss Logarithmic Harmonicity for the Origin–Infinity
Imbalance Modulus Squared `|Δ_k(l, τ)|² = Δ_k^{\cos}(l, τ)² + Δ_k^{\sin}(l, τ)²` across
`|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
At every point `(l, τ)` in `|l| < 1/8, τ ∈ ℝ`,
`|Δ_k(l, τ)|² · ((Δ_l² |Δ_k|² + Δ_τ² |Δ_k|²) / h²) −
  (((|Δ_k(l + h, τ)|² − |Δ_k(l, τ)|²) / h)² + ((|Δ_k(l, τ + h)|² − |Δ_k(l, τ)|²) / h)²) → 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_imbalanceModulusSq_liouville_gauss_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
          ((((((∫ x in Ioi (1 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                (((∫ x in Ioi (1 : ℝ),
                      x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                2 * (((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
              ((((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                (((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                2 * (((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h ^ 2) -
          ((((((∫ x in Ioi (1 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                (((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h) ^ 2 +
            (((((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                (((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h) ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) :=
  tendsto_liouville_gauss_modulusSq_nhdsWithin_zero
    (tendsto_div_imbalanceCos_sub_left_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceCos_sub_right_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceSin_sub_left_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceSin_sub_right_nhds_zero hk hν hl τ)
    (tendsto_div_sq_imbalanceModulusSq_fivePoint_laplacian_nhds_zero hk hν hl τ)


/-! ## Section 3: Full-Strip Partial Derivatives, Conjugate Gradient Decomposition, and Exact Jacobian Determinant of the Sector Modulus Imbalance `H_k` and Sector Wronskian `W_k` -/

/-- **Full-strip horizontal partial derivative `∂_l H_k(l, τ)` of the Hermitian pairing
`H_k = M_k Δ_k^{\cos} + N_k Δ_k^{\sin}` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((H_k(l + h, τ) − H_k(l, τ)) / h) →
  M_k ∂_l Δ_k^{\cos} + Δ_k^{\cos} ∂_l M_k + N_k ∂_l Δ_k^{\sin} + Δ_k^{\sin} ∂_l N_k`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_hermitianPairing_horiz_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (0 : ℝ),
                x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (0 : ℝ),
                x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
          ((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
        ((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) := by
  have h1 := tendsto_div_mul_sub_nhdsWithin_zero
    (tendsto_div_oscillatoryMellin_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceCos_sub_left_nhds_zero hk hν hl τ)
  have h2 := tendsto_div_mul_sub_nhdsWithin_zero
    (tendsto_div_sineMellin_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceSin_sub_left_nhds_zero hk hν hl τ)
  exact (h1.add h2).congr (fun h => by ring)

/-- **Full-strip horizontal partial derivative `∂_l (|F_k^+(l, τ)|² − |F_k^-(l, τ)|²)` of the
sector modulus imbalance across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`).** -/
theorem tendsto_div_sectorModulusSq_sub_horiz_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((((∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
              ((∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) -
          (((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
              ((∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
        ((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) := by
  refine (tendsto_div_hermitianPairing_horiz_shift_nhds_zero hk hν hl τ).congr' ?_
  have hmem : Ioo (-(1 / 8 : ℝ)) (1 / 8 : ℝ) ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [hmem] with h hh_mem
  have hh_eighth : |h| < 1 / 8 := abs_lt.mpr hh_mem
  have hl_half : |l| < 1 / 2 := by linarith
  have hlh_pos : |l + h| < 1 / 2 := by
    have := abs_add_le l h
    linarith
  rw [← sectorModulusSq_sub_eq_oscillatoryMellin_mul_imbalance hk hν hlh_pos τ,
    ← sectorModulusSq_sub_eq_oscillatoryMellin_mul_imbalance hk hν hl_half τ]

/-- **Full-strip vertical partial derivative `∂_τ H_k(l, τ)` of the Hermitian pairing
`H_k = M_k Δ_k^{\cos} + N_k Δ_k^{\sin}` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((H_k(l, τ + h) − H_k(l, τ)) / h) →
  M_k (−∂_l Δ_k^{\sin}) + Δ_k^{\cos} (−∂_l N_k) + N_k ∂_l Δ_k^{\cos} + Δ_k^{\sin} ∂_l M_k`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_hermitianPairing_vert_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
          ((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (-(∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
          ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (-(∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) +
        ((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) := by
  have h1 := tendsto_div_mul_sub_nhdsWithin_zero
    (tendsto_div_oscillatoryMellin_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceCos_sub_right_nhds_zero hk hν hl τ)
  have h2 := tendsto_div_mul_sub_nhdsWithin_zero
    (tendsto_div_sineMellin_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceSin_sub_right_nhds_zero hk hν hl τ)
  exact (h1.add h2).congr (fun h => by ring)

/-- **Full-strip horizontal partial derivative `∂_l W_k(l, τ)` of the origin–infinity sector
Wronskian `W_k = M_k Δ_k^{\sin} − N_k Δ_k^{\cos}` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`).** -/
theorem tendsto_div_sectorWronskian_horiz_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (0 : ℝ),
                x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            (∫ x in Ioi (0 : ℝ),
                x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
          ((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) -
        ((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) := by
  have h1 := tendsto_div_mul_sub_nhdsWithin_zero
    (tendsto_div_oscillatoryMellin_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceSin_sub_left_nhds_zero hk hν hl τ)
  have h2 := tendsto_div_mul_sub_nhdsWithin_zero
    (tendsto_div_sineMellin_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceCos_sub_left_nhds_zero hk hν hl τ)
  exact (h1.sub h2).congr (fun h => by ring)

/-- **Full-strip vertical partial derivative `∂_τ W_k(l, τ)` of the origin–infinity sector
Wronskian `W_k = M_k Δ_k^{\sin} − N_k Δ_k^{\cos}` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`).** -/
theorem tendsto_div_sectorWronskian_vert_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
          ((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (-(∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) -
        ((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (-(∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
          ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) := by
  have h1 := tendsto_div_mul_sub_nhdsWithin_zero
    (tendsto_div_oscillatoryMellin_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceSin_sub_right_nhds_zero hk hν hl τ)
  have h2 := tendsto_div_mul_sub_nhdsWithin_zero
    (tendsto_div_sineMellin_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceCos_sub_right_nhds_zero hk hν hl τ)
  exact (h1.sub h2).congr (fun h => by ring)

/-- **Exact Finite-Difference Jacobian Determinant Limit for `(H_k, W_k)` across
`|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((H_k(l + h, τ) − H_k(l, τ)) / h) · ((W_k(l, τ + h) − W_k(l, τ)) / h) −
  ((H_k(l, τ + h) − H_k(l, τ)) / h) · ((W_k(l + h, τ) − W_k(l, τ)) / h) →
  (M_k(l, τ)² + N_k(l, τ)²) · ((∂_l Δ_k^{\cos}(l, τ))² + (∂_l Δ_k^{\sin}(l, τ))²) −
  (Δ_k^{\cos}(l, τ)² + Δ_k^{\sin}(l, τ)²) · ((∂_l M_k(l, τ))² + (∂_l N_k(l, τ))²)`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_hermitian_wronskian_jacobian_det_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((((∫ x in Ioi (0 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) *
          ((((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)) -
        (((((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) *
          ((((∫ x in Ioi (0 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
          ((∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2) -
        (((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
          ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
            (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2))) := by
  have hHl := tendsto_div_hermitianPairing_horiz_shift_nhds_zero hk hν hl τ
  have hHt := tendsto_div_hermitianPairing_vert_shift_nhds_zero hk hν hl τ
  have hWl := tendsto_div_sectorWronskian_horiz_shift_nhds_zero hk hν hl τ
  have hWt := tendsto_div_sectorWronskian_vert_shift_nhds_zero hk hν hl τ
  have hcomb := (hHl.mul hWt).sub (hHt.mul hWl)
  have hlim :
      (((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
        ((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) *
      ((((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (-(∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) -
        ((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (-(∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
          ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) -
      ((((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (-(∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
          ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (-(∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) +
        ((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))) *
      ((((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) -
        ((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))))) =
      (((∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
          (∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
        ((∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2) -
      (((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
        ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
          (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2)) := by
    ring
  rw [hlim] at hcomb
  exact hcomb

/-- **Zero-Locus Anti-Conformal Jacobian Non-Positivity (`k ≥ 2`, `|l| < 1/8`, `τ ∈ ℝ`):**
At any point `(l, τ)` in `|l| < 1/8, τ ∈ ℝ` where `M_k(l, τ)² + N_k(l, τ)² = 0`, the Jacobian
determinant of `(H_k, W_k)` converges to the non-positive quantity
`−(|Δ_k(l, τ)|² · ((∂_l M_k(l, τ))² + (∂_l N_k(l, τ))²)) ≤ 0`. -/
theorem tendsto_hermitian_wronskian_jacobian_det_at_zero_locus
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) {τ : ℝ}
    (hzero :
      (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 = 0) :
    Tendsto
      (fun h : ℝ =>
        (((((∫ x in Ioi (0 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) *
          ((((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)) -
        (((((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) *
          ((((∫ x in Ioi (0 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
            ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (-((((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
          ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
            (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2)))) := by
  have h := tendsto_hermitian_wronskian_jacobian_det_nhds_zero hk hν hl τ
  rw [hzero, zero_mul, zero_sub] at h
  exact h


/-! ## Section 4: Critical-Line Reduction, Even/Odd Symmetry, and Critical-Line Zero-Locus Anti-Conformality of the Origin–Infinity Sector Wronskian `W_k` -/

/-- **Even reflection symmetry `l ↦ −l` of the origin–infinity sector Wronskian
`W_k(l, τ) = M_k(l, τ) Δ_k^{\sin}(l, τ) − N_k(l, τ) Δ_k^{\cos}(l, τ)` (`k ≥ 1`, `l, τ ∈ ℝ`).** -/
theorem sectorWronskian_neg_left
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (-l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
      ((∫ x in Ioi (1 : ℝ),
          x ^ (-l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (-l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
    (∫ x in Ioi (0 : ℝ),
        x ^ (-l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
      ((∫ x in Ioi (1 : ℝ),
          x ^ (-l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (-l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
    (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
      ((∫ x in Ioi (1 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
    (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
      ((∫ x in Ioi (1 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) := by
  rw [setIntegral_Ioi_rpow_neg_sub_half_mul_cos_log_mul_arcLineInfiniteDyadicVector hk ν l τ,
    setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_neg_mul_sin_log hk ν l τ,
    setIntegral_Ioi_rpow_neg_mul_sin_log_eq_neg hk ν l τ,
    setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_neg_mul_cos_log hk ν l τ]
  ring

/-- **Odd vertical frequency antisymmetry `τ ↦ −τ` of the origin–infinity sector Wronskian
`W_k(l, τ)` (`k ≥ 1`, `l, τ ∈ ℝ`).** -/
theorem sectorWronskian_neg_right
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos ((-τ) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
      ((∫ x in Ioi (1 : ℝ),
          x ^ (l - 1 / 2) * Real.sin ((-τ) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (l - 1 / 2) * Real.sin ((-τ) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
    (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin ((-τ) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
      ((∫ x in Ioi (1 : ℝ),
          x ^ (l - 1 / 2) * Real.cos ((-τ) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (l - 1 / 2) * Real.cos ((-τ) * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
    -((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) := by
  have hcos :
      (fun x : ℝ =>
        x ^ (l - 1 / 2) * Real.cos ((-τ) * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      fun x : ℝ =>
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x := by
    funext x
    rw [neg_mul, Real.cos_neg]
  rw [setIntegral_Ioi_rpow_mul_cos_neg_log_mul_arcLineInfiniteDyadicVector hk ν l τ,
    setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_sin_neg_log k ν l τ,
    setIntegral_Ioi_rpow_mul_sin_neg_log_eq_neg k ν l τ,
    hcos]
  ring

/-- **Critical-Line Factorization of the Origin–Infinity Sector Wronskian (`l = 0`, `k ≥ 1`, `τ ∈ ℝ`):**
On the critical line `l = 0`,
`W_k(0, τ) = M_k(0, τ) · (2 ∫_{v > 0} sin(τv) Φ_k(v) dv)`. -/
theorem sectorWronskian_at_criticalLine_eq
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (τ : ℝ) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
      ((∫ x in Ioi (1 : ℝ),
          x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
    (∫ x in Ioi (0 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
      ((∫ x in Ioi (1 : ℝ),
          x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
    (∫ x in Ioi (0 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
      (2 * ∫ v in Ioi (0 : ℝ), Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
  have hl0 : (0 : ℝ) - 1 / 2 = -(1 / 2 : ℝ) := by ring
  have hΔs0 := setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_zero_mul_sin_log hk ν τ
  rw [hl0] at hΔs0
  rw [setIntegral_Ioi_rpow_neg_half_mul_sin_log_eq_zero hk ν τ, hΔs0]
  ring

/-- **Critical-Line Zero Vanishing of the Origin–Infinity Sector Wronskian (`l = 0`, `k ≥ 1`, `τ₀ ∈ ℝ`):**
At any critical-line zero `M_k(0, τ₀) = 0`, the origin–infinity sector Wronskian vanishes:
`W_k(0, τ₀) = 0`. -/
theorem sectorWronskian_at_criticalLine_zero_eq_zero
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) {τ₀ : ℝ}
    (hzero :
      (∫ x in Ioi (0 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) = 0) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
      ((∫ x in Ioi (1 : ℝ),
          x ^ (-(1 / 2 : ℝ)) * Real.sin (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (-(1 / 2 : ℝ)) * Real.sin (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
    (∫ x in Ioi (0 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.sin (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
      ((∫ x in Ioi (1 : ℝ),
          x ^ (-(1 / 2 : ℝ)) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (-(1 / 2 : ℝ)) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) = 0 := by
  rw [sectorWronskian_at_criticalLine_eq hk ν τ₀, hzero, zero_mul]

/-- **Critical-Line Horizontal Stationarity of the Origin–Infinity Sector Wronskian
(`l = 0`, `k ≥ 2`, `τ ∈ ℝ`):**
`((W_k(h, τ) − W_k(0, τ)) / h) → 0` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sectorWronskian_horiz_shift_at_criticalLine_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (0 : ℝ),
                x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            (∫ x in Ioi (0 : ℝ),
                x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
          ((∫ x in Ioi (0 : ℝ),
                x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            (∫ x in Ioi (0 : ℝ),
                x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have hk1 : 1 ≤ k := by omega
  have h := tendsto_div_sectorWronskian_horiz_shift_nhds_zero
    hk hν (by norm_num : |(0 : ℝ)| < 1 / 8) τ
  have hl0 : (0 : ℝ) - 1 / 2 = -(1 / 2 : ℝ) := by ring
  have hN0 := setIntegral_Ioi_rpow_neg_half_mul_sin_log_eq_zero hk1 ν τ
  have hΔc0 := setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_zero_mul_cos_log hk1 ν τ
  rw [hl0] at hΔc0
  have hsinh_full :
      (∫ v : ℝ, v * Real.sinh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) = 0 := by
    simp
  have hsinh_half :
      (∫ v in Ioi (0 : ℝ),
        2 * v * Real.sinh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) = 0 := by
    simp
  have hlim :
      (((∫ x in Ioi (0 : ℝ),
            x ^ ((0 : ℝ) - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
        ((∫ x in Ioi (1 : ℝ),
              x ^ ((0 : ℝ) - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ ((0 : ℝ) - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          (∫ v : ℝ, v * Real.sinh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) -
      ((∫ x in Ioi (0 : ℝ),
            x ^ ((0 : ℝ) - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
        ((∫ x in Ioi (1 : ℝ),
              x ^ ((0 : ℝ) - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ ((0 : ℝ) - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          (∫ v : ℝ, v * Real.cosh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) = 0 := by
    rw [hl0, hN0, hΔc0, hsinh_full, hsinh_half]
    ring
  rw [hlim] at h
  refine h.congr (fun h' => ?_)
  have hh0 : (0 : ℝ) + h' - 1 / 2 = h' - 1 / 2 := by ring
  rw [hh0, hl0]

/-- **Critical-Line Vertical Derivative `∂_τ W_k(0, τ)` of the Origin–Infinity Sector Wronskian
(`l = 0`, `k ≥ 2`, `τ ∈ ℝ`):**
`((W_k(0, τ + h) − W_k(0, τ)) / h) →
  M_k(0, τ) · (∫_{v > 0} 2 v cos(τv) Φ_k(v) dv) −
  (2 ∫_{v > 0} sin(τv) Φ_k(v) dv) · (∫_ℝ v sin(τv) Φ_k(v) dv)`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sectorWronskian_vert_shift_at_criticalLine_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (0 : ℝ),
                x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            (∫ x in Ioi (0 : ℝ),
                x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
          ((∫ x in Ioi (0 : ℝ),
                x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            (∫ x in Ioi (0 : ℝ),
                x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        ((∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
        (2 * ∫ v in Ioi (0 : ℝ), Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) := by
  have hk1 : 1 ≤ k := by omega
  have h := tendsto_div_sectorWronskian_vert_shift_nhds_zero
    hk hν (by norm_num : |(0 : ℝ)| < 1 / 8) τ
  have hl0 : (0 : ℝ) - 1 / 2 = -(1 / 2 : ℝ) := by ring
  have hN0 := setIntegral_Ioi_rpow_neg_half_mul_sin_log_eq_zero hk1 ν τ
  have hΔc0 := setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_zero_mul_cos_log hk1 ν τ
  have hΔs0 := setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_zero_mul_sin_log hk1 ν τ
  rw [hl0] at hΔc0 hΔs0
  have hcosh_half :
      (∫ v in Ioi (0 : ℝ),
        2 * v * Real.cosh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      ∫ v in Ioi (0 : ℝ),
        2 * v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    rw [zero_mul, Real.cosh_zero, mul_one]
  have hcosh_full :
      (∫ v : ℝ, v * Real.cosh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      ∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    dsimp only; rw [zero_mul, Real.cosh_zero, mul_one]
  have hlim :
      (((∫ x in Ioi (0 : ℝ),
            x ^ ((0 : ℝ) - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
        ((∫ x in Ioi (1 : ℝ),
              x ^ ((0 : ℝ) - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ ((0 : ℝ) - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          (-(∫ v : ℝ, v * Real.cosh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) -
      ((∫ x in Ioi (0 : ℝ),
            x ^ ((0 : ℝ) - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          (-(∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
        ((∫ x in Ioi (1 : ℝ),
              x ^ ((0 : ℝ) - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ ((0 : ℝ) - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          (∫ v : ℝ, v * Real.sinh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))) =
      (∫ x in Ioi (0 : ℝ),
          x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
        (∫ v in Ioi (0 : ℝ),
          2 * v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
      (2 * ∫ v in Ioi (0 : ℝ), Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
        (∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
    rw [hl0, hN0, hΔc0, hΔs0, hcosh_half, hcosh_full]
    ring
  rw [hlim] at h
  refine h.congr (fun h' => ?_)
  rw [hl0]

/-- **Critical-Line Zero-Locus Anti-Conformal Derivative Law (`l = 0`, `k ≥ 2`, `τ₀ ∈ ℝ`):**
At any critical-line zero `M_k(0, τ₀) = 0`, the vertical derivative of the origin–infinity sector
Wronskian `W_k(0, τ₀ + h) / h` converges to
`−(2 ∫_{v > 0} sin(τ₀ v) Φ_k(v) dv) · (∫_ℝ v sin(τ₀ v) Φ_k(v) dv) = −∂_l H_k(0, τ₀)`. -/
theorem tendsto_div_sectorWronskian_vert_shift_at_criticalLine_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {τ₀ : ℝ}
    (hzero :
      (∫ x in Ioi (0 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) = 0) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (0 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ₀ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            ((∫ x in Ioi (1 : ℝ),
                x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ₀ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ₀ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          (∫ x in Ioi (0 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ₀ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            ((∫ x in Ioi (1 : ℝ),
                x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ₀ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ₀ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) / h))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (-((2 * ∫ v in Ioi (0 : ℝ), Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v : ℝ, v * Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v)))) := by
  have hk1 : 1 ≤ k := by omega
  have h := tendsto_div_sectorWronskian_vert_shift_at_criticalLine_nhds_zero hk hν τ₀
  have hW0 := sectorWronskian_at_criticalLine_zero_eq_zero hk1 ν hzero
  rw [hW0, hzero, zero_mul, zero_sub] at h
  refine h.congr (fun h' => ?_)
  rw [sub_zero]

/-- **Master Witness Theorem for Division-Free Liouville–Gauss Logarithmic Harmonicity, Full-Strip
Jacobian Determinant of `(H_k, W_k)`, and Critical-Line Zero-Locus Anti-Conformality:**
There exists an explicit symmetric non-zero finite arc measure `ν` on `ArcParam` such that for all
`k ≥ 2`:
1. Across `|l| < 1/8` and `τ ∈ ℝ`, the complex Mellin modulus squared `|F_k(l, τ)|²` and the
   origin–infinity imbalance modulus squared `|Δ_k(l, τ)|²` satisfy the division-free
   Liouville–Gauss logarithmic harmonicity laws
   `|F_k|² · Δ(|F_k|²) − ((∂_l |F_k|²)² + (∂_τ |F_k|²)²) → 0` and
   `|Δ_k|² · Δ(|Δ_k|²) − ((∂_l |Δ_k|²)² + (∂_τ |Δ_k|²)²) → 0`;
2. Across `|l| < 1/8` and `τ ∈ ℝ`, the finite-difference Jacobian determinant of `(H_k, W_k)`
   converges to `|F_k(l, τ)|² · |Δ_k'(l, τ)|² − |Δ_k(l, τ)|² · |F_k'(l, τ)|²`;
3. On the critical line `l = 0`, the origin–infinity sector Wronskian `W_k(l, τ)` satisfies
   `W_k(−l, τ) = W_k(l, τ)`, `W_k(0, τ) = M_k(0, τ) (2 ∫_{v > 0} sin(τv) Φ_k(v) dv)`, horizontal
   stationarity `(W_k(h, τ) − W_k(0, τ)) / h → 0`, and vertical derivative `∂_τ W_k(0, τ) = ∂_l P_k(0, τ)`. -/
theorem exists_dyadic_logarithmicSubharmonicity_wronskianJacobian_arcWitness :
    ∃ ν : Measure ArcParam,
      IsFiniteMeasure ν ∧
      ν.map arcNeg = ν ∧
      ν ≠ 0 ∧
      ∀ ⦃k : ℕ⦄, 2 ≤ k →
        (∀ ⦃l : ℝ⦄, |l| < 1 / 8 → ∀ τ : ℝ,
          Tendsto
            (fun h : ℝ =>
              ((∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                (((((∫ x in Ioi (0 : ℝ),
                          x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (0 : ℝ),
                          x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                      ((∫ x in Ioi (0 : ℝ),
                          x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (0 : ℝ),
                          x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                      2 * ((∫ x in Ioi (0 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (0 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
                    (((∫ x in Ioi (0 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (0 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                      ((∫ x in Ioi (0 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (0 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                      2 * ((∫ x in Ioi (0 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (0 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h ^ 2) -
                (((((∫ x in Ioi (0 : ℝ),
                          x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (0 : ℝ),
                          x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                      ((∫ x in Ioi (0 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (0 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h) ^ 2 +
                  ((((∫ x in Ioi (0 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (0 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                      ((∫ x in Ioi (0 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (0 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h) ^ 2))
            (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0)) ∧
        (∀ ⦃l : ℝ⦄, |l| < 1 / 8 → ∀ τ : ℝ,
          Tendsto
            (fun h : ℝ =>
              (((((∫ x in Ioi (0 : ℝ),
                        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
                    (∫ x in Ioi (0 : ℝ),
                        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
                  ((∫ x in Ioi (0 : ℝ),
                        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
                    (∫ x in Ioi (0 : ℝ),
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) *
                ((((∫ x in Ioi (0 : ℝ),
                        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    (∫ x in Ioi (0 : ℝ),
                        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
                  ((∫ x in Ioi (0 : ℝ),
                        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    (∫ x in Ioi (0 : ℝ),
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)) -
              (((((∫ x in Ioi (0 : ℝ),
                        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
                    (∫ x in Ioi (0 : ℝ),
                        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
                  ((∫ x in Ioi (0 : ℝ),
                        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
                    (∫ x in Ioi (0 : ℝ),
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h) *
                ((((∫ x in Ioi (0 : ℝ),
                        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    (∫ x in Ioi (0 : ℝ),
                        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
                  ((∫ x in Ioi (0 : ℝ),
                        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    (∫ x in Ioi (0 : ℝ),
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                        ∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)))
            (nhdsWithin 0 {(0 : ℝ)}ᶜ)
            (nhds
              (((∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                ((∫ v in Ioi (0 : ℝ),
                    2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
                  (∫ v in Ioi (0 : ℝ),
                    2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2) -
              (((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
                  (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2)))) ∧
        (∀ τ : ℝ,
          Tendsto
            (fun h : ℝ =>
              (((∫ x in Ioi (0 : ℝ),
                      x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    ((∫ x in Ioi (1 : ℝ),
                        x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                        x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  (∫ x in Ioi (0 : ℝ),
                      x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    ((∫ x in Ioi (1 : ℝ),
                        x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                        x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
                ((∫ x in Ioi (0 : ℝ),
                      x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    ((∫ x in Ioi (1 : ℝ),
                        x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                        x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  (∫ x in Ioi (0 : ℝ),
                      x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    ((∫ x in Ioi (1 : ℝ),
                        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) ∧
          Tendsto
            (fun h : ℝ =>
              (((∫ x in Ioi (0 : ℝ),
                      x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    ((∫ x in Ioi (1 : ℝ),
                        x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                        x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  (∫ x in Ioi (0 : ℝ),
                      x ^ (-(1 / 2 : ℝ)) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    ((∫ x in Ioi (1 : ℝ),
                        x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                        x ^ (-(1 / 2 : ℝ)) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
                ((∫ x in Ioi (0 : ℝ),
                      x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    ((∫ x in Ioi (1 : ℝ),
                        x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                        x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  (∫ x in Ioi (0 : ℝ),
                      x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                    ((∫ x in Ioi (1 : ℝ),
                        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                      ∫ x in Ioc (0 : ℝ) 1,
                        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ)
            (nhds
              ((∫ x in Ioi (0 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
              (2 * ∫ v in Ioi (0 : ℝ), Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
                (∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) := by
  obtain ⟨ν, hfin, hne, hν, _, _⟩ := exists_arcWitness
  refine ⟨ν, hfin, hν, hne, fun k hk => ?_⟩
  refine ⟨fun l hl τ => tendsto_complexModulusSq_liouville_gauss_nhds_zero hk hν hl τ,
    fun l hl τ => tendsto_hermitian_wronskian_jacobian_det_nhds_zero hk hν hl τ,
    fun τ =>
      ⟨tendsto_div_sectorWronskian_horiz_shift_at_criticalLine_nhds_zero hk hν τ,
       tendsto_div_sectorWronskian_vert_shift_at_criticalLine_nhds_zero hk hν τ⟩⟩

end

end RHTower

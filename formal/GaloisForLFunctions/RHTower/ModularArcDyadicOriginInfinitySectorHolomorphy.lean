import GaloisForLFunctions.RHTower.ModularArcDyadicHarmonicLaplacianSubharmonicModulus

/-!
# Origin–infinity complex Mellin sector duality, Cauchy–Riemann holomorphy and five-point harmonicity of the complex Mellin imbalance, sector modulus parallelogram and polarization laws, and zero-locus sector equipartition

In `ModularArcDyadicConjugateSineCauchyRiemann` and
`ModularArcDyadicHarmonicLaplacianSubharmonicModulus`, we established the full-line complex
oscillatory Mellin transform
`F_k(l, τ) = M_k(l, τ) + i N_k(l, τ)`
with real (cosine) part
`M_k(l, τ) = ∫_{x > 0} x^{l − 1/2} cos(τ log x) V_k(x) dx = ∫_ℝ cosh(lv) cos(τv) Φ_k(v) dv`
and imaginary (sine) part
`N_k(l, τ) = ∫_{x > 0} x^{l − 1/2} sin(τ log x) V_k(x) dx = ∫_ℝ sinh(lv) sin(τv) Φ_k(v) dv`.

In this module we develop the **origin–infinity sector decomposition** (`(0, 1]` vs `(1, ∞)`) of
the complex oscillatory Mellin transform across the critical strip `|l| < 1/2`, `τ ∈ ℝ`:

1. **Section 1 — Origin–infinity complex Mellin sector duality and the conjugate sine imbalance
   `Δ_k^{\sin}(l, τ)`:**
   - Origin–infinity sector reflection laws (`setIntegral_Ioc_zero_one_rpow_mul_sin_log_eq_neg_setIntegral_Ioi_one_neg`,
     `setIntegral_Ioc_zero_one_rpow_neg_half_mul_sin_log_eq_neg_Ioi_one`).
   - Exact `2 cosh(lv) sin(τv)` representation of the origin–infinity sine imbalance:
     `Δ_k^{\sin}(l, τ) := ∫_{x > 1} x^{l − 1/2} sin(τ log x) V_k(x) dx − ∫_{x ∈ (0, 1]} x^{l − 1/2} sin(τ log x) V_k(x) dx = ∫_{v > 0} 2 cosh(lv) sin(τv) Φ_k(v) dv`
     (`setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_sin_log_eq`).
   - Parity, real-axis vanishing, critical-line reduction, and full-line sector decompositions
     (`setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors`,
     `setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors`).

2. **Section 2 — Cauchy–Riemann holomorphic partial derivatives and five-point harmonicity of the
   origin–infinity complex Mellin imbalance `(Δ_k^{\cos}(l, τ), Δ_k^{\sin}(l, τ))`:**
   - Height-uniform quadratic `O(h²)` finite-difference remainder bounds and directional partial
     derivatives for `Δ_k^{\cos}(l, τ)` and `Δ_k^{\sin}(l, τ)` across `|l| < 1/8`, `τ ∈ ℝ`:
     `∂_l Δ_k^{\cos}(l, τ) = ∂_τ Δ_k^{\sin}(l, τ) = ∫_{v > 0} 2 v cosh(lv) cos(τv) Φ_k(v) dv` and
     `∂_l Δ_k^{\sin}(l, τ) = −∂_τ Δ_k^{\cos}(l, τ) = ∫_{v > 0} 2 v sinh(lv) sin(τv) Φ_k(v) dv`.
   - Height-uniform quartic `O(h⁴)` five-point discrete Laplacian bounds and normalized five-point
     harmonic Laplacian vanishing for both `Δ_k^{\cos}(l, τ)` and `Δ_k^{\sin}(l, τ)`.

3. **Section 3 — Sector modulus parallelogram law, polarization identity, and zero-locus sector
   equipartition:**
   - Universal and Mellin-instantiated parallelogram law:
     `(M_k² + N_k²) + ((Δ_k^{\cos})² + (Δ_k^{\sin})²) = 2 ((C_k^+² + S_k^+²) + (C_k^-² + S_k^-²))`.
   - Exact sector modulus imbalance polarization identity:
     `(C_k^+² + S_k^+²) − (C_k^-² + S_k^-²) = M_k · Δ_k^{\cos} + N_k · Δ_k^{\sin}`.
   - Brahmagupta–Fibonacci identity, Cauchy–Schwarz inequality for the sector modulus imbalance,
     critical-line (`l = 0`) complex sector equipartition, and zero-locus complex sector
     equipartition (`M_k(l, τ)² + N_k(l, τ)² = 0 → C_k^+(l, τ)² + S_k^+(l, τ)² = C_k^-(l, τ)² + S_k^-(l, τ)²`).

4. **Section 4 — Five-point subharmonicity of the imbalance modulus squared and critical-line
   transversality of the sector modulus imbalance:**
   - Global five-point subharmonic Laplacian law for `(Δ_k^{\cos})² + (Δ_k^{\sin})²` across
     `|l| < 1/8`, `τ ∈ ℝ`.
   - Exact first-order horizontal transversal derivative of the sector modulus imbalance on the
     critical line `l = 0` at every height `τ ∈ ℝ`, and its specialization at critical-line zeros
     `M_k(0, τ₀) = 0` (`exists_dyadic_originInfinity_sectorHolomorphy_arcWitness`).
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ## Section 1: Origin–Infinity Complex Mellin Sector Duality and the Conjugate Sine Imbalance `Δ_k^{\sin}(l, τ)` -/

/-- **Origin–infinity sector reflection law for the sine oscillatory Mellin transform (`k ≥ 1`, `l, τ ∈ ℝ`):**
`∫_{x ∈ (0, 1]} x^{l − 1/2} sin(τ log x) V_k(x) dx = −∫_{x > 1} x^{−l − 1/2} sin(τ log x) V_k(x) dx`. -/
theorem setIntegral_Ioc_zero_one_rpow_mul_sin_log_eq_neg_setIntegral_Ioi_one_neg
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      -(∫ x in Ioi (1 : ℝ),
        x ^ (-l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) := by
  rw [setIntegral_Ioc_zero_one_rpow_mul_sin_log_eq_neg_setIntegral_Ioi_zero hk ν l τ,
    setIntegral_Ioi_one_rpow_mul_sin_log_eq_setIntegral_Ioi_zero hk ν (-l) τ]

/-- **Critical-line (`l = 0`) origin–infinity antisymmetry for the sine oscillatory Mellin sectors (`k ≥ 1`, `τ ∈ ℝ`):**
`∫_{x ∈ (0, 1]} x^{−1/2} sin(τ log x) V_k(x) dx = −∫_{x > 1} x^{−1/2} sin(τ log x) V_k(x) dx`. -/
theorem setIntegral_Ioc_zero_one_rpow_neg_half_mul_sin_log_eq_neg_Ioi_one
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (τ : ℝ) :
    (∫ x in Ioc (0 : ℝ) 1,
        x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      -(∫ x in Ioi (1 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) := by
  have h := setIntegral_Ioc_zero_one_rpow_mul_sin_log_eq_neg_setIntegral_Ioi_one_neg hk ν 0 τ
  simpa using h

/-- **Integrability of `2 cosh(lv) sin(τv) Φ_k(v)` on `(0, ∞)` across `|l| < 1/2` and `τ ∈ ℝ` (`k ≥ 2`).** -/
theorem integrableOn_Ioi_zero_two_mul_cosh_mul_sin_mul_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    IntegrableOn
      (fun v : ℝ => 2 * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)
      (Ioi (0 : ℝ)) := by
  have e : (fun v : ℝ =>
        2 * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      fun v : ℝ =>
        Real.exp (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v +
          Real.exp ((-l) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
    funext v; rw [Real.cosh_eq, neg_mul]; ring
  rw [e]
  exact (integrable_exp_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν hl τ).integrableOn.add
    (integrable_exp_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν (by simpa using hl) τ).integrableOn

/-- **Exact `2 cosh(lv) sin(τv)` representation of the origin–infinity sine Mellin imbalance
(`|l| < 1/2`, `τ ∈ ℝ`, `k ≥ 2`):**
`∫_{x > 1} x^{l − 1/2} sin(τ log x) V_k(x) dx − ∫_{x ∈ (0, 1]} x^{l − 1/2} sin(τ log x) V_k(x) dx = ∫_{v > 0} 2 cosh(lv) sin(τv) Φ_k(v) dv`. -/
theorem setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_sin_log_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      (∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      ∫ v in Ioi (0 : ℝ),
        2 * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
  have hk1 : 1 ≤ k := by omega
  have hnl : |-l| < 1 / 2 := by simpa using hl
  have hI_pos := (integrable_exp_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν hl τ).integrableOn
    (s := Ioi (0 : ℝ))
  have hI_neg := (integrable_exp_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν hnl τ).integrableOn
    (s := Ioi (0 : ℝ))
  rw [setIntegral_Ioi_one_rpow_mul_sin_log_eq_setIntegral_Ioi_zero hk1 ν l τ,
    setIntegral_Ioc_zero_one_rpow_mul_sin_log_eq_neg_setIntegral_Ioi_zero hk1 ν l τ,
    sub_neg_eq_add, ← integral_add hI_pos hI_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [Real.cosh_eq, neg_mul]
  ring

/-- **Even reflection symmetry `l ↦ −l` of the origin–infinity sine Mellin imbalance
(`k ≥ 1`, `l, τ ∈ ℝ`).** -/
theorem setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_neg_mul_sin_log
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ x in Ioi (1 : ℝ),
        x ^ (-l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      (∫ x in Ioc (0 : ℝ) 1,
        x ^ (-l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      (∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) := by
  have h1 := setIntegral_Ioc_zero_one_rpow_mul_sin_log_eq_neg_setIntegral_Ioi_one_neg hk ν l τ
  have h2 := setIntegral_Ioc_zero_one_rpow_mul_sin_log_eq_neg_setIntegral_Ioi_one_neg hk ν (-l) τ
  rw [neg_neg] at h2
  linarith

/-- **Odd vertical frequency antisymmetry `τ ↦ −τ` of the origin–infinity sine Mellin imbalance
(`k : ℕ`, `l, τ ∈ ℝ`).** -/
theorem setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_sin_neg_log
    (k : ℕ) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (-τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      (∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.sin (-τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      -((∫ x in Ioi (1 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        (∫ x in Ioc (0 : ℝ) 1,
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) := by
  have hfun :
      (fun x : ℝ =>
        x ^ (l - 1 / 2) * Real.sin (-τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      fun x : ℝ =>
        -(x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) := by
    funext x
    rw [neg_mul, Real.sin_neg]
    ring
  rw [hfun, integral_neg, integral_neg]
  ring

/-- **Identical vanishing of the origin–infinity sine Mellin imbalance on the real axis `τ = 0`
for all `l ∈ ℝ` (`k : ℕ`).** -/
theorem setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_sin_zero_log
    (k : ℕ) (ν : Measure ArcParam) (l : ℝ) :
    (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (0 * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      (∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.sin (0 * Real.log x) * arcLineInfiniteDyadicVector k ν x) = 0 := by
  simp

/-- **Critical-line (`l = 0`) doubling formula for the origin–infinity sine Mellin imbalance
(`k ≥ 1`, `τ ∈ ℝ`):**
`Δ_k^{\sin}(0, τ) = 2 ∫_{x > 1} x^{−1/2} sin(τ log x) V_k(x) dx = 2 ∫_{v > 0} sin(τv) Φ_k(v) dv`. -/
theorem setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_zero_mul_sin_log
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (τ : ℝ) :
    (∫ x in Ioi (1 : ℝ),
        x ^ ((0 : ℝ) - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      (∫ x in Ioc (0 : ℝ) 1,
        x ^ ((0 : ℝ) - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      2 * ∫ v in Ioi (0 : ℝ), Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
  rw [zero_sub, setIntegral_Ioc_zero_one_rpow_neg_half_mul_sin_log_eq_neg_Ioi_one hk ν τ,
    sub_neg_eq_add, ← two_mul]
  congr 1
  have h := setIntegral_Ioi_one_rpow_mul_sin_log_eq_setIntegral_Ioi_zero hk ν 0 τ
  simpa using h

/-- **Full-line decomposition of `M_k(l, τ)` into the `(1, ∞)` and `(0, 1]` cosine sectors
(`k ≥ 2`, `|l| < 1/2`, `τ ∈ ℝ`).** -/
theorem setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
      (∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) := by
  have hk1 : 1 ≤ k := by omega
  have hg : IntegrableOn
      (fun x : ℝ =>
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)
      (Ioi (0 : ℝ)) := by
    rw [integrableOn_Ioi_iff_integrable_exp_mul]
    refine (integrable_exp_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl τ).congr
      (Eventually.of_forall fun v => ?_)
    dsimp only
    rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp,
      ← exp_half_mul_arcLineInfiniteDyadicVector hk1 ν v]
    have hexp : Real.exp v * Real.exp (v * (l - 1 / 2)) =
        Real.exp (l * v) * Real.exp (v / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc Real.exp (l * v) * Real.cos (τ * v) *
            (Real.exp (v / 2) * arcLineInfiniteDyadicVector k ν (Real.exp v))
        = (Real.exp (l * v) * Real.exp (v / 2)) * Real.cos (τ * v) *
            arcLineInfiniteDyadicVector k ν (Real.exp v) := by ring
      _ = (Real.exp v * Real.exp (v * (l - 1 / 2))) * Real.cos (τ * v) *
            arcLineInfiniteDyadicVector k ν (Real.exp v) := by rw [← hexp]
      _ = Real.exp v * (Real.exp (v * (l - 1 / 2)) * Real.cos (τ * v) *
            arcLineInfiniteDyadicVector k ν (Real.exp v)) := by ring
  rw [← setIntegral_Ioc_zero_one_add_setIntegral_Ioi_one hg, add_comm]

/-- **Full-line decomposition of `N_k(l, τ)` into the `(1, ∞)` and `(0, 1]` sine sectors
(`k ≥ 2`, `|l| < 1/2`, `τ ∈ ℝ`).** -/
theorem setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
      (∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) := by
  have hk1 : 1 ≤ k := by omega
  have hg : IntegrableOn
      (fun x : ℝ =>
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)
      (Ioi (0 : ℝ)) := by
    rw [integrableOn_Ioi_iff_integrable_exp_mul]
    refine (integrable_exp_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν hl τ).congr
      (Eventually.of_forall fun v => ?_)
    dsimp only
    rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp,
      ← exp_half_mul_arcLineInfiniteDyadicVector hk1 ν v]
    have hexp : Real.exp v * Real.exp (v * (l - 1 / 2)) =
        Real.exp (l * v) * Real.exp (v / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc Real.exp (l * v) * Real.sin (τ * v) *
            (Real.exp (v / 2) * arcLineInfiniteDyadicVector k ν (Real.exp v))
        = (Real.exp (l * v) * Real.exp (v / 2)) * Real.sin (τ * v) *
            arcLineInfiniteDyadicVector k ν (Real.exp v) := by ring
      _ = (Real.exp v * Real.exp (v * (l - 1 / 2))) * Real.sin (τ * v) *
            arcLineInfiniteDyadicVector k ν (Real.exp v) := by rw [← hexp]
      _ = Real.exp v * (Real.exp (v * (l - 1 / 2)) * Real.sin (τ * v) *
            arcLineInfiniteDyadicVector k ν (Real.exp v)) := by ring
  rw [← setIntegral_Ioc_zero_one_add_setIntegral_Ioi_one hg, add_comm]


/-! ## Section 2: Cauchy–Riemann Holomorphic Partial Derivatives and Five-Point Harmonicity of the Origin–Infinity Complex Imbalance `(Δ_k^{\cos}(l, τ), Δ_k^{\sin}(l, τ))` -/

/-- **Integrability of `2 v^n cosh(lv) cos(τv) Φ_k(v)` on `(0, ∞)` (`k ≥ 2`, `|l| < 1/8`, `n ∈ ℕ`, `τ ∈ ℝ`).** -/
theorem integrableOn_Ioi_zero_two_mul_pow_mul_cosh_mul_cos_mul_profile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (n : ℕ) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    IntegrableOn
      (fun v : ℝ =>
        2 * v ^ n * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)
      (Ioi (0 : ℝ)) := by
  have hInt := (integrable_pow_mul_cosh_mul_cos_mul_arcLineInfiniteDyadicProfile
    hk hν hl n τ).const_mul 2
  refine hInt.integrableOn.congr_fun (fun v _ => ?_) measurableSet_Ioi
  dsimp only; ring

/-- **Integrability of `2 v^n sinh(lv) sin(τv) Φ_k(v)` on `(0, ∞)` (`k ≥ 2`, `|l| < 1/8`, `n ∈ ℕ`, `τ ∈ ℝ`).** -/
theorem integrableOn_Ioi_zero_two_mul_pow_mul_sinh_mul_sin_mul_profile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (n : ℕ) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    IntegrableOn
      (fun v : ℝ =>
        2 * v ^ n * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)
      (Ioi (0 : ℝ)) := by
  have hInt := (integrable_pow_mul_sinh_mul_sin_mul_arcLineInfiniteDyadicProfile
    hk hν hl n τ).const_mul 2
  refine hInt.integrableOn.congr_fun (fun v _ => ?_) measurableSet_Ioi
  dsimp only; ring

/-- **Height-uniform quadratic `O(h²)` horizontal finite-difference remainder bound for the
origin–infinity cosine imbalance `Δ_k^{\cos}(l, τ)` (`k ≥ 2`, `|l| + |h| < 1/8`, `τ ∈ ℝ`):**
`|Δ_k^{\cos}(l + h, τ) − Δ_k^{\cos}(l, τ) − h ∫_{v > 0} 2 v cosh(lv) cos(τv) Φ_k(v) dv| ≤
  (422400 · ν.real univ / (1/8 − |l| − |h|)) · h²`. -/
theorem abs_imbalanceCos_diff_sub_linear_left_le_sq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l h : ℝ} (hlh : |l| + |h| < 1 / 8) (τ : ℝ) :
    |(((∫ x in Ioi (1 : ℝ),
            x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
        h * ∫ v in Ioi (0 : ℝ),
          2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v| ≤
      (422400 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := by
  have hl : |l| < 1 / 8 := by linarith [abs_nonneg h]
  have hl_half : |l| < 1 / 2 := by linarith
  have hlh_abs : |l + h| < 1 / 8 := (abs_add_le l h).trans_lt hlh
  have hlh_half : |l + h| < 1 / 2 := by linarith
  have hc : 0 < 1 / 8 - |l| - |h| := by linarith
  rw [setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_cos_log_eq hk hν hlh_half τ,
    setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_cos_log_eq hk hν hl_half τ]
  have hInt1 := integrableOn_Ioi_zero_two_mul_sinh_mul_cos_mul_arcLineInfiniteDyadicProfile
    hk hν hlh_half τ
  have hInt2 := integrableOn_Ioi_zero_two_mul_sinh_mul_cos_mul_arcLineInfiniteDyadicProfile
    hk hν hl_half τ
  have hInt3 : IntegrableOn
      (fun v : ℝ => 2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)
      (Ioi (0 : ℝ)) := by
    simpa only [pow_one] using
      integrableOn_Ioi_zero_two_mul_pow_mul_cosh_mul_cos_mul_profile hk hν 1 hl τ
  have hInt12 : IntegrableOn
      (fun v : ℝ =>
        2 * Real.sinh ((l + h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          2 * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)
      (Ioi (0 : ℝ)) := hInt1.sub hInt2
  have hInt3h : IntegrableOn
      (fun v : ℝ =>
        h * (2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))
      (Ioi (0 : ℝ)) := hInt3.const_mul h
  rw [← integral_sub hInt1 hInt2, ← integral_const_mul, ← integral_sub hInt12 hInt3h]
  set B := 2 * (105600 * ν.real univ * h ^ 2)
  have hdom_full : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  have hdom : IntegrableOn
      (fun v : ℝ => B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) (Ioi (0 : ℝ)) :=
    hdom_full.integrableOn
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      2 * Real.sinh ((l + h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
        2 * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
        h * (2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))
    hdom (ae_restrict_mem measurableSet_Ioi |>.mono fun v _ => ?_)
  · have hle_full :
        (∫ v in Ioi (0 : ℝ), B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) ≤
          ∫ v : ℝ, B * Real.exp (-((1 / 8 - |l| - |h|) * |v|)) := by
      refine setIntegral_le_integral hdom_full (Eventually.of_forall fun v => ?_)
      have := measureReal_nonneg (μ := ν) (s := univ)
      dsimp [B]; positivity
    have hfull_eq :
        (∫ v : ℝ, B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) =
          (422400 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := by
      rw [integral_const_mul, integral_rexp_neg_mul_abs hc]
      dsimp [B]; ring
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (hle_full.trans hfull_eq.le)
  · have hfac :
        2 * Real.sinh ((l + h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          2 * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          h * (2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
        2 * (((Real.sinh ((l + h) * v) - Real.sinh (l * v) - (h * v) * Real.cosh (l * v)) *
          Real.cos (τ * v)) * arcLineInfiniteDyadicProfile k ν v) := by ring
    rw [Real.norm_eq_abs, hfac, abs_mul, abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hker := abs_sinh_add_sub_sinh_sub_mul_cosh_le l h v
    have hcos := Real.abs_cos_le_one (τ * v)
    have hprod :
        |Real.sinh ((l + h) * v) - Real.sinh (l * v) - (h * v) * Real.cosh (l * v)| *
          |Real.cos (τ * v)| ≤
        h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|) := by
      calc |Real.sinh ((l + h) * v) - Real.sinh (l * v) - (h * v) * Real.cosh (l * v)| *
              |Real.cos (τ * v)|
          ≤ (h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|)) * 1 :=
            mul_le_mul hker hcos (abs_nonneg _) (by positivity)
        _ = h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|) := mul_one _
    have hprof := quadratic_shift_envelope_mul_abs_arcLineInfiniteDyadicProfile_le hk hν l h v
    have hstep := (mul_le_mul_of_nonneg_right hprod (abs_nonneg _)).trans hprof
    linarith

/-- **Height-uniform quadratic `O(h²)` vertical finite-difference remainder bound for the
origin–infinity sine imbalance `Δ_k^{\sin}(l, τ)` (`k ≥ 2`, `|l| + |h| < 1/8`, `τ ∈ ℝ`):**
`|Δ_k^{\sin}(l, τ + h) − Δ_k^{\sin}(l, τ) − h ∫_{v > 0} 2 v cosh(lv) cos(τv) Φ_k(v) dv| ≤
  (422400 · ν.real univ / (1/8 − |l| − |h|)) · h²`. -/
theorem abs_imbalanceSin_diff_sub_linear_right_le_sq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l h : ℝ} (hlh : |l| + |h| < 1 / 8) (τ : ℝ) :
    |(((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
        h * ∫ v in Ioi (0 : ℝ),
          2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v| ≤
      (422400 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := by
  have hl : |l| < 1 / 8 := by linarith [abs_nonneg h]
  have hl_half : |l| < 1 / 2 := by linarith
  have hc : 0 < 1 / 8 - |l| - |h| := by linarith
  rw [setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_sin_log_eq hk hν hl_half (τ + h),
    setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_sin_log_eq hk hν hl_half τ]
  have hInt1 := integrableOn_Ioi_zero_two_mul_cosh_mul_sin_mul_arcLineInfiniteDyadicProfile
    hk hν hl_half (τ + h)
  have hInt2 := integrableOn_Ioi_zero_two_mul_cosh_mul_sin_mul_arcLineInfiniteDyadicProfile
    hk hν hl_half τ
  have hInt3 : IntegrableOn
      (fun v : ℝ => 2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)
      (Ioi (0 : ℝ)) := by
    simpa only [pow_one] using
      integrableOn_Ioi_zero_two_mul_pow_mul_cosh_mul_cos_mul_profile hk hν 1 hl τ
  have hInt12 : IntegrableOn
      (fun v : ℝ =>
        2 * Real.cosh (l * v) * Real.sin ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v -
          2 * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)
      (Ioi (0 : ℝ)) := hInt1.sub hInt2
  have hInt3h : IntegrableOn
      (fun v : ℝ =>
        h * (2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))
      (Ioi (0 : ℝ)) := hInt3.const_mul h
  rw [← integral_sub hInt1 hInt2, ← integral_const_mul, ← integral_sub hInt12 hInt3h]
  set B := 2 * (105600 * ν.real univ * h ^ 2)
  have hdom_full : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  have hdom : IntegrableOn
      (fun v : ℝ => B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) (Ioi (0 : ℝ)) :=
    hdom_full.integrableOn
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      2 * Real.cosh (l * v) * Real.sin ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v -
        2 * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
        h * (2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))
    hdom (ae_restrict_mem measurableSet_Ioi |>.mono fun v _ => ?_)
  · have hle_full :
        (∫ v in Ioi (0 : ℝ), B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) ≤
          ∫ v : ℝ, B * Real.exp (-((1 / 8 - |l| - |h|) * |v|)) := by
      refine setIntegral_le_integral hdom_full (Eventually.of_forall fun v => ?_)
      have := measureReal_nonneg (μ := ν) (s := univ)
      dsimp [B]; positivity
    have hfull_eq :
        (∫ v : ℝ, B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) =
          (422400 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := by
      rw [integral_const_mul, integral_rexp_neg_mul_abs hc]
      dsimp [B]; ring
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (hle_full.trans hfull_eq.le)
  · have hfac :
        2 * Real.cosh (l * v) * Real.sin ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v -
          2 * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          h * (2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
        2 * ((Real.cosh (l * v) *
          (Real.sin ((τ + h) * v) - Real.sin (τ * v) - (h * v) * Real.cos (τ * v))) *
          arcLineInfiniteDyadicProfile k ν v) := by ring
    rw [Real.norm_eq_abs, hfac, abs_mul, abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos (Real.cosh_pos (l * v))]
    have hker := abs_sin_add_sub_sin_sub_mul_cos_le τ h v
    have hcosh : Real.cosh (l * v) ≤ Real.exp (|l| * |v|) := by
      rw [← abs_mul]; exact cosh_le_exp_abs (l * v)
    have hprod :
        Real.cosh (l * v) *
          |Real.sin ((τ + h) * v) - Real.sin (τ * v) - (h * v) * Real.cos (τ * v)| ≤
        h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|) := by
      calc Real.cosh (l * v) *
              |Real.sin ((τ + h) * v) - Real.sin (τ * v) - (h * v) * Real.cos (τ * v)|
          ≤ Real.exp (|l| * |v|) * (h ^ 2 * v ^ 2 * Real.exp (|h| * |v|)) :=
            mul_le_mul hcosh hker (abs_nonneg _) (Real.exp_nonneg _)
        _ = h ^ 2 * v ^ 2 * (Real.exp (|l| * |v|) * Real.exp (|h| * |v|)) := by ring
        _ = h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|) := by
            rw [← Real.exp_add]; congr 2; ring
    have hprof := quadratic_shift_envelope_mul_abs_arcLineInfiniteDyadicProfile_le hk hν l h v
    have hstep := (mul_le_mul_of_nonneg_right hprod (abs_nonneg _)).trans hprof
    linarith

/-- **Height-uniform quadratic `O(h²)` horizontal finite-difference remainder bound for the
origin–infinity sine imbalance `Δ_k^{\sin}(l, τ)` (`k ≥ 2`, `|l| + |h| < 1/8`, `τ ∈ ℝ`):**
`|Δ_k^{\sin}(l + h, τ) − Δ_k^{\sin}(l, τ) − h ∫_{v > 0} 2 v sinh(lv) sin(τv) Φ_k(v) dv| ≤
  (422400 · ν.real univ / (1/8 − |l| − |h|)) · h²`. -/
theorem abs_imbalanceSin_diff_sub_linear_left_le_sq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l h : ℝ} (hlh : |l| + |h| < 1 / 8) (τ : ℝ) :
    |(((∫ x in Ioi (1 : ℝ),
            x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
        h * ∫ v in Ioi (0 : ℝ),
          2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v| ≤
      (422400 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := by
  have hl : |l| < 1 / 8 := by linarith [abs_nonneg h]
  have hl_half : |l| < 1 / 2 := by linarith
  have hlh_abs : |l + h| < 1 / 8 := (abs_add_le l h).trans_lt hlh
  have hlh_half : |l + h| < 1 / 2 := by linarith
  have hc : 0 < 1 / 8 - |l| - |h| := by linarith
  rw [setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_sin_log_eq hk hν hlh_half τ,
    setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_sin_log_eq hk hν hl_half τ]
  have hInt1 := integrableOn_Ioi_zero_two_mul_cosh_mul_sin_mul_arcLineInfiniteDyadicProfile
    hk hν hlh_half τ
  have hInt2 := integrableOn_Ioi_zero_two_mul_cosh_mul_sin_mul_arcLineInfiniteDyadicProfile
    hk hν hl_half τ
  have hInt3 : IntegrableOn
      (fun v : ℝ => 2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)
      (Ioi (0 : ℝ)) := by
    simpa only [pow_one] using
      integrableOn_Ioi_zero_two_mul_pow_mul_sinh_mul_sin_mul_profile hk hν 1 hl τ
  have hInt12 : IntegrableOn
      (fun v : ℝ =>
        2 * Real.cosh ((l + h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          2 * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)
      (Ioi (0 : ℝ)) := hInt1.sub hInt2
  have hInt3h : IntegrableOn
      (fun v : ℝ =>
        h * (2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))
      (Ioi (0 : ℝ)) := hInt3.const_mul h
  rw [← integral_sub hInt1 hInt2, ← integral_const_mul, ← integral_sub hInt12 hInt3h]
  set B := 2 * (105600 * ν.real univ * h ^ 2)
  have hdom_full : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  have hdom : IntegrableOn
      (fun v : ℝ => B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) (Ioi (0 : ℝ)) :=
    hdom_full.integrableOn
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      2 * Real.cosh ((l + h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
        2 * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
        h * (2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))
    hdom (ae_restrict_mem measurableSet_Ioi |>.mono fun v _ => ?_)
  · have hle_full :
        (∫ v in Ioi (0 : ℝ), B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) ≤
          ∫ v : ℝ, B * Real.exp (-((1 / 8 - |l| - |h|) * |v|)) := by
      refine setIntegral_le_integral hdom_full (Eventually.of_forall fun v => ?_)
      have := measureReal_nonneg (μ := ν) (s := univ)
      dsimp [B]; positivity
    have hfull_eq :
        (∫ v : ℝ, B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) =
          (422400 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := by
      rw [integral_const_mul, integral_rexp_neg_mul_abs hc]
      dsimp [B]; ring
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (hle_full.trans hfull_eq.le)
  · have hfac :
        2 * Real.cosh ((l + h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          2 * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          h * (2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
        2 * (((Real.cosh ((l + h) * v) - Real.cosh (l * v) - (h * v) * Real.sinh (l * v)) *
          Real.sin (τ * v)) * arcLineInfiniteDyadicProfile k ν v) := by ring
    rw [Real.norm_eq_abs, hfac, abs_mul, abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hker := abs_cosh_add_sub_cosh_sub_mul_sinh_le l h v
    have hsin := Real.abs_sin_le_one (τ * v)
    have hprod :
        |Real.cosh ((l + h) * v) - Real.cosh (l * v) - (h * v) * Real.sinh (l * v)| *
          |Real.sin (τ * v)| ≤
        h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|) := by
      calc |Real.cosh ((l + h) * v) - Real.cosh (l * v) - (h * v) * Real.sinh (l * v)| *
              |Real.sin (τ * v)|
          ≤ (h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|)) * 1 :=
            mul_le_mul hker hsin (abs_nonneg _) (by positivity)
        _ = h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|) := mul_one _
    have hprof := quadratic_shift_envelope_mul_abs_arcLineInfiniteDyadicProfile_le hk hν l h v
    have hstep := (mul_le_mul_of_nonneg_right hprod (abs_nonneg _)).trans hprof
    linarith

/-- **Height-uniform quadratic `O(h²)` vertical finite-difference remainder bound for the
origin–infinity cosine imbalance `Δ_k^{\cos}(l, τ)` (`k ≥ 2`, `|l| + |h| < 1/8`, `τ ∈ ℝ`):**
`|Δ_k^{\cos}(l, τ + h) − Δ_k^{\cos}(l, τ) + h ∫_{v > 0} 2 v sinh(lv) sin(τv) Φ_k(v) dv| ≤
  (422400 · ν.real univ / (1/8 − |l| − |h|)) · h²`. -/
theorem abs_imbalanceCos_diff_sub_linear_right_le_sq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l h : ℝ} (hlh : |l| + |h| < 1 / 8) (τ : ℝ) :
    |(((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
        h * ∫ v in Ioi (0 : ℝ),
          2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v| ≤
      (422400 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := by
  have hl : |l| < 1 / 8 := by linarith [abs_nonneg h]
  have hl_half : |l| < 1 / 2 := by linarith
  have hc : 0 < 1 / 8 - |l| - |h| := by linarith
  rw [setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_cos_log_eq hk hν hl_half (τ + h),
    setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_cos_log_eq hk hν hl_half τ]
  have hInt1 := integrableOn_Ioi_zero_two_mul_sinh_mul_cos_mul_arcLineInfiniteDyadicProfile
    hk hν hl_half (τ + h)
  have hInt2 := integrableOn_Ioi_zero_two_mul_sinh_mul_cos_mul_arcLineInfiniteDyadicProfile
    hk hν hl_half τ
  have hInt3 : IntegrableOn
      (fun v : ℝ => 2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)
      (Ioi (0 : ℝ)) := by
    simpa only [pow_one] using
      integrableOn_Ioi_zero_two_mul_pow_mul_sinh_mul_sin_mul_profile hk hν 1 hl τ
  have hInt12 : IntegrableOn
      (fun v : ℝ =>
        2 * Real.sinh (l * v) * Real.cos ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v -
          2 * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)
      (Ioi (0 : ℝ)) := hInt1.sub hInt2
  have hInt3h : IntegrableOn
      (fun v : ℝ =>
        h * (2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))
      (Ioi (0 : ℝ)) := hInt3.const_mul h
  rw [← integral_sub hInt1 hInt2, ← integral_const_mul, ← integral_add hInt12 hInt3h]
  set B := 2 * (105600 * ν.real univ * h ^ 2)
  have hdom_full : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  have hdom : IntegrableOn
      (fun v : ℝ => B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) (Ioi (0 : ℝ)) :=
    hdom_full.integrableOn
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      2 * Real.sinh (l * v) * Real.cos ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v -
        2 * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v +
        h * (2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))
    hdom (ae_restrict_mem measurableSet_Ioi |>.mono fun v _ => ?_)
  · have hle_full :
        (∫ v in Ioi (0 : ℝ), B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) ≤
          ∫ v : ℝ, B * Real.exp (-((1 / 8 - |l| - |h|) * |v|)) := by
      refine setIntegral_le_integral hdom_full (Eventually.of_forall fun v => ?_)
      have := measureReal_nonneg (μ := ν) (s := univ)
      dsimp [B]; positivity
    have hfull_eq :
        (∫ v : ℝ, B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) =
          (422400 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := by
      rw [integral_const_mul, integral_rexp_neg_mul_abs hc]
      dsimp [B]; ring
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (hle_full.trans hfull_eq.le)
  · have hfac :
        2 * Real.sinh (l * v) * Real.cos ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v -
          2 * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v +
          h * (2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
        2 * ((Real.sinh (l * v) *
          (Real.cos ((τ + h) * v) - Real.cos (τ * v) + (h * v) * Real.sin (τ * v))) *
          arcLineInfiniteDyadicProfile k ν v) := by ring
    rw [Real.norm_eq_abs, hfac, abs_mul, abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hker := abs_cos_add_sub_cos_add_mul_sin_le τ h v
    have hsinh : |Real.sinh (l * v)| ≤ Real.exp (|l| * |v|) := by
      rw [← abs_mul]; exact abs_sinh_le_exp_abs (l * v)
    have hprod :
        |Real.sinh (l * v)| *
          |Real.cos ((τ + h) * v) - Real.cos (τ * v) + (h * v) * Real.sin (τ * v)| ≤
        h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|) := by
      calc |Real.sinh (l * v)| *
              |Real.cos ((τ + h) * v) - Real.cos (τ * v) + (h * v) * Real.sin (τ * v)|
          ≤ Real.exp (|l| * |v|) * (h ^ 2 * v ^ 2 * Real.exp (|h| * |v|)) :=
            mul_le_mul hsinh hker (abs_nonneg _) (Real.exp_nonneg _)
        _ = h ^ 2 * v ^ 2 * (Real.exp (|l| * |v|) * Real.exp (|h| * |v|)) := by ring
        _ = h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|) := by
            rw [← Real.exp_add]; congr 2; ring
    have hprof := quadratic_shift_envelope_mul_abs_arcLineInfiniteDyadicProfile_le hk hν l h v
    have hstep := (mul_le_mul_of_nonneg_right hprod (abs_nonneg _)).trans hprof
    linarith

/-- **Exact horizontal partial derivative `∂_l Δ_k^{\cos}(l, τ)` (`k ≥ 2`, `|l| < 1/8`, `τ ∈ ℝ`):**
`(Δ_k^{\cos}(l + h, τ) − Δ_k^{\cos}(l, τ)) / h → ∫_{v > 0} 2 v cosh(lv) cos(τv) Φ_k(v) dv`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_imbalanceCos_sub_left_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (1 : ℝ),
              x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (∫ v in Ioi (0 : ℝ),
        2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) := by
  set D := ∫ v in Ioi (0 : ℝ),
    2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v
  set δ : ℝ := (1 / 8 - |l|) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  set C := (422400 * ν.real univ) / δ
  have hmaj : Tendsto (fun h : ℝ => C * |h|) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    have h0 : Tendsto (fun h : ℝ => C * |h|) (nhds 0) (nhds (C * |0|)) :=
      (continuous_const.mul continuous_abs).tendsto 0
    rw [abs_zero, mul_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
  have hmem1 : Ioo (-δ) δ ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith) hδ)
  have hmem2 : {(0 : ℝ)}ᶜ ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ := self_mem_nhdsWithin
  filter_upwards [hmem1, hmem2] with h hh hne
  have hh_ne : h ≠ 0 := mem_compl_singleton_iff.mp hne
  have hh_abs : |h| < δ := abs_lt.mpr hh
  have hlh : |l| + |h| < 1 / 8 := by dsimp [δ] at hh_abs; linarith
  have hdenom : δ ≤ 1 / 8 - |l| - |h| := by dsimp [δ] at hh_abs ⊢; linarith
  rw [Real.norm_eq_abs]
  have hdiv :
      (((∫ x in Ioi (1 : ℝ),
            x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) / h - D =
      ((((∫ x in Ioi (1 : ℝ),
              x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
        h * D) / h := by
    field_simp
  rw [hdiv, abs_div]
  have hrem := abs_imbalanceCos_diff_sub_linear_left_le_sq hk hν hlh τ
  have hC : 422400 * ν.real univ / (1 / 8 - |l| - |h|) ≤ C :=
    div_le_div_of_nonneg_left (by positivity) hδ hdenom
  have hnum :
      |(((∫ x in Ioi (1 : ℝ),
              x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
        h * D| ≤ C * |h| ^ 2 := by
    calc |(((∫ x in Ioi (1 : ℝ),
                x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
          h * D|
        ≤ (422400 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := hrem
      _ ≤ C * h ^ 2 := mul_le_mul_of_nonneg_right hC (sq_nonneg h)
      _ = C * |h| ^ 2 := by rw [sq_abs]
  have habs_pos : 0 < |h| := abs_pos.mpr hh_ne
  exact (div_le_iff₀ habs_pos).mpr (by calc
    |(((∫ x in Ioi (1 : ℝ),
            x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
      h * D| ≤ C * |h| ^ 2 := hnum
    _ = C * |h| * |h| := by ring)

/-- **Exact vertical partial derivative `∂_τ Δ_k^{\sin}(l, τ)` (`k ≥ 2`, `|l| < 1/8`, `τ ∈ ℝ`):**
`(Δ_k^{\sin}(l, τ + h) − Δ_k^{\sin}(l, τ)) / h → ∫_{v > 0} 2 v cosh(lv) cos(τv) Φ_k(v) dv`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_imbalanceSin_sub_right_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (∫ v in Ioi (0 : ℝ),
        2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) := by
  set D := ∫ v in Ioi (0 : ℝ),
    2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v
  set δ : ℝ := (1 / 8 - |l|) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  set C := (422400 * ν.real univ) / δ
  have hmaj : Tendsto (fun h : ℝ => C * |h|) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    have h0 : Tendsto (fun h : ℝ => C * |h|) (nhds 0) (nhds (C * |0|)) :=
      (continuous_const.mul continuous_abs).tendsto 0
    rw [abs_zero, mul_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
  have hmem1 : Ioo (-δ) δ ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith) hδ)
  have hmem2 : {(0 : ℝ)}ᶜ ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ := self_mem_nhdsWithin
  filter_upwards [hmem1, hmem2] with h hh hne
  have hh_ne : h ≠ 0 := mem_compl_singleton_iff.mp hne
  have hh_abs : |h| < δ := abs_lt.mpr hh
  have hlh : |l| + |h| < 1 / 8 := by dsimp [δ] at hh_abs; linarith
  have hdenom : δ ≤ 1 / 8 - |l| - |h| := by dsimp [δ] at hh_abs ⊢; linarith
  rw [Real.norm_eq_abs]
  have hdiv :
      (((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) / h - D =
      ((((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
        h * D) / h := by
    field_simp
  rw [hdiv, abs_div]
  have hrem := abs_imbalanceSin_diff_sub_linear_right_le_sq hk hν hlh τ
  have hC : 422400 * ν.real univ / (1 / 8 - |l| - |h|) ≤ C :=
    div_le_div_of_nonneg_left (by positivity) hδ hdenom
  have hnum :
      |(((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
        h * D| ≤ C * |h| ^ 2 := by
    calc |(((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
          h * D|
        ≤ (422400 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := hrem
      _ ≤ C * h ^ 2 := mul_le_mul_of_nonneg_right hC (sq_nonneg h)
      _ = C * |h| ^ 2 := by rw [sq_abs]
  have habs_pos : 0 < |h| := abs_pos.mpr hh_ne
  exact (div_le_iff₀ habs_pos).mpr (by calc
    |(((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
      h * D| ≤ C * |h| ^ 2 := hnum
    _ = C * |h| * |h| := by ring)

/-- **First Cauchy–Riemann Equation `∂_l Δ_k^{\cos}(l, τ) = ∂_τ Δ_k^{\sin}(l, τ)` for the
origin–infinity complex Mellin imbalance (`k ≥ 2`, `|l| < 1/8`, `τ ∈ ℝ`):**
`((Δ_k^{\cos}(l + h, τ) − Δ_k^{\cos}(l, τ)) − (Δ_k^{\sin}(l, τ + h) − Δ_k^{\sin}(l, τ))) / h → 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_imbalance_cauchyRiemann_first_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (1 : ℝ),
                x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
          (((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
  have h1 := tendsto_div_imbalanceCos_sub_left_nhds_zero hk hν hl τ
  have h2 := tendsto_div_imbalanceSin_sub_right_nhds_zero hk hν hl τ
  have hsub := h1.sub h2
  rw [sub_self] at hsub
  exact hsub.congr (fun h => by ring)

/-- **Exact horizontal partial derivative `∂_l Δ_k^{\sin}(l, τ)` (`k ≥ 2`, `|l| < 1/8`, `τ ∈ ℝ`):**
`(Δ_k^{\sin}(l + h, τ) − Δ_k^{\sin}(l, τ)) / h → ∫_{v > 0} 2 v sinh(lv) sin(τv) Φ_k(v) dv`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_imbalanceSin_sub_left_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (1 : ℝ),
              x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (∫ v in Ioi (0 : ℝ),
        2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) := by
  set D := ∫ v in Ioi (0 : ℝ),
    2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v
  set δ : ℝ := (1 / 8 - |l|) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  set C := (422400 * ν.real univ) / δ
  have hmaj : Tendsto (fun h : ℝ => C * |h|) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    have h0 : Tendsto (fun h : ℝ => C * |h|) (nhds 0) (nhds (C * |0|)) :=
      (continuous_const.mul continuous_abs).tendsto 0
    rw [abs_zero, mul_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
  have hmem1 : Ioo (-δ) δ ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith) hδ)
  have hmem2 : {(0 : ℝ)}ᶜ ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ := self_mem_nhdsWithin
  filter_upwards [hmem1, hmem2] with h hh hne
  have hh_ne : h ≠ 0 := mem_compl_singleton_iff.mp hne
  have hh_abs : |h| < δ := abs_lt.mpr hh
  have hlh : |l| + |h| < 1 / 8 := by dsimp [δ] at hh_abs; linarith
  have hdenom : δ ≤ 1 / 8 - |l| - |h| := by dsimp [δ] at hh_abs ⊢; linarith
  rw [Real.norm_eq_abs]
  have hdiv :
      (((∫ x in Ioi (1 : ℝ),
            x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) / h - D =
      ((((∫ x in Ioi (1 : ℝ),
              x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
        h * D) / h := by
    field_simp
  rw [hdiv, abs_div]
  have hrem := abs_imbalanceSin_diff_sub_linear_left_le_sq hk hν hlh τ
  have hC : 422400 * ν.real univ / (1 / 8 - |l| - |h|) ≤ C :=
    div_le_div_of_nonneg_left (by positivity) hδ hdenom
  have hnum :
      |(((∫ x in Ioi (1 : ℝ),
              x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
        h * D| ≤ C * |h| ^ 2 := by
    calc |(((∫ x in Ioi (1 : ℝ),
                x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
          h * D|
        ≤ (422400 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := hrem
      _ ≤ C * h ^ 2 := mul_le_mul_of_nonneg_right hC (sq_nonneg h)
      _ = C * |h| ^ 2 := by rw [sq_abs]
  have habs_pos : 0 < |h| := abs_pos.mpr hh_ne
  exact (div_le_iff₀ habs_pos).mpr (by calc
    |(((∫ x in Ioi (1 : ℝ),
            x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
      h * D| ≤ C * |h| ^ 2 := hnum
    _ = C * |h| * |h| := by ring)

/-- **Exact vertical partial derivative `∂_τ Δ_k^{\cos}(l, τ)` (`k ≥ 2`, `|l| < 1/8`, `τ ∈ ℝ`):**
`(Δ_k^{\cos}(l, τ + h) − Δ_k^{\cos}(l, τ)) / h → −∫_{v > 0} 2 v sinh(lv) sin(τv) Φ_k(v) dv`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_imbalanceCos_sub_right_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (-(∫ v in Ioi (0 : ℝ),
        2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) := by
  set D := ∫ v in Ioi (0 : ℝ),
    2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v
  set δ : ℝ := (1 / 8 - |l|) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  set C := (422400 * ν.real univ) / δ
  have hmaj : Tendsto (fun h : ℝ => C * |h|) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    have h0 : Tendsto (fun h : ℝ => C * |h|) (nhds 0) (nhds (C * |0|)) :=
      (continuous_const.mul continuous_abs).tendsto 0
    rw [abs_zero, mul_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
  have hmem1 : Ioo (-δ) δ ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith) hδ)
  have hmem2 : {(0 : ℝ)}ᶜ ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ := self_mem_nhdsWithin
  filter_upwards [hmem1, hmem2] with h hh hne
  have hh_ne : h ≠ 0 := mem_compl_singleton_iff.mp hne
  have hh_abs : |h| < δ := abs_lt.mpr hh
  have hlh : |l| + |h| < 1 / 8 := by dsimp [δ] at hh_abs; linarith
  have hdenom : δ ≤ 1 / 8 - |l| - |h| := by dsimp [δ] at hh_abs ⊢; linarith
  rw [Real.norm_eq_abs]
  have hdiv :
      (((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) / h -
        (-D) =
      ((((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
        h * D) / h := by
    rw [sub_neg_eq_add, add_div, mul_div_cancel_left₀ D hh_ne]
  rw [hdiv, abs_div]
  have hrem := abs_imbalanceCos_diff_sub_linear_right_le_sq hk hν hlh τ
  have hC : 422400 * ν.real univ / (1 / 8 - |l| - |h|) ≤ C :=
    div_le_div_of_nonneg_left (by positivity) hδ hdenom
  have hnum :
      |(((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
        h * D| ≤ C * |h| ^ 2 := by
    calc |(((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
          h * D|
        ≤ (422400 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := hrem
      _ ≤ C * h ^ 2 := mul_le_mul_of_nonneg_right hC (sq_nonneg h)
      _ = C * |h| ^ 2 := by rw [sq_abs]
  have habs_pos : 0 < |h| := abs_pos.mpr hh_ne
  exact (div_le_iff₀ habs_pos).mpr (by calc
    |(((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
      h * D| ≤ C * |h| ^ 2 := hnum
    _ = C * |h| * |h| := by ring)

/-- **Second Cauchy–Riemann Equation `∂_l Δ_k^{\sin}(l, τ) = −∂_τ Δ_k^{\cos}(l, τ)` for the
origin–infinity complex Mellin imbalance (`k ≥ 2`, `|l| < 1/8`, `τ ∈ ℝ`):**
`((Δ_k^{\sin}(l + h, τ) − Δ_k^{\sin}(l, τ)) + (Δ_k^{\cos}(l, τ + h) − Δ_k^{\cos}(l, τ))) / h → 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_imbalance_cauchyRiemann_second_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (1 : ℝ),
                x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
          (((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
  have h1 := tendsto_div_imbalanceSin_sub_left_nhds_zero hk hν hl τ
  have h2 := tendsto_div_imbalanceCos_sub_right_nhds_zero hk hν hl τ
  have hadd := h1.add h2
  rw [add_neg_cancel] at hadd
  exact hadd.congr (fun h => by ring)

/-- **Height-uniform quartic `O(h⁴)` five-point discrete Laplacian bound for the origin–infinity
cosine imbalance `Δ_k^{\cos}(l, τ)` (`k ≥ 2`, `|l| + |h| < 1/8`, `τ ∈ ℝ`):**
`|(Δ_k^{\cos}(l + h, τ) + Δ_k^{\cos}(l − h, τ) − 2 Δ_k^{\cos}(l, τ)) +
  (Δ_k^{\cos}(l, τ + h) + Δ_k^{\cos}(l, τ − h) − 2 Δ_k^{\cos}(l, τ))| ≤
  (54067200 · ν.real univ / (1/8 − |l| − |h|)) · h⁴`. -/
theorem abs_imbalanceCos_fivePoint_laplacian_le_pow_four
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l h : ℝ} (hlh : |l| + |h| < 1 / 8) (τ : ℝ) :
    |((((∫ x in Ioi (1 : ℝ),
              x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          2 * ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
        (((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          2 * ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)))| ≤
      (54067200 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 4 := by
  have hl_half : |l| < 1 / 2 := by linarith [abs_nonneg h]
  have hlph_half : |l + h| < 1 / 2 := by linarith [abs_add_le l h]
  have hlmh_half : |l - h| < 1 / 2 := by linarith [abs_sub l h]
  have hc : 0 < 1 / 8 - |l| - |h| := by linarith
  rw [setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_cos_log_eq hk hν hlph_half τ,
    setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_cos_log_eq hk hν hlmh_half τ,
    setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_cos_log_eq hk hν hl_half τ,
    setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_cos_log_eq hk hν hl_half (τ + h),
    setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_cos_log_eq hk hν hl_half (τ - h)]
  have hI_lph := integrableOn_Ioi_zero_two_mul_sinh_mul_cos_mul_arcLineInfiniteDyadicProfile
    hk hν hlph_half τ
  have hI_lmh := integrableOn_Ioi_zero_two_mul_sinh_mul_cos_mul_arcLineInfiniteDyadicProfile
    hk hν hlmh_half τ
  have hI_l := integrableOn_Ioi_zero_two_mul_sinh_mul_cos_mul_arcLineInfiniteDyadicProfile
    hk hν hl_half τ
  have hI_tph := integrableOn_Ioi_zero_two_mul_sinh_mul_cos_mul_arcLineInfiniteDyadicProfile
    hk hν hl_half (τ + h)
  have hI_tmh := integrableOn_Ioi_zero_two_mul_sinh_mul_cos_mul_arcLineInfiniteDyadicProfile
    hk hν hl_half (τ - h)
  have hI_l12 : IntegrableOn
      (fun v : ℝ =>
        2 * Real.sinh ((l + h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v +
          2 * Real.sinh ((l - h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)
      (Ioi (0 : ℝ)) := hI_lph.add hI_lmh
  have hI_2l : IntegrableOn
      (fun v : ℝ =>
        2 * (2 * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))
      (Ioi (0 : ℝ)) := hI_l.const_mul 2
  have hI_left : IntegrableOn
      (fun v : ℝ =>
        2 * Real.sinh ((l + h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v +
          2 * Real.sinh ((l - h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          2 * (2 * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))
      (Ioi (0 : ℝ)) := hI_l12.sub hI_2l
  have hI_t12 : IntegrableOn
      (fun v : ℝ =>
        2 * Real.sinh (l * v) * Real.cos ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v +
          2 * Real.sinh (l * v) * Real.cos ((τ - h) * v) * arcLineInfiniteDyadicProfile k ν v)
      (Ioi (0 : ℝ)) := hI_tph.add hI_tmh
  have hI_right : IntegrableOn
      (fun v : ℝ =>
        2 * Real.sinh (l * v) * Real.cos ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v +
          2 * Real.sinh (l * v) * Real.cos ((τ - h) * v) * arcLineInfiniteDyadicProfile k ν v -
          2 * (2 * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))
      (Ioi (0 : ℝ)) := hI_t12.sub hI_2l
  rw [← integral_add hI_lph hI_lmh, ← integral_const_mul, ← integral_sub hI_l12 hI_2l,
    ← integral_add hI_tph hI_tmh, ← integral_sub hI_t12 hI_2l, ← integral_add hI_left hI_right]
  set B := 4 * (6758400 * ν.real univ * h ^ 4)
  have hdom_full : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  have hdom : IntegrableOn
      (fun v : ℝ => B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) (Ioi (0 : ℝ)) :=
    hdom_full.integrableOn
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      (2 * Real.sinh ((l + h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v +
        2 * Real.sinh ((l - h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
        2 * (2 * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
      (2 * Real.sinh (l * v) * Real.cos ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v +
        2 * Real.sinh (l * v) * Real.cos ((τ - h) * v) * arcLineInfiniteDyadicProfile k ν v -
        2 * (2 * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)))
    hdom (ae_restrict_mem measurableSet_Ioi |>.mono fun v _ => ?_)
  · have hle_full :
        (∫ v in Ioi (0 : ℝ), B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) ≤
          ∫ v : ℝ, B * Real.exp (-((1 / 8 - |l| - |h|) * |v|)) := by
      refine setIntegral_le_integral hdom_full (Eventually.of_forall fun v => ?_)
      have := measureReal_nonneg (μ := ν) (s := univ)
      dsimp [B]; positivity
    have hfull_eq :
        (∫ v : ℝ, B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) =
          (54067200 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 4 := by
      rw [integral_const_mul, integral_rexp_neg_mul_abs hc]
      dsimp [B]; ring
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (hle_full.trans hfull_eq.le)
  · have hfac :
        (2 * Real.sinh ((l + h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v +
          2 * Real.sinh ((l - h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          2 * (2 * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
        (2 * Real.sinh (l * v) * Real.cos ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v +
          2 * Real.sinh (l * v) * Real.cos ((τ - h) * v) * arcLineInfiniteDyadicProfile k ν v -
          2 * (2 * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) =
        2 * (((Real.sinh ((l + h) * v) + Real.sinh ((l - h) * v) -
              2 * Real.sinh (l * v) - (h * v) ^ 2 * Real.sinh (l * v)) * Real.cos (τ * v) +
            Real.sinh (l * v) * (Real.cos ((τ + h) * v) + Real.cos ((τ - h) * v) -
              2 * Real.cos (τ * v) + (h * v) ^ 2 * Real.cos (τ * v))) *
          arcLineInfiniteDyadicProfile k ν v) := by ring
    rw [Real.norm_eq_abs, hfac, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hker1 := abs_sinh_central_diff_sub_sq_mul_sinh_le l h v
    have hker2 := abs_cos_central_diff_add_sq_mul_cos_le τ h v
    have hsinh : |Real.sinh (l * v)| ≤ Real.exp (|l| * |v|) := by
      rw [← abs_mul]; exact abs_sinh_le_exp_abs (l * v)
    have hcos : |Real.cos (τ * v)| ≤ 1 := Real.abs_cos_le_one (τ * v)
    have hA :
        |(Real.sinh ((l + h) * v) + Real.sinh ((l - h) * v) -
            2 * Real.sinh (l * v) - (h * v) ^ 2 * Real.sinh (l * v)) * Real.cos (τ * v)| ≤
        (h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) := by
      rw [abs_mul]
      calc |Real.sinh ((l + h) * v) + Real.sinh ((l - h) * v) -
              2 * Real.sinh (l * v) - (h * v) ^ 2 * Real.sinh (l * v)| * |Real.cos (τ * v)|
          ≤ ((h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|)) * 1 :=
            mul_le_mul hker1 hcos (abs_nonneg _) (by positivity)
        _ = (h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) := mul_one _
    have hB :
        |Real.sinh (l * v) * (Real.cos ((τ + h) * v) + Real.cos ((τ - h) * v) -
            2 * Real.cos (τ * v) + (h * v) ^ 2 * Real.cos (τ * v))| ≤
        (h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) := by
      rw [abs_mul]
      calc |Real.sinh (l * v)| *
              |Real.cos ((τ + h) * v) + Real.cos ((τ - h) * v) -
                2 * Real.cos (τ * v) + (h * v) ^ 2 * Real.cos (τ * v)|
          ≤ Real.exp (|l| * |v|) * ((h ^ 4 * v ^ 4 / 12) * Real.exp (|h| * |v|)) :=
            mul_le_mul hsinh hker2 (abs_nonneg _) (Real.exp_nonneg _)
        _ = (h ^ 4 * v ^ 4 / 12) * (Real.exp (|l| * |v|) * Real.exp (|h| * |v|)) := by ring
        _ = (h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) := by
            rw [← Real.exp_add]; congr 2; ring
    have hsum_ker :
        |(Real.sinh ((l + h) * v) + Real.sinh ((l - h) * v) -
            2 * Real.sinh (l * v) - (h * v) ^ 2 * Real.sinh (l * v)) * Real.cos (τ * v) +
          Real.sinh (l * v) * (Real.cos ((τ + h) * v) + Real.cos ((τ - h) * v) -
            2 * Real.cos (τ * v) + (h * v) ^ 2 * Real.cos (τ * v))| ≤
        2 * ((h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|)) := by
      calc |(Real.sinh ((l + h) * v) + Real.sinh ((l - h) * v) -
              2 * Real.sinh (l * v) - (h * v) ^ 2 * Real.sinh (l * v)) * Real.cos (τ * v) +
            Real.sinh (l * v) * (Real.cos ((τ + h) * v) + Real.cos ((τ - h) * v) -
              2 * Real.cos (τ * v) + (h * v) ^ 2 * Real.cos (τ * v))|
          ≤ |(Real.sinh ((l + h) * v) + Real.sinh ((l - h) * v) -
              2 * Real.sinh (l * v) - (h * v) ^ 2 * Real.sinh (l * v)) * Real.cos (τ * v)| +
            |Real.sinh (l * v) * (Real.cos ((τ + h) * v) + Real.cos ((τ - h) * v) -
              2 * Real.cos (τ * v) + (h * v) ^ 2 * Real.cos (τ * v))| := abs_add_le _ _
        _ ≤ (h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) +
            (h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) := add_le_add hA hB
        _ = 2 * ((h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|)) := by ring
    have hprof := quartic_shift_mul_abs_arcLineInfiniteDyadicProfile_le hk hν l h v
    have hstep := mul_le_mul_of_nonneg_right hsum_ker (abs_nonneg (arcLineInfiniteDyadicProfile k ν v))
    linarith

/-- **Height-uniform quartic `O(h⁴)` five-point discrete Laplacian bound for the origin–infinity
sine imbalance `Δ_k^{\sin}(l, τ)` (`k ≥ 2`, `|l| + |h| < 1/8`, `τ ∈ ℝ`):**
`|(Δ_k^{\sin}(l + h, τ) + Δ_k^{\sin}(l − h, τ) − 2 Δ_k^{\sin}(l, τ)) +
  (Δ_k^{\sin}(l, τ + h) + Δ_k^{\sin}(l, τ − h) − 2 Δ_k^{\sin}(l, τ))| ≤
  (54067200 · ν.real univ / (1/8 − |l| − |h|)) · h⁴`. -/
theorem abs_imbalanceSin_fivePoint_laplacian_le_pow_four
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l h : ℝ} (hlh : |l| + |h| < 1 / 8) (τ : ℝ) :
    |((((∫ x in Ioi (1 : ℝ),
              x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          2 * ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
        (((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          2 * ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)))| ≤
      (54067200 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 4 := by
  have hl_half : |l| < 1 / 2 := by linarith [abs_nonneg h]
  have hlph_half : |l + h| < 1 / 2 := by linarith [abs_add_le l h]
  have hlmh_half : |l - h| < 1 / 2 := by linarith [abs_sub l h]
  have hc : 0 < 1 / 8 - |l| - |h| := by linarith
  rw [setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_sin_log_eq hk hν hlph_half τ,
    setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_sin_log_eq hk hν hlmh_half τ,
    setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_sin_log_eq hk hν hl_half τ,
    setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_sin_log_eq hk hν hl_half (τ + h),
    setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_sin_log_eq hk hν hl_half (τ - h)]
  have hI_lph := integrableOn_Ioi_zero_two_mul_cosh_mul_sin_mul_arcLineInfiniteDyadicProfile
    hk hν hlph_half τ
  have hI_lmh := integrableOn_Ioi_zero_two_mul_cosh_mul_sin_mul_arcLineInfiniteDyadicProfile
    hk hν hlmh_half τ
  have hI_l := integrableOn_Ioi_zero_two_mul_cosh_mul_sin_mul_arcLineInfiniteDyadicProfile
    hk hν hl_half τ
  have hI_tph := integrableOn_Ioi_zero_two_mul_cosh_mul_sin_mul_arcLineInfiniteDyadicProfile
    hk hν hl_half (τ + h)
  have hI_tmh := integrableOn_Ioi_zero_two_mul_cosh_mul_sin_mul_arcLineInfiniteDyadicProfile
    hk hν hl_half (τ - h)
  have hI_l12 : IntegrableOn
      (fun v : ℝ =>
        2 * Real.cosh ((l + h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v +
          2 * Real.cosh ((l - h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)
      (Ioi (0 : ℝ)) := hI_lph.add hI_lmh
  have hI_2l : IntegrableOn
      (fun v : ℝ =>
        2 * (2 * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))
      (Ioi (0 : ℝ)) := hI_l.const_mul 2
  have hI_left : IntegrableOn
      (fun v : ℝ =>
        2 * Real.cosh ((l + h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v +
          2 * Real.cosh ((l - h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          2 * (2 * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))
      (Ioi (0 : ℝ)) := hI_l12.sub hI_2l
  have hI_t12 : IntegrableOn
      (fun v : ℝ =>
        2 * Real.cosh (l * v) * Real.sin ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v +
          2 * Real.cosh (l * v) * Real.sin ((τ - h) * v) * arcLineInfiniteDyadicProfile k ν v)
      (Ioi (0 : ℝ)) := hI_tph.add hI_tmh
  have hI_right : IntegrableOn
      (fun v : ℝ =>
        2 * Real.cosh (l * v) * Real.sin ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v +
          2 * Real.cosh (l * v) * Real.sin ((τ - h) * v) * arcLineInfiniteDyadicProfile k ν v -
          2 * (2 * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))
      (Ioi (0 : ℝ)) := hI_t12.sub hI_2l
  rw [← integral_add hI_lph hI_lmh, ← integral_const_mul, ← integral_sub hI_l12 hI_2l,
    ← integral_add hI_tph hI_tmh, ← integral_sub hI_t12 hI_2l, ← integral_add hI_left hI_right]
  set B := 4 * (6758400 * ν.real univ * h ^ 4)
  have hdom_full : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  have hdom : IntegrableOn
      (fun v : ℝ => B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) (Ioi (0 : ℝ)) :=
    hdom_full.integrableOn
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      (2 * Real.cosh ((l + h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v +
        2 * Real.cosh ((l - h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
        2 * (2 * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
      (2 * Real.cosh (l * v) * Real.sin ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v +
        2 * Real.cosh (l * v) * Real.sin ((τ - h) * v) * arcLineInfiniteDyadicProfile k ν v -
        2 * (2 * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)))
    hdom (ae_restrict_mem measurableSet_Ioi |>.mono fun v _ => ?_)
  · have hle_full :
        (∫ v in Ioi (0 : ℝ), B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) ≤
          ∫ v : ℝ, B * Real.exp (-((1 / 8 - |l| - |h|) * |v|)) := by
      refine setIntegral_le_integral hdom_full (Eventually.of_forall fun v => ?_)
      have := measureReal_nonneg (μ := ν) (s := univ)
      dsimp [B]; positivity
    have hfull_eq :
        (∫ v : ℝ, B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) =
          (54067200 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 4 := by
      rw [integral_const_mul, integral_rexp_neg_mul_abs hc]
      dsimp [B]; ring
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (hle_full.trans hfull_eq.le)
  · have hfac :
        (2 * Real.cosh ((l + h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v +
          2 * Real.cosh ((l - h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          2 * (2 * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
        (2 * Real.cosh (l * v) * Real.sin ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v +
          2 * Real.cosh (l * v) * Real.sin ((τ - h) * v) * arcLineInfiniteDyadicProfile k ν v -
          2 * (2 * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) =
        2 * (((Real.cosh ((l + h) * v) + Real.cosh ((l - h) * v) -
              2 * Real.cosh (l * v) - (h * v) ^ 2 * Real.cosh (l * v)) * Real.sin (τ * v) +
            Real.cosh (l * v) * (Real.sin ((τ + h) * v) + Real.sin ((τ - h) * v) -
              2 * Real.sin (τ * v) + (h * v) ^ 2 * Real.sin (τ * v))) *
          arcLineInfiniteDyadicProfile k ν v) := by ring
    rw [Real.norm_eq_abs, hfac, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hker1 := abs_cosh_central_diff_sub_sq_mul_cosh_le l h v
    have hker2 := abs_sin_central_diff_add_sq_mul_sin_le τ h v
    have hcosh : Real.cosh (l * v) ≤ Real.exp (|l| * |v|) := by
      rw [← abs_mul]; exact cosh_le_exp_abs (l * v)
    have hsin : |Real.sin (τ * v)| ≤ 1 := Real.abs_sin_le_one (τ * v)
    have hA :
        |(Real.cosh ((l + h) * v) + Real.cosh ((l - h) * v) -
            2 * Real.cosh (l * v) - (h * v) ^ 2 * Real.cosh (l * v)) * Real.sin (τ * v)| ≤
        (h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) := by
      rw [abs_mul]
      calc |Real.cosh ((l + h) * v) + Real.cosh ((l - h) * v) -
              2 * Real.cosh (l * v) - (h * v) ^ 2 * Real.cosh (l * v)| * |Real.sin (τ * v)|
          ≤ ((h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|)) * 1 :=
            mul_le_mul hker1 hsin (abs_nonneg _) (by positivity)
        _ = (h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) := mul_one _
    have hB :
        |Real.cosh (l * v) * (Real.sin ((τ + h) * v) + Real.sin ((τ - h) * v) -
            2 * Real.sin (τ * v) + (h * v) ^ 2 * Real.sin (τ * v))| ≤
        (h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) := by
      rw [abs_mul, abs_of_pos (Real.cosh_pos (l * v))]
      calc Real.cosh (l * v) *
              |Real.sin ((τ + h) * v) + Real.sin ((τ - h) * v) -
                2 * Real.sin (τ * v) + (h * v) ^ 2 * Real.sin (τ * v)|
          ≤ Real.exp (|l| * |v|) * ((h ^ 4 * v ^ 4 / 12) * Real.exp (|h| * |v|)) :=
            mul_le_mul hcosh hker2 (abs_nonneg _) (Real.exp_nonneg _)
        _ = (h ^ 4 * v ^ 4 / 12) * (Real.exp (|l| * |v|) * Real.exp (|h| * |v|)) := by ring
        _ = (h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) := by
            rw [← Real.exp_add]; congr 2; ring
    have hsum_ker :
        |(Real.cosh ((l + h) * v) + Real.cosh ((l - h) * v) -
            2 * Real.cosh (l * v) - (h * v) ^ 2 * Real.cosh (l * v)) * Real.sin (τ * v) +
          Real.cosh (l * v) * (Real.sin ((τ + h) * v) + Real.sin ((τ - h) * v) -
            2 * Real.sin (τ * v) + (h * v) ^ 2 * Real.sin (τ * v))| ≤
        2 * ((h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|)) := by
      calc |(Real.cosh ((l + h) * v) + Real.cosh ((l - h) * v) -
              2 * Real.cosh (l * v) - (h * v) ^ 2 * Real.cosh (l * v)) * Real.sin (τ * v) +
            Real.cosh (l * v) * (Real.sin ((τ + h) * v) + Real.sin ((τ - h) * v) -
              2 * Real.sin (τ * v) + (h * v) ^ 2 * Real.sin (τ * v))|
          ≤ |(Real.cosh ((l + h) * v) + Real.cosh ((l - h) * v) -
              2 * Real.cosh (l * v) - (h * v) ^ 2 * Real.cosh (l * v)) * Real.sin (τ * v)| +
            |Real.cosh (l * v) * (Real.sin ((τ + h) * v) + Real.sin ((τ - h) * v) -
              2 * Real.sin (τ * v) + (h * v) ^ 2 * Real.sin (τ * v))| := abs_add_le _ _
        _ ≤ (h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) +
            (h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|) := add_le_add hA hB
        _ = 2 * ((h ^ 4 * v ^ 4 / 12) * Real.exp ((|l| + |h|) * |v|)) := by ring
    have hprof := quartic_shift_mul_abs_arcLineInfiniteDyadicProfile_le hk hν l h v
    have hstep := mul_le_mul_of_nonneg_right hsum_ker (abs_nonneg (arcLineInfiniteDyadicProfile k ν v))
    linarith

/-- **Normalized five-point harmonic Laplacian vanishing for `Δ_k^{\cos}(l, τ)`
(`k ≥ 2`, `|l| < 1/8`, `τ ∈ ℝ`):**
`((Δ_k^{\cos}(l + h, τ) + Δ_k^{\cos}(l − h, τ) − 2 Δ_k^{\cos}(l, τ)) +
  (Δ_k^{\cos}(l, τ + h) + Δ_k^{\cos}(l, τ − h) − 2 Δ_k^{\cos}(l, τ))) / h² → 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_imbalanceCos_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (1 : ℝ),
                x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            ((∫ x in Ioi (1 : ℝ),
                x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
          (((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
  set δ : ℝ := (1 / 8 - |l|) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  set C := (54067200 * ν.real univ) / δ
  have hmaj : Tendsto (fun h : ℝ => C * h ^ 2) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    have h0 : Tendsto (fun h : ℝ => C * h ^ 2) (nhds 0) (nhds 0) := by
      simpa using ((continuous_id.pow 2).tendsto 0).const_mul C
    exact h0.mono_left nhdsWithin_le_nhds
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
  have hmem1 : Ioo (-δ) δ ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith) hδ)
  filter_upwards [hmem1, self_mem_nhdsWithin] with h hh hne
  have hh_ne : h ≠ 0 := mem_compl_singleton_iff.mp hne
  have hh_abs : |h| < δ := abs_lt.mpr hh
  have hlh : |l| + |h| < 1 / 8 := by dsimp [δ] at hh_abs; linarith
  have hdenom : δ ≤ 1 / 8 - |l| - |h| := by dsimp [δ] at hh_abs ⊢; linarith
  have hsq_pos : 0 < h ^ 2 := sq_pos_of_ne_zero hh_ne
  rw [sub_zero, Real.norm_eq_abs, abs_div, abs_of_pos hsq_pos]
  have hrem := abs_imbalanceCos_fivePoint_laplacian_le_pow_four hk hν hlh τ
  have hC : 54067200 * ν.real univ / (1 / 8 - |l| - |h|) ≤ C :=
    div_le_div_of_nonneg_left (by positivity) hδ hdenom
  have hle := hrem.trans (mul_le_mul_of_nonneg_right hC (by positivity))
  exact (div_le_iff₀ hsq_pos).mpr (by linarith [hle, (by ring : C * h ^ 2 * h ^ 2 = C * h ^ 4)])

/-- **Normalized five-point harmonic Laplacian vanishing for `Δ_k^{\sin}(l, τ)`
(`k ≥ 2`, `|l| < 1/8`, `τ ∈ ℝ`):**
`((Δ_k^{\sin}(l + h, τ) + Δ_k^{\sin}(l − h, τ) − 2 Δ_k^{\sin}(l, τ)) +
  (Δ_k^{\sin}(l, τ + h) + Δ_k^{\sin}(l, τ − h) − 2 Δ_k^{\sin}(l, τ))) / h² → 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_imbalanceSin_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (1 : ℝ),
                x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            ((∫ x in Ioi (1 : ℝ),
                x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
          (((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
  set δ : ℝ := (1 / 8 - |l|) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  set C := (54067200 * ν.real univ) / δ
  have hmaj : Tendsto (fun h : ℝ => C * h ^ 2) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    have h0 : Tendsto (fun h : ℝ => C * h ^ 2) (nhds 0) (nhds 0) := by
      simpa using ((continuous_id.pow 2).tendsto 0).const_mul C
    exact h0.mono_left nhdsWithin_le_nhds
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
  have hmem1 : Ioo (-δ) δ ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith) hδ)
  filter_upwards [hmem1, self_mem_nhdsWithin] with h hh hne
  have hh_ne : h ≠ 0 := mem_compl_singleton_iff.mp hne
  have hh_abs : |h| < δ := abs_lt.mpr hh
  have hlh : |l| + |h| < 1 / 8 := by dsimp [δ] at hh_abs; linarith
  have hdenom : δ ≤ 1 / 8 - |l| - |h| := by dsimp [δ] at hh_abs ⊢; linarith
  have hsq_pos : 0 < h ^ 2 := sq_pos_of_ne_zero hh_ne
  rw [sub_zero, Real.norm_eq_abs, abs_div, abs_of_pos hsq_pos]
  have hrem := abs_imbalanceSin_fivePoint_laplacian_le_pow_four hk hν hlh τ
  have hC : 54067200 * ν.real univ / (1 / 8 - |l| - |h|) ≤ C :=
    div_le_div_of_nonneg_left (by positivity) hδ hdenom
  have hle := hrem.trans (mul_le_mul_of_nonneg_right hC (by positivity))
  exact (div_le_iff₀ hsq_pos).mpr (by linarith [hle, (by ring : C * h ^ 2 * h ^ 2 = C * h ^ 4)])


/-! ## Section 3: Sector Modulus Parallelogram Law, Polarization Identity, and Zero-Locus Sector Equipartition -/

/-- **Universal sector parallelogram identity:**
For all `c_pos, s_pos, c_neg, s_neg : ℝ`,
`((c_pos + c_neg)² + (s_pos + s_neg)²) + ((c_pos − c_neg)² + (s_pos − s_neg)²) =
  2 ((c_pos² + s_pos²) + (c_neg² + s_neg²))`. -/
theorem sector_parallelogram_law (c_pos s_pos c_neg s_neg : ℝ) :
    ((c_pos + c_neg) ^ 2 + (s_pos + s_neg) ^ 2) +
      ((c_pos - c_neg) ^ 2 + (s_pos - s_neg) ^ 2) =
    2 * ((c_pos ^ 2 + s_pos ^ 2) + (c_neg ^ 2 + s_neg ^ 2)) := by
  ring

/-- **Universal sector modulus imbalance polarization identity:**
For all `c_pos, s_pos, c_neg, s_neg : ℝ`,
`(c_pos² + s_pos²) − (c_neg² + s_neg²) =
  (c_pos + c_neg) (c_pos − c_neg) + (s_pos + s_neg) (s_pos − s_neg)`. -/
theorem sector_polarization_identity (c_pos s_pos c_neg s_neg : ℝ) :
    (c_pos ^ 2 + s_pos ^ 2) - (c_neg ^ 2 + s_neg ^ 2) =
      (c_pos + c_neg) * (c_pos - c_neg) + (s_pos + s_neg) * (s_pos - s_neg) := by
  ring

/-- **Universal Brahmagupta–Fibonacci sector modulus decomposition:**
For all `c_pos, s_pos, c_neg, s_neg : ℝ`,
`((c_pos + c_neg)² + (s_pos + s_neg)²) ((c_pos − c_neg)² + (s_pos − s_neg)²) =
  ((c_pos² + s_pos²) − (c_neg² + s_neg²))² +
    ((c_pos + c_neg) (s_pos − s_neg) − (s_pos + s_neg) (c_pos − c_neg))²`. -/
theorem sector_brahmagupta_fibonacci_identity (c_pos s_pos c_neg s_neg : ℝ) :
    ((c_pos + c_neg) ^ 2 + (s_pos + s_neg) ^ 2) *
      ((c_pos - c_neg) ^ 2 + (s_pos - s_neg) ^ 2) =
    ((c_pos ^ 2 + s_pos ^ 2) - (c_neg ^ 2 + s_neg ^ 2)) ^ 2 +
      ((c_pos + c_neg) * (s_pos - s_neg) - (s_pos + s_neg) * (c_pos - c_neg)) ^ 2 := by
  ring

/-- **Universal Cauchy–Schwarz inequality for the sector modulus imbalance:**
For all `c_pos, s_pos, c_neg, s_neg : ℝ`,
`((c_pos² + s_pos²) − (c_neg² + s_neg²))² ≤
  ((c_pos + c_neg)² + (s_pos + s_neg)²) ((c_pos − c_neg)² + (s_pos − s_neg)²)`. -/
theorem sq_sector_modulus_sub_le (c_pos s_pos c_neg s_neg : ℝ) :
    ((c_pos ^ 2 + s_pos ^ 2) - (c_neg ^ 2 + s_neg ^ 2)) ^ 2 ≤
      ((c_pos + c_neg) ^ 2 + (s_pos + s_neg) ^ 2) *
        ((c_pos - c_neg) ^ 2 + (s_pos - s_neg) ^ 2) := by
  rw [sector_brahmagupta_fibonacci_identity]
  linarith [sq_nonneg ((c_pos + c_neg) * (s_pos - s_neg) - (s_pos + s_neg) * (c_pos - c_neg))]

/-- **Complex Mellin Parallelogram Law across the open critical strip `|l| < 1/2`, `τ ∈ ℝ` (`k ≥ 2`):**
The sum of the full-line complex modulus squared `M_k(l, τ)² + N_k(l, τ)²` and the origin–infinity
complex imbalance modulus squared `Δ_k^{\cos}(l, τ)² + Δ_k^{\sin}(l, τ)²` equals twice the sum of
the `(1, ∞)` and `(0, 1]` sector moduli squared. -/
theorem complexModulusSq_add_imbalanceModulusSq_eq_two_mul_sectorModulusSq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    ((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
      (((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) =
    2 * (((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
          (∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
        ((∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
          (∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) := by
  rw [setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν hl τ,
    setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν hl τ]
  exact sector_parallelogram_law _ _ _ _

/-- **Sector Modulus Imbalance Polarization Identity across `|l| < 1/2`, `τ ∈ ℝ` (`k ≥ 2`):**
The difference between the infinity-sector modulus squared `C_k^+(l, τ)² + S_k^+(l, τ)²` and the
origin-sector modulus squared `C_k^-(l, τ)² + S_k^-(l, τ)²` equals the real inner product
`M_k(l, τ) · Δ_k^{\cos}(l, τ) + N_k(l, τ) · Δ_k^{\sin}(l, τ)`. -/
theorem sectorModulusSq_sub_eq_oscillatoryMellin_mul_imbalance
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    ((∫ x in Ioi (1 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
        (∫ x in Ioi (1 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
      ((∫ x in Ioc (0 : ℝ) 1,
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
        (∫ x in Ioc (0 : ℝ) 1,
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) =
    (∫ x in Ioi (0 : ℝ),
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
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) := by
  rw [setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν hl τ,
    setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν hl τ]
  exact sector_polarization_identity _ _ _ _

/-- **Sector Modulus Cauchy–Schwarz Inequality across `|l| < 1/2`, `τ ∈ ℝ` (`k ≥ 2`):**
`((C_k^+(l, τ)² + S_k^+(l, τ)²) − (C_k^-(l, τ)² + S_k^-(l, τ)²))² ≤
  (M_k(l, τ)² + N_k(l, τ)²) · (Δ_k^{\cos}(l, τ)² + Δ_k^{\sin}(l, τ)²)`. -/
theorem sq_sectorModulusSq_sub_le_complexModulusSq_mul_imbalanceModulusSq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    (((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
          (∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
        ((∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
          (∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) ^ 2 ≤
    ((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
      (((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) := by
  rw [setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν hl τ,
    setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν hl τ]
  exact sq_sector_modulus_sub_le _ _ _ _

/-- **Critical-Line Complex Sector Equipartition (`l = 0`, `k ≥ 1`, `τ ∈ ℝ`):**
On the critical line `l = 0`, the infinity-sector modulus squared and the origin-sector modulus
squared are equal at every vertical height `τ ∈ ℝ`. -/
theorem sectorModulusSq_Ioi_one_eq_Ioc_zero_one_at_criticalLine
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (τ : ℝ) :
    (∫ x in Ioi (1 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
      (∫ x in Ioi (1 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 =
    (∫ x in Ioc (0 : ℝ) 1,
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
      (∫ x in Ioc (0 : ℝ) 1,
        x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 := by
  rw [setIntegral_Ioc_zero_one_cos_log_eq_setIntegral_Ioi_one hk ν τ,
    setIntegral_Ioc_zero_one_rpow_neg_half_mul_sin_log_eq_neg_Ioi_one hk ν τ]
  ring

/-- **Zero-Locus Complex Sector Equipartition Theorem (`k ≥ 2`, `|l| < 1/2`, `τ ∈ ℝ`):**
At any point `(l, τ)` in the open critical strip where the full-line complex Mellin modulus squared
vanishes (`M_k(l, τ)² + N_k(l, τ)² = 0`), the infinity-sector modulus squared and the origin-sector
modulus squared are strictly equal:
`C_k^+(l, τ)² + S_k^+(l, τ)² = C_k^-(l, τ)² + S_k^-(l, τ)²`. -/
theorem sectorModulusSq_eq_of_complexModulusSq_eq_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) {τ : ℝ}
    (hzero :
      (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 = 0) :
    (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
      (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 =
    (∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
      (∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 := by
  have hcs := sq_sectorModulusSq_sub_le_complexModulusSq_mul_imbalanceModulusSq hk hν hl τ
  rw [hzero, zero_mul] at hcs
  have hsq_eq :
      (((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
          ((∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) ^ 2 = 0 :=
    le_antisymm hcs (sq_nonneg _)
  linarith [sq_eq_zero_iff.mp hsq_eq]


/-! ## Section 4: Five-Point Subharmonicity of the Imbalance Modulus Squared and Critical-Line Transversality of the Sector Modulus Imbalance -/

private theorem fivePoint_sq_div_sq_eq (a₁ b₁ a₂ b₂ c h : ℝ) :
    ((a₁ ^ 2 + b₁ ^ 2 - 2 * c ^ 2) + (a₂ ^ 2 + b₂ ^ 2 - 2 * c ^ 2)) / h ^ 2 =
      2 * c * (((a₁ + b₁ - 2 * c) + (a₂ + b₂ - 2 * c)) / h ^ 2) +
        (((a₁ - c) / h) ^ 2 + ((b₁ - c) / (-h)) ^ 2) +
        (((a₂ - c) / h) ^ 2 + ((b₂ - c) / (-h)) ^ 2) := by
  have h1 := central_diff_sq_div_sq_eq a₁ b₁ c h
  have h2 := central_diff_sq_div_sq_eq a₂ b₂ c h
  rw [add_div, h1, h2, add_div]
  ring

/-- **Five-point subharmonic Laplacian limit for the squared cosine imbalance `Δ_k^{\cos}(l, τ)²`
across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`(Δ_l² (Δ_k^{\cos})² + Δ_τ² (Δ_k^{\cos})²) / h² →
  2 ((∫_{v > 0} 2 v cosh(lv) cos(τv) Φ_k(v) dv)² + (∫_{v > 0} 2 v sinh(lv) sin(τv) Φ_k(v) dv)²)`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_imbalanceCos_sq_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((((∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
              2 * ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
            (((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
              2 * ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (2 * ((∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2))) := by
  set F_l : ℝ → ℝ := fun h =>
    (∫ x in Ioi (1 : ℝ),
        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set F_t : ℝ → ℝ := fun h =>
    (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set F₀ : ℝ :=
    (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set D_l : ℝ := ∫ v in Ioi (0 : ℝ),
    2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v
  set D_t : ℝ := -(∫ v in Ioi (0 : ℝ),
    2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)
  have h1_l : Tendsto (fun h : ℝ => (F_l h - F₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_l) :=
    tendsto_div_imbalanceCos_sub_left_nhds_zero hk hν hl τ
  have h1_t : Tendsto (fun h : ℝ => (F_t h - F₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_t) :=
    tendsto_div_imbalanceCos_sub_right_nhds_zero hk hν hl τ
  have hneg : Tendsto (fun h : ℝ => -h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhdsWithin 0 {(0 : ℝ)}ᶜ) :=
    tendsto_neg_nhdsWithin_zero
  have h1_lm : Tendsto (fun h : ℝ => (F_l (-h) - F₀) / (-h)) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_l) :=
    h1_l.comp hneg
  have h1_tm : Tendsto (fun h : ℝ => (F_t (-h) - F₀) / (-h)) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_t) :=
    h1_t.comp hneg
  have hlap : Tendsto
      (fun h : ℝ => ((F_l h + F_l (-h) - 2 * F₀) + (F_t h + F_t (-h) - 2 * F₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_imbalanceCos_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [F_l, F_t, F₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have hcomb := ((hlap.const_mul (2 * F₀)).add ((h1_l.pow 2).add (h1_lm.pow 2))).add
    ((h1_t.pow 2).add (h1_tm.pow 2))
  have hlim_eq :
      2 * F₀ * 0 + (D_l ^ 2 + D_l ^ 2) + (D_t ^ 2 + D_t ^ 2) =
        2 * ((∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
    dsimp [D_l, D_t]; ring
  rw [hlim_eq] at hcomb
  refine hcomb.congr (fun h => ?_)
  refine (fivePoint_sq_div_sq_eq (F_l h) (F_l (-h)) (F_t h) (F_t (-h)) F₀ h).symm.trans ?_
  dsimp [F_l, F_t, F₀]
  have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
  have ht_sub : τ + -h = τ - h := by ring
  rw [hl_sub, ht_sub]

/-- **Five-point subharmonic Laplacian limit for the squared sine imbalance `Δ_k^{\sin}(l, τ)²`
across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`(Δ_l² (Δ_k^{\sin})² + Δ_τ² (Δ_k^{\sin})²) / h² →
  2 ((∫_{v > 0} 2 v cosh(lv) cos(τv) Φ_k(v) dv)² + (∫_{v > 0} 2 v sinh(lv) sin(τv) Φ_k(v) dv)²)`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_imbalanceSin_sq_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((((∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
              2 * ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
            (((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 -
              2 * ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (2 * ((∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2))) := by
  set F_l : ℝ → ℝ := fun h =>
    (∫ x in Ioi (1 : ℝ),
        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set F_t : ℝ → ℝ := fun h =>
    (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set F₀ : ℝ :=
    (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set D_l : ℝ := ∫ v in Ioi (0 : ℝ),
    2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v
  set D_t : ℝ := ∫ v in Ioi (0 : ℝ),
    2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v
  have h1_l : Tendsto (fun h : ℝ => (F_l h - F₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_l) :=
    tendsto_div_imbalanceSin_sub_left_nhds_zero hk hν hl τ
  have h1_t : Tendsto (fun h : ℝ => (F_t h - F₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_t) :=
    tendsto_div_imbalanceSin_sub_right_nhds_zero hk hν hl τ
  have hneg : Tendsto (fun h : ℝ => -h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhdsWithin 0 {(0 : ℝ)}ᶜ) :=
    tendsto_neg_nhdsWithin_zero
  have h1_lm : Tendsto (fun h : ℝ => (F_l (-h) - F₀) / (-h)) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_l) :=
    h1_l.comp hneg
  have h1_tm : Tendsto (fun h : ℝ => (F_t (-h) - F₀) / (-h)) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_t) :=
    h1_t.comp hneg
  have hlap : Tendsto
      (fun h : ℝ => ((F_l h + F_l (-h) - 2 * F₀) + (F_t h + F_t (-h) - 2 * F₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    refine (tendsto_div_sq_imbalanceSin_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [F_l, F_t, F₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have hcomb := ((hlap.const_mul (2 * F₀)).add ((h1_l.pow 2).add (h1_lm.pow 2))).add
    ((h1_t.pow 2).add (h1_tm.pow 2))
  have hlim_eq :
      2 * F₀ * 0 + (D_l ^ 2 + D_l ^ 2) + (D_t ^ 2 + D_t ^ 2) =
        2 * ((∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
    dsimp [D_l, D_t]; ring
  rw [hlim_eq] at hcomb
  refine hcomb.congr (fun h => ?_)
  refine (fivePoint_sq_div_sq_eq (F_l h) (F_l (-h)) (F_t h) (F_t (-h)) F₀ h).symm.trans ?_
  dsimp [F_l, F_t, F₀]
  have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
  have ht_sub : τ + -h = τ - h := by ring
  rw [hl_sub, ht_sub]

/-- **Global Five-Point Subharmonic Laplacian Law for the Origin–Infinity Complex Imbalance
Modulus Squared `|Δ_k(l, τ)|² = Δ_k^{\cos}(l, τ)² + Δ_k^{\sin}(l, τ)²` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`(Δ_l² |Δ_k|² + Δ_τ² |Δ_k|²) / h² →
  4 ((∫_{v > 0} 2 v cosh(lv) cos(τv) Φ_k(v) dv)² + (∫_{v > 0} 2 v sinh(lv) sin(τv) Φ_k(v) dv)²) ≥ 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_imbalanceModulusSq_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
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
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (4 * ((∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2))) := by
  have h1 := tendsto_div_sq_imbalanceCos_sq_fivePoint_laplacian_nhds_zero hk hν hl τ
  have h2 := tendsto_div_sq_imbalanceSin_sq_fivePoint_laplacian_nhds_zero hk hν hl τ
  have hadd := h1.add h2
  have hlim :
      2 * ((∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2) +
        2 * ((∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      4 * ((∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
    ring
  rw [hlim] at hadd
  exact hadd.congr (fun h => by ring)

/-- **Exact first-order horizontal transversal derivative of the sector modulus imbalance on the
critical line `l = 0` at every vertical height `τ ∈ ℝ` (`k ≥ 2`):**
`(((C_k^+(l, τ)² + S_k^+(l, τ)²) − (C_k^-(l, τ)² + S_k^-(l, τ)²)) / l) →
  M_k(0, τ) · (2 ∫_{v > 0} v cos(τv) Φ_k(v) dv) +
  (2 ∫_{v > 0} sin(τv) Φ_k(v) dv) · (∫_ℝ v sin(τv) Φ_k(v) dv)`
as `l → 0` (`l ≠ 0`). -/
theorem tendsto_div_sectorModulusSq_sub_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    Tendsto
      (fun l : ℝ =>
        (((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
          ((∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / l)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        ((∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          (2 * ∫ v in Ioi (0 : ℝ),
            v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          (∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (2 * ∫ v in Ioi (0 : ℝ),
            Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) := by
  have hk1 : 1 ≤ k := by omega
  have hM_cont :
      Tendsto
        (fun l : ℝ =>
          ∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)
        (nhdsWithin 0 {(0 : ℝ)}ᶜ)
        (nhds
          (∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) :=
    tendsto_of_tendsto_div_nhdsWithin_zero
      ((tendsto_div_oscillatoryMellin_sub_criticalLine_nhds_zero hk hν τ).mono_left
        nhdsWithin_le_nhds)
  have hΔc_div :
      Tendsto
        (fun l : ℝ =>
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / l)
        (nhdsWithin 0 {(0 : ℝ)}ᶜ)
        (nhds (2 * ∫ v in Ioi (0 : ℝ),
          v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) :=
    tendsto_div_oscillatoryMellin_imbalance_nhds_zero hk hν τ
  have hN_div :
      Tendsto
        (fun l : ℝ =>
          (∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / l)
        (nhdsWithin 0 {(0 : ℝ)}ᶜ)
        (nhds (∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) :=
    tendsto_div_sineMellin_nhds_zero hk hν τ
  have hΔs_div :
      Tendsto
        (fun l : ℝ =>
          (((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            (2 * ∫ v in Ioi (0 : ℝ), Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / l)
        (nhdsWithin 0 {(0 : ℝ)}ᶜ)
        (nhds 0) := by
    have h0 := tendsto_div_imbalanceSin_sub_left_nhds_zero hk hν (by norm_num : |(0 : ℝ)| < 1 / 8) τ
    have hlim0 :
        (∫ v in Ioi (0 : ℝ),
          2 * v * Real.sinh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) = 0 := by
      simp [Real.sinh_zero]
    rw [hlim0] at h0
    refine h0.congr (fun l => ?_)
    rw [zero_add, setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_zero_mul_sin_log hk1 ν τ]
  have hΔs_cont := tendsto_of_tendsto_div_nhdsWithin_zero hΔs_div
  have hcomb := (hM_cont.mul hΔc_div).add (hN_div.mul hΔs_cont)
  refine hcomb.congr' ?_
  have hmem : Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [hmem] with l hl_mem
  have hl_half : |l| < 1 / 2 := abs_lt.mpr hl_mem
  rw [sectorModulusSq_sub_eq_oscillatoryMellin_mul_imbalance hk hν hl_half τ]
  ring

/-- **Critical-Line Zero Specialization of the Sector Modulus Imbalance Derivative (`k ≥ 2`, `τ₀ ∈ ℝ`):**
At any critical-line zero `M_k(0, τ₀) = 0`, the horizontal transversal derivative of the sector
modulus imbalance on the critical line reduces to the product of the critical-line sine imbalance
and the first logarithmic-sine moment:
`(((C_k^+(l, τ₀)² + S_k^+(l, τ₀)²) − (C_k^-(l, τ₀)² + S_k^-(l, τ₀)²)) / l) →
  (∫_ℝ v sin(τ₀ v) Φ_k(v) dv) · (2 ∫_{v > 0} sin(τ₀ v) Φ_k(v) dv)`. -/
theorem tendsto_div_sectorModulusSq_sub_at_criticalLine_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {τ₀ : ℝ}
    (hzero :
      (∫ x in Ioi (0 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) = 0) :
    Tendsto
      (fun l : ℝ =>
        (((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
          ((∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / l)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        ((∫ v : ℝ, v * Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (2 * ∫ v in Ioi (0 : ℝ),
            Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v))) := by
  have h := tendsto_div_sectorModulusSq_sub_nhds_zero hk hν τ₀
  rw [hzero, zero_mul, zero_add] at h
  exact h

/-- **Master Witness Theorem for Origin–Infinity Complex Mellin Sector Holomorphy, Parallelogram
and Polarization Laws, Zero-Locus Sector Equipartition, and Subharmonic Imbalance Modulus:**
There exists an explicit symmetric non-zero finite arc measure `ν` on `ArcParam` such that for all
`k ≥ 2`:
1. Across `|l| < 1/8` and `τ ∈ ℝ`, the origin–infinity complex Mellin imbalance
   `(Δ_k^{\cos}(l, τ), Δ_k^{\sin}(l, τ))` satisfies both Cauchy–Riemann equations
   `∂_l Δ_k^{\cos} = ∂_τ Δ_k^{\sin}` and `∂_l Δ_k^{\sin} = −∂_τ Δ_k^{\cos}` and the quartic `O(h⁴)`
   five-point harmonic Laplacian bounds;
2. Across `|l| < 1/2` and `τ ∈ ℝ`, the complex Mellin modulus squared, imbalance modulus squared,
   and `(1, ∞)` / `(0, 1]` sector moduli squared obey the exact parallelogram law, polarization
   identity, Cauchy–Schwarz inequality, and zero-locus complex sector equipartition;
3. Across `|l| < 1/8` and `τ ∈ ℝ`, the imbalance modulus squared `Δ_k^{\cos}(l, τ)² + Δ_k^{\sin}(l, τ)²`
   satisfies the global five-point subharmonic Laplacian law with non-negative limit
   `4 ((∂_l Δ_k^{\cos})² + (∂_l Δ_k^{\sin})²)`, and the sector modulus imbalance obeys the exact
   critical-line transversal derivative law at every `τ ∈ ℝ`. -/
theorem exists_dyadic_originInfinity_sectorHolomorphy_arcWitness :
    ∃ ν : Measure ArcParam,
      IsFiniteMeasure ν ∧
      ν.map arcNeg = ν ∧
      ν ≠ 0 ∧
      ∀ ⦃k : ℕ⦄, 2 ≤ k →
        (∀ ⦃l : ℝ⦄, |l| < 1 / 8 → ∀ τ : ℝ,
          Tendsto
            (fun h : ℝ =>
              ((((∫ x in Ioi (1 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) -
                (((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) ∧
          Tendsto
            (fun h : ℝ =>
              ((((∫ x in Ioi (1 : ℝ),
                      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) +
                (((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) / h)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0)) ∧
        (∀ ⦃l : ℝ⦄, |l| < 1 / 2 → ∀ τ : ℝ,
          ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
            ((∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) =
          (∫ x in Ioi (0 : ℝ),
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
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) ∧
        (∀ ⦃l : ℝ⦄, |l| < 1 / 8 → ∀ τ : ℝ,
          Tendsto
            (fun h : ℝ =>
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
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h ^ 2))
            (nhdsWithin 0 {(0 : ℝ)}ᶜ)
            (nhds
              (4 * ((∫ v in Ioi (0 : ℝ),
                    2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
                  (∫ v in Ioi (0 : ℝ),
                    2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2)))) ∧
        (∀ τ : ℝ,
          Tendsto
            (fun l : ℝ =>
              (((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                ((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / l)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ)
            (nhds
              ((∫ x in Ioi (0 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (2 * ∫ v in Ioi (0 : ℝ),
                  v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
                (∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
                (2 * ∫ v in Ioi (0 : ℝ),
                  Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) := by
  obtain ⟨ν, hfin, hne, hν, _, _⟩ := exists_arcWitness
  refine ⟨ν, hfin, hν, hne, fun k hk => ?_⟩
  refine ⟨fun l hl τ => ⟨tendsto_div_imbalance_cauchyRiemann_first_nhds_zero hk hν hl τ,
      tendsto_div_imbalance_cauchyRiemann_second_nhds_zero hk hν hl τ⟩,
    fun l hl τ => sectorModulusSq_sub_eq_oscillatoryMellin_mul_imbalance hk hν hl τ,
    fun l hl τ => tendsto_div_sq_imbalanceModulusSq_fivePoint_laplacian_nhds_zero hk hν hl τ,
    fun τ => tendsto_div_sectorModulusSq_sub_nhds_zero hk hν τ⟩

end

end RHTower

import GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.HalfGateClosureAndDensityEquivalence
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Unit-Window Minimum Selection, Ordinate Oscillation Calculus, and Separation Classification

This module resolves Directive 3 on Criterion 5 of `riemannHypothesis_finiteTheta_poleNodal_dyadic_tfae`
(`min_{γ ∈ [T, T + 1]} finiteThetaSourceMomentReading (baseTwistTest γ) L_k(T) 1 (apertureStage L_k(T) T)`)
by establishing the exact `γ`-oscillation calculus of `finiteThetaSourceMomentReading` and
`polynomialThetaSourceMomentReading` and isolating the three-way separation between unit-window
minimum selection, unit-window mean control (`heckeDefect_log_unitWindow_tfae`), and dyadic
variation:

1. **Zero-coordinate-free `L`-lossless `γ`-derivative bounds (§1)**
   (`abs_deriv_finiteThetaSourceMomentReading_le`,
    `abs_deriv_deriv_finiteThetaSourceMomentReading_le`,
    `abs_deriv_polynomialThetaSourceMomentReading_le`,
    `abs_deriv_deriv_polynomialThetaSourceMomentReading_le`):
   Defining the support-preserving moment-weighted source tests `momentCompactTest m f`
   (`u ↦ u^m f(u)`), differentiating `tr (sourceTwist γ f).1 z` and the compactly supported
   curvature readings under the integral sign yields exact `C²` regularity in `γ` and stage-uniform,
   `L`-lossless bounds (`∀ κ > 0`):
   - `|∂_γ R_{L,j,n}(f; γ)| ≤ κ R_{L,j,n}(f; γ) + κ⁻¹ R_{L,j,n}(f₁; γ)`,
   - `|∂_γ² R_{L,j,n}(f; γ)| ≤ R_{L,j,n}(f; γ) + 2 R_{L,j,n}(f₁; γ) + R_{L,j,n}(f₂; γ)`,
   and identically for `polynomialThetaSourceMomentReading`.

2. **Unit-window Taylor mean-minus-min & Sobolev `L¹` bounds (§2)**
   (`unitWindow_mean_sub_min_le_half_sup_deriv`,
    `unitWindow_mean_sub_interior_min_le_sixth_sup_deriv2`,
    `sSup_finiteThetaSourceMomentReading_unitWindow_le`,
    `sSup_polynomialThetaSourceMomentReading_unitWindow_le`):
   On every unit window `[T, T + 1]`, `∫_T^{T+1} g - min_{[T,T+1]} g ≤ (1/2) sup_{[T,T+1]} |g'|`
   (sharpened to `(1/6) sup_{[T,T+1]} |g''|` at any interior minimizer `γ_* ∈ (T, T + 1)`), while
   1D Sobolev embedding yields `sup_{[T,T+1]} R(f) ≤ 2 ∫_T^{T+1} R(f) + ∫_T^{T+1} R(f₁)`.

3. **Five-way dyadic `RH` equivalence & five-way fixed-`c` collapse (§3–§4)**
   (`riemannHypothesis_unitWindow_min_mean_max_finiteTheta_tfae`,
    `polynomialTheta_unitWindow_min_mean_max_log_tfae`):
   - Across dyadic scales `L_k(T) = 2^k c₀ log T` (`c₀ > 0`), `RiemannHypothesis` is unconditionally
     equivalent (`List.TFAE`) to uniform boundedness of the unit-window minimum (Criterion 5),
     unit-window mean, unit-window supremum, and unit-window `C²`-jet supremum of
     `finiteThetaSourceMomentReading` at `apertureStage L_k(T) T`.
   - At any fixed `c ∈ (0, 2]`, eventual boundedness as `T → ∞` of the unit-window minimum, mean,
     supremum, and `C²`-jet supremum of `polynomialThetaSourceMomentReading` at
     `linearThetaStage (T + 1)` are 5-way equivalent (`List.TFAE`) to eventual boundedness of
     `unitWindowDepthCharge T (c * Real.log T)` (hence to `heckeDefect_log_unitWindow_tfae`).

4. **Unconditional dyadic unit-window supremum `O_c(log U)` collapse & three-part separation (§5)**
   (`exists_dyadicMean_unitWindow_sup_polynomialTheta_le_log_up_to_half`,
    `unitWindow_singleWindow_local_vs_offWindow_separation`,
    `finiteOffLine_not_rh_unitWindow_separation`):
   - For every `0 < c < 1 / 2`, the dyadic mean over `T ∈ [U, 2U]` of the **unit-window supremum**
     `sup_{γ ∈ [T, T+1]} polynomialThetaSourceMomentReading (baseTwistTest γ) (c log T) 1 (linearThetaStage (2U + 2))`
     is unconditionally `O_c(log U)`.
   - On a single window `[T, T + 1]`, the unit-window minimum lower-bounds only the local charge
     `unitWindowDepthCharge T L`, whereas `heckeDefect` decomposes into local `xiUnitWindowZeros T`
     charge plus the nonnegative off-window Lorentzian tail; under `FiniteOffLine ∧ ¬RiemannHypothesis`,
     all fixed-`c ∈ (0, 2]` unit-window `C²`-jets converge to `0` while all four dyadic-`k`
     unit-window quantities (minimum, mean, supremum, `C²`-jet) are unbounded.
-/

set_option autoImplicit false

open Complex Filter Topology Set MeasureTheory intervalIntegral
open scoped BigOperators Real ComplexConjugate ContDiff ENNReal

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect

open GaloisForLFunctions.ConjugateDiagonalGeometry
open GaloisForLFunctions.ArithmeticOrientationGeometry
open GaloisForLFunctions.BiScaleUncertainty.ZeroDensityFilteredCriticalDeficitLaw
open ArithmeticPolarization SquareRootThreshold _root_.RHTower _root_.Zeta23
open _root_.RHTower.DeBruijn

/-! ## §1. Moment-weighted source tests and `L`-lossless `γ`-derivative bounds -/

/-- Support-preserving `m`-th moment source test `u ↦ u^m f(u)`. -/
def momentCompactTest (m : ℕ) (f : CompactTest) : CompactTest :=
  ⟨fun u => (u : ℂ) ^ m * f.1 u,
    ((Complex.ofRealCLM.contDiff).pow m).mul f.2.1,
    f.2.2.mul_left⟩

@[simp]
theorem momentCompactTest_zero (f : CompactTest) : momentCompactTest 0 f = f :=
  Subtype.ext (funext fun u => by simp [momentCompactTest])

theorem momentCompactTest_one_momentCompactTest_one (f : CompactTest) :
    momentCompactTest 1 (momentCompactTest 1 f) = momentCompactTest 2 f :=
  Subtype.ext (funext fun u => by dsimp [momentCompactTest]; ring)

theorem abs_le_of_momentCompactTest_ne_zero (m : ℕ) (f : CompactTest) {a : ℝ}
    (hsupp : ∀ u, f.1 u ≠ 0 → |u| ≤ a) (u : ℝ)
    (hu : (momentCompactTest m f).1 u ≠ 0) : |u| ≤ a :=
  hsupp u (right_ne_zero_of_mul hu)

/-- Differentiating `γ ↦ tr (sourceTwist γ f).1 z` under the compactly supported Fourier–Laplace
integral yields `(-I) * tr (sourceTwist γ₀ (momentCompactTest 1 f)).1 z`. -/
theorem hasDerivAt_tr_sourceTwist (f : CompactTest) (z : ℂ) (γ₀ : ℝ) :
    HasDerivAt (fun γ : ℝ => tr (sourceTwist γ f).1 z)
      ((-I) * tr (sourceTwist γ₀ (momentCompactTest 1 f)).1 z) γ₀ := by
  let F : ℝ → ℝ → ℂ := fun γ u =>
    (Complex.exp (-((γ : ℂ) * I * (u : ℂ))) * f.1 u) * Complex.exp ((z - 1 / 2) * (u : ℂ))
  let F' : ℝ → ℝ → ℂ := fun γ u =>
    (-I) * ((Complex.exp (-((γ : ℂ) * I * (u : ℂ))) * ((u : ℂ) ^ 1 * f.1 u)) *
      Complex.exp ((z - 1 / 2) * (u : ℂ)))
  let bound : ℝ → ℝ := fun u =>
    ‖((u : ℂ) ^ 1 * f.1 u) * Complex.exp ((z - 1 / 2) * (u : ℂ))‖
  have hF_supp : ∀ γ : ℝ, HasCompactSupport (F γ) := fun γ =>
    ((f.2.2.mul_left).mul_right)
  have hbound_supp : HasCompactSupport bound :=
    (((momentCompactTest 1 f).2.2.mul_right).norm)
  have hdom := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (s := Set.univ) (x₀ := γ₀) (F := F) (F' := F') (bound := bound)
    Filter.univ_mem
    (Eventually.of_forall fun γ =>
      (by dsimp [F]; fun_prop : Continuous (F γ)).aestronglyMeasurable)
    ((by dsimp [F]; fun_prop : Continuous (F γ₀)).integrable_of_hasCompactSupport (hF_supp γ₀))
    ((by dsimp [F']; fun_prop : Continuous (F' γ₀)).aestronglyMeasurable)
    (Eventually.of_forall fun u γ _ => by
      dsimp [F', bound]
      have hexp_norm : ‖Complex.exp (-((γ : ℂ) * I * (u : ℂ)))‖ = 1 := by
        have hrew : -((γ : ℂ) * I * (u : ℂ)) = ((-(γ * u) : ℝ) : ℂ) * I := by
          push_cast; ring
        rw [hrew]
        exact Complex.norm_exp_ofReal_mul_I (-(γ * u))
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul, norm_mul, norm_mul, hexp_norm, one_mul,
        ← norm_mul])
    ((by dsimp [bound]; fun_prop : Continuous bound).integrable_of_hasCompactSupport hbound_supp)
    (Eventually.of_forall fun u γ _ => by
      dsimp [F, F']
      have hlin : HasDerivAt (fun x : ℝ => -((x : ℂ) * I * (u : ℂ))) (-(1 * I * (u : ℂ))) γ :=
        ((((hasDerivAt_id γ).ofReal_comp).mul_const I).mul_const (u : ℂ)).neg
      have hexp : HasDerivAt (fun x : ℝ => Complex.exp (-((x : ℂ) * I * (u : ℂ))))
          (Complex.exp (-((γ : ℂ) * I * (u : ℂ))) * (-(1 * I * (u : ℂ)))) γ :=
        (Complex.hasDerivAt_exp _).comp γ hlin
      exact ((hexp.mul_const (f.1 u)).mul_const
        (Complex.exp ((z - 1 / 2) * (u : ℂ)))).congr_deriv (by ring))
  have hF_eq : (fun γ : ℝ => ∫ u : ℝ, F γ u) = fun γ : ℝ => tr (sourceTwist γ f).1 z := by
    funext γ
    rw [tr_eq]
    rfl
  have hF'_eq : (∫ u : ℝ, F' γ₀ u) =
      (-I) * tr (sourceTwist γ₀ (momentCompactTest 1 f)).1 z := by
    dsimp [F']
    rw [MeasureTheory.integral_const_mul, tr_eq]
    rfl
  simpa only [hF_eq, hF'_eq] using hdom.2

/-- Exact first ordinate derivative of `γ ↦ Complex.normSq (tr (sourceTwist γ f).1 z)`. -/
def trTwistNormSqDeriv1 (f : CompactTest) (z : ℂ) (γ : ℝ) : ℝ :=
  2 * ((tr (sourceTwist γ f).1 z).re * (tr (sourceTwist γ (momentCompactTest 1 f)).1 z).im -
    (tr (sourceTwist γ f).1 z).im * (tr (sourceTwist γ (momentCompactTest 1 f)).1 z).re)

/-- Exact second ordinate derivative of `γ ↦ Complex.normSq (tr (sourceTwist γ f).1 z)`. -/
def trTwistNormSqDeriv2 (f : CompactTest) (z : ℂ) (γ : ℝ) : ℝ :=
  2 * Complex.normSq (tr (sourceTwist γ (momentCompactTest 1 f)).1 z) -
    2 * ((tr (sourceTwist γ f).1 z).re * (tr (sourceTwist γ (momentCompactTest 2 f)).1 z).re +
      (tr (sourceTwist γ f).1 z).im * (tr (sourceTwist γ (momentCompactTest 2 f)).1 z).im)

theorem hasDerivAt_normSq_tr_sourceTwist (f : CompactTest) (z : ℂ) (γ₀ : ℝ) :
    HasDerivAt (fun γ : ℝ => Complex.normSq (tr (sourceTwist γ f).1 z))
      (trTwistNormSqDeriv1 f z γ₀) γ₀ := by
  have h0 := hasDerivAt_tr_sourceTwist f z γ₀
  have hre0 : HasDerivAt (fun γ : ℝ => (tr (sourceTwist γ f).1 z).re)
      ((tr (sourceTwist γ₀ (momentCompactTest 1 f)).1 z).im) γ₀ := by
    have h := (Complex.reCLM.hasFDerivAt).comp_hasDerivAt γ₀ h0
    exact h.congr_deriv (by simp)
  have him0 : HasDerivAt (fun γ : ℝ => (tr (sourceTwist γ f).1 z).im)
      (-(tr (sourceTwist γ₀ (momentCompactTest 1 f)).1 z).re) γ₀ := by
    have h := (Complex.imCLM.hasFDerivAt).comp_hasDerivAt γ₀ h0
    exact h.congr_deriv (by simp)
  have hnsq_eq : (fun γ : ℝ => Complex.normSq (tr (sourceTwist γ f).1 z)) =
      fun γ : ℝ => (tr (sourceTwist γ f).1 z).re * (tr (sourceTwist γ f).1 z).re +
        (tr (sourceTwist γ f).1 z).im * (tr (sourceTwist γ f).1 z).im :=
    funext fun γ => Complex.normSq_apply _
  rw [hnsq_eq]
  exact ((hre0.mul hre0).add (him0.mul him0)).congr_deriv (by
    dsimp [trTwistNormSqDeriv1]; ring)

theorem hasDerivAt_trTwistNormSqDeriv1 (f : CompactTest) (z : ℂ) (γ₀ : ℝ) :
    HasDerivAt (trTwistNormSqDeriv1 f z) (trTwistNormSqDeriv2 f z γ₀) γ₀ := by
  have h0 := hasDerivAt_tr_sourceTwist f z γ₀
  have h1_raw := hasDerivAt_tr_sourceTwist (momentCompactTest 1 f) z γ₀
  rw [momentCompactTest_one_momentCompactTest_one] at h1_raw
  have hre0 : HasDerivAt (fun γ : ℝ => (tr (sourceTwist γ f).1 z).re)
      ((tr (sourceTwist γ₀ (momentCompactTest 1 f)).1 z).im) γ₀ :=
    ((Complex.reCLM.hasFDerivAt).comp_hasDerivAt γ₀ h0).congr_deriv (by simp)
  have him0 : HasDerivAt (fun γ : ℝ => (tr (sourceTwist γ f).1 z).im)
      (-(tr (sourceTwist γ₀ (momentCompactTest 1 f)).1 z).re) γ₀ :=
    ((Complex.imCLM.hasFDerivAt).comp_hasDerivAt γ₀ h0).congr_deriv (by simp)
  have hre1 : HasDerivAt (fun γ : ℝ => (tr (sourceTwist γ (momentCompactTest 1 f)).1 z).re)
      ((tr (sourceTwist γ₀ (momentCompactTest 2 f)).1 z).im) γ₀ :=
    ((Complex.reCLM.hasFDerivAt).comp_hasDerivAt γ₀ h1_raw).congr_deriv (by simp)
  have him1 : HasDerivAt (fun γ : ℝ => (tr (sourceTwist γ (momentCompactTest 1 f)).1 z).im)
      (-(tr (sourceTwist γ₀ (momentCompactTest 2 f)).1 z).re) γ₀ :=
    ((Complex.imCLM.hasFDerivAt).comp_hasDerivAt γ₀ h1_raw).congr_deriv (by simp)
  unfold trTwistNormSqDeriv1
  refine (((hre0.mul him1).sub (him0.mul hre1)).const_mul 2).congr_deriv ?_
  dsimp [trTwistNormSqDeriv2]
  rw [Complex.normSq_apply]
  ring

/-- Completing-the-square Cauchy–Schwarz bound on `trTwistNormSqDeriv1`. -/
theorem abs_trTwistNormSqDeriv1_le (f : CompactTest) (z : ℂ) (γ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    |trTwistNormSqDeriv1 f z γ| ≤
      κ * Complex.normSq (tr (sourceTwist γ f).1 z) +
        κ⁻¹ * Complex.normSq (tr (sourceTwist γ (momentCompactTest 1 f)).1 z) := by
  let x₀ := (tr (sourceTwist γ f).1 z).re
  let y₀ := (tr (sourceTwist γ f).1 z).im
  let x₁ := (tr (sourceTwist γ (momentCompactTest 1 f)).1 z).re
  let y₁ := (tr (sourceTwist γ (momentCompactTest 1 f)).1 z).im
  rw [Complex.normSq_apply, Complex.normSq_apply]
  change |2 * (x₀ * y₁ - y₀ * x₁)| ≤ κ * (x₀ * x₀ + y₀ * y₀) + κ⁻¹ * (x₁ * x₁ + y₁ * y₁)
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hnn : 0 ≤ κ⁻¹ * ((κ * x₀ + y₁) ^ 2 + (κ * y₀ - x₁) ^ 2) := by positivity
    have hid : κ * (x₀ * x₀ + y₀ * y₀) + κ⁻¹ * (x₁ * x₁ + y₁ * y₁) + 2 * (x₀ * y₁ - y₀ * x₁) =
        κ⁻¹ * ((κ * x₀ + y₁) ^ 2 + (κ * y₀ - x₁) ^ 2) := by
      field_simp [hκ.ne']; ring
    linarith only [hnn, hid]
  · have hnn : 0 ≤ κ⁻¹ * ((κ * x₀ - y₁) ^ 2 + (κ * y₀ + x₁) ^ 2) := by positivity
    have hid : κ * (x₀ * x₀ + y₀ * y₀) + κ⁻¹ * (x₁ * x₁ + y₁ * y₁) - 2 * (x₀ * y₁ - y₀ * x₁) =
        κ⁻¹ * ((κ * x₀ - y₁) ^ 2 + (κ * y₀ + x₁) ^ 2) := by
      field_simp [hκ.ne']; ring
    linarith only [hnn, hid]

/-- Completing-the-square Cauchy–Schwarz bound on `trTwistNormSqDeriv2`. -/
theorem abs_trTwistNormSqDeriv2_le (f : CompactTest) (z : ℂ) (γ : ℝ) :
    |trTwistNormSqDeriv2 f z γ| ≤
      Complex.normSq (tr (sourceTwist γ f).1 z) +
        2 * Complex.normSq (tr (sourceTwist γ (momentCompactTest 1 f)).1 z) +
        Complex.normSq (tr (sourceTwist γ (momentCompactTest 2 f)).1 z) := by
  let x₀ := (tr (sourceTwist γ f).1 z).re
  let y₀ := (tr (sourceTwist γ f).1 z).im
  let x₁ := (tr (sourceTwist γ (momentCompactTest 1 f)).1 z).re
  let y₁ := (tr (sourceTwist γ (momentCompactTest 1 f)).1 z).im
  let x₂ := (tr (sourceTwist γ (momentCompactTest 2 f)).1 z).re
  let y₂ := (tr (sourceTwist γ (momentCompactTest 2 f)).1 z).im
  unfold trTwistNormSqDeriv2
  rw [Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply]
  change |2 * (x₁ * x₁ + y₁ * y₁) - 2 * (x₀ * x₂ + y₀ * y₂)| ≤
    (x₀ * x₀ + y₀ * y₀) + 2 * (x₁ * x₁ + y₁ * y₁) + (x₂ * x₂ + y₂ * y₂)
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hnn : 0 ≤ 4 * (x₁ ^ 2 + y₁ ^ 2) + (x₀ - x₂) ^ 2 + (y₀ - y₂) ^ 2 := by positivity
    linarith only [hnn,
      show (x₀ * x₀ + y₀ * y₀) + 2 * (x₁ * x₁ + y₁ * y₁) + (x₂ * x₂ + y₂ * y₂) +
          (2 * (x₁ * x₁ + y₁ * y₁) - 2 * (x₀ * x₂ + y₀ * y₂)) =
        4 * (x₁ ^ 2 + y₁ ^ 2) + (x₀ - x₂) ^ 2 + (y₀ - y₂) ^ 2 by ring]
  · have hnn : 0 ≤ (x₀ + x₂) ^ 2 + (y₀ + y₂) ^ 2 := by positivity
    linarith only [hnn,
      show (x₀ * x₀ + y₀ * y₀) + 2 * (x₁ * x₁ + y₁ * y₁) + (x₂ * x₂ + y₂ * y₂) -
          (2 * (x₁ * x₁ + y₁ * y₁) - 2 * (x₀ * x₂ + y₀ * y₂)) =
        (x₀ + x₂) ^ 2 + (y₀ + y₂) ^ 2 by ring]

/-- Unified planar moment reading against a continuous nonnegative compactly supported spectral
weight `W : ℂ → ℝ`. -/
private def weightedMomentReading (W : ℂ → ℝ) (f : CompactTest) (L : ℝ) (j : ℕ) : ℝ :=
  Real.pi⁻¹ * ∫ z : ℂ, W z * (Complex.normSq (tr f.1 z) * depthKernel L (z.re - 1 / 2) ^ j)

private def weightedMomentDeriv1 (W : ℂ → ℝ) (f : CompactTest) (L : ℝ) (j : ℕ) (γ : ℝ) : ℝ :=
  Real.pi⁻¹ * ∫ z : ℂ, W z * (trTwistNormSqDeriv1 f z γ * depthKernel L (z.re - 1 / 2) ^ j)

private def weightedMomentDeriv2 (W : ℂ → ℝ) (f : CompactTest) (L : ℝ) (j : ℕ) (γ : ℝ) : ℝ :=
  Real.pi⁻¹ * ∫ z : ℂ, W z * (trTwistNormSqDeriv2 f z γ * depthKernel L (z.re - 1 / 2) ^ j)

private theorem normSq_tr_sourceTwist_le_ball (g : CompactTest) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ w : ℂ, ‖tr g.1 w‖ ≤ A * Real.exp (‖w‖ ^ 2)) {γ₀ γ : ℝ}
    (hγ : γ ∈ Metric.ball γ₀ 1) (z : ℂ) :
    Complex.normSq (tr (sourceTwist γ g).1 z) ≤
      A ^ 2 * Real.exp (2 * (‖z‖ + |γ₀| + 1) ^ 2) := by
  have hdist : |γ - γ₀| < 1 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hγ
  have hγ_abs : |γ| ≤ |γ₀| + 1 := by
    have h1 := abs_add_le (γ - γ₀) γ₀
    rw [sub_add_cancel] at h1
    linarith only [h1, hdist]
  have hshift : ‖z - (γ : ℂ) * I‖ ≤ ‖z‖ + |γ₀| + 1 := by
    have ht := norm_sub_le z ((γ : ℂ) * I)
    have hi : ‖(γ : ℂ) * I‖ = |γ| := by simp
    linarith only [ht, hi, hγ_abs]
  have hsq : ‖z - (γ : ℂ) * I‖ ^ 2 ≤ (‖z‖ + |γ₀| + 1) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hshift 2
  rw [sourceTwist, tr_twist, Complex.normSq_eq_norm_sq]
  calc ‖tr g.1 (z - (γ : ℂ) * I)‖ ^ 2
      ≤ (A * Real.exp (‖z - (γ : ℂ) * I‖ ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hA _) 2
    _ = A ^ 2 * Real.exp (2 * ‖z - (γ : ℂ) * I‖ ^ 2) := by
        rw [mul_pow, sq (Real.exp _), ← Real.exp_add]; congr 2; ring
    _ ≤ A ^ 2 * Real.exp (2 * (‖z‖ + |γ₀| + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hsq])) (sq_nonneg A)

private theorem continuous_tr_sourceTwist_pair (g : CompactTest) :
    Continuous (fun p : ℝ × ℂ => tr (sourceTwist p.1 g).1 p.2) := by
  have heq : (fun p : ℝ × ℂ => tr (sourceTwist p.1 g).1 p.2) =
      fun p : ℝ × ℂ => tr g.1 (p.2 - (p.1 : ℂ) * I) :=
    funext fun p => tr_twist p.1 g.1 p.2
  rw [heq]
  exact (contDiff_tr g).continuous.comp
    (continuous_snd.sub ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const))

private theorem continuous_trTwistNormSqDeriv1_pair (f : CompactTest) :
    Continuous (fun p : ℝ × ℂ => trTwistNormSqDeriv1 f p.2 p.1) := by
  unfold trTwistNormSqDeriv1
  have h0 := continuous_tr_sourceTwist_pair f
  have h1 := continuous_tr_sourceTwist_pair (momentCompactTest 1 f)
  exact continuous_const.mul
    (((Complex.continuous_re.comp h0).mul (Complex.continuous_im.comp h1)).sub
      ((Complex.continuous_im.comp h0).mul (Complex.continuous_re.comp h1)))

private theorem continuous_trTwistNormSqDeriv2_pair (f : CompactTest) :
    Continuous (fun p : ℝ × ℂ => trTwistNormSqDeriv2 f p.2 p.1) := by
  unfold trTwistNormSqDeriv2
  have h0 := continuous_tr_sourceTwist_pair f
  have h1 := continuous_tr_sourceTwist_pair (momentCompactTest 1 f)
  have h2 := continuous_tr_sourceTwist_pair (momentCompactTest 2 f)
  exact (continuous_const.mul (Complex.continuous_normSq.comp h1)).sub
    (continuous_const.mul
      (((Complex.continuous_re.comp h0).mul (Complex.continuous_re.comp h2)).add
        ((Complex.continuous_im.comp h0).mul (Complex.continuous_im.comp h2))))

private theorem hasDerivAt_weightedMomentReading {W : ℂ → ℝ} (hW_cont : Continuous W)
    (hW_supp : HasCompactSupport W) (hW_nn : ∀ z, 0 ≤ W z)
    (f : CompactTest) (L : ℝ) (j : ℕ) (γ₀ : ℝ) :
    HasDerivAt (fun γ : ℝ => weightedMomentReading W (sourceTwist γ f) L j)
      (weightedMomentDeriv1 W f L j γ₀) γ₀ := by
  obtain ⟨A₀, hA₀1, hA₀⟩ := norm_tr_le_sourceGaussian f
  obtain ⟨A₁, hA₁1, hA₁⟩ := norm_tr_le_sourceGaussian (momentCompactTest 1 f)
  let dk : ℂ → ℝ := fun z => depthKernel L (z.re - 1 / 2) ^ j
  have hdk_cont : Continuous dk := by
    dsimp [dk]; unfold depthKernel
    exact ((continuous_const.mul (Real.continuous_cosh.comp
      ((continuous_const.mul (Complex.continuous_re.sub continuous_const)).mul
        continuous_const))).sub continuous_const).pow j
  let F : ℝ → ℂ → ℝ := fun γ z => W z * (Complex.normSq (tr (sourceTwist γ f).1 z) * dk z)
  let F' : ℝ → ℂ → ℝ := fun γ z => W z * (trTwistNormSqDeriv1 f z γ * dk z)
  let bound : ℂ → ℝ := fun z =>
    W z * (((A₀ ^ 2 + A₁ ^ 2) * Real.exp (2 * (‖z‖ + |γ₀| + 1) ^ 2)) * dk z)
  have hdom := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (s := Metric.ball γ₀ 1) (x₀ := γ₀) (F := F) (F' := F') (bound := bound)
    (Metric.ball_mem_nhds γ₀ zero_lt_one)
    (Eventually.of_forall fun γ =>
      (hW_cont.mul ((Complex.continuous_normSq.comp
        ((continuous_tr_sourceTwist_pair f).comp (continuous_const.prodMk continuous_id))).mul
        hdk_cont)).aestronglyMeasurable)
    ((hW_cont.mul ((Complex.continuous_normSq.comp
        ((continuous_tr_sourceTwist_pair f).comp (continuous_const.prodMk continuous_id))).mul
        hdk_cont)).integrable_of_hasCompactSupport hW_supp.mul_right)
    ((hW_cont.mul (((continuous_trTwistNormSqDeriv1_pair f).comp
        (continuous_const.prodMk continuous_id)).mul hdk_cont)).aestronglyMeasurable)
    (Eventually.of_forall fun z γ hγ => by
      dsimp [F', bound]
      have hb0 := normSq_tr_sourceTwist_le_ball f (by linarith only [hA₀1]) hA₀ hγ z
      have hb1 := normSq_tr_sourceTwist_le_ball (momentCompactTest 1 f)
        (by linarith only [hA₁1]) hA₁ hγ z
      have hd1 := abs_trTwistNormSqDeriv1_le f z γ zero_lt_one
      rw [one_mul, inv_one, one_mul] at hd1
      have hdk_nn : 0 ≤ dk z := pow_nonneg (depthKernel_nonneg _ _) j
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hW_nn z), abs_of_nonneg hdk_nn]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hdk_nn) (hW_nn z)
      exact (hd1.trans (add_le_add hb0 hb1)).trans_eq (by ring))
    ((hW_cont.mul (((continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul (((continuous_norm.add continuous_const).add
          continuous_const).pow 2)))).mul hdk_cont))).integrable_of_hasCompactSupport
        hW_supp.mul_right)
    (Eventually.of_forall fun z γ _ => by
      dsimp [F, F']
      exact ((hasDerivAt_normSq_tr_sourceTwist f z γ).mul_const (dk z)).const_mul (W z))
  exact hdom.2.const_mul Real.pi⁻¹

private theorem hasDerivAt_weightedMomentDeriv1 {W : ℂ → ℝ} (hW_cont : Continuous W)
    (hW_supp : HasCompactSupport W) (hW_nn : ∀ z, 0 ≤ W z)
    (f : CompactTest) (L : ℝ) (j : ℕ) (γ₀ : ℝ) :
    HasDerivAt (weightedMomentDeriv1 W f L j)
      (weightedMomentDeriv2 W f L j γ₀) γ₀ := by
  obtain ⟨A₀, hA₀1, hA₀⟩ := norm_tr_le_sourceGaussian f
  obtain ⟨A₁, hA₁1, hA₁⟩ := norm_tr_le_sourceGaussian (momentCompactTest 1 f)
  obtain ⟨A₂, hA₂1, hA₂⟩ := norm_tr_le_sourceGaussian (momentCompactTest 2 f)
  let dk : ℂ → ℝ := fun z => depthKernel L (z.re - 1 / 2) ^ j
  have hdk_cont : Continuous dk := by
    dsimp [dk]; unfold depthKernel
    exact ((continuous_const.mul (Real.continuous_cosh.comp
      ((continuous_const.mul (Complex.continuous_re.sub continuous_const)).mul
        continuous_const))).sub continuous_const).pow j
  let F : ℝ → ℂ → ℝ := fun γ z => W z * (trTwistNormSqDeriv1 f z γ * dk z)
  let F' : ℝ → ℂ → ℝ := fun γ z => W z * (trTwistNormSqDeriv2 f z γ * dk z)
  let bound : ℂ → ℝ := fun z =>
    W z * (((A₀ ^ 2 + 2 * A₁ ^ 2 + A₂ ^ 2) * Real.exp (2 * (‖z‖ + |γ₀| + 1) ^ 2)) * dk z)
  have hdom := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (s := Metric.ball γ₀ 1) (x₀ := γ₀) (F := F) (F' := F') (bound := bound)
    (Metric.ball_mem_nhds γ₀ zero_lt_one)
    (Eventually.of_forall fun γ =>
      (hW_cont.mul (((continuous_trTwistNormSqDeriv1_pair f).comp
        (continuous_const.prodMk continuous_id)).mul hdk_cont)).aestronglyMeasurable)
    ((hW_cont.mul (((continuous_trTwistNormSqDeriv1_pair f).comp
        (continuous_const.prodMk continuous_id)).mul
        hdk_cont)).integrable_of_hasCompactSupport hW_supp.mul_right)
    ((hW_cont.mul (((continuous_trTwistNormSqDeriv2_pair f).comp
        (continuous_const.prodMk continuous_id)).mul hdk_cont)).aestronglyMeasurable)
    (Eventually.of_forall fun z γ hγ => by
      dsimp [F', bound]
      have hb0 := normSq_tr_sourceTwist_le_ball f (by linarith only [hA₀1]) hA₀ hγ z
      have hb1 := normSq_tr_sourceTwist_le_ball (momentCompactTest 1 f)
        (by linarith only [hA₁1]) hA₁ hγ z
      have hb2 := normSq_tr_sourceTwist_le_ball (momentCompactTest 2 f)
        (by linarith only [hA₂1]) hA₂ hγ z
      have hd2 := abs_trTwistNormSqDeriv2_le f z γ
      have hdk_nn : 0 ≤ dk z := pow_nonneg (depthKernel_nonneg _ _) j
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hW_nn z), abs_of_nonneg hdk_nn]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hdk_nn) (hW_nn z)
      exact (hd2.trans (add_le_add (add_le_add hb0 (mul_le_mul_of_nonneg_left hb1 zero_le_two))
        hb2)).trans_eq (by ring))
    ((hW_cont.mul (((continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul (((continuous_norm.add continuous_const).add
          continuous_const).pow 2)))).mul hdk_cont))).integrable_of_hasCompactSupport
        hW_supp.mul_right)
    (Eventually.of_forall fun z γ _ => by
      dsimp [F, F']
      exact ((hasDerivAt_trTwistNormSqDeriv1 f z γ).mul_const (dk z)).const_mul (W z))
  exact hdom.2.const_mul Real.pi⁻¹

private theorem continuous_weightedMomentDeriv2 {W : ℂ → ℝ} (hW_cont : Continuous W)
    (hW_supp : HasCompactSupport W) (f : CompactTest) (L : ℝ) (j : ℕ) :
    Continuous (weightedMomentDeriv2 W f L j) := by
  unfold weightedMomentDeriv2
  let dk : ℂ → ℝ := fun z => depthKernel L (z.re - 1 / 2) ^ j
  have hdk_cont : Continuous dk := by
    dsimp [dk]; unfold depthKernel
    exact ((continuous_const.mul (Real.continuous_cosh.comp
      ((continuous_const.mul (Complex.continuous_re.sub continuous_const)).mul
        continuous_const))).sub continuous_const).pow j
  let G : ℝ → ℂ → ℝ := fun γ z => W z * (trTwistNormSqDeriv2 f z γ * dk z)
  have hG_cont : Continuous G.uncurry :=
    (hW_cont.comp continuous_snd).mul
      (((continuous_trTwistNormSqDeriv2_pair f).mul (hdk_cont.comp continuous_snd)))
  have hint : Continuous (fun γ : ℝ => ∫ z : ℂ, G γ z) := by
    rw [← continuousOn_univ]
    refine continuousOn_integral_of_compact_support hW_supp hG_cont.continuousOn ?_
    intro γ z _ hz
    dsimp [G]
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
  exact continuous_const.mul hint

private theorem abs_weightedMomentDeriv1_le {W : ℂ → ℝ} (hW_cont : Continuous W)
    (hW_supp : HasCompactSupport W) (hW_nn : ∀ z, 0 ≤ W z)
    (f : CompactTest) (L : ℝ) (j : ℕ) (γ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    |weightedMomentDeriv1 W f L j γ| ≤
      κ * weightedMomentReading W (sourceTwist γ f) L j +
        κ⁻¹ * weightedMomentReading W (sourceTwist γ (momentCompactTest 1 f)) L j := by
  unfold weightedMomentDeriv1 weightedMomentReading
  let dk : ℂ → ℝ := fun z => depthKernel L (z.re - 1 / 2) ^ j
  have hdk_cont : Continuous dk := by
    dsimp [dk]; unfold depthKernel
    exact ((continuous_const.mul (Real.continuous_cosh.comp
      ((continuous_const.mul (Complex.continuous_re.sub continuous_const)).mul
        continuous_const))).sub continuous_const).pow j
  have hint_abs : Integrable
      (fun z : ℂ => |W z * (trTwistNormSqDeriv1 f z γ * dk z)|) volume :=
    ((hW_cont.mul (((continuous_trTwistNormSqDeriv1_pair f).comp
      (continuous_const.prodMk continuous_id)).mul
      hdk_cont)).abs).integrable_of_hasCompactSupport (hW_supp.mul_right.norm)
  have hint0 : Integrable
      (fun z : ℂ => W z * (Complex.normSq (tr (sourceTwist γ f).1 z) * dk z)) volume :=
    (hW_cont.mul ((Complex.continuous_normSq.comp
      ((continuous_tr_sourceTwist_pair f).comp (continuous_const.prodMk continuous_id))).mul
      hdk_cont)).integrable_of_hasCompactSupport hW_supp.mul_right
  have hint1 : Integrable
      (fun z : ℂ =>
        W z * (Complex.normSq (tr (sourceTwist γ (momentCompactTest 1 f)).1 z) * dk z)) volume :=
    (hW_cont.mul ((Complex.continuous_normSq.comp
      ((continuous_tr_sourceTwist_pair (momentCompactTest 1 f)).comp
        (continuous_const.prodMk continuous_id))).mul
      hdk_cont)).integrable_of_hasCompactSupport hW_supp.mul_right
  rw [abs_mul, abs_of_pos (inv_pos.mpr Real.pi_pos)]
  have hnorm := norm_integral_le_integral_norm
    (fun z : ℂ => W z * (trTwistNormSqDeriv1 f z γ * dk z))
  simp only [Real.norm_eq_abs] at hnorm
  have hmono : (∫ z : ℂ, |W z * (trTwistNormSqDeriv1 f z γ * dk z)|) ≤
      ∫ z : ℂ, (κ * (W z * (Complex.normSq (tr (sourceTwist γ f).1 z) * dk z)) +
        κ⁻¹ * (W z * (Complex.normSq (tr (sourceTwist γ (momentCompactTest 1 f)).1 z) * dk z))) := by
    refine MeasureTheory.integral_mono hint_abs ((hint0.const_mul κ).add (hint1.const_mul κ⁻¹))
      fun z => ?_
    have hdk_nn : 0 ≤ dk z := pow_nonneg (depthKernel_nonneg _ _) j
    rw [abs_mul, abs_mul, abs_of_nonneg (hW_nn z), abs_of_nonneg hdk_nn]
    have h1 := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (abs_trTwistNormSqDeriv1_le f z γ hκ) hdk_nn) (hW_nn z)
    exact h1.trans_eq (by ring)
  rw [MeasureTheory.integral_add (hint0.const_mul κ) (hint1.const_mul κ⁻¹),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hmono
  exact (mul_le_mul_of_nonneg_left (hnorm.trans hmono) (inv_nonneg.mpr Real.pi_pos.le)).trans_eq
    (by ring)

private theorem abs_weightedMomentDeriv2_le {W : ℂ → ℝ} (hW_cont : Continuous W)
    (hW_supp : HasCompactSupport W) (hW_nn : ∀ z, 0 ≤ W z)
    (f : CompactTest) (L : ℝ) (j : ℕ) (γ : ℝ) :
    |weightedMomentDeriv2 W f L j γ| ≤
      weightedMomentReading W (sourceTwist γ f) L j +
        2 * weightedMomentReading W (sourceTwist γ (momentCompactTest 1 f)) L j +
        weightedMomentReading W (sourceTwist γ (momentCompactTest 2 f)) L j := by
  unfold weightedMomentDeriv2 weightedMomentReading
  let dk : ℂ → ℝ := fun z => depthKernel L (z.re - 1 / 2) ^ j
  have hdk_cont : Continuous dk := by
    dsimp [dk]; unfold depthKernel
    exact ((continuous_const.mul (Real.continuous_cosh.comp
      ((continuous_const.mul (Complex.continuous_re.sub continuous_const)).mul
        continuous_const))).sub continuous_const).pow j
  have hint_abs : Integrable
      (fun z : ℂ => |W z * (trTwistNormSqDeriv2 f z γ * dk z)|) volume :=
    ((hW_cont.mul (((continuous_trTwistNormSqDeriv2_pair f).comp
      (continuous_const.prodMk continuous_id)).mul
      hdk_cont)).abs).integrable_of_hasCompactSupport (hW_supp.mul_right.norm)
  have hint_m : ∀ g : CompactTest, Integrable
      (fun z : ℂ => W z * (Complex.normSq (tr (sourceTwist γ g).1 z) * dk z)) volume := fun g =>
    (hW_cont.mul ((Complex.continuous_normSq.comp
      ((continuous_tr_sourceTwist_pair g).comp (continuous_const.prodMk continuous_id))).mul
      hdk_cont)).integrable_of_hasCompactSupport hW_supp.mul_right
  rw [abs_mul, abs_of_pos (inv_pos.mpr Real.pi_pos)]
  have hnorm := norm_integral_le_integral_norm
    (fun z : ℂ => W z * (trTwistNormSqDeriv2 f z γ * dk z))
  simp only [Real.norm_eq_abs] at hnorm
  have hmono : (∫ z : ℂ, |W z * (trTwistNormSqDeriv2 f z γ * dk z)|) ≤
      ∫ z : ℂ, ((W z * (Complex.normSq (tr (sourceTwist γ f).1 z) * dk z) +
          2 * (W z * (Complex.normSq (tr (sourceTwist γ (momentCompactTest 1 f)).1 z) * dk z))) +
        W z * (Complex.normSq (tr (sourceTwist γ (momentCompactTest 2 f)).1 z) * dk z)) := by
    refine MeasureTheory.integral_mono hint_abs
      (((hint_m f).add ((hint_m (momentCompactTest 1 f)).const_mul 2)).add
        (hint_m (momentCompactTest 2 f))) fun z => ?_
    have hdk_nn : 0 ≤ dk z := pow_nonneg (depthKernel_nonneg _ _) j
    rw [abs_mul, abs_mul, abs_of_nonneg (hW_nn z), abs_of_nonneg hdk_nn]
    have h1 := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (abs_trTwistNormSqDeriv2_le f z γ) hdk_nn) (hW_nn z)
    exact h1.trans_eq (by ring)
  rw [MeasureTheory.integral_add ((hint_m f).add ((hint_m (momentCompactTest 1 f)).const_mul 2))
      (hint_m (momentCompactTest 2 f)),
    MeasureTheory.integral_add (hint_m f) ((hint_m (momentCompactTest 1 f)).const_mul 2),
    MeasureTheory.integral_const_mul] at hmono
  exact (mul_le_mul_of_nonneg_left (hnorm.trans hmono) (inv_nonneg.mpr Real.pi_pos.le)).trans_eq
    (by ring)

private def finThetaWeight (n : ℕ) (z : ℂ) : ℝ :=
  sourceCutoff n z *
    finiteThetaSourceCurvature (explicitSourceRegulator n) (explicitThetaIntegerCutoff n) z

private def polyThetaWeight (n : ℕ) (z : ℂ) : ℝ :=
  stripSourceCutoff n z *
    finiteThetaSourceCurvature (polynomialSourceRegulator n) (polynomialThetaIntegerCutoff n) z

private theorem continuous_finThetaWeight (n : ℕ) : Continuous (finThetaWeight n) :=
  (sourceCutoff n).contDiff.continuous.mul
    (continuous_finiteThetaSourceCurvature (explicitSourceRegulator_pos n) _)

private theorem hasCompactSupport_finThetaWeight (n : ℕ) : HasCompactSupport (finThetaWeight n) :=
  (sourceCutoff n).hasCompactSupport.mul_right

private theorem finThetaWeight_nonneg (n : ℕ) (z : ℂ) : 0 ≤ finThetaWeight n z :=
  mul_nonneg (sourceCutoff n).nonneg
    (finiteThetaSourceCurvature_nonneg (explicitSourceRegulator_pos n).le _ z)

private theorem weightedMomentReading_finThetaWeight_eq (f : CompactTest) (L : ℝ) (j n : ℕ) :
    weightedMomentReading (finThetaWeight n) f L j = finiteThetaSourceMomentReading f L j n := by
  unfold weightedMomentReading finThetaWeight finiteThetaSourceMomentReading
    finiteThetaSourceReading sourceDepthKernel
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun z => by ring)

private theorem continuous_polyThetaWeight (n : ℕ) : Continuous (polyThetaWeight n) :=
  (contDiff_stripSourceCutoff n).continuous.mul
    (continuous_finiteThetaSourceCurvature (polynomialSourceRegulator_pos n) _)

private theorem hasCompactSupport_polyThetaWeight (n : ℕ) : HasCompactSupport (polyThetaWeight n) :=
  (hasCompactSupport_stripSourceCutoff n).mul_right

private theorem polyThetaWeight_nonneg (n : ℕ) (z : ℂ) : 0 ≤ polyThetaWeight n z :=
  mul_nonneg (stripSourceCutoff_nonneg n z)
    (finiteThetaSourceCurvature_nonneg (polynomialSourceRegulator_pos n).le _ z)

private theorem weightedMomentReading_polyThetaWeight_eq (f : CompactTest) (L : ℝ) (j n : ℕ) :
    weightedMomentReading (polyThetaWeight n) f L j =
      polynomialThetaSourceMomentReading f L j n := by
  unfold weightedMomentReading polyThetaWeight polynomialThetaSourceMomentReading
    polynomialThetaSourceReading sourceDepthKernel
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun z => by ring)

theorem differentiable_finiteThetaSourceMomentReading_sourceTwist
    (f : CompactTest) (L : ℝ) (j n : ℕ) :
    Differentiable ℝ (fun γ : ℝ => finiteThetaSourceMomentReading (sourceTwist γ f) L j n) := by
  simp_rw [← weightedMomentReading_finThetaWeight_eq]
  exact fun γ => (hasDerivAt_weightedMomentReading (continuous_finThetaWeight n)
    (hasCompactSupport_finThetaWeight n) (finThetaWeight_nonneg n) f L j γ).differentiableAt

theorem differentiable_deriv_finiteThetaSourceMomentReading_sourceTwist
    (f : CompactTest) (L : ℝ) (j n : ℕ) :
    Differentiable ℝ
      (deriv (fun γ : ℝ => finiteThetaSourceMomentReading (sourceTwist γ f) L j n)) := by
  simp_rw [← weightedMomentReading_finThetaWeight_eq]
  have heq : deriv (fun γ : ℝ => weightedMomentReading (finThetaWeight n) (sourceTwist γ f) L j) =
      weightedMomentDeriv1 (finThetaWeight n) f L j :=
    funext fun γ => (hasDerivAt_weightedMomentReading (continuous_finThetaWeight n)
      (hasCompactSupport_finThetaWeight n) (finThetaWeight_nonneg n) f L j γ).deriv
  rw [heq]
  exact fun γ => (hasDerivAt_weightedMomentDeriv1 (continuous_finThetaWeight n)
    (hasCompactSupport_finThetaWeight n) (finThetaWeight_nonneg n) f L j γ).differentiableAt

theorem continuous_deriv2_finiteThetaSourceMomentReading_sourceTwist
    (f : CompactTest) (L : ℝ) (j n : ℕ) :
    Continuous (deriv (deriv
      (fun γ : ℝ => finiteThetaSourceMomentReading (sourceTwist γ f) L j n))) := by
  simp_rw [← weightedMomentReading_finThetaWeight_eq]
  have heq1 : deriv (fun γ : ℝ => weightedMomentReading (finThetaWeight n) (sourceTwist γ f) L j) =
      weightedMomentDeriv1 (finThetaWeight n) f L j :=
    funext fun γ => (hasDerivAt_weightedMomentReading (continuous_finThetaWeight n)
      (hasCompactSupport_finThetaWeight n) (finThetaWeight_nonneg n) f L j γ).deriv
  have heq2 : deriv (weightedMomentDeriv1 (finThetaWeight n) f L j) =
      weightedMomentDeriv2 (finThetaWeight n) f L j :=
    funext fun γ => (hasDerivAt_weightedMomentDeriv1 (continuous_finThetaWeight n)
      (hasCompactSupport_finThetaWeight n) (finThetaWeight_nonneg n) f L j γ).deriv
  rw [heq1, heq2]
  exact continuous_weightedMomentDeriv2 (continuous_finThetaWeight n)
    (hasCompactSupport_finThetaWeight n) f L j

/-- **Stage-Uniform `L`-Lossless First Ordinate Derivative Bound (`finiteThetaSourceMomentReading`).** -/
theorem abs_deriv_finiteThetaSourceMomentReading_le
    (f : CompactTest) (L : ℝ) (j n : ℕ) (γ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    |deriv (fun τ : ℝ => finiteThetaSourceMomentReading (sourceTwist τ f) L j n) γ| ≤
      κ * finiteThetaSourceMomentReading (sourceTwist γ f) L j n +
        κ⁻¹ * finiteThetaSourceMomentReading (sourceTwist γ (momentCompactTest 1 f)) L j n := by
  simp_rw [← weightedMomentReading_finThetaWeight_eq]
  rw [(hasDerivAt_weightedMomentReading (continuous_finThetaWeight n)
    (hasCompactSupport_finThetaWeight n) (finThetaWeight_nonneg n) f L j γ).deriv]
  exact abs_weightedMomentDeriv1_le (continuous_finThetaWeight n)
    (hasCompactSupport_finThetaWeight n) (finThetaWeight_nonneg n) f L j γ hκ

/-- **Stage-Uniform `L`-Lossless Second Ordinate Derivative Bound (`finiteThetaSourceMomentReading`).** -/
theorem abs_deriv_deriv_finiteThetaSourceMomentReading_le
    (f : CompactTest) (L : ℝ) (j n : ℕ) (γ : ℝ) :
    |deriv (deriv (fun τ : ℝ => finiteThetaSourceMomentReading (sourceTwist τ f) L j n)) γ| ≤
      finiteThetaSourceMomentReading (sourceTwist γ f) L j n +
        2 * finiteThetaSourceMomentReading (sourceTwist γ (momentCompactTest 1 f)) L j n +
        finiteThetaSourceMomentReading (sourceTwist γ (momentCompactTest 2 f)) L j n := by
  simp_rw [← weightedMomentReading_finThetaWeight_eq]
  have heq1 : deriv (fun τ : ℝ => weightedMomentReading (finThetaWeight n) (sourceTwist τ f) L j) =
      weightedMomentDeriv1 (finThetaWeight n) f L j :=
    funext fun τ => (hasDerivAt_weightedMomentReading (continuous_finThetaWeight n)
      (hasCompactSupport_finThetaWeight n) (finThetaWeight_nonneg n) f L j τ).deriv
  rw [heq1, (hasDerivAt_weightedMomentDeriv1 (continuous_finThetaWeight n)
    (hasCompactSupport_finThetaWeight n) (finThetaWeight_nonneg n) f L j γ).deriv]
  exact abs_weightedMomentDeriv2_le (continuous_finThetaWeight n)
    (hasCompactSupport_finThetaWeight n) (finThetaWeight_nonneg n) f L j γ

theorem differentiable_polynomialThetaSourceMomentReading_sourceTwist
    (f : CompactTest) (L : ℝ) (j n : ℕ) :
    Differentiable ℝ
      (fun γ : ℝ => polynomialThetaSourceMomentReading (sourceTwist γ f) L j n) := by
  simp_rw [← weightedMomentReading_polyThetaWeight_eq]
  exact fun γ => (hasDerivAt_weightedMomentReading (continuous_polyThetaWeight n)
    (hasCompactSupport_polyThetaWeight n) (polyThetaWeight_nonneg n) f L j γ).differentiableAt

theorem differentiable_deriv_polynomialThetaSourceMomentReading_sourceTwist
    (f : CompactTest) (L : ℝ) (j n : ℕ) :
    Differentiable ℝ
      (deriv (fun γ : ℝ => polynomialThetaSourceMomentReading (sourceTwist γ f) L j n)) := by
  simp_rw [← weightedMomentReading_polyThetaWeight_eq]
  have heq : deriv (fun γ : ℝ => weightedMomentReading (polyThetaWeight n) (sourceTwist γ f) L j) =
      weightedMomentDeriv1 (polyThetaWeight n) f L j :=
    funext fun γ => (hasDerivAt_weightedMomentReading (continuous_polyThetaWeight n)
      (hasCompactSupport_polyThetaWeight n) (polyThetaWeight_nonneg n) f L j γ).deriv
  rw [heq]
  exact fun γ => (hasDerivAt_weightedMomentDeriv1 (continuous_polyThetaWeight n)
    (hasCompactSupport_polyThetaWeight n) (polyThetaWeight_nonneg n) f L j γ).differentiableAt

theorem continuous_deriv2_polynomialThetaSourceMomentReading_sourceTwist
    (f : CompactTest) (L : ℝ) (j n : ℕ) :
    Continuous (deriv (deriv
      (fun γ : ℝ => polynomialThetaSourceMomentReading (sourceTwist γ f) L j n))) := by
  simp_rw [← weightedMomentReading_polyThetaWeight_eq]
  have heq1 : deriv (fun γ : ℝ => weightedMomentReading (polyThetaWeight n) (sourceTwist γ f) L j) =
      weightedMomentDeriv1 (polyThetaWeight n) f L j :=
    funext fun γ => (hasDerivAt_weightedMomentReading (continuous_polyThetaWeight n)
      (hasCompactSupport_polyThetaWeight n) (polyThetaWeight_nonneg n) f L j γ).deriv
  have heq2 : deriv (weightedMomentDeriv1 (polyThetaWeight n) f L j) =
      weightedMomentDeriv2 (polyThetaWeight n) f L j :=
    funext fun γ => (hasDerivAt_weightedMomentDeriv1 (continuous_polyThetaWeight n)
      (hasCompactSupport_polyThetaWeight n) (polyThetaWeight_nonneg n) f L j γ).deriv
  rw [heq1, heq2]
  exact continuous_weightedMomentDeriv2 (continuous_polyThetaWeight n)
    (hasCompactSupport_polyThetaWeight n) f L j

/-- **Stage-Uniform `L`-Lossless First Ordinate Derivative Bound
(`polynomialThetaSourceMomentReading`).** -/
theorem abs_deriv_polynomialThetaSourceMomentReading_le
    (f : CompactTest) (L : ℝ) (j n : ℕ) (γ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    |deriv (fun τ : ℝ => polynomialThetaSourceMomentReading (sourceTwist τ f) L j n) γ| ≤
      κ * polynomialThetaSourceMomentReading (sourceTwist γ f) L j n +
        κ⁻¹ * polynomialThetaSourceMomentReading (sourceTwist γ (momentCompactTest 1 f)) L j n := by
  simp_rw [← weightedMomentReading_polyThetaWeight_eq]
  rw [(hasDerivAt_weightedMomentReading (continuous_polyThetaWeight n)
    (hasCompactSupport_polyThetaWeight n) (polyThetaWeight_nonneg n) f L j γ).deriv]
  exact abs_weightedMomentDeriv1_le (continuous_polyThetaWeight n)
    (hasCompactSupport_polyThetaWeight n) (polyThetaWeight_nonneg n) f L j γ hκ

/-- **Stage-Uniform `L`-Lossless Second Ordinate Derivative Bound
(`polynomialThetaSourceMomentReading`).** -/
theorem abs_deriv_deriv_polynomialThetaSourceMomentReading_le
    (f : CompactTest) (L : ℝ) (j n : ℕ) (γ : ℝ) :
    |deriv (deriv (fun τ : ℝ => polynomialThetaSourceMomentReading (sourceTwist τ f) L j n)) γ| ≤
      polynomialThetaSourceMomentReading (sourceTwist γ f) L j n +
        2 * polynomialThetaSourceMomentReading (sourceTwist γ (momentCompactTest 1 f)) L j n +
        polynomialThetaSourceMomentReading (sourceTwist γ (momentCompactTest 2 f)) L j n := by
  simp_rw [← weightedMomentReading_polyThetaWeight_eq]
  have heq1 : deriv (fun τ : ℝ => weightedMomentReading (polyThetaWeight n) (sourceTwist τ f) L j) =
      weightedMomentDeriv1 (polyThetaWeight n) f L j :=
    funext fun τ => (hasDerivAt_weightedMomentReading (continuous_polyThetaWeight n)
      (hasCompactSupport_polyThetaWeight n) (polyThetaWeight_nonneg n) f L j τ).deriv
  rw [heq1, (hasDerivAt_weightedMomentDeriv1 (continuous_polyThetaWeight n)
    (hasCompactSupport_polyThetaWeight n) (polyThetaWeight_nonneg n) f L j γ).deriv]
  exact abs_weightedMomentDeriv2_le (continuous_polyThetaWeight n)
    (hasCompactSupport_polyThetaWeight n) (polyThetaWeight_nonneg n) f L j γ


/-! ## §2. 1D unit-window oscillation, Taylor mean-minus-min, Sobolev bounds, and sliding windows -/

/-- Attainment of `sInf` on `[T, T + 1]` and inequality `sInf ≤ ∫_T^{T+1} g ≤ sSup`. -/
theorem exists_unitWindow_sInf_eq_and_le_mean_le_sSup {g : ℝ → ℝ} (T : ℝ)
    (hg : ContinuousOn g (Icc T (T + 1))) :
    (∃ γ_min ∈ Icc T (T + 1), sInf (g '' Icc T (T + 1)) = g γ_min ∧
      ∀ γ ∈ Icc T (T + 1), g γ_min ≤ g γ) ∧
    sInf (g '' Icc T (T + 1)) ≤ (∫ γ in Icc T (T + 1), g γ) ∧
    (∫ γ in Icc T (T + 1), g γ) ≤ sSup (g '' Icc T (T + 1)) := by
  have hne : (Icc T (T + 1)).Nonempty := ⟨T, le_rfl, by linarith⟩
  obtain ⟨γ_min, hγ_min, hmin_eq, hmin_le⟩ :=
    isCompact_Icc.exists_sInf_image_eq_and_le hne hg
  obtain ⟨γ_max, hγ_max, hmax_eq, hmax_ge⟩ :=
    isCompact_Icc.exists_sSup_image_eq_and_ge hne hg
  have hint : IntegrableOn g (Icc T (T + 1)) volume := hg.integrableOn_compact isCompact_Icc
  have hvol : volume.real (Icc T (T + 1)) = 1 := by
    rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  have hc1 : IntegrableOn (fun _ : ℝ => g γ_min) (Icc T (T + 1)) volume :=
    integrableOn_const (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hc2 : IntegrableOn (fun _ : ℝ => g γ_max) (Icc T (T + 1)) volume :=
    integrableOn_const (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hlo := setIntegral_mono_on hc1 hint measurableSet_Icc hmin_le
  have hhi := setIntegral_mono_on hint hc2 measurableSet_Icc hmax_ge
  rw [setIntegral_const, hvol, one_smul] at hlo hhi
  exact ⟨⟨γ_min, hγ_min, hmin_eq, hmin_le⟩, hmin_eq.trans_le hlo, hhi.trans_eq hmax_eq.symm⟩

/-- Equivalence between `sInf (g '' Icc T (T + 1)) ≤ C` and `∃ γ ∈ Icc T (T + 1), g γ ≤ C` for
continuous `g`. -/
theorem sInf_unitWindow_le_iff_exists_le {g : ℝ → ℝ} {T C : ℝ}
    (hg : ContinuousOn g (Icc T (T + 1))) :
    sInf (g '' Icc T (T + 1)) ≤ C ↔ ∃ γ ∈ Icc T (T + 1), g γ ≤ C := by
  obtain ⟨⟨γ_min, hγ_min, hmin_eq, hmin_le⟩, _, _⟩ :=
    exists_unitWindow_sInf_eq_and_le_mean_le_sSup T hg
  constructor
  · intro hle
    exact ⟨γ_min, hγ_min, hmin_eq ▸ hle⟩
  · rintro ⟨γ, hγ, hγC⟩
    exact (hmin_eq.trans_le (hmin_le γ hγ)).trans hγC

/-- **First-Derivative Unit-Window Mean-Minus-Min Bound (`≤ 1 / 2 * M₁`).**
Since `∫_T^{T+1} |γ - γ_*| dγ = ((γ_* - T)² + (T + 1 - γ_*)²) / 2 ≤ 1 / 2` for every
`γ_* ∈ [T, T + 1]`, the unit-window mean exceeds the unit-window minimum by at most `(1/2) M₁`. -/
theorem unitWindow_mean_sub_min_le_half_sup_deriv {g : ℝ → ℝ} (T : ℝ) {M₁ : ℝ}
    (hM₁ : 0 ≤ M₁) (hg_diff : Differentiable ℝ g) (hg'_cont : Continuous (deriv g))
    (hbd : ∀ γ ∈ Icc T (T + 1), |deriv g γ| ≤ M₁) :
    (∫ γ in Icc T (T + 1), g γ) - sInf (g '' Icc T (T + 1)) ≤ (1 / 2) * M₁ := by
  obtain ⟨⟨γ_min, hγ_min, hmin_eq, _⟩, _, _⟩ :=
    exists_unitWindow_sInf_eq_and_le_mean_le_sSup T hg_diff.continuous.continuousOn
  rw [hmin_eq]
  have hlip : ∀ γ ∈ Icc T (T + 1), g γ - g γ_min ≤ M₁ * |γ - γ_min| := by
    intro γ hγ
    have hftc : (∫ u in γ_min..γ, deriv g u) = g γ - g γ_min :=
      integral_eq_sub_of_hasDerivAt (fun u _ => hg_diff.differentiableAt.hasDerivAt)
        (hg'_cont.intervalIntegrable (μ := volume) _ _)
    have huIoc : Set.uIoc γ_min γ ⊆ Icc T (T + 1) :=
      uIoc_subset_uIcc.trans (uIcc_subset_Icc hγ_min hγ)
    have hnorm := norm_integral_le_of_norm_le_const (a := γ_min) (b := γ) (C := M₁)
      (f := deriv g) fun u hu => by
        rw [Real.norm_eq_abs]
        exact hbd u (huIoc hu)
    rw [hftc, Real.norm_eq_abs] at hnorm
    exact (le_abs_self _).trans hnorm
  have hint_g : IntegrableOn g (Icc T (T + 1)) volume :=
    hg_diff.continuous.continuousOn.integrableOn_compact isCompact_Icc
  have hint_c : IntegrableOn (fun _ : ℝ => g γ_min) (Icc T (T + 1)) volume :=
    integrableOn_const (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hvol : volume.real (Icc T (T + 1)) = 1 := by
    rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  have hsub_int : (∫ γ in Icc T (T + 1), g γ) - g γ_min =
      ∫ γ in T..(T + 1), (g γ - g γ_min) := by
    rw [← MeasureTheory.integral_Icc_eq_integral_Ioc, integral_of_le (by linarith : T ≤ T + 1),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_sub hint_g hint_c,
      setIntegral_const, hvol, one_smul]
  rw [hsub_int]
  have hi_lhs : IntervalIntegrable (fun γ : ℝ => g γ - g γ_min) volume T (T + 1) :=
    (hg_diff.continuous.sub continuous_const).intervalIntegrable (μ := volume) _ _
  have hi_rhs : IntervalIntegrable (fun γ : ℝ => M₁ * |γ - γ_min|) volume T (T + 1) :=
    (continuous_const.mul (continuous_id.sub continuous_const).abs).intervalIntegrable
      (μ := volume) _ _
  have hmono := integral_mono_on (μ := volume) (by linarith : T ≤ T + 1) hi_lhs hi_rhs hlip
  rw [intervalIntegral.integral_const_mul] at hmono
  have hint_abs : (∫ γ in T..(T + 1), |γ - γ_min|) ≤ 1 / 2 := by
    have hsplit := (integral_add_adjacent_intervals
      (a := T) (b := γ_min) (c := T + 1) (f := fun γ : ℝ => |γ - γ_min|)
      ((continuous_id.sub continuous_const).abs.intervalIntegrable (μ := volume) _ _)
      ((continuous_id.sub continuous_const).abs.intervalIntegrable (μ := volume) _ _)).symm
    rw [hsplit]
    have hleft : (∫ γ in T..γ_min, |γ - γ_min|) = (γ_min - T) ^ 2 / 2 := by
      have hcongr : EqOn (fun γ : ℝ => |γ - γ_min|) (fun γ : ℝ => γ_min - γ)
          (Set.uIcc T γ_min) := by
        rw [uIcc_of_le hγ_min.1]
        intro γ hγ
        rw [abs_of_nonpos (by linarith only [hγ.2])]
        ring
      rw [integral_congr hcongr,
        integral_eq_sub_of_hasDerivAt (f := fun γ : ℝ => -(γ_min - γ) ^ 2 / 2)
          (fun γ _ => by
            have h1 : HasDerivAt (fun u : ℝ => γ_min - u) (-1) γ :=
              (hasDerivAt_const γ γ_min).sub (hasDerivAt_id γ) |>.congr_deriv (by ring)
            exact (((h1.pow 2).neg).div_const 2).congr_deriv (by ring))
          ((by fun_prop : Continuous _).intervalIntegrable (μ := volume) _ _)]
      ring
    have hright : (∫ γ in γ_min..(T + 1), |γ - γ_min|) = (T + 1 - γ_min) ^ 2 / 2 := by
      have hcongr : EqOn (fun γ : ℝ => |γ - γ_min|) (fun γ : ℝ => γ - γ_min)
          (Set.uIcc γ_min (T + 1)) := by
        rw [uIcc_of_le hγ_min.2]
        intro γ hγ
        exact abs_of_nonneg (by linarith only [hγ.1])
      rw [integral_congr hcongr,
        integral_eq_sub_of_hasDerivAt (f := fun γ : ℝ => (γ - γ_min) ^ 2 / 2)
          (fun γ _ => by
            have h1 : HasDerivAt (fun u : ℝ => u - γ_min) 1 γ :=
              ((hasDerivAt_id γ).sub (hasDerivAt_const γ γ_min)).congr_deriv (by ring)
            exact ((h1.pow 2).div_const 2).congr_deriv (by ring))
          ((by fun_prop : Continuous _).intervalIntegrable (μ := volume) _ _)]
      ring
    rw [hleft, hright]
    have ha : 0 ≤ γ_min - T := by linarith only [hγ_min.1]
    have hb : 0 ≤ T + 1 - γ_min := by linarith only [hγ_min.2]
    nlinarith only [mul_nonneg ha hb]
  exact hmono.trans ((mul_le_mul_of_nonneg_left hint_abs hM₁).trans_eq (by ring))

/-- **Second-Derivative Interior-Minimum Taylor Bound (`≤ 1 / 6 * M₂`).**
At any interior minimizer `γ_* ∈ (T, T + 1)` of `g` on `[T, T + 1]`, `g'(γ_*) = 0`, so quadratic
Taylor expansion and `(γ_* - T)³ + (T + 1 - γ_*)³ ≤ 1` bound `∫_T^{T+1} g - g(γ_*) ≤ (1 / 6) M₂`. -/
theorem unitWindow_mean_sub_interior_min_le_sixth_sup_deriv2 {g : ℝ → ℝ} (T : ℝ)
    {γ_min M₂ : ℝ} (hγ_int : γ_min ∈ Ioo T (T + 1))
    (hmin : IsMinOn g (Icc T (T + 1)) γ_min) (hM₂ : 0 ≤ M₂)
    (hg_diff : Differentiable ℝ g) (hg'_diff : Differentiable ℝ (deriv g))
    (hg''_cont : Continuous (deriv (deriv g)))
    (hbd2 : ∀ γ ∈ Icc T (T + 1), |deriv (deriv g) γ| ≤ M₂) :
    (∫ γ in Icc T (T + 1), g γ) - g γ_min ≤ (1 / 6) * M₂ := by
  have hγ_Icc : γ_min ∈ Icc T (T + 1) := ⟨hγ_int.1.le, hγ_int.2.le⟩
  have hg'_zero : deriv g γ_min = 0 :=
    (hmin.isLocalMin (Icc_mem_nhds hγ_int.1 hγ_int.2)).hasDerivAt_eq_zero
      hg_diff.differentiableAt.hasDerivAt
  have hg'_lip : ∀ u ∈ Icc T (T + 1), |deriv g u| ≤ M₂ * |u - γ_min| := by
    intro u hu
    have hftc : (∫ s in γ_min..u, deriv (deriv g) s) = deriv g u - deriv g γ_min :=
      integral_eq_sub_of_hasDerivAt (fun s _ => hg'_diff.differentiableAt.hasDerivAt)
        (hg''_cont.intervalIntegrable (μ := volume) _ _)
    rw [hg'_zero, sub_zero] at hftc
    have huIoc : Set.uIoc γ_min u ⊆ Icc T (T + 1) :=
      uIoc_subset_uIcc.trans (uIcc_subset_Icc hγ_Icc hu)
    have hnorm := norm_integral_le_of_norm_le_const (a := γ_min) (b := u) (C := M₂)
      (f := deriv (deriv g)) fun s hs => by
        rw [Real.norm_eq_abs]
        exact hbd2 s (huIoc hs)
    rwa [hftc, Real.norm_eq_abs] at hnorm
  have hquad : ∀ γ ∈ Icc T (T + 1), g γ - g γ_min ≤ (M₂ / 2) * (γ - γ_min) ^ 2 := by
    intro γ hγ
    have hftc : (∫ u in γ_min..γ, deriv g u) = g γ - g γ_min :=
      integral_eq_sub_of_hasDerivAt (fun u _ => hg_diff.differentiableAt.hasDerivAt)
        (hg'_diff.continuous.intervalIntegrable (μ := volume) _ _)
    rw [← hftc]
    rcases le_total γ_min γ with hle | hge
    · have hmono := integral_mono_on (μ := volume) hle
        (hg'_diff.continuous.intervalIntegrable (μ := volume) _ _)
        ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable
          (μ := volume) _ _)
        fun u hu => by
          have hu_Icc : u ∈ Icc T (T + 1) := ⟨hγ_Icc.1.trans hu.1, hu.2.trans hγ.2⟩
          have h1 := (le_abs_self _).trans (hg'_lip u hu_Icc)
          rwa [abs_of_nonneg (by linarith only [hu.1])] at h1
      have hrhs : (∫ u in γ_min..γ, M₂ * (u - γ_min)) = (M₂ / 2) * (γ - γ_min) ^ 2 := by
        rw [integral_eq_sub_of_hasDerivAt (f := fun u : ℝ => (M₂ / 2) * (u - γ_min) ^ 2)
          (fun u _ => by
            have h1 : HasDerivAt (fun s : ℝ => s - γ_min) 1 u :=
              ((hasDerivAt_id u).sub (hasDerivAt_const u γ_min)).congr_deriv (by ring)
            exact ((h1.pow 2).const_mul (M₂ / 2)).congr_deriv (by ring))
          ((by fun_prop : Continuous _).intervalIntegrable (μ := volume) _ _)]
        ring
      exact hmono.trans_eq hrhs
    · rw [integral_symm]
      have hmono := integral_mono_on (μ := volume) hge
        (hg'_diff.continuous.neg.intervalIntegrable (μ := volume) _ _)
        ((continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable
          (μ := volume) _ _)
        fun u hu => by
          have hu_Icc : u ∈ Icc T (T + 1) := ⟨hγ.1.trans hu.1, hu.2.trans hγ_Icc.2⟩
          have h1 := (neg_le_abs _).trans (hg'_lip u hu_Icc)
          rwa [abs_of_nonpos (by linarith only [hu.2]), mul_neg, le_neg] at h1
      have h1 : -(∫ u in γ..γ_min, deriv g u) = ∫ u in γ..γ_min, -deriv g u :=
        (intervalIntegral.integral_neg).symm
      rw [h1]
      have hrhs : (∫ u in γ..γ_min, M₂ * (γ_min - u)) = (M₂ / 2) * (γ - γ_min) ^ 2 := by
        rw [integral_eq_sub_of_hasDerivAt (f := fun u : ℝ => -(M₂ / 2) * (γ_min - u) ^ 2)
          (fun u _ => by
            have hd : HasDerivAt (fun s : ℝ => γ_min - s) (-1) u :=
              ((hasDerivAt_const u γ_min).sub (hasDerivAt_id u)).congr_deriv (by ring)
            exact ((hd.pow 2).const_mul (-(M₂ / 2))).congr_deriv (by ring))
          ((by fun_prop : Continuous _).intervalIntegrable (μ := volume) _ _)]
        ring
      exact hmono.trans_eq hrhs
  have hint_g : IntegrableOn g (Icc T (T + 1)) volume :=
    hg_diff.continuous.continuousOn.integrableOn_compact isCompact_Icc
  have hint_c : IntegrableOn (fun _ : ℝ => g γ_min) (Icc T (T + 1)) volume :=
    integrableOn_const (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hvol : volume.real (Icc T (T + 1)) = 1 := by
    rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  have hsub_int : (∫ γ in Icc T (T + 1), g γ) - g γ_min =
      ∫ γ in T..(T + 1), (g γ - g γ_min) := by
    rw [← MeasureTheory.integral_Icc_eq_integral_Ioc, integral_of_le (by linarith : T ≤ T + 1),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_sub hint_g hint_c,
      setIntegral_const, hvol, one_smul]
  rw [hsub_int]
  have hmono := integral_mono_on (μ := volume) (by linarith : T ≤ T + 1)
    ((hg_diff.continuous.sub continuous_const).intervalIntegrable (μ := volume) _ _)
    ((by fun_prop : Continuous fun γ : ℝ => (M₂ / 2) * (γ - γ_min) ^ 2).intervalIntegrable
      (μ := volume) _ _)
    hquad
  rw [intervalIntegral.integral_const_mul] at hmono
  have hint_sq : (∫ γ in T..(T + 1), (γ - γ_min) ^ 2) ≤ 1 / 3 := by
    rw [integral_eq_sub_of_hasDerivAt (f := fun γ : ℝ => (γ - γ_min) ^ 3 / 3)
      (fun γ _ => by
        have h1 : HasDerivAt (fun s : ℝ => s - γ_min) 1 γ :=
          ((hasDerivAt_id γ).sub (hasDerivAt_const γ γ_min)).congr_deriv (by ring)
        exact ((h1.pow 3).div_const 3).congr_deriv (by ring))
      ((by fun_prop : Continuous _).intervalIntegrable (μ := volume) _ _)]
    have ha : 0 ≤ γ_min - T := by linarith only [hγ_Icc.1]
    have hb : 0 ≤ T + 1 - γ_min := by linarith only [hγ_Icc.2]
    have hab : (γ_min - T) + (T + 1 - γ_min) = 1 := by ring
    have hprod : 0 ≤ 3 * (γ_min - T) * (T + 1 - γ_min) * ((γ_min - T) + (T + 1 - γ_min)) := by
      positivity
    nlinarith only [hab, hprod]
  exact hmono.trans ((mul_le_mul_of_nonneg_left hint_sq (by positivity)).trans_eq (by ring))

/-- **1D Unit-Window Sobolev Inequality (`sSup ≤ ∫ g + ∫ |g'|`).** -/
theorem unitWindow_sSup_le_mean_add_l1_deriv {g : ℝ → ℝ} (T : ℝ)
    (hg_diff : Differentiable ℝ g) (hg'_cont : Continuous (deriv g)) :
    sSup (g '' Icc T (T + 1)) ≤
      (∫ γ in Icc T (T + 1), g γ) + (∫ γ in Icc T (T + 1), |deriv g γ|) := by
  obtain ⟨⟨γ_min, hγ_min, hmin_eq, _⟩, hmin_le_mean, _⟩ :=
    exists_unitWindow_sInf_eq_and_le_mean_le_sSup T hg_diff.continuous.continuousOn
  have hne : (g '' Icc T (T + 1)).Nonempty := ⟨g T, T, ⟨le_rfl, by linarith⟩, rfl⟩
  refine csSup_le hne ?_
  rintro _ ⟨γ, hγ, rfl⟩
  have hftc : (∫ u in γ_min..γ, deriv g u) = g γ - g γ_min :=
    integral_eq_sub_of_hasDerivAt (fun u _ => hg_diff.differentiableAt.hasDerivAt)
      (hg'_cont.intervalIntegrable (μ := volume) _ _)
  have hnorm : |∫ u in γ_min..γ, deriv g u| ≤ ∫ u in Icc T (T + 1), |deriv g u| := by
    have h1 : |∫ u in γ_min..γ, deriv g u| = |∫ u in Set.uIoc γ_min γ, deriv g u| :=
      abs_integral_eq_abs_integral_uIoc (deriv g)
    have h2 : |∫ u in Set.uIoc γ_min γ, deriv g u| ≤ ∫ u in Set.uIoc γ_min γ, |deriv g u| := by
      simpa only [Real.norm_eq_abs] using
        MeasureTheory.norm_integral_le_integral_norm (f := deriv g)
          (μ := volume.restrict (Set.uIoc γ_min γ))
    have hsub : Set.uIoc γ_min γ ⊆ Icc T (T + 1) :=
      uIoc_subset_uIcc.trans (uIcc_subset_Icc hγ_min hγ)
    have h3 : (∫ u in Set.uIoc γ_min γ, |deriv g u|) ≤ ∫ u in Icc T (T + 1), |deriv g u| :=
      setIntegral_mono_set (hg'_cont.abs.continuousOn.integrableOn_compact isCompact_Icc)
        (Eventually.of_forall fun _ => abs_nonneg _) hsub.eventuallyLE
    exact (h1.trans_le h2).trans h3
  rw [hftc] at hnorm
  have hdiff_le : g γ - g γ_min ≤ ∫ u in Icc T (T + 1), |deriv g u| :=
    (le_abs_self _).trans hnorm
  have hmin_val : g γ_min ≤ ∫ u in Icc T (T + 1), g u := hmin_eq ▸ hmin_le_mean
  linarith only [hdiff_le, hmin_val]


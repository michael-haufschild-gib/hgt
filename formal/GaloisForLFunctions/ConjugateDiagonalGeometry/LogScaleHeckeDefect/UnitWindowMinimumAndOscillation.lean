import GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.HalfGateClosureAndDensityEquivalence
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheIndexExit
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Unit-Window Minimum Selection, Ordinate Oscillation Calculus, and Separation Classification

This module establishes the ordinate (`γ`) oscillation calculus for Criterion 5 of
`riemannHypothesis_finiteTheta_poleNodal_dyadic_tfae`
(`min_{γ ∈ [T, T + 1]} finiteThetaSourceMomentReading (baseTwistTest γ) L_k(T) 1 (apertureStage L_k(T) T)`)
on `finiteThetaSourceMomentReading` and `polynomialThetaSourceMomentReading` and isolates the
three-way separation between unit-window minimum selection, unit-window mean control
(`heckeDefect_log_unitWindow_tfae`), and dyadic variation:

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
open ArithmeticPolarization SquareRootThreshold _root_.RHTower _root_.Zeta23
open _root_.RHTower.DeBruijn _root_.RHTower.BacklundConverse

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
  have hF_cont : ∀ γ : ℝ, Continuous (F γ) := fun γ =>
    ((Complex.continuous_exp.comp
        (continuous_neg.comp (((continuous_const (y := (γ : ℂ))).mul
          (continuous_const (y := I))).mul Complex.continuous_ofReal))).mul f.2.1.continuous).mul
      (Complex.continuous_exp.comp ((continuous_const (y := z - 1 / 2)).mul
        Complex.continuous_ofReal))
  have hF'_cont : Continuous (F' γ₀) :=
    (continuous_const (y := -I)).mul
      (((Complex.continuous_exp.comp
          (continuous_neg.comp (((continuous_const (y := (γ₀ : ℂ))).mul
            (continuous_const (y := I))).mul Complex.continuous_ofReal))).mul
        ((Complex.continuous_ofReal.pow 1).mul f.2.1.continuous)).mul
        (Complex.continuous_exp.comp ((continuous_const (y := z - 1 / 2)).mul
          Complex.continuous_ofReal)))
  have hbound_cont : Continuous bound :=
    (((Complex.continuous_ofReal.pow 1).mul f.2.1.continuous).mul
      (Complex.continuous_exp.comp ((continuous_const (y := z - 1 / 2)).mul
        Complex.continuous_ofReal))).norm
  have hdom := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (s := Set.univ) (x₀ := γ₀) (F := F) (F' := F') (bound := bound)
    Filter.univ_mem
    (Eventually.of_forall fun γ => (hF_cont γ).aestronglyMeasurable)
    ((hF_cont γ₀).integrable_of_hasCompactSupport (hF_supp γ₀))
    hF'_cont.aestronglyMeasurable
    (Eventually.of_forall fun u γ _ => by
      dsimp [F', bound]
      have hexp_norm : ‖Complex.exp (-((γ : ℂ) * I * (u : ℂ)))‖ = 1 := by
        have hrew : -((γ : ℂ) * I * (u : ℂ)) = ((-(γ * u) : ℝ) : ℂ) * I := by
          push_cast; ring
        rw [hrew]
        exact Complex.norm_exp_ofReal_mul_I (-(γ * u))
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul, norm_mul, norm_mul, hexp_norm, one_mul,
        ← norm_mul])
    (hbound_cont.integrable_of_hasCompactSupport hbound_supp)
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

private theorem normSq_tr_sourceTwist_le_ball (g : CompactTest) {A : ℝ}
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
  obtain ⟨A₀, _, hA₀⟩ := norm_tr_le_sourceGaussian f
  obtain ⟨A₁, _, hA₁⟩ := norm_tr_le_sourceGaussian (momentCompactTest 1 f)
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
      change |W z * (trTwistNormSqDeriv1 f z γ * dk z)| ≤
        W z * (((A₀ ^ 2 + A₁ ^ 2) * Real.exp (2 * (‖z‖ + |γ₀| + 1) ^ 2)) * dk z)
      have hb0 := normSq_tr_sourceTwist_le_ball f hA₀ hγ z
      have hb1 := normSq_tr_sourceTwist_le_ball (momentCompactTest 1 f) hA₁ hγ z
      have hd1 := abs_trTwistNormSqDeriv1_le f z γ zero_lt_one
      rw [one_mul, inv_one, one_mul] at hd1
      have hdk_nn : 0 ≤ dk z := pow_nonneg (depthKernel_nonneg _ _) j
      rw [abs_mul, abs_mul, abs_of_nonneg (hW_nn z), abs_of_nonneg hdk_nn]
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
  obtain ⟨A₀, _, hA₀⟩ := norm_tr_le_sourceGaussian f
  obtain ⟨A₁, _, hA₁⟩ := norm_tr_le_sourceGaussian (momentCompactTest 1 f)
  obtain ⟨A₂, _, hA₂⟩ := norm_tr_le_sourceGaussian (momentCompactTest 2 f)
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
      change |W z * (trTwistNormSqDeriv2 f z γ * dk z)| ≤
        W z * (((A₀ ^ 2 + 2 * A₁ ^ 2 + A₂ ^ 2) * Real.exp (2 * (‖z‖ + |γ₀| + 1) ^ 2)) * dk z)
      have hb0 := normSq_tr_sourceTwist_le_ball f hA₀ hγ z
      have hb1 := normSq_tr_sourceTwist_le_ball (momentCompactTest 1 f) hA₁ hγ z
      have hb2 := normSq_tr_sourceTwist_le_ball (momentCompactTest 2 f) hA₂ hγ z
      have hd2 := abs_trTwistNormSqDeriv2_le f z γ
      have hdk_nn : 0 ≤ dk z := pow_nonneg (depthKernel_nonneg _ _) j
      rw [abs_mul, abs_mul, abs_of_nonneg (hW_nn z), abs_of_nonneg hdk_nn]
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
  have hnorm : |∫ z : ℂ, W z * (trTwistNormSqDeriv1 f z γ * dk z)| ≤
      ∫ z : ℂ, |W z * (trTwistNormSqDeriv1 f z γ * dk z)| := by
    simpa only [Real.norm_eq_abs] using
      MeasureTheory.norm_integral_le_integral_norm (μ := volume)
        (fun z : ℂ => W z * (trTwistNormSqDeriv1 f z γ * dk z))
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
  have hnorm : |∫ z : ℂ, W z * (trTwistNormSqDeriv2 f z γ * dk z)| ≤
      ∫ z : ℂ, |W z * (trTwistNormSqDeriv2 f z γ * dk z)| := by
    simpa only [Real.norm_eq_abs] using
      MeasureTheory.norm_integral_le_integral_norm (μ := volume)
        (fun z : ℂ => W z * (trTwistNormSqDeriv2 f z γ * dk z))
  have hint01 : Integrable (fun z : ℂ =>
      W z * (Complex.normSq (tr (sourceTwist γ f).1 z) * dk z) +
        2 * (W z * (Complex.normSq (tr (sourceTwist γ (momentCompactTest 1 f)).1 z) * dk z)))
      volume :=
    (hint_m f).add ((hint_m (momentCompactTest 1 f)).const_mul 2)
  have hmono : (∫ z : ℂ, |W z * (trTwistNormSqDeriv2 f z γ * dk z)|) ≤
      ∫ z : ℂ, ((W z * (Complex.normSq (tr (sourceTwist γ f).1 z) * dk z) +
          2 * (W z * (Complex.normSq (tr (sourceTwist γ (momentCompactTest 1 f)).1 z) * dk z))) +
        W z * (Complex.normSq (tr (sourceTwist γ (momentCompactTest 2 f)).1 z) * dk z)) := by
    refine MeasureTheory.integral_mono hint_abs
      (hint01.add (hint_m (momentCompactTest 2 f))) fun z => ?_
    have hdk_nn : 0 ≤ dk z := pow_nonneg (depthKernel_nonneg _ _) j
    rw [abs_mul, abs_mul, abs_of_nonneg (hW_nn z), abs_of_nonneg hdk_nn]
    have h1 := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (abs_trTwistNormSqDeriv2_le f z γ) hdk_nn) (hW_nn z)
    exact h1.trans_eq (by ring)
  rw [MeasureTheory.integral_add hint01 (hint_m (momentCompactTest 2 f)),
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

private theorem continuous_finThetaWeight (n : ℕ) : Continuous (finThetaWeight n) := by
  have hc : ContDiff ℝ 2 (sourceCutoff n : ℂ → ℝ) := (sourceCutoff n).contDiff
  exact hc.continuous.mul
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
  have hsub_int : (∫ γ in Icc T (T + 1), g γ) - g γ_min =
      ∫ γ in T..(T + 1), (g γ - g γ_min) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : T ≤ T + 1),
      intervalIntegral.integral_sub
        (hg_diff.continuous.intervalIntegrable (μ := volume) _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
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
        dsimp only
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
        dsimp only
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
      have hi_l : IntervalIntegrable (fun u : ℝ => -deriv g u) volume γ γ_min :=
        hg'_diff.continuous.neg.intervalIntegrable (μ := volume) _ _
      have hi_r : IntervalIntegrable (fun u : ℝ => M₂ * (γ_min - u)) volume γ γ_min :=
        (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable
          (μ := volume) _ _
      have hmono := integral_mono_on (μ := volume) hge hi_l hi_r
        fun u hu => by
          have hu_Icc : u ∈ Icc T (T + 1) := ⟨hγ.1.trans hu.1, hu.2.trans hγ_Icc.2⟩
          have h1 := (neg_le_abs (deriv g u)).trans (hg'_lip u hu_Icc)
          rw [abs_of_nonpos (by linarith only [hu.2])] at h1
          linarith only [h1]
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
  have hsub_int : (∫ γ in Icc T (T + 1), g γ) - g γ_min =
      ∫ γ in T..(T + 1), (g γ - g γ_min) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : T ≤ T + 1),
      intervalIntegral.integral_sub
        (hg_diff.continuous.intervalIntegrable (μ := volume) _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
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


/-- **Unit-Window Supremum Bound for `finiteThetaSourceMomentReading` (`≤ 2 ∫ R(f) + ∫ R(f₁)`).** -/
theorem sSup_finiteThetaSourceMomentReading_unitWindow_le
    (f : CompactTest) (L : ℝ) (j n : ℕ) (T : ℝ) :
    sSup ((fun γ => finiteThetaSourceMomentReading (sourceTwist γ f) L j n) '' Icc T (T + 1)) ≤
      2 * (∫ γ in Icc T (T + 1), finiteThetaSourceMomentReading (sourceTwist γ f) L j n) +
        (∫ γ in Icc T (T + 1),
          finiteThetaSourceMomentReading (sourceTwist γ (momentCompactTest 1 f)) L j n) := by
  let g : ℝ → ℝ := fun γ => finiteThetaSourceMomentReading (sourceTwist γ f) L j n
  let g₁ : ℝ → ℝ := fun γ =>
    finiteThetaSourceMomentReading (sourceTwist γ (momentCompactTest 1 f)) L j n
  have hg_diff := differentiable_finiteThetaSourceMomentReading_sourceTwist f L j n
  have hg'_cont := (differentiable_deriv_finiteThetaSourceMomentReading_sourceTwist f L j n).continuous
  have hg₁_cont :=
    (differentiable_finiteThetaSourceMomentReading_sourceTwist (momentCompactTest 1 f) L j n).continuous
  have hsob := unitWindow_sSup_le_mean_add_l1_deriv T hg_diff hg'_cont
  have hint_abs : IntegrableOn (fun γ : ℝ => |deriv g γ|) (Icc T (T + 1)) volume :=
    hg'_cont.abs.continuousOn.integrableOn_compact isCompact_Icc
  have hint_g : IntegrableOn g (Icc T (T + 1)) volume :=
    hg_diff.continuous.continuousOn.integrableOn_compact isCompact_Icc
  have hint_g₁ : IntegrableOn g₁ (Icc T (T + 1)) volume :=
    hg₁_cont.continuousOn.integrableOn_compact isCompact_Icc
  have hmono : (∫ γ in Icc T (T + 1), |deriv g γ|) ≤
      ∫ γ in Icc T (T + 1), (g γ + g₁ γ) := by
    refine setIntegral_mono_on hint_abs (hint_g.add hint_g₁) measurableSet_Icc fun γ _ => ?_
    have hd := abs_deriv_finiteThetaSourceMomentReading_le f L j n γ zero_lt_one
    rw [one_mul, inv_one, one_mul] at hd
    exact hd
  rw [MeasureTheory.integral_add hint_g hint_g₁] at hmono
  dsimp only [g, g₁] at hsob hmono
  linarith only [hsob, hmono]

/-- **Unit-Window Supremum Bound for `polynomialThetaSourceMomentReading`
(`≤ 2 ∫ P(f) + ∫ P(f₁)`).** -/
theorem sSup_polynomialThetaSourceMomentReading_unitWindow_le
    (f : CompactTest) (L : ℝ) (j n : ℕ) (T : ℝ) :
    sSup ((fun γ => polynomialThetaSourceMomentReading (sourceTwist γ f) L j n) '' Icc T (T + 1)) ≤
      2 * (∫ γ in Icc T (T + 1), polynomialThetaSourceMomentReading (sourceTwist γ f) L j n) +
        (∫ γ in Icc T (T + 1),
          polynomialThetaSourceMomentReading (sourceTwist γ (momentCompactTest 1 f)) L j n) := by
  let g : ℝ → ℝ := fun γ => polynomialThetaSourceMomentReading (sourceTwist γ f) L j n
  let g₁ : ℝ → ℝ := fun γ =>
    polynomialThetaSourceMomentReading (sourceTwist γ (momentCompactTest 1 f)) L j n
  have hg_diff := differentiable_polynomialThetaSourceMomentReading_sourceTwist f L j n
  have hg'_cont :=
    (differentiable_deriv_polynomialThetaSourceMomentReading_sourceTwist f L j n).continuous
  have hg₁_cont :=
    (differentiable_polynomialThetaSourceMomentReading_sourceTwist (momentCompactTest 1 f) L j n).continuous
  have hsob := unitWindow_sSup_le_mean_add_l1_deriv T hg_diff hg'_cont
  have hint_abs : IntegrableOn (fun γ : ℝ => |deriv g γ|) (Icc T (T + 1)) volume :=
    hg'_cont.abs.continuousOn.integrableOn_compact isCompact_Icc
  have hint_g : IntegrableOn g (Icc T (T + 1)) volume :=
    hg_diff.continuous.continuousOn.integrableOn_compact isCompact_Icc
  have hint_g₁ : IntegrableOn g₁ (Icc T (T + 1)) volume :=
    hg₁_cont.continuousOn.integrableOn_compact isCompact_Icc
  have hmono : (∫ γ in Icc T (T + 1), |deriv g γ|) ≤
      ∫ γ in Icc T (T + 1), (g γ + g₁ γ) := by
    refine setIntegral_mono_on hint_abs (hint_g.add hint_g₁) measurableSet_Icc fun γ _ => ?_
    have hd := abs_deriv_polynomialThetaSourceMomentReading_le f L j n γ zero_lt_one
    rw [one_mul, inv_one, one_mul] at hd
    exact hd
  rw [MeasureTheory.integral_add hint_g hint_g₁] at hmono
  dsimp only [g, g₁] at hsob hmono
  linarith only [hsob, hmono]

/-- Continuity of the sliding unit-window supremum `T ↦ sSup ((fun γ => G (γ, T)) '' Icc T (T + 1))`
for any jointly continuous `G : ℝ × ℝ → ℝ` (via Heine–Cantor on `Icc a b ×ˢ Icc 0 1`). -/
theorem continuousOn_sSup_unitWindow_of_continuous {G : ℝ × ℝ → ℝ} (hG : Continuous G)
    {a b : ℝ} :
    ContinuousOn (fun T : ℝ => sSup ((fun γ => G (γ, T)) '' Icc T (T + 1))) (Icc a b) := by
  let H : ℝ × ℝ → ℝ := fun p => G (p.1 + p.2, p.1)
  have hH_cont : Continuous H :=
    hG.comp ((continuous_fst.add continuous_snd).prodMk continuous_fst)
  have himg_eq : ∀ T : ℝ,
      (fun γ => G (γ, T)) '' Icc T (T + 1) = (fun u => H (T, u)) '' Icc 0 1 := by
    intro T
    ext y
    simp only [mem_image, mem_Icc, H]
    constructor
    · rintro ⟨γ, ⟨h1, h2⟩, rfl⟩
      exact ⟨γ - T, ⟨by linarith only [h1], by linarith only [h2]⟩, by ring_nf⟩
    · rintro ⟨u, ⟨h1, h2⟩, rfl⟩
      exact ⟨T + u, ⟨by linarith only [h1], by linarith only [h2]⟩, rfl⟩
  simp_rw [himg_eq]
  have huc : UniformContinuousOn H (Icc a b ×ˢ Icc 0 1) :=
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hH_cont.continuousOn
  rw [Metric.continuousOn_iff]
  intro T hT ε hε
  obtain ⟨δ, hδ, huc_δ⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun T' hT' hdist => ?_⟩
  have hne : ∀ x : ℝ, ((fun u => H (x, u)) '' Icc 0 1).Nonempty := fun x =>
    ⟨H (x, 0), 0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have hbdd : ∀ x : ℝ, BddAbove ((fun u => H (x, u)) '' Icc 0 1) := fun x =>
    (isCompact_Icc.image (hH_cont.comp (continuous_const.prodMk continuous_id))).bddAbove
  have hptw : ∀ u ∈ Icc (0 : ℝ) 1, |H (T', u) - H (T, u)| ≤ ε / 2 := by
    intro u hu
    have hp' : (T', u) ∈ Icc a b ×ˢ Icc 0 1 := ⟨hT', hu⟩
    have hp : (T, u) ∈ Icc a b ×ˢ Icc 0 1 := ⟨hT, hu⟩
    have hd_prod : dist (T', u) (T, u) < δ := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      exact hdist
    exact (Real.dist_eq _ _ ▸ huc_δ (T', u) hp' (T, u) hp hd_prod).le
  have hle1 : sSup ((fun u => H (T', u)) '' Icc 0 1) ≤
      sSup ((fun u => H (T, u)) '' Icc 0 1) + ε / 2 := by
    refine csSup_le (hne T') ?_
    rintro _ ⟨u, hu, rfl⟩
    have h1 : H (T', u) ≤ H (T, u) + ε / 2 := by
      have := (le_abs_self _).trans (hptw u hu)
      linarith only [this]
    have h2 : H (T, u) ≤ sSup ((fun v => H (T, v)) '' Icc 0 1) :=
      le_csSup (hbdd T) ⟨u, hu, rfl⟩
    linarith only [h1, h2]
  have hle2 : sSup ((fun u => H (T, u)) '' Icc 0 1) ≤
      sSup ((fun u => H (T', u)) '' Icc 0 1) + ε / 2 := by
    refine csSup_le (hne T) ?_
    rintro _ ⟨u, hu, rfl⟩
    have h1 : H (T, u) ≤ H (T', u) + ε / 2 := by
      have := (neg_le_abs _).trans (hptw u hu)
      linarith only [this]
    have h2 : H (T', u) ≤ sSup ((fun v => H (T', v)) '' Icc 0 1) :=
      le_csSup (hbdd T') ⟨u, hu, rfl⟩
    linarith only [h1, h2]
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith only [hle2, hε], by linarith only [hle1, hε]⟩

/-- 1D sliding-window integral inequality (via the primitive `H x = ∫ u in U..x, h u`, avoiding
product-measure Fubini): for continuous nonnegative `h : ℝ → ℝ` and `U ≥ 0`,
`∫ T in Icc U (2 * U), (∫ γ in Icc T (T + 1), h γ) ≤ ∫ u in Icc U (2 * U + 1), h u`. -/
theorem integral_Icc_unitWindow_integral_le {h : ℝ → ℝ} (hh_cont : Continuous h)
    (hh_nn : ∀ u, 0 ≤ h u) {U : ℝ} (hU : 0 ≤ U) :
    (∫ T in Icc U (2 * U), (∫ γ in Icc T (T + 1), h γ)) ≤ ∫ u in Icc U (2 * U + 1), h u := by
  let H : ℝ → ℝ := fun x => ∫ u in U..x, h u
  have hH_cont : Continuous H := by
    rw [Metric.continuous_iff]
    intro x₀ ε hε
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (s := Icc (x₀ - 1) (x₀ + 1)) hh_cont.continuousOn
    have hM_nn : 0 ≤ M := (norm_nonneg (h x₀)).trans (hM x₀ ⟨by linarith, by linarith⟩)
    let M₁ : ℝ := M + 1
    have hM₁_pos : 0 < M₁ := by dsimp [M₁]; linarith only [hM_nn]
    let δ : ℝ := min 1 (ε / (2 * M₁))
    have hδ_pos : 0 < δ := lt_min zero_lt_one (by positivity)
    refine ⟨δ, hδ_pos, fun y hy => ?_⟩
    have hy_abs : |y - x₀| < 1 := (Real.dist_eq y x₀ ▸ hy).trans_le (min_le_left _ _)
    have hy_δ : |y - x₀| < ε / (2 * M₁) :=
      (Real.dist_eq y x₀ ▸ hy).trans_le (min_le_right _ _)
    have hadj := integral_add_adjacent_intervals (a := U) (b := x₀) (c := y)
      (hh_cont.intervalIntegrable (μ := volume) _ _)
      (hh_cont.intervalIntegrable (μ := volume) _ _)
    have hdiff : H y - H x₀ = ∫ u in x₀..y, h u := by dsimp [H]; linarith only [hadj]
    have huIoc : Set.uIoc x₀ y ⊆ Icc (x₀ - 1) (x₀ + 1) := by
      refine uIoc_subset_uIcc.trans (uIcc_subset_Icc ⟨by linarith, by linarith⟩ ?_)
      rw [abs_lt] at hy_abs
      exact ⟨by linarith only [hy_abs.1], by linarith only [hy_abs.2]⟩
    have hnorm := norm_integral_le_of_norm_le_const (a := x₀) (b := y) (C := M₁) (f := h)
      fun u hu => (hM u (huIoc hu)).trans (by dsimp [M₁]; linarith)
    rw [← hdiff, Real.norm_eq_abs] at hnorm
    rw [Real.dist_eq]
    calc |H y - H x₀| ≤ M₁ * |y - x₀| := hnorm
      _ < M₁ * (ε / (2 * M₁)) := mul_lt_mul_of_pos_left hy_δ hM₁_pos
      _ = ε / 2 := by field_simp [hM₁_pos.ne']
      _ < ε := half_lt_self hε
  have hwin_eq : ∀ T : ℝ, (∫ γ in Icc T (T + 1), h γ) = H (T + 1) - H T := by
    intro T
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    have hadj := integral_add_adjacent_intervals (a := U) (b := T) (c := T + 1)
      (hh_cont.intervalIntegrable (μ := volume) _ _)
      (hh_cont.intervalIntegrable (μ := volume) _ _)
    dsimp [H]
    linarith only [hadj]
  simp_rw [hwin_eq]
  have hi_H1 : IntervalIntegrable (fun x : ℝ => H (x + 1)) volume U (2 * U) :=
    (hH_cont.comp (continuous_id.add (continuous_const (y := (1 : ℝ))))).intervalIntegrable
      (μ := volume) _ _
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith only [hU] : U ≤ 2 * U),
    intervalIntegral.integral_sub hi_H1 (hH_cont.intervalIntegrable (μ := volume) _ _),
    intervalIntegral.integral_comp_add_right (f := H) 1]
  have hs1 := integral_add_adjacent_intervals (a := U) (b := U + 1) (c := 2 * U + 1)
    (hH_cont.intervalIntegrable (μ := volume) _ _)
    (hH_cont.intervalIntegrable (μ := volume) _ _)
  have hs2 := integral_add_adjacent_intervals (a := U) (b := 2 * U) (c := 2 * U + 1)
    (hH_cont.intervalIntegrable (μ := volume) _ _)
    (hH_cont.intervalIntegrable (μ := volume) _ _)
  have hcomm : (∫ x in (U + 1)..(2 * U + 1), H x) - (∫ x in U..(2 * U), H x) =
      (∫ x in (2 * U)..(2 * U + 1), H x) - (∫ x in U..(U + 1), H x) := by
    linarith only [hs1, hs2]
  rw [hcomm]
  have hlo_nn : 0 ≤ ∫ x in U..(U + 1), H x :=
    intervalIntegral.integral_nonneg (by linarith) fun x hx =>
      intervalIntegral.integral_nonneg hx.1 fun u _ => hh_nn u
  have hhi_le : (∫ x in (2 * U)..(2 * U + 1), H x) ≤ H (2 * U + 1) := by
    have hptw : ∀ x ∈ Icc (2 * U) (2 * U + 1), H x ≤ H (2 * U + 1) := by
      intro x hx
      have hadj := integral_add_adjacent_intervals (a := U) (b := x) (c := 2 * U + 1)
        (hh_cont.intervalIntegrable (μ := volume) _ _)
        (hh_cont.intervalIntegrable (μ := volume) _ _)
      have hnn : 0 ≤ ∫ u in x..(2 * U + 1), h u :=
        intervalIntegral.integral_nonneg hx.2 fun u _ => hh_nn u
      dsimp [H]
      linarith only [hadj, hnn]
    have hmono := integral_mono_on (μ := volume) (by linarith : 2 * U ≤ 2 * U + 1)
      (hH_cont.intervalIntegrable (μ := volume) _ _)
      (intervalIntegrable_const) hptw
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    linarith only [hmono]
  have hH_end : H (2 * U + 1) = ∫ u in Icc U (2 * U + 1), h u := by
    dsimp [H]
    rw [intervalIntegral.integral_of_le (by linarith only [hU]),
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  linarith only [hlo_nn, hhi_le, hH_end]


/-! ## §3. Nonnegativity, scale monotonicity, and compact-test transfer lemmas -/

private theorem weightedMomentReading_nonneg {W : ℂ → ℝ} (hW_nn : ∀ z, 0 ≤ W z)
    (g : CompactTest) (L : ℝ) (j : ℕ) :
    0 ≤ weightedMomentReading W g L j := by
  unfold weightedMomentReading
  exact mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
    (MeasureTheory.integral_nonneg fun z =>
      mul_nonneg (hW_nn z)
        (mul_nonneg (Complex.normSq_nonneg _) (pow_nonneg (depthKernel_nonneg _ _) j)))

private theorem weightedMomentReading_mono_scale {W : ℂ → ℝ} (hW_cont : Continuous W)
    (hW_supp : HasCompactSupport W) (hW_nn : ∀ z, 0 ≤ W z)
    (g : CompactTest) {L₁ L₂ : ℝ} (hL₁ : 0 ≤ L₁) (hL : L₁ ≤ L₂) (j : ℕ) :
    weightedMomentReading W g L₁ j ≤ weightedMomentReading W g L₂ j := by
  unfold weightedMomentReading
  have hdk_cont : ∀ L : ℝ, Continuous (fun z : ℂ => depthKernel L (z.re - 1 / 2) ^ j) := fun L => by
    unfold depthKernel
    exact ((continuous_const.mul (Real.continuous_cosh.comp
      ((continuous_const.mul (Complex.continuous_re.sub continuous_const)).mul
        continuous_const))).sub continuous_const).pow j
  have hint : ∀ L : ℝ, Integrable
      (fun z : ℂ => W z * (Complex.normSq (tr g.1 z) * depthKernel L (z.re - 1 / 2) ^ j))
      volume := fun L =>
    (hW_cont.mul ((Complex.continuous_normSq.comp (contDiff_tr g).continuous).mul
      (hdk_cont L))).integrable_of_hasCompactSupport hW_supp.mul_right
  refine mul_le_mul_of_nonneg_left (MeasureTheory.integral_mono (hint L₁) (hint L₂) fun z => ?_)
    (inv_nonneg.mpr Real.pi_pos.le)
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (depthKernel_nonneg _ _) (depthKernel_mono_scale hL₁ hL _) j)
      (Complex.normSq_nonneg _))
    (hW_nn z)

theorem finiteThetaSourceMomentReading_nonneg (g : CompactTest) (L : ℝ) (j n : ℕ) :
    0 ≤ finiteThetaSourceMomentReading g L j n := by
  rw [← weightedMomentReading_finThetaWeight_eq]
  exact weightedMomentReading_nonneg (finThetaWeight_nonneg n) g L j

theorem polynomialThetaSourceMomentReading_nonneg (g : CompactTest) (L : ℝ) (j n : ℕ) :
    0 ≤ polynomialThetaSourceMomentReading g L j n := by
  rw [← weightedMomentReading_polyThetaWeight_eq]
  exact weightedMomentReading_nonneg (polyThetaWeight_nonneg n) g L j

theorem finiteThetaSourceMomentReading_mono_scale (g : CompactTest) {L₁ L₂ : ℝ}
    (hL₁ : 0 ≤ L₁) (hL : L₁ ≤ L₂) (j n : ℕ) :
    finiteThetaSourceMomentReading g L₁ j n ≤ finiteThetaSourceMomentReading g L₂ j n := by
  rw [← weightedMomentReading_finThetaWeight_eq, ← weightedMomentReading_finThetaWeight_eq]
  exact weightedMomentReading_mono_scale (continuous_finThetaWeight n)
    (hasCompactSupport_finThetaWeight n) (finThetaWeight_nonneg n) g hL₁ hL j

theorem polynomialThetaSourceMomentReading_mono_scale (g : CompactTest) {L₁ L₂ : ℝ}
    (hL₁ : 0 ≤ L₁) (hL : L₁ ≤ L₂) (j n : ℕ) :
    polynomialThetaSourceMomentReading g L₁ j n ≤ polynomialThetaSourceMomentReading g L₂ j n := by
  rw [← weightedMomentReading_polyThetaWeight_eq, ← weightedMomentReading_polyThetaWeight_eq]
  exact weightedMomentReading_mono_scale (continuous_polyThetaWeight n)
    (hasCompactSupport_polyThetaWeight n) (polyThetaWeight_nonneg n) g hL₁ hL j

/-- Under `RiemannHypothesis`, `heckeDefect g L = 0` for every `g : CompactTest` and `L : ℝ`. -/
theorem heckeDefect_compactTest_eq_zero_of_riemannHypothesis (hRH : RiemannHypothesis)
    (g : CompactTest) (L : ℝ) :
    heckeDefect g L = 0 := by
  have hon := CrossRouteReceiverBridges.riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH
  unfold heckeDefect
  have hzero : (fun ρ : zetaZeroConfig.carrier =>
      zetaWeight g ρ * depthKernel L (zetaDepth ρ)) = fun _ => 0 := by
    funext ρ
    have hre : (ρ : ℂ).re = 1 / 2 := hon (ρ : ℂ) ρ.2
    have hd0 : zetaDepth ρ = 0 := by simp [zetaDepth, hre]
    rw [hd0, depthKernel_zero_depth, mul_zero]
  rw [hzero, tsum_zero]

private theorem exists_forall_abs_le_of_tendsto_zero' {e : ℕ → ℝ} (ht : Tendsto e atTop (𝓝 0)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, |e n| ≤ M := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht 1 zero_lt_one
  let prefMax : ℝ := ∑ k ∈ Finset.range N, |e k|
  have hpref_nn : 0 ≤ prefMax := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨prefMax + 1, by linarith, fun n => ?_⟩
  by_cases hn : n < N
  · have hle : |e n| ≤ prefMax :=
      Finset.single_le_sum (f := fun k => |e k|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr hn)
    linarith
  · have h1 := hN n (not_lt.mp hn)
    rw [Real.dist_eq, sub_zero] at h1
    linarith

/-- Uniform stage-independent aperture error bound for any `f : CompactTest` supported in
`[-1/4, 1/4]`. -/
theorem exists_uniform_aperture_compactTest_error_bounds (f : CompactTest)
    (hsupp : ∀ u, f.1 u ≠ 0 → |u| ≤ 1 / 4) :
    ∃ E_f : ℝ, 0 ≤ E_f ∧
      ∀ n : ℕ, 1 ≤ n → ∀ L γ : ℝ,
        |γ| ≤ (n : ℝ) / 2 → 1 / 4 + |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
        |finiteThetaSourceMomentReading (sourceTwist γ f) L 1 n -
            heckeDefect (sourceTwist γ f) L| ≤ E_f ∧
          |polynomialThetaSourceMomentReading (sourceTwist γ f) L 1 n -
            heckeDefect (sourceTwist γ f) L| ≤ E_f := by
  obtain ⟨B₁, _, hb₁⟩ := exists_finiteThetaSource_aperture_error_bound
  obtain ⟨B₂, _, hb₂⟩ := exists_polynomialThetaSource_aperture_error_bound
  have ht₁ : Tendsto (fun n : ℕ =>
      B₁ * Real.exp (-((n : ℝ) ^ 4) + 68 * (n : ℝ) ^ 2 + 66) +
        40 * sourceReferenceTail n) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_sourceApertureWindowError B₁).add (tendsto_sourceReferenceTail.const_mul 40)
  have ht₂ : Tendsto (fun n : ℕ =>
      B₂ / ((n : ℝ) + 1) ^ 2 + 40 * sourceReferenceTail n) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_polynomialSourceWindowError B₂).add (tendsto_sourceReferenceTail.const_mul 40)
  obtain ⟨M₁, hM₁, hbd₁⟩ := exists_forall_abs_le_of_tendsto_zero' ht₁
  obtain ⟨M₂, hM₂, hbd₂⟩ := exists_forall_abs_le_of_tendsto_zero' ht₂
  set S₂ : ℝ := 4 * sourceTestSize f ^ 2
  have hS₂_nn : 0 ≤ S₂ := by dsimp [S₂]; positivity
  refine ⟨S₂ * (M₁ + M₂), mul_nonneg hS₂_nn (add_nonneg hM₁ hM₂),
    fun n hn L γ hγ hwin => ?_⟩
  have hwin' : (1 / 4 : ℝ) + ((1 : ℕ) : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) := by
    simpa only [Nat.cast_one, one_mul] using hwin
  have h1 := hb₁ n hn f (1 / 4) (by norm_num) hsupp 1 L γ hγ hwin'
  have h2 := hb₂ n hn f (1 / 4) (by norm_num) hsupp 1 L γ hγ hwin'
  have hsum_eq : (∑' ρ : zetaZeroConfig.carrier,
      zetaWeight (sourceTwist γ f) ρ * depthKernel L (zetaDepth ρ) ^ 1) =
      heckeDefect (sourceTwist γ f) L := by
    simp only [pow_one, heckeDefect]
  rw [hsum_eq, pow_one, div_le_iff₀ (by norm_num : (0 : ℝ) < 4)] at h1 h2
  have he₁ : B₁ * Real.exp (-((n : ℝ) ^ 4) + 68 * (n : ℝ) ^ 2 + 66) +
      40 * sourceReferenceTail n ≤ M₁ := (le_abs_self _).trans (hbd₁ n)
  have he₂ : B₂ / ((n : ℝ) + 1) ^ 2 + 40 * sourceReferenceTail n ≤ M₂ :=
    (le_abs_self _).trans (hbd₂ n)
  constructor
  · calc |finiteThetaSourceMomentReading (sourceTwist γ f) L 1 n -
            heckeDefect (sourceTwist γ f) L|
        ≤ sourceTestSize f ^ 2 * M₁ * 4 := by
          nlinarith [h1, he₁, sq_nonneg (sourceTestSize f)]
      _ ≤ S₂ * (M₁ + M₂) := by dsimp [S₂]; nlinarith [hS₂_nn, hM₂]
  · calc |polynomialThetaSourceMomentReading (sourceTwist γ f) L 1 n -
            heckeDefect (sourceTwist γ f) L|
        ≤ sourceTestSize f ^ 2 * M₂ * 4 := by
          nlinarith [h2, he₂, sq_nonneg (sourceTestSize f)]
      _ ≤ S₂ * (M₁ + M₂) := by dsimp [S₂]; nlinarith [hS₂_nn, hM₁]

/-- Exact hyperbolic double-scale polynomial identity
`depthKernel (2 * L) d = (4 + depthKernel L d) * depthKernel L d`. -/
theorem depthKernel_two_mul_eq (L d : ℝ) :
    depthKernel (2 * L) d = (4 + depthKernel L d) * depthKernel L d := by
  rw [depthKernel_double]; ring

/-- Eventual uniform `O(1)` bound on `heckeDefect (sourceTwist γ f) (c * Real.log T)` for any
`f : CompactTest` supported in `[-1/4, 1/4]` and `0 < c ≤ 2` from eventual boundedness of
`unitWindowDepthCharge U (c * Real.log U)`. -/
theorem eventually_heckeDefect_compactTest_le_of_unitWindowDepthCharge_le
    (f : CompactTest) (hsupp : ∀ u, f.1 u ≠ 0 → |u| ≤ 1 / 4)
    {c B : ℝ} (hc0 : 0 < c) (hc2 : c ≤ 2) (hB : 0 ≤ B)
    (hev : ∀ᶠ U : ℝ in atTop, unitWindowDepthCharge U (c * Real.log U) ≤ B) :
    ∃ B_f : ℝ, 0 < B_f ∧ ∀ᶠ T : ℝ in atTop, ∀ γ ∈ Icc T (T + 1),
      heckeDefect (sourceTwist γ f) (c * Real.log T) ≤ B_f := by
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hev
  have hsum_lor : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2)) := by
    simpa only [zero_sub, neg_sq] using
      ArithmeticCastelnuovoSeveri.summable_zetaCarrier_of_xiZeroCopy
        (g := fun z : ℂ => 1 / (1 + (0 - z.im) ^ 2)) (fun _ => by positivity)
        (RHTower.summable_lorentzMassTerm 0)
  let L_mass : ℝ := ∑' ρ : zetaZeroConfig.carrier,
    (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2))
  have hLmass_nn : 0 ≤ L_mass := tsum_nonneg fun _ => by positivity
  let M₀ : ℝ := sourceTestSize f ^ 2 * Real.exp (1 / 4) + 1
  have hM₀_pos : 0 < M₀ := by dsimp [M₀]; positivity
  let B_f : ℝ := 3 * Real.pi * M₀ * (4 + B) * B + 64 * M₀ * L_mass + 1
  refine ⟨B_f, by dsimp [B_f]; positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max 16 (2 * max 0 U₀ + 4))] with T hT γ hγ
  classical
  have hT16 : 16 ≤ T := (le_max_left _ _).trans hT
  have hT_U₀ : U₀ ≤ T / 2 := by
    have h1 : 2 * max 0 U₀ + 4 ≤ T := (le_max_right _ _).trans hT
    have h2 : U₀ ≤ max 0 U₀ := le_max_right _ _
    linarith only [h1, h2]
  have hT_pos : 0 < T := by linarith only [hT16]
  have hγ_le_2T : γ ≤ 2 * T := by linarith only [hγ.2, hT16]
  let L : ℝ := c * Real.log T
  have hL_nn : 0 ≤ L := mul_nonneg hc0.le (Real.log_nonneg (by linarith only [hT16]))
  have hmem_c : ∀ z ∈ shellZeros (T / 2) (4 * T), z ∈ zetaZeroConfig.carrier := by
    intro z hz
    obtain ⟨h0, h1, _, _, hxi⟩ := mem_stripFinsetPos.mp (Finset.mem_filter.mp hz).1
    exact CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mpr
      ⟨hxi, h0, h1⟩
  let emb : {z // z ∈ shellZeros (T / 2) (4 * T)} → zetaZeroConfig.carrier :=
    fun z => ⟨z.1, hmem_c z.1 z.2⟩
  have hinj : Function.Injective emb := fun a b h =>
    Subtype.ext (congrArg (fun x : zetaZeroConfig.carrier => (x : ℂ)) h)
  let S_loc : Finset zetaZeroConfig.carrier := (shellZeros (T / 2) (4 * T)).attach.image emb
  have hnsq_quartic : ∀ ρ : zetaZeroConfig.carrier,
      Complex.normSq (tr (sourceTwist γ f).1 ρ) ≤
        M₀ / (1 + ((ρ : ℂ).im - γ) ^ 2) ^ 2 := by
    intro ρ
    have hstrip := abs_re_sub_half_le_of_zeroConfig zetaZeroConfig ρ
    have hz_re : 0 ≤ ((ρ : ℂ) - (γ : ℂ) * I).re ∧ ((ρ : ℂ) - (γ : ℂ) * I).re ≤ 1 := by
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero]
      rw [abs_le] at hstrip
      exact ⟨by linarith only [hstrip.1], by linarith only [hstrip.2]⟩
    have hb := normSq_tr_strip_le_sourceTestSize f (by norm_num : (0 : ℝ) ≤ 1 / 4) hsupp hz_re
    have him_eq : ((ρ : ℂ) - (γ : ℂ) * I).im = (ρ : ℂ).im - γ := by simp
    rw [him_eq, ← tr_twist γ f.1 (ρ : ℂ)] at hb
    exact hb.trans (div_le_div_of_nonneg_right (by dsimp [M₀]; linarith) (by positivity))
  have hsum_split :=
    ((summable_heckeDefect (sourceTwist γ f) L).sum_add_tsum_compl (s := S_loc)).symm
  change (∑' ρ : zetaZeroConfig.carrier,
    zetaWeight (sourceTwist γ f) ρ * depthKernel L (zetaDepth ρ)) ≤ B_f
  rw [hsum_split]
  -- 1. Local shell `shellZeros (T / 2) (4 * T)` covered by `N = ⌈4 * T⌉₊` unit windows `U_m = T / 2 + m`
  have hloc_le : (∑ ρ ∈ S_loc, zetaWeight (sourceTwist γ f) ρ * depthKernel L (zetaDepth ρ)) ≤
      3 * Real.pi * M₀ * (4 + B) * B := by
    let N : ℕ := ⌈4 * T⌉₊
    have hcov_sh : shellZeros (T / 2) (4 * T) ⊆
        (Finset.range N).biUnion (fun m => xiUnitWindowZeros (T / 2 + (m : ℝ))) := by
      intro z hz
      obtain ⟨hz_pos, him_gt⟩ := Finset.mem_filter.mp hz
      obtain ⟨h0, h1, _, him_le, hxi⟩ := mem_stripFinsetPos.mp hz_pos
      let m : ℕ := ⌊z.im - T / 2⌋₊
      have hsub_nn : 0 ≤ z.im - T / 2 := by linarith only [him_gt]
      have hm_le : (m : ℝ) ≤ z.im - T / 2 := Nat.floor_le hsub_nn
      have hm_lt : z.im - T / 2 < (m : ℝ) + 1 := Nat.lt_floor_add_one _
      have hm_N : m < N := by
        have h1' : (m : ℝ) < 4 * T := by linarith only [hm_le, him_le, hT16]
        have h2' : 4 * T ≤ (N : ℝ) := Nat.le_ceil _
        exact_mod_cast h1'.trans_le h2'
      refine Finset.mem_biUnion.mpr ⟨m, Finset.mem_range.mpr hm_N, ?_⟩
      rw [mem_xiUnitWindowZeros]
      exact ⟨(Set.Finite.mem_toFinset _).mpr
        ⟨⟨h0, h1, by linarith only [hT16, him_gt], by linarith only [hm_lt]⟩, hxi⟩,
        by linarith only [hm_le]⟩
    have h1 : (∑ ρ ∈ S_loc, zetaWeight (sourceTwist γ f) ρ * depthKernel L (zetaDepth ρ)) ≤
        M₀ * ∑ z ∈ shellZeros (T / 2) (4 * T),
          ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2) *
            (1 / (1 + (z.im - γ) ^ 2)) := by
      rw [Finset.sum_image (fun a _ b _ h => hinj h), ← Finset.sum_attach (shellZeros (T / 2) (4 * T)),
        Finset.mul_sum]
      refine Finset.sum_le_sum fun z _ => ?_
      obtain ⟨h0, h1, _, _, _⟩ := mem_stripFinsetPos.mp (Finset.mem_filter.mp z.2).1
      have hmult : (zetaZeroConfig.mult z.1 : ℝ) = ((analyticOrderAt xi z.1).toNat : ℝ) := by
        change ((analyticOrderAt riemannZeta z.1).toNat : ℝ) = _
        exact congrArg (fun k : ℕ => (k : ℝ))
          (congrArg ENat.toNat (xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨h0, h1⟩)).symm
      have hq := hnsq_quartic (emb z)
      have hden : 1 + (z.1.im - γ) ^ 2 ≤ (1 + (z.1.im - γ) ^ 2) ^ 2 := by
        nlinarith only [sq_nonneg (z.1.im - γ)]
      have hq_z : Complex.normSq (tr (sourceTwist γ f).1 z.1) ≤
          M₀ / (1 + (z.1.im - γ) ^ 2) ^ 2 := hq
      have hlor : Complex.normSq (tr (sourceTwist γ f).1 z.1) ≤
          M₀ * (1 / (1 + (z.1.im - γ) ^ 2)) :=
        (hq_z.trans (div_le_div_of_nonneg_left hM₀_pos.le (by positivity) hden)).trans_eq
          (div_eq_mul_one_div _ _)
      have hzd : zetaDepth (emb z) = z.1.re - 1 / 2 := rfl
      have hzw : zetaWeight (sourceTwist γ f) (emb z) =
          ((analyticOrderAt xi z.1).toNat : ℝ) * Complex.normSq (tr (sourceTwist γ f).1 z.1) := by
        change (zetaZeroConfig.mult z.1 : ℝ) * Complex.normSq (tr (sourceTwist γ f).1 z.1) = _
        rw [hmult]
      rw [hzw, hzd]
      calc ((analyticOrderAt xi z.1).toNat : ℝ) * Complex.normSq (tr (sourceTwist γ f).1 z.1) *
              depthKernel L (z.1.re - 1 / 2)
          ≤ ((analyticOrderAt xi z.1).toNat : ℝ) * (M₀ * (1 / (1 + (z.1.im - γ) ^ 2))) *
              depthKernel L (z.1.re - 1 / 2) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hlor (Nat.cast_nonneg _)) (depthKernel_nonneg _ _)
        _ = M₀ * (((analyticOrderAt xi z.1).toNat : ℝ) * depthKernel L (z.1.re - 1 / 2) *
              (1 / (1 + (z.1.im - γ) ^ 2))) := by ring
    have hwin_m : ∀ m ∈ Finset.range N,
        (∑ z ∈ xiUnitWindowZeros (T / 2 + (m : ℝ)),
          ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2) *
            (1 / (1 + (z.im - γ) ^ 2))) ≤
        3 * (4 + B) * B *
          (∫ u in (T / 2 + (m : ℝ))..(T / 2 + ((m + 1 : ℕ) : ℝ)), 1 / (1 + (u - γ) ^ 2)) := by
      intro m _
      let U_m : ℝ := T / 2 + (m : ℝ)
      have hUm_ge8 : 8 ≤ U_m := by
        dsimp [U_m]; linarith only [hT16, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      have hUm_B : unitWindowDepthCharge U_m (c * Real.log U_m) ≤ B :=
        hU₀ U_m (hT_U₀.trans (by dsimp [U_m]; linarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]))
      have hL_le_2Lm : L ≤ 2 * (c * Real.log U_m) := by
        have hT_le_sq : T ≤ U_m ^ 2 := by
          have : (T / 2) ^ 2 ≤ U_m ^ 2 :=
            pow_le_pow_left₀ (by positivity)
              (by dsimp [U_m]; linarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]) 2
          nlinarith only [this, hT16]
        have hlog_le : Real.log T ≤ 2 * Real.log U_m := by
          calc Real.log T ≤ Real.log (U_m ^ 2) := Real.log_le_log hT_pos hT_le_sq
            _ = 2 * Real.log U_m := by rw [Real.log_pow]; push_cast; rfl
        dsimp [L]; nlinarith only [hc0, hlog_le]
      have hlor_m : ∀ z ∈ xiUnitWindowZeros U_m,
          1 / (1 + (z.im - γ) ^ 2) ≤
            3 * ∫ u in U_m..(U_m + 1), 1 / (1 + (u - γ) ^ 2) := by
        intro z hz
        obtain ⟨hS, him_ge⟩ := mem_xiUnitWindowZeros.mp hz
        have him_lt : z.im < U_m + 1 := ((Set.Finite.mem_toFinset _).mp hS).1.2.2.2
        have hptw : ∀ u ∈ Icc U_m (U_m + 1),
            1 / (1 + (z.im - γ) ^ 2) ≤ 3 * (1 / (1 + (u - γ) ^ 2)) := by
          intro u hu
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
          let x : ℝ := u - γ
          let δ : ℝ := u - z.im
          have hδ_sq : δ ^ 2 ≤ 1 := by
            have h1' : -1 ≤ δ := by dsimp [δ]; linarith only [hu.1, him_lt]
            have h2' : δ ≤ 1 := by dsimp [δ]; linarith only [hu.2, him_ge]
            nlinarith only [h1', h2']
          have hid : 3 * (1 + (z.im - γ) ^ 2) - (1 + (u - γ) ^ 2) =
              2 * (x - (3 / 2) * δ) ^ 2 + (2 - (3 / 2) * δ ^ 2) := by
            dsimp [x, δ]; ring
          have hsq_nn : 0 ≤ 2 * (x - (3 / 2) * δ) ^ 2 := by positivity
          linarith only [hid, hδ_sq, hsq_nn]
        have hi_c : IntervalIntegrable (fun _ : ℝ => 1 / (1 + (z.im - γ) ^ 2)) volume U_m (U_m + 1) :=
          intervalIntegrable_const
        have hi_u : IntervalIntegrable (fun u : ℝ => 3 * (1 / (1 + (u - γ) ^ 2))) volume U_m (U_m + 1) :=
          (continuous_const.mul (continuous_const.div (by fun_prop)
            fun _ => by positivity)).intervalIntegrable (μ := volume) _ _
        have hmono := integral_mono_on (μ := volume) (by linarith : U_m ≤ U_m + 1)
          hi_c hi_u hptw
        rw [intervalIntegral.integral_const, smul_eq_mul,
          intervalIntegral.integral_const_mul] at hmono
        linarith only [hmono]
      have hdk_m : ∀ z ∈ xiUnitWindowZeros U_m,
          depthKernel L (z.re - 1 / 2) ≤
            (4 + B) * depthKernel (c * Real.log U_m) (z.re - 1 / 2) := by
        intro z hz
        have hdk_B : depthKernel (c * Real.log U_m) (z.re - 1 / 2) ≤ B :=
          (depthKernel_le_unitWindowDepthCharge hz).trans hUm_B
        calc depthKernel L (z.re - 1 / 2)
            ≤ depthKernel (2 * (c * Real.log U_m)) (z.re - 1 / 2) :=
              depthKernel_mono_scale hL_nn hL_le_2Lm _
          _ = (4 + depthKernel (c * Real.log U_m) (z.re - 1 / 2)) *
                depthKernel (c * Real.log U_m) (z.re - 1 / 2) :=
              depthKernel_two_mul_eq _ _
          _ ≤ (4 + B) * depthKernel (c * Real.log U_m) (z.re - 1 / 2) :=
              mul_le_mul_of_nonneg_right (by linarith only [hdk_B]) (depthKernel_nonneg _ _)
      have hcast_m1 : T / 2 + ((m + 1 : ℕ) : ℝ) = U_m + 1 := by
        dsimp [U_m]; push_cast; ring
      rw [hcast_m1]
      calc ∑ z ∈ xiUnitWindowZeros U_m,
              ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2) *
                (1 / (1 + (z.im - γ) ^ 2))
          ≤ ∑ z ∈ xiUnitWindowZeros U_m,
              (((analyticOrderAt xi z).toNat : ℝ) *
                ((4 + B) * depthKernel (c * Real.log U_m) (z.re - 1 / 2))) *
                (3 * ∫ u in U_m..(U_m + 1), 1 / (1 + (u - γ) ^ 2)) := by
            refine Finset.sum_le_sum fun z hz => ?_
            refine mul_le_mul (mul_le_mul_of_nonneg_left (hdk_m z hz) (Nat.cast_nonneg _))
              (hlor_m z hz) (by positivity)
              (mul_nonneg (Nat.cast_nonneg _)
                (mul_nonneg (by positivity) (depthKernel_nonneg _ _)))
        _ = (3 * (4 + B) * (∫ u in U_m..(U_m + 1), 1 / (1 + (u - γ) ^ 2))) *
              unitWindowDepthCharge U_m (c * Real.log U_m) := by
            unfold unitWindowDepthCharge
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun z _ => by ring
        _ ≤ (3 * (4 + B) * (∫ u in U_m..(U_m + 1), 1 / (1 + (u - γ) ^ 2))) * B := by
            refine mul_le_mul_of_nonneg_left hUm_B ?_
            exact mul_nonneg (by positivity)
              (intervalIntegral.integral_nonneg (by linarith) fun _ _ => by positivity)
        _ = 3 * (4 + B) * B * (∫ u in U_m..(U_m + 1), 1 / (1 + (u - γ) ^ 2)) := by ring
    have hbi_le : (∑ z ∈ shellZeros (T / 2) (4 * T),
          ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2) *
            (1 / (1 + (z.im - γ) ^ 2))) ≤
        3 * (4 + B) * B * Real.pi := by
      have hsub := Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun z : ℂ => ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2) *
          (1 / (1 + (z.im - γ) ^ 2)))
        hcov_sh fun _ _ _ =>
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (depthKernel_nonneg _ _)) (by positivity)
      have hbi : (∑ z ∈ (Finset.range N).biUnion (fun m => xiUnitWindowZeros (T / 2 + (m : ℝ))),
          ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2) *
            (1 / (1 + (z.im - γ) ^ 2))) =
          ∑ m ∈ Finset.range N, ∑ z ∈ xiUnitWindowZeros (T / 2 + (m : ℝ)),
            ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2) *
              (1 / (1 + (z.im - γ) ^ 2)) := by
        refine Finset.sum_biUnion fun m₁ _ m₂ _ hne => Finset.disjoint_left.mpr fun z hz₁ hz₂ =>
          hne ?_
        obtain ⟨hS₁, hlo₁⟩ := mem_xiUnitWindowZeros.mp hz₁
        obtain ⟨hS₂, hlo₂⟩ := mem_xiUnitWindowZeros.mp hz₂
        have hhi₁ := ((Set.Finite.mem_toFinset _).mp hS₁).1.2.2.2
        have hhi₂ := ((Set.Finite.mem_toFinset _).mp hS₂).1.2.2.2
        have hlt₁ : (m₁ : ℝ) < (m₂ : ℝ) + 1 := by linarith only [hlo₁, hhi₂]
        have hlt₂ : (m₂ : ℝ) < (m₁ : ℝ) + 1 := by linarith only [hlo₂, hhi₁]
        have hlt₁' : m₁ < m₂ + 1 := by exact_mod_cast hlt₁
        have hlt₂' : m₂ < m₁ + 1 := by exact_mod_cast hlt₂
        omega
      have hm_sum := Finset.sum_le_sum hwin_m
      rw [← Finset.mul_sum] at hm_sum
      have hadj_N := sum_integral_adjacent_intervals (n := N)
        (a := fun m : ℕ => T / 2 + (m : ℝ))
        (f := fun u : ℝ => 1 / (1 + (u - γ) ^ 2)) fun m _ =>
          (continuous_const.div (by fun_prop) fun _ => by positivity).intervalIntegrable
            (μ := volume) _ _
      simp only [Nat.cast_zero, add_zero] at hadj_N
      rw [hadj_N] at hm_sum
      have hpi : (∫ u in (T / 2)..(T / 2 + (N : ℝ)), 1 / (1 + (u - γ) ^ 2)) ≤ Real.pi := by
        rw [integral_eq_sub_of_hasDerivAt
          (f := fun u : ℝ => Real.arctan (u - γ))
          (fun u _ => (((hasDerivAt_id' u).sub_const γ).arctan).congr_deriv (mul_one _))
          ((continuous_const.div (by fun_prop) fun _ => by positivity).intervalIntegrable
            (μ := volume) _ _)]
        have hhi := Real.arctan_lt_pi_div_two (T / 2 + (N : ℝ) - γ)
        have hlo := Real.neg_pi_div_two_lt_arctan (T / 2 - γ)
        linarith only [hhi, hlo]
      exact (hsub.trans_eq hbi).trans (hm_sum.trans
        (mul_le_mul_of_nonneg_left hpi (by positivity)))
    exact h1.trans ((mul_le_mul_of_nonneg_left hbi_le hM₀_pos.le).trans_eq (by ring))
  -- 2. Remote complement outside `shellZeros (T / 2) (4 * T)` (`0 < c ≤ 2` gives `O(1)`)
  have hrem_le : (∑' ρ : ↥(S_loc : Set zetaZeroConfig.carrier)ᶜ,
      zetaWeight (sourceTwist γ f) ρ.1 * depthKernel L (zetaDepth ρ.1)) ≤
      64 * M₀ * L_mass := by
    have hrem_ptw : ∀ ρ : ↥(S_loc : Set zetaZeroConfig.carrier)ᶜ,
        zetaWeight (sourceTwist γ f) ρ.1 * depthKernel L (zetaDepth ρ.1) ≤
          (64 * M₀) * ((zetaZeroConfig.mult ρ.1 : ℝ) * (1 / (1 + (ρ.1 : ℂ).im ^ 2))) := by
      intro ρ
      have hnot_sh : (ρ.1 : ℂ) ∉ shellZeros (T / 2) (4 * T) := fun hsh =>
        ρ.2 (Finset.mem_image.mpr ⟨⟨(ρ.1 : ℂ), hsh⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩)
      have hxi_01 :=
        CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp ρ.1.2
      have him_out : (ρ.1 : ℂ).im ≤ T / 2 ∨ 4 * T < (ρ.1 : ℂ).im := by
        by_contra hmid
        push Not at hmid
        exact hnot_sh (Finset.mem_filter.mpr
          ⟨mem_stripFinsetPos.mpr
            ⟨hxi_01.2.1, hxi_01.2.2, by linarith only [hT16, hmid.1], hmid.2, hxi_01.1⟩,
            hmid.1⟩)
      have hquartic : (1 / 16 : ℝ) * T ^ 2 * (1 + (ρ.1 : ℂ).im ^ 2) ≤
          (1 + ((ρ.1 : ℂ).im - γ) ^ 2) ^ 2 := by
        have hp4_le : ((ρ.1 : ℂ).im - γ) ^ 4 ≤ (1 + ((ρ.1 : ℂ).im - γ) ^ 2) ^ 2 := by
          nlinarith only [sq_nonneg ((ρ.1 : ℂ).im - γ)]
        refine le_trans ?_ hp4_le
        have hnn_q : 0 ≤ T ^ 2 * (1 + (ρ.1 : ℂ).im ^ 2) := by positivity
        rcases him_out with hle_half | hgt_4T
        · rcases lt_or_ge ((ρ.1 : ℂ).im) 0 with hneg | hnn
          · have h1' : T ≤ γ - (ρ.1 : ℂ).im := by linarith only [hγ.1, hneg]
            have h2' : -(ρ.1 : ℂ).im ≤ γ - (ρ.1 : ℂ).im := by linarith only [hT16, hγ.1]
            have hsq1 : T ^ 2 ≤ ((ρ.1 : ℂ).im - γ) ^ 2 := by nlinarith only [h1', hT16]
            have hsq2 : 1 + (ρ.1 : ℂ).im ^ 2 ≤ 2 * ((ρ.1 : ℂ).im - γ) ^ 2 := by
              nlinarith only [h2', hneg, hsq1, hT16]
            have hm := mul_le_mul hsq1 hsq2 (by positivity) (sq_nonneg _)
            have hp4 : ((ρ.1 : ℂ).im - γ) ^ 2 * (2 * ((ρ.1 : ℂ).im - γ) ^ 2) =
                2 * ((ρ.1 : ℂ).im - γ) ^ 4 := by ring
            linarith only [hm, hp4, hnn_q]
          · have h1' : T / 2 ≤ γ - (ρ.1 : ℂ).im := by linarith only [hγ.1, hle_half]
            have hsq1 : T ^ 2 / 4 ≤ ((ρ.1 : ℂ).im - γ) ^ 2 := by nlinarith only [h1', hT16]
            have him_sq : 1 + (ρ.1 : ℂ).im ^ 2 ≤ T ^ 2 := by nlinarith only [hnn, hle_half, hT16]
            have hm := mul_le_mul hsq1 hsq1 (by positivity) (sq_nonneg _)
            have hp4 : ((ρ.1 : ℂ).im - γ) ^ 2 * ((ρ.1 : ℂ).im - γ) ^ 2 =
                ((ρ.1 : ℂ).im - γ) ^ 4 := by ring
            nlinarith only [him_sq, hm, hp4]
        · have h1' : (ρ.1 : ℂ).im / 2 ≤ (ρ.1 : ℂ).im - γ := by linarith only [hγ_le_2T, hgt_4T]
          have h2' : 2 * T ≤ (ρ.1 : ℂ).im - γ := by linarith only [hγ_le_2T, hgt_4T]
          have hsq1 : 4 * T ^ 2 ≤ ((ρ.1 : ℂ).im - γ) ^ 2 := by nlinarith only [h2', hT16]
          have hsq2 : (1 / 8 : ℝ) * (1 + (ρ.1 : ℂ).im ^ 2) ≤ ((ρ.1 : ℂ).im - γ) ^ 2 := by
            nlinarith only [h1', hgt_4T, hT16]
          have hm := mul_le_mul hsq1 hsq2 (by positivity) (sq_nonneg _)
          have hp4 : ((ρ.1 : ℂ).im - γ) ^ 2 * ((ρ.1 : ℂ).im - γ) ^ 2 =
              ((ρ.1 : ℂ).im - γ) ^ 4 := by ring
          linarith only [hm, hp4, hnn_q]
      have hnsq_rem : Complex.normSq (tr (sourceTwist γ f).1 ρ.1) ≤
          (16 * M₀ / T ^ 2) * (1 / (1 + (ρ.1 : ℂ).im ^ 2)) := by
        refine (hnsq_quartic ρ.1).trans ?_
        refine (div_le_div_of_nonneg_left hM₀_pos.le (by positivity) hquartic).trans_eq ?_
        rw [mul_one_div, div_div, div_eq_div_iff (by positivity) (by positivity)]
        ring
      have hstrip := abs_re_sub_half_le_of_zeroConfig zetaZeroConfig ρ.1
      have hdk_le_4T2 : depthKernel L (zetaDepth ρ.1) ≤ 4 * T ^ 2 := by
        calc depthKernel L (zetaDepth ρ.1)
            ≤ Real.exp L := depthKernel_le_exp_of_abs_le_half hL_nn hstrip
          _ ≤ Real.exp (2 * Real.log T) :=
              Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc2
                (Real.log_nonneg (by linarith only [hT16])))
          _ = T ^ 2 := by
              rw [show (2 : ℝ) * Real.log T = ((2 : ℕ) : ℝ) * Real.log T by norm_num,
                Real.exp_nat_mul, Real.exp_log hT_pos]
          _ ≤ 4 * T ^ 2 := by nlinarith only [sq_nonneg T]
      dsimp only [zetaWeight]
      calc (zetaZeroConfig.mult ρ.1 : ℝ) * Complex.normSq (tr (sourceTwist γ f).1 ρ.1) *
              depthKernel L (zetaDepth ρ.1)
          ≤ (zetaZeroConfig.mult ρ.1 : ℝ) *
              ((16 * M₀ / T ^ 2) * (1 / (1 + (ρ.1 : ℂ).im ^ 2))) * (4 * T ^ 2) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hnsq_rem (Nat.cast_nonneg _)) hdk_le_4T2
              (depthKernel_nonneg _ _) (by positivity)
        _ = (64 * M₀) * ((zetaZeroConfig.mult ρ.1 : ℝ) * (1 / (1 + (ρ.1 : ℂ).im ^ 2))) := by
            field_simp [hT_pos.ne']; ring
    have htsum1 := Summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
      (fun _ _ => by positivity) hrem_ptw
      ((summable_heckeDefect (sourceTwist γ f) L).subtype
        (S_loc : Set zetaZeroConfig.carrier)ᶜ)
      (hsum_lor.mul_left _)
    rwa [tsum_mul_left] at htsum1
  exact (add_le_add hloc_le hrem_le).trans (by dsimp [B_f]; linarith)

/-- Under `FiniteOffLine`, for any `f : CompactTest` supported in `[-1/4, 1/4]` and `0 < c ≤ 2`,
`heckeDefect (sourceTwist γ f) (c * Real.log T) ≤ C_f / T ^ 2` for all `T ≥ 2` and
`γ ∈ Icc T (T + 1)`. -/
theorem exists_heckeDefect_compactTest_le_div_sq_of_finiteOffLine
    (hF : FiniteOffLine) (f : CompactTest) (hsupp : ∀ u, f.1 u ≠ 0 → |u| ≤ 1 / 4)
    {c : ℝ} (hc0 : 0 < c) (hc2 : c ≤ 2) :
    ∃ C_f : ℝ, 0 < C_f ∧ ∀ T : ℝ, 2 ≤ T → ∀ γ ∈ Icc T (T + 1),
      heckeDefect (sourceTwist γ f) (c * Real.log T) ≤ C_f / T ^ 2 := by
  classical
  obtain ⟨T₀, hT₀⟩ := finiteOffLine_iff_exists_onLine_above.mp hF
  let R₀ : ℝ := |T₀| + 1
  let S₀ : Finset ℂ := (zetaZeroConfig.finite_window (-R₀ - 1) R₀).toFinset
  let emb : {z // z ∈ S₀} → zetaZeroConfig.carrier :=
    fun z => ⟨z.1, ((Set.Finite.mem_toFinset _).mp z.2).1⟩
  let S_off : Finset zetaZeroConfig.carrier := S₀.attach.image emb
  have hS_im : ∀ ρ ∈ S_off, |(ρ : ℂ).im| ≤ R₀ + 1 := by
    intro ρ hρ
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hρ
    obtain ⟨_, h1, h2⟩ := (Set.Finite.mem_toFinset _).mp z.2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hsum_eq : ∀ (g : CompactTest) (L : ℝ), heckeDefect g L =
      ∑ ρ ∈ S_off, zetaWeight g ρ * depthKernel L (zetaDepth ρ) := by
    intro g L
    refine tsum_eq_sum fun ρ hρ_not => ?_
    have hgt : R₀ < |(ρ : ℂ).im| := by
      by_contra hle
      have habs := abs_le.mp (not_lt.mp hle)
      have hz : (ρ : ℂ) ∈ S₀ :=
        (Set.Finite.mem_toFinset _).mpr ⟨ρ.2, by linarith [habs.1], habs.2⟩
      exact hρ_not (Finset.mem_image.mpr ⟨⟨(ρ : ℂ), hz⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩)
    have hT₀_lt : T₀ < |(ρ : ℂ).im| :=
      lt_of_le_of_lt (by dsimp [R₀]; linarith [le_abs_self T₀]) hgt
    have hre : (ρ : ℂ).re = 1 / 2 := hT₀ (ρ : ℂ) ρ.2 hT₀_lt
    have hd0 : zetaDepth ρ = 0 := by simp [zetaDepth, hre]
    rw [hd0, depthKernel_zero_depth, mul_zero]
  let M₀ : ℝ := sourceTestSize f ^ 2 * Real.exp (1 / 4) + 1
  have hM₀_pos : 0 < M₀ := by dsimp [M₀]; positivity
  let M_mult : ℝ := ∑ ρ ∈ S_off, (zetaZeroConfig.mult ρ : ℝ)
  have hM_nn : 0 ≤ M_mult := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  let T₁ : ℝ := 2 * (R₀ + 1) + 4
  have hT₁_pos : 0 < T₁ := by dsimp [R₀, T₁]; positivity
  let C_low : ℝ := (M_mult + 1) * M₀ * T₁ ^ 4
  let C_high : ℝ := 16 * (M_mult + 1) * M₀
  refine ⟨C_low + C_high + 1, by dsimp [C_low, C_high]; positivity, fun T hT2 γ hγ => ?_⟩
  rw [hsum_eq (sourceTwist γ f) (c * Real.log T)]
  have hT_pos : 0 < T := by linarith only [hT2]
  have hL_nn : 0 ≤ c * Real.log T := mul_nonneg hc0.le (Real.log_nonneg (by linarith only [hT2]))
  have hdk_T2 : ∀ ρ : zetaZeroConfig.carrier,
      depthKernel (c * Real.log T) (zetaDepth ρ) ≤ T ^ 2 := by
    intro ρ
    calc depthKernel (c * Real.log T) (zetaDepth ρ)
        ≤ Real.exp (c * Real.log T) :=
          depthKernel_le_exp_of_abs_le_half hL_nn (abs_zetaDepth_le ρ)
      _ ≤ Real.exp (2 * Real.log T) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc2
            (Real.log_nonneg (by linarith only [hT2])))
      _ = T ^ 2 := by
          rw [show (2 : ℝ) * Real.log T = ((2 : ℕ) : ℝ) * Real.log T by norm_num,
            Real.exp_nat_mul, Real.exp_log hT_pos]
  have hnsq_quartic : ∀ ρ : zetaZeroConfig.carrier,
      Complex.normSq (tr (sourceTwist γ f).1 ρ) ≤ M₀ / (1 + ((ρ : ℂ).im - γ) ^ 2) ^ 2 := by
    intro ρ
    have hstrip := abs_re_sub_half_le_of_zeroConfig zetaZeroConfig ρ
    have hz_re : 0 ≤ ((ρ : ℂ) - (γ : ℂ) * I).re ∧ ((ρ : ℂ) - (γ : ℂ) * I).re ≤ 1 := by
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero]
      rw [abs_le] at hstrip
      exact ⟨by linarith only [hstrip.1], by linarith only [hstrip.2]⟩
    have hb := normSq_tr_strip_le_sourceTestSize f (by norm_num : (0 : ℝ) ≤ 1 / 4) hsupp hz_re
    have him_eq : ((ρ : ℂ) - (γ : ℂ) * I).im = (ρ : ℂ).im - γ := by simp
    rw [him_eq, ← tr_twist γ f.1 (ρ : ℂ)] at hb
    exact hb.trans (div_le_div_of_nonneg_right (by dsimp [M₀]; linarith) (by positivity))
  rcases le_or_gt T T₁ with hT_le | hT_gt
  · have hptw : ∀ ρ ∈ S_off,
        zetaWeight (sourceTwist γ f) ρ * depthKernel (c * Real.log T) (zetaDepth ρ) ≤
          (zetaZeroConfig.mult ρ : ℝ) * (M₀ * T₁ ^ 2) := by
      intro ρ _
      have hb1 : Complex.normSq (tr (sourceTwist γ f).1 ρ) ≤ M₀ :=
        (hnsq_quartic ρ).trans (div_le_self hM₀_pos.le (by nlinarith only [sq_nonneg ((ρ : ℂ).im - γ)]))
      have hb2 : depthKernel (c * Real.log T) (zetaDepth ρ) ≤ T₁ ^ 2 :=
        (hdk_T2 ρ).trans (pow_le_pow_left₀ hT_pos.le hT_le 2)
      dsimp only [zetaWeight]
      calc (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (sourceTwist γ f).1 ρ) *
              depthKernel (c * Real.log T) (zetaDepth ρ)
          ≤ (zetaZeroConfig.mult ρ : ℝ) * M₀ * T₁ ^ 2 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hb1 (Nat.cast_nonneg _)) hb2
              (depthKernel_nonneg _ _) (by positivity)
        _ = (zetaZeroConfig.mult ρ : ℝ) * (M₀ * T₁ ^ 2) := by ring
    have hsum1 : ∑ ρ ∈ S_off,
        zetaWeight (sourceTwist γ f) ρ * depthKernel (c * Real.log T) (zetaDepth ρ) ≤
          (M_mult + 1) * M₀ * T₁ ^ 2 := by
      refine (Finset.sum_le_sum hptw).trans ?_
      rw [← Finset.sum_mul]
      have : 0 ≤ M₀ * T₁ ^ 2 := by positivity
      nlinarith only [this, hM_nn]
    have hrat : 1 ≤ T₁ ^ 2 / T ^ 2 :=
      (one_le_div (by positivity)).mpr (pow_le_pow_left₀ hT_pos.le hT_le 2)
    have hCh_nn : 0 ≤ C_high := by dsimp [C_high]; positivity
    calc ∑ ρ ∈ S_off, zetaWeight (sourceTwist γ f) ρ * depthKernel (c * Real.log T) (zetaDepth ρ)
        ≤ ((M_mult + 1) * M₀ * T₁ ^ 2) * (T₁ ^ 2 / T ^ 2) :=
          hsum1.trans (le_mul_of_one_le_right (by positivity) hrat)
      _ = C_low / T ^ 2 := by dsimp [C_low]; ring
      _ ≤ (C_low + C_high + 1) / T ^ 2 :=
          div_le_div_of_nonneg_right (by linarith only [hCh_nn]) (by positivity)
  · have hptw : ∀ ρ ∈ S_off,
        zetaWeight (sourceTwist γ f) ρ * depthKernel (c * Real.log T) (zetaDepth ρ) ≤
          (zetaZeroConfig.mult ρ : ℝ) * (16 * M₀ / T ^ 2) := by
      intro ρ hρ
      have him_le : (ρ : ℂ).im ≤ R₀ + 1 := (abs_le.mp (hS_im ρ hρ)).2
      have hsep : T / 2 ≤ γ - (ρ : ℂ).im := by dsimp [T₁] at hT_gt; linarith only [hT_gt, hγ.1, him_le]
      have hden4 : T ^ 4 / 16 ≤ (1 + ((ρ : ℂ).im - γ) ^ 2) ^ 2 := by
        have hsq : T ^ 2 / 4 ≤ ((ρ : ℂ).im - γ) ^ 2 := by nlinarith only [hsep, hT2]
        nlinarith only [hsq, sq_nonneg (T ^ 2 / 4)]
      have hnsq_ρ : Complex.normSq (tr (sourceTwist γ f).1 ρ) ≤ 16 * M₀ / T ^ 4 :=
        (hnsq_quartic ρ).trans ((div_le_div_of_nonneg_left hM₀_pos.le (by positivity) hden4).trans_eq
          (by field_simp [hT_pos.ne']))
      dsimp only [zetaWeight]
      calc (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (sourceTwist γ f).1 ρ) *
              depthKernel (c * Real.log T) (zetaDepth ρ)
          ≤ (zetaZeroConfig.mult ρ : ℝ) * (16 * M₀ / T ^ 4) * T ^ 2 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hnsq_ρ (Nat.cast_nonneg _)) (hdk_T2 ρ)
              (depthKernel_nonneg _ _) (by positivity)
        _ = (zetaZeroConfig.mult ρ : ℝ) * (16 * M₀ / T ^ 2) := by field_simp [hT_pos.ne']
    have hsum1 : ∑ ρ ∈ S_off,
        zetaWeight (sourceTwist γ f) ρ * depthKernel (c * Real.log T) (zetaDepth ρ) ≤
          C_high / T ^ 2 := by
      refine (Finset.sum_le_sum hptw).trans ?_
      rw [← Finset.sum_mul]
      have h1 : 0 ≤ 16 * M₀ / T ^ 2 := by positivity
      have h2 : M_mult * (16 * M₀ / T ^ 2) ≤ (M_mult + 1) * (16 * M₀ / T ^ 2) := by
        nlinarith only [h1, hM_nn]
      exact h2.trans_eq (by dsimp [C_high]; ring)
    have hCl_nn : 0 ≤ C_low := by dsimp [C_low]; positivity
    exact hsum1.trans (div_le_div_of_nonneg_right (by linarith only [hCl_nn]) (by positivity))


/-! ## §4. Five-way dyadic `RH` equivalence and five-way fixed-`c` unit-window collapse -/

private theorem baseTwist_finTheta_c2Jet_le (L : ℝ) (n : ℕ) (γ : ℝ) :
    (let R := fun τ : ℝ => finiteThetaSourceMomentReading (baseTwistTest τ) L 1 n;
      R γ + |deriv R γ| + |deriv (deriv R) γ|) ≤
      3 * finiteThetaSourceMomentReading (sourceTwist γ baseBumpTest) L 1 n +
        3 * finiteThetaSourceMomentReading
          (sourceTwist γ (momentCompactTest 1 baseBumpTest)) L 1 n +
        finiteThetaSourceMomentReading
          (sourceTwist γ (momentCompactTest 2 baseBumpTest)) L 1 n := by
  have hfun : (fun τ : ℝ => finiteThetaSourceMomentReading (baseTwistTest τ) L 1 n) =
      fun τ : ℝ => finiteThetaSourceMomentReading (sourceTwist τ baseBumpTest) L 1 n :=
    funext fun τ => by rw [sourceTwist_baseBumpTest_eq]
  dsimp only
  rw [hfun, ← sourceTwist_baseBumpTest_eq]
  have hd1 := abs_deriv_finiteThetaSourceMomentReading_le baseBumpTest L 1 n γ zero_lt_one
  rw [one_mul, inv_one, one_mul] at hd1
  have hd2 := abs_deriv_deriv_finiteThetaSourceMomentReading_le baseBumpTest L 1 n γ
  linarith only [hd1, hd2]

private theorem baseTwist_polyTheta_c2Jet_le (L : ℝ) (n : ℕ) (γ : ℝ) :
    (let P := fun τ : ℝ => polynomialThetaSourceMomentReading (baseTwistTest τ) L 1 n;
      P γ + |deriv P γ| + |deriv (deriv P) γ|) ≤
      3 * polynomialThetaSourceMomentReading (sourceTwist γ baseBumpTest) L 1 n +
        3 * polynomialThetaSourceMomentReading
          (sourceTwist γ (momentCompactTest 1 baseBumpTest)) L 1 n +
        polynomialThetaSourceMomentReading
          (sourceTwist γ (momentCompactTest 2 baseBumpTest)) L 1 n := by
  have hfun : (fun τ : ℝ => polynomialThetaSourceMomentReading (baseTwistTest τ) L 1 n) =
      fun τ : ℝ => polynomialThetaSourceMomentReading (sourceTwist τ baseBumpTest) L 1 n :=
    funext fun τ => by rw [sourceTwist_baseBumpTest_eq]
  dsimp only
  rw [hfun, ← sourceTwist_baseBumpTest_eq]
  have hd1 := abs_deriv_polynomialThetaSourceMomentReading_le baseBumpTest L 1 n γ zero_lt_one
  rw [one_mul, inv_one, one_mul] at hd1
  have hd2 := abs_deriv_deriv_polynomialThetaSourceMomentReading_le baseBumpTest L 1 n γ
  linarith only [hd1, hd2]

private theorem continuous_baseTwist_finTheta_c2Jet (L : ℝ) (n : ℕ) :
    Continuous (fun γ : ℝ =>
      let R := fun τ : ℝ => finiteThetaSourceMomentReading (baseTwistTest τ) L 1 n;
      R γ + |deriv R γ| + |deriv (deriv R) γ|) := by
  have hfun : (fun τ : ℝ => finiteThetaSourceMomentReading (baseTwistTest τ) L 1 n) =
      fun τ : ℝ => finiteThetaSourceMomentReading (sourceTwist τ baseBumpTest) L 1 n :=
    funext fun τ => by rw [sourceTwist_baseBumpTest_eq]
  dsimp only
  rw [hfun]
  exact ((differentiable_finiteThetaSourceMomentReading_sourceTwist baseBumpTest L 1 n).continuous.add
    (differentiable_deriv_finiteThetaSourceMomentReading_sourceTwist
      baseBumpTest L 1 n).continuous.abs).add
    (continuous_deriv2_finiteThetaSourceMomentReading_sourceTwist baseBumpTest L 1 n).abs

private theorem continuous_baseTwist_polyTheta_c2Jet (L : ℝ) (n : ℕ) :
    Continuous (fun γ : ℝ =>
      let P := fun τ : ℝ => polynomialThetaSourceMomentReading (baseTwistTest τ) L 1 n;
      P γ + |deriv P γ| + |deriv (deriv P) γ|) := by
  have hfun : (fun τ : ℝ => polynomialThetaSourceMomentReading (baseTwistTest τ) L 1 n) =
      fun τ : ℝ => polynomialThetaSourceMomentReading (sourceTwist τ baseBumpTest) L 1 n :=
    funext fun τ => by rw [sourceTwist_baseBumpTest_eq]
  dsimp only
  rw [hfun]
  exact ((differentiable_polynomialThetaSourceMomentReading_sourceTwist
      baseBumpTest L 1 n).continuous.add
    (differentiable_deriv_polynomialThetaSourceMomentReading_sourceTwist
      baseBumpTest L 1 n).continuous.abs).add
    (continuous_deriv2_polynomialThetaSourceMomentReading_sourceTwist baseBumpTest L 1 n).abs

/-- **Five-Way Dyadic Unit-Window `min` / `mean` / `sup` / `C²`-Jet Equivalence for
`RiemannHypothesis` (`riemannHypothesis_unitWindow_min_mean_max_finiteTheta_tfae`).**
For every `c₀ > 0`, with `L_k(T) = 2^k c₀ log T` and `n_ap = apertureStage L_k(T) T`,
`RiemannHypothesis` is unconditionally equivalent (`List.TFAE`) to uniform boundedness across
`(k, T)` (`k : ℕ`, `T ≥ 2`) of:
- (2) the unit-window minimum `sInf` (Criterion 5 of `riemannHypothesis_finiteTheta_poleNodal_dyadic_tfae`),
- (3) the unit-window mean `∫_{T}^{T+1}`,
- (4) the unit-window supremum `sSup`,
- (5) the unit-window `C²`-jet supremum `sSup (R + |R'| + |R''|)`. -/
theorem riemannHypothesis_unitWindow_min_mean_max_finiteTheta_tfae {c₀ : ℝ} (hc₀ : 0 < c₀) :
    List.TFAE [
      RiemannHypothesis,
      ∃ C : ℝ, ∀ (k : ℕ) (T : ℝ), 2 ≤ T →
        sInf ((fun γ => finiteThetaSourceMomentReading (baseTwistTest γ)
          ((2 : ℝ) ^ k * c₀ * Real.log T) 1
          (apertureStage ((2 : ℝ) ^ k * c₀ * Real.log T) T)) '' Icc T (T + 1)) ≤ C,
      ∃ C : ℝ, ∀ (k : ℕ) (T : ℝ), 2 ≤ T →
        (∫ γ in Icc T (T + 1), finiteThetaSourceMomentReading (baseTwistTest γ)
          ((2 : ℝ) ^ k * c₀ * Real.log T) 1
          (apertureStage ((2 : ℝ) ^ k * c₀ * Real.log T) T)) ≤ C,
      ∃ C : ℝ, ∀ (k : ℕ) (T : ℝ), 2 ≤ T →
        sSup ((fun γ => finiteThetaSourceMomentReading (baseTwistTest γ)
          ((2 : ℝ) ^ k * c₀ * Real.log T) 1
          (apertureStage ((2 : ℝ) ^ k * c₀ * Real.log T) T)) '' Icc T (T + 1)) ≤ C,
      ∃ C : ℝ, ∀ (k : ℕ) (T : ℝ), 2 ≤ T →
        sSup ((fun γ =>
          let R := fun τ : ℝ => finiteThetaSourceMomentReading (baseTwistTest τ)
            ((2 : ℝ) ^ k * c₀ * Real.log T) 1
            (apertureStage ((2 : ℝ) ^ k * c₀ * Real.log T) T)
          R γ + |deriv R γ| + |deriv (deriv R) γ|) '' Icc T (T + 1)) ≤ C
    ] := by
  have hR_cont : ∀ L : ℝ, ∀ n : ℕ, Continuous
      (fun γ : ℝ => finiteThetaSourceMomentReading (baseTwistTest γ) L 1 n) := fun L n => by
    have hfun : (fun γ : ℝ => finiteThetaSourceMomentReading (baseTwistTest γ) L 1 n) =
        fun γ : ℝ => finiteThetaSourceMomentReading (sourceTwist γ baseBumpTest) L 1 n :=
      funext fun γ => by rw [sourceTwist_baseBumpTest_eq]
    rw [hfun]
    exact (differentiable_finiteThetaSourceMomentReading_sourceTwist baseBumpTest L 1 n).continuous
  tfae_have 5 → 4 := by
    rintro ⟨C, h5⟩
    refine ⟨C, fun k T hT => ?_⟩
    let L := (2 : ℝ) ^ k * c₀ * Real.log T
    let n := apertureStage L T
    let R := fun τ : ℝ => finiteThetaSourceMomentReading (baseTwistTest τ) L 1 n
    let J := fun γ : ℝ => R γ + |deriv R γ| + |deriv (deriv R) γ|
    have hJ_bdd : BddAbove (J '' Icc T (T + 1)) :=
      (isCompact_Icc.image (continuous_baseTwist_finTheta_c2Jet L n)).bddAbove
    have hne : (R '' Icc T (T + 1)).Nonempty := ⟨R T, T, ⟨le_rfl, by linarith⟩, rfl⟩
    refine (csSup_le hne ?_).trans (h5 k T hT)
    rintro _ ⟨γ, hγ, rfl⟩
    have hle : R γ ≤ J γ := by
      dsimp [J]; linarith only [abs_nonneg (deriv R γ), abs_nonneg (deriv (deriv R) γ)]
    exact hle.trans (le_csSup hJ_bdd ⟨γ, hγ, rfl⟩)
  tfae_have 4 → 3 := by
    rintro ⟨C, h4⟩
    refine ⟨C, fun k T hT => ?_⟩
    let L := (2 : ℝ) ^ k * c₀ * Real.log T
    let n := apertureStage L T
    exact (exists_unitWindow_sInf_eq_and_le_mean_le_sSup T (hR_cont L n).continuousOn).2.2.trans
      (h4 k T hT)
  tfae_have 3 → 2 := by
    rintro ⟨C, h3⟩
    refine ⟨C, fun k T hT => ?_⟩
    let L := (2 : ℝ) ^ k * c₀ * Real.log T
    let n := apertureStage L T
    exact (exists_unitWindow_sInf_eq_and_le_mean_le_sSup T (hR_cont L n).continuousOn).2.1.trans
      (h3 k T hT)
  tfae_have 2 → 1 := by
    rintro ⟨C, h2⟩
    have h5_crit : ∃ C : ℝ, ∀ (k : ℕ) (T : ℝ), 2 ≤ T → ∃ γ ∈ Icc T (T + 1),
        finiteThetaSourceMomentReading (baseTwistTest γ) ((2 : ℝ) ^ k * c₀ * Real.log T) 1
          (apertureStage ((2 : ℝ) ^ k * c₀ * Real.log T) T) ≤ C := by
      refine ⟨C, fun k T hT => ?_⟩
      let L := (2 : ℝ) ^ k * c₀ * Real.log T
      let n := apertureStage L T
      exact (sInf_unitWindow_le_iff_exists_le (hR_cont L n).continuousOn).mp (h2 k T hT)
    exact ((riemannHypothesis_finiteTheta_poleNodal_dyadic_tfae hc₀ zero_le_one).out 4 0).mp h5_crit
  tfae_have 1 → 5 := by
    intro hRH
    obtain ⟨E₀, _, hb₀⟩ := exists_uniform_aperture_compactTest_error_bounds
      baseBumpTest abs_le_quarter_of_baseBumpTest_ne_zero
    obtain ⟨E₁, _, hb₁⟩ := exists_uniform_aperture_compactTest_error_bounds
      (momentCompactTest 1 baseBumpTest)
      (abs_le_of_momentCompactTest_ne_zero 1 baseBumpTest abs_le_quarter_of_baseBumpTest_ne_zero)
    obtain ⟨E₂, _, hb₂⟩ := exists_uniform_aperture_compactTest_error_bounds
      (momentCompactTest 2 baseBumpTest)
      (abs_le_of_momentCompactTest_ne_zero 2 baseBumpTest abs_le_quarter_of_baseBumpTest_ne_zero)
    refine ⟨3 * E₀ + 3 * E₁ + E₂, fun k T _ => ?_⟩
    let L := (2 : ℝ) ^ k * c₀ * Real.log T
    let n := apertureStage L T
    let R := fun τ : ℝ => finiteThetaSourceMomentReading (baseTwistTest τ) L 1 n
    let J := fun γ : ℝ => R γ + |deriv R γ| + |deriv (deriv R) γ|
    have hne : (J '' Icc T (T + 1)).Nonempty := ⟨J T, T, ⟨le_rfl, by linarith⟩, rfl⟩
    refine csSup_le hne ?_
    rintro _ ⟨γ, hγ, rfl⟩
    obtain ⟨hγ_adm, hL_adm⟩ := apertureStage_admissible L T hγ
    rw [one_mul] at hL_adm
    have hn1 := one_le_apertureStage L T
    have he0 := (hb₀ n hn1 L γ hγ_adm hL_adm).1
    have he1 := (hb₁ n hn1 L γ hγ_adm hL_adm).1
    have he2 := (hb₂ n hn1 L γ hγ_adm hL_adm).1
    rw [heckeDefect_compactTest_eq_zero_of_riemannHypothesis hRH, sub_zero] at he0 he1 he2
    have h0 := le_of_abs_le he0
    have h1 := le_of_abs_le he1
    have h2 := le_of_abs_le he2
    have hjet := baseTwist_finTheta_c2Jet_le L n γ
    dsimp only [J, R] at hjet ⊢
    linarith only [hjet, h0, h1, h2]
  tfae_finish

/-- **Five-Way Fixed-`c` Unit-Window `min` / `mean` / `sup` / `C²`-Jet Equivalence
(`polynomialTheta_unitWindow_min_mean_max_log_tfae`).**
At any fixed logarithmic scale `L = c * Real.log T` (`0 < c ≤ 2`) and linear stage
`linearThetaStage (T + 1)`, eventual `O(1)` boundedness of `unitWindowDepthCharge T (c log T)`
is unconditionally equivalent (`List.TFAE`) to eventual `O(1)` boundedness of the unit-window
minimum `sInf`, unit-window mean, unit-window supremum `sSup`, and unit-window `C²`-jet supremum
of `polynomialThetaSourceMomentReading (baseTwistTest ·) (c log T) 1 (linearThetaStage (T + 1))`. -/
theorem polynomialTheta_unitWindow_min_mean_max_log_tfae {c : ℝ} (hc0 : 0 < c) (hc2 : c ≤ 2) :
    List.TFAE [
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T : ℝ in atTop, unitWindowDepthCharge T (c * Real.log T) ≤ B,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T : ℝ in atTop,
        sInf ((fun γ => polynomialThetaSourceMomentReading (baseTwistTest γ) (c * Real.log T) 1
          (linearThetaStage (T + 1))) '' Icc T (T + 1)) ≤ B,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T : ℝ in atTop,
        (∫ γ in Icc T (T + 1), polynomialThetaSourceMomentReading (baseTwistTest γ)
          (c * Real.log T) 1 (linearThetaStage (T + 1))) ≤ B,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T : ℝ in atTop,
        sSup ((fun γ => polynomialThetaSourceMomentReading (baseTwistTest γ) (c * Real.log T) 1
          (linearThetaStage (T + 1))) '' Icc T (T + 1)) ≤ B,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T : ℝ in atTop,
        sSup ((fun γ =>
          let P := fun τ : ℝ => polynomialThetaSourceMomentReading (baseTwistTest τ)
            (c * Real.log T) 1 (linearThetaStage (T + 1))
          P γ + |deriv P γ| + |deriv (deriv P) γ|) '' Icc T (T + 1)) ≤ B
    ] := by
  have hP_cont : ∀ L : ℝ, ∀ n : ℕ, Continuous
      (fun γ : ℝ => polynomialThetaSourceMomentReading (baseTwistTest γ) L 1 n) := fun L n => by
    have hfun : (fun γ : ℝ => polynomialThetaSourceMomentReading (baseTwistTest γ) L 1 n) =
        fun γ : ℝ => polynomialThetaSourceMomentReading (sourceTwist γ baseBumpTest) L 1 n :=
      funext fun γ => by rw [sourceTwist_baseBumpTest_eq]
    rw [hfun]
    exact (differentiable_polynomialThetaSourceMomentReading_sourceTwist
      baseBumpTest L 1 n).continuous
  tfae_have 5 → 4 := by
    rintro ⟨B, hB, hev⟩
    refine ⟨B, hB, hev.mono fun T hT => ?_⟩
    let L := c * Real.log T
    let n := linearThetaStage (T + 1)
    let P := fun τ : ℝ => polynomialThetaSourceMomentReading (baseTwistTest τ) L 1 n
    let J := fun γ : ℝ => P γ + |deriv P γ| + |deriv (deriv P) γ|
    have hJ_bdd : BddAbove (J '' Icc T (T + 1)) :=
      (isCompact_Icc.image (continuous_baseTwist_polyTheta_c2Jet L n)).bddAbove
    have hne : (P '' Icc T (T + 1)).Nonempty := ⟨P T, T, ⟨le_rfl, by linarith⟩, rfl⟩
    refine (csSup_le hne ?_).trans hT
    rintro _ ⟨γ, hγ, rfl⟩
    have hle : P γ ≤ J γ := by
      dsimp [J]; linarith only [abs_nonneg (deriv P γ), abs_nonneg (deriv (deriv P) γ)]
    exact hle.trans (le_csSup hJ_bdd ⟨γ, hγ, rfl⟩)
  tfae_have 4 → 3 := by
    rintro ⟨B, hB, hev⟩
    refine ⟨B, hB, hev.mono fun T hT => ?_⟩
    exact (exists_unitWindow_sInf_eq_and_le_mean_le_sSup T
      (hP_cont (c * Real.log T) (linearThetaStage (T + 1))).continuousOn).2.2.trans hT
  tfae_have 3 → 2 := by
    rintro ⟨B, hB, hev⟩
    refine ⟨B, hB, hev.mono fun T hT => ?_⟩
    exact (exists_unitWindow_sInf_eq_and_le_mean_le_sSup T
      (hP_cont (c * Real.log T) (linearThetaStage (T + 1))).continuousOn).2.1.trans hT
  tfae_have 2 → 1 := by
    rintro ⟨B, hB, hev⟩
    obtain ⟨C_lin, hC_lin, hpoly_ptw⟩ :=
      exists_compactTest_polynomialReading_sub_heckeDefect_le_log_div
        baseBumpTest abs_le_quarter_of_baseBumpTest_ne_zero
    have hcos_pos := cos_quarter_sq_pos
    refine ⟨(B + 2 * C_lin + 1) / Real.cos (1 / 4 : ℝ) ^ 2, by positivity, ?_⟩
    filter_upwards [hev, eventually_ge_atTop (4 : ℝ)] with T hT_inf hT4
    let L := c * Real.log T
    let n := linearThetaStage (T + 1)
    obtain ⟨γ_min, hγ_min, hFB⟩ :=
      (sInf_unitWindow_le_iff_exists_le (hP_cont L n).continuousOn).mp hT_inf
    have hT_pos : 0 < T := by linarith only [hT4]
    have hγ_ge2 : 2 ≤ γ_min := by linarith only [hT4, hγ_min.1]
    have hL0 : 0 ≤ L := mul_nonneg hc0.le (Real.log_nonneg (by linarith only [hT4]))
    have hL2 : L ≤ 2 * Real.log γ_min :=
      (mul_le_mul_of_nonneg_right hc2 (Real.log_nonneg (by linarith only [hT4]))).trans
        (mul_le_mul_of_nonneg_left (Real.log_le_log hT_pos hγ_min.1) zero_le_two)
    have hn_lo : linearThetaStage γ_min ≤ n :=
      linearThetaStage_mono (by linarith only [hγ_ge2]) hγ_min.2
    have hn_hi : (n : ℝ) ≤ 10 * γ_min + 15 := by
      have hb := (linearThetaStage_bounds (by linarith only [hT4] : 1 ≤ T + 1)).2
      dsimp [n]; linarith only [hb, hγ_min.1, hT4]
    have hdiff := hpoly_ptw γ_min L n hγ_ge2 hL0 hL2 hn_lo hn_hi
    rw [sourceTwist_baseBumpTest_eq] at hdiff
    have herr_le : C_lin * Real.log γ_min / γ_min ≤ 2 * C_lin := by
      have hγ_pos : 0 < γ_min := by linarith only [hγ_ge2]
      have hlog_le : Real.log γ_min ≤ γ_min := by
        have h1 := Real.add_one_le_exp (Real.log γ_min)
        rw [Real.exp_log hγ_pos] at h1
        linarith only [h1]
      calc C_lin * Real.log γ_min / γ_min
          ≤ C_lin * γ_min / γ_min :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog_le hC_lin.le) hγ_pos.le
        _ = C_lin := mul_div_cancel_right₀ C_lin hγ_pos.ne'
        _ ≤ 2 * C_lin := by linarith only [hC_lin]
    have hhd_le : heckeDefect (baseTwistTest γ_min) L ≤ B + 2 * C_lin + 1 := by
      have h1 := (abs_le.mp hdiff).1
      linarith only [h1, hFB, herr_le]
    have hcoer : Real.cos (1 / 4 : ℝ) ^ 2 * unitWindowDepthCharge T L ≤
        heckeDefect (baseTwistTest γ_min) L :=
      unitWindow_depthCharge_le_heckeDefect T L hγ_min.1 hγ_min.2
    exact (le_div_iff₀' hcos_pos).mpr (hcoer.trans hhd_le)
  tfae_have 1 → 5 := by
    rintro ⟨B, hB, hev⟩
    let f₀ := baseBumpTest
    let f₁ := momentCompactTest 1 baseBumpTest
    let f₂ := momentCompactTest 2 baseBumpTest
    have hs₀ := abs_le_quarter_of_baseBumpTest_ne_zero
    have hs₁ := abs_le_of_momentCompactTest_ne_zero 1 baseBumpTest hs₀
    have hs₂ := abs_le_of_momentCompactTest_ne_zero 2 baseBumpTest hs₀
    obtain ⟨B₀, hB₀, hev₀⟩ :=
      eventually_heckeDefect_compactTest_le_of_unitWindowDepthCharge_le f₀ hs₀ hc0 hc2 hB hev
    obtain ⟨B₁, hB₁, hev₁⟩ :=
      eventually_heckeDefect_compactTest_le_of_unitWindowDepthCharge_le f₁ hs₁ hc0 hc2 hB hev
    obtain ⟨B₂, hB₂, hev₂⟩ :=
      eventually_heckeDefect_compactTest_le_of_unitWindowDepthCharge_le f₂ hs₂ hc0 hc2 hB hev
    obtain ⟨C₀, hC₀, hp₀⟩ := exists_compactTest_polynomialReading_sub_heckeDefect_le_log_div f₀ hs₀
    obtain ⟨C₁, hC₁, hp₁⟩ := exists_compactTest_polynomialReading_sub_heckeDefect_le_log_div f₁ hs₁
    obtain ⟨C₂, hC₂, hp₂⟩ := exists_compactTest_polynomialReading_sub_heckeDefect_le_log_div f₂ hs₂
    let B_jet : ℝ := 3 * (B₀ + C₀) + 3 * (B₁ + C₁) + (B₂ + C₂) + 1
    refine ⟨B_jet, by dsimp [B_jet]; positivity, ?_⟩
    filter_upwards [hev₀, hev₁, hev₂, eventually_ge_atTop (4 : ℝ)]
      with T hh₀ hh₁ hh₂ hT4
    let L := c * Real.log T
    let n := linearThetaStage (T + 1)
    let P := fun τ : ℝ => polynomialThetaSourceMomentReading (baseTwistTest τ) L 1 n
    let J := fun γ : ℝ => P γ + |deriv P γ| + |deriv (deriv P) γ|
    have hne : (J '' Icc T (T + 1)).Nonempty := ⟨J T, T, ⟨le_rfl, by linarith⟩, rfl⟩
    refine csSup_le hne ?_
    rintro _ ⟨γ, hγ, rfl⟩
    have hT_pos : 0 < T := by linarith only [hT4]
    have hγ_ge2 : 2 ≤ γ := by linarith only [hT4, hγ.1]
    have hγ_pos : 0 < γ := by linarith only [hγ_ge2]
    have hL0 : 0 ≤ L := mul_nonneg hc0.le (Real.log_nonneg (by linarith only [hT4]))
    have hL2 : L ≤ 2 * Real.log γ :=
      (mul_le_mul_of_nonneg_right hc2 (Real.log_nonneg (by linarith only [hT4]))).trans
        (mul_le_mul_of_nonneg_left (Real.log_le_log hT_pos hγ.1) zero_le_two)
    have hn_lo : linearThetaStage γ ≤ n :=
      linearThetaStage_mono (by linarith only [hγ_ge2]) hγ.2
    have hn_hi : (n : ℝ) ≤ 10 * γ + 15 := by
      have hb := (linearThetaStage_bounds (by linarith only [hT4] : 1 ≤ T + 1)).2
      dsimp [n]; linarith only [hb, hγ.1, hT4]
    have hlog_div_le1 : Real.log γ / γ ≤ 1 := by
      rw [div_le_one hγ_pos]
      have h1 := Real.add_one_le_exp (Real.log γ)
      rw [Real.exp_log hγ_pos] at h1
      linarith only [h1]
    have hb_poly : ∀ (g : CompactTest) {Bg Cg : ℝ}, 0 < Cg →
        heckeDefect (sourceTwist γ g) L ≤ Bg →
        |polynomialThetaSourceMomentReading (sourceTwist γ g) L 1 n -
            heckeDefect (sourceTwist γ g) L| ≤ Cg * Real.log γ / γ →
        polynomialThetaSourceMomentReading (sourceTwist γ g) L 1 n ≤ Bg + Cg := by
      intro g Bg Cg hCg hhd hdiff
      have h1 := (le_abs_self _).trans hdiff
      have h2 : Cg * Real.log γ / γ ≤ Cg := by
        rw [mul_div_assoc]
        exact (mul_le_mul_of_nonneg_left hlog_div_le1 hCg.le).trans_eq (mul_one _)
      linarith only [h1, h2, hhd]
    have hv₀ := hb_poly f₀ hC₀ (hh₀ γ hγ) (hp₀ γ L n hγ_ge2 hL0 hL2 hn_lo hn_hi)
    have hv₁ := hb_poly f₁ hC₁ (hh₁ γ hγ) (hp₁ γ L n hγ_ge2 hL0 hL2 hn_lo hn_hi)
    have hv₂ := hb_poly f₂ hC₂ (hh₂ γ hγ) (hp₂ γ L n hγ_ge2 hL0 hL2 hn_lo hn_hi)
    have hjet := baseTwist_polyTheta_c2Jet_le L n γ
    dsimp only [J, P, f₀, f₁, f₂, B_jet] at hjet hv₀ hv₁ hv₂ ⊢
    linarith only [hjet, hv₀, hv₁, hv₂]
  tfae_finish


/-! ## §5. Dyadic unit-window supremum `O_c(log U)` collapse and three-part separation -/

/-- **Unconditional Half-Gate (`0 < c < 1 / 2`) Dyadic Collapse of the Unit-Window Supremum
(`exists_dyadicMean_unitWindow_sup_polynomialTheta_le_log_up_to_half`).**
For every `0 < c < 1 / 2`, the dyadic mean over `T ∈ [U, 2 * U]` of the **unit-window supremum**
`sSup_{γ ∈ [T, T+1]} polynomialThetaSourceMomentReading (baseTwistTest γ) (c log T) 1 (linearThetaStage (2U + 2))`
collapses unconditionally to `O_c(log U)`. -/
theorem exists_dyadicMean_unitWindow_sup_polynomialTheta_le_log_up_to_half
    {c : ℝ} (hc0 : 0 < c) (hc_hi : c < 1 / 2) :
    ∃ K_sup : ℝ, 0 < K_sup ∧ ∀ᶠ U : ℝ in atTop,
      (1 / U) * (∫ T in Icc U (2 * U),
        sSup ((fun γ => polynomialThetaSourceMomentReading (baseTwistTest γ)
          (c * Real.log T) 1 (linearThetaStage (2 * U + 2))) '' Icc T (T + 1))) ≤
        K_sup * Real.log U := by
  let f₀ := baseBumpTest
  let f₁ := momentCompactTest 1 baseBumpTest
  have hs₀ := abs_le_quarter_of_baseBumpTest_ne_zero
  have hs₁ := abs_le_of_momentCompactTest_ne_zero 1 baseBumpTest hs₀
  obtain ⟨K₀, hK₀, hev₀⟩ :=
    exists_dyadicMean_compactTest_polynomialTheta_le_log_up_to_half f₀ hs₀ hc0 hc_hi
  obtain ⟨K₁, hK₁, hev₁⟩ :=
    exists_dyadicMean_compactTest_polynomialTheta_le_log_up_to_half f₁ hs₁ hc0 hc_hi
  have ht_w1 : Tendsto (fun U : ℝ => (3 / 4 : ℝ) * U) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have ht_w2 : Tendsto (fun U : ℝ => U + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_id
  let K_sup : ℝ := 12 * K₀ + 6 * K₁ + 1
  refine ⟨K_sup, by dsimp [K_sup]; positivity, ?_⟩
  filter_upwards [ht_w1.eventually hev₀, ht_w2.eventually hev₀,
    ht_w1.eventually hev₁, ht_w2.eventually hev₁,
    eventually_ge_atTop (16 : ℝ)]
    with U hw1_0 hw2_0 hw1_1 hw2_1 hU16
  have hU_pos : 0 < U := by linarith only [hU16]
  have hlogU_ge2 : 2 ≤ Real.log U := by
    have h2 := Real.log_two_gt_d9
    have h16_eq : (2 : ℝ) ^ (4 : ℕ) = 16 := by norm_num
    have h16 : Real.log ((2 : ℝ) ^ (4 : ℕ)) ≤ Real.log U :=
      Real.log_le_log (by norm_num) (h16_eq.trans_le hU16)
    rw [Real.log_pow] at h16; push_cast at h16; linarith only [h2, h16]
  let n : ℕ := linearThetaStage (2 * U + 2)
  let h_fn : CompactTest → ℝ → ℝ := fun g γ =>
    polynomialThetaSourceMomentReading (sourceTwist γ g) (c * Real.log (max 1 γ)) 1 n
  have hh_cont : ∀ g : CompactTest, Continuous (h_fn g) := fun g => by
    have hmax_cont : Continuous (fun γ : ℝ => max (1 : ℝ) γ) :=
      (continuous_const (y := (1 : ℝ))).max continuous_id
    have hlog_cont : Continuous (fun γ : ℝ => Real.log (max 1 γ)) :=
      Real.continuousOn_log.comp_continuous hmax_cont fun x =>
        (lt_of_lt_of_le zero_lt_one (le_max_left 1 x)).ne'
    dsimp only [h_fn]
    exact Continuous.comp
      (g := fun p : ℝ × ℝ => polynomialThetaSourceMomentReading (sourceTwist p.1 g) p.2 1 n)
      (f := fun γ : ℝ => (γ, c * Real.log (max 1 γ)))
      (continuous_polynomialThetaSourceMomentReading_sourceTwist_pair g n)
      (continuous_id.prodMk ((continuous_const (y := c)).mul hlog_cont))
  have hh_nn : ∀ g : CompactTest, ∀ γ : ℝ, 0 ≤ h_fn g γ := fun g γ =>
    polynomialThetaSourceMomentReading_nonneg _ _ _ _
  -- Integrability of `T ↦ sSup ...` on `Icc U (2 * U)` via `continuousOn_sSup_unitWindow_of_continuous`
  let G_clamped : ℝ × ℝ → ℝ := fun p =>
    polynomialThetaSourceMomentReading (sourceTwist p.1 f₀) (c * Real.log (max 1 p.2)) 1 n
  have hG_cont : Continuous G_clamped := by
    have hlog_snd : Continuous (fun p : ℝ × ℝ => Real.log (max 1 p.2)) :=
      Real.continuousOn_log.comp_continuous
        ((continuous_const (y := (1 : ℝ))).max continuous_snd) fun p =>
          (lt_of_lt_of_le zero_lt_one (le_max_left 1 p.2)).ne'
    dsimp only [G_clamped]
    exact Continuous.comp
      (g := fun p : ℝ × ℝ => polynomialThetaSourceMomentReading (sourceTwist p.1 f₀) p.2 1 n)
      (f := fun p : ℝ × ℝ => (p.1, c * Real.log (max 1 p.2)))
      (continuous_polynomialThetaSourceMomentReading_sourceTwist_pair f₀ n)
      (continuous_fst.prodMk ((continuous_const (y := c)).mul hlog_snd))
  let supFn : ℝ → ℝ := fun T =>
    sSup ((fun γ => polynomialThetaSourceMomentReading (baseTwistTest γ)
      (c * Real.log T) 1 n) '' Icc T (T + 1))
  have hsup_eq_on : EqOn (fun T : ℝ => sSup ((fun γ => G_clamped (γ, T)) '' Icc T (T + 1)))
      supFn (Icc U (2 * U)) := by
    intro T hT
    have hmax_T : max (1 : ℝ) T = T := max_eq_right (by linarith only [hU16, hT.1])
    dsimp only [G_clamped, supFn, f₀]
    congr 1
    ext y
    simp only [mem_image]
    constructor <;> rintro ⟨γ, hγ, rfl⟩ <;>
      exact ⟨γ, hγ, by rw [hmax_T, sourceTwist_baseBumpTest_eq]⟩
  have hsup_contOn : ContinuousOn supFn (Icc U (2 * U)) :=
    (continuousOn_sSup_unitWindow_of_continuous hG_cont).congr hsup_eq_on.symm
  have hsup_int : IntegrableOn supFn (Icc U (2 * U)) volume :=
    hsup_contOn.integrableOn_compact isCompact_Icc
  -- Pointwise bound on `supFn T` for `T ∈ Icc U (2 * U)`
  have hptw_T : ∀ T ∈ Icc U (2 * U),
      supFn T ≤ 2 * (∫ γ in Icc T (T + 1), h_fn f₀ γ) + (∫ γ in Icc T (T + 1), h_fn f₁ γ) := by
    intro T hT
    have hT1 : 1 ≤ T := by linarith only [hU16, hT.1]
    have hT_pos : 0 < T := by linarith only [hT1]
    have hL_nn : 0 ≤ c * Real.log T := mul_nonneg hc0.le (Real.log_nonneg hT1)
    have hsob : supFn T ≤
        2 * (∫ γ in Icc T (T + 1),
          polynomialThetaSourceMomentReading (sourceTwist γ f₀) (c * Real.log T) 1 n) +
        (∫ γ in Icc T (T + 1),
          polynomialThetaSourceMomentReading (sourceTwist γ f₁) (c * Real.log T) 1 n) := by
      have himg : (fun γ => polynomialThetaSourceMomentReading (baseTwistTest γ)
          (c * Real.log T) 1 n) '' Icc T (T + 1) =
          (fun γ => polynomialThetaSourceMomentReading (sourceTwist γ f₀)
            (c * Real.log T) 1 n) '' Icc T (T + 1) := by
        ext y; simp only [mem_image, f₀]
        constructor <;> rintro ⟨γ, hγ, rfl⟩ <;>
          exact ⟨γ, hγ, by rw [sourceTwist_baseBumpTest_eq]⟩
      dsimp only [supFn, f₁]
      rw [himg]
      exact sSup_polynomialThetaSourceMomentReading_unitWindow_le f₀ (c * Real.log T) 1 n T
    have hmono_g : ∀ g : CompactTest,
        (∫ γ in Icc T (T + 1),
          polynomialThetaSourceMomentReading (sourceTwist γ g) (c * Real.log T) 1 n) ≤
        ∫ γ in Icc T (T + 1), h_fn g γ := by
      intro g
      refine setIntegral_mono_on
        ((differentiable_polynomialThetaSourceMomentReading_sourceTwist g
          (c * Real.log T) 1 n).continuous.continuousOn.integrableOn_compact isCompact_Icc)
        ((hh_cont g).continuousOn.integrableOn_compact isCompact_Icc)
        measurableSet_Icc fun γ hγ => ?_
      have hmax_γ : max (1 : ℝ) γ = γ := max_eq_right (hT1.trans hγ.1)
      dsimp only [h_fn]
      rw [hmax_γ]
      exact polynomialThetaSourceMomentReading_mono_scale (sourceTwist γ g) hL_nn
        (mul_le_mul_of_nonneg_left (Real.log_le_log hT_pos hγ.1) hc0.le) 1 n
    linarith only [hsob, hmono_g f₀, hmono_g f₁]
  -- Continuity of `T ↦ ∫ γ in Icc T (T + 1), h_fn g γ`
  have hwin_int : ∀ g : CompactTest,
      IntegrableOn (fun T : ℝ => ∫ γ in Icc T (T + 1), h_fn g γ) (Icc U (2 * U)) volume := by
    intro g
    have hcont_win : ContinuousOn (fun T : ℝ => ∫ γ in Icc T (T + 1), h_fn g γ)
        (Icc U (2 * U)) := by
      let H : ℝ → ℝ := fun x => ∫ u in U..x, h_fn g u
      have hH_diff : ∀ x : ℝ, HasDerivAt H (h_fn g x) x := fun x =>
        intervalIntegral.integral_hasDerivAt_right
          ((hh_cont g).intervalIntegrable (μ := volume) _ _)
          ((hh_cont g).stronglyMeasurableAtFilter volume (𝓝 x))
          (hh_cont g).continuousAt
      have hH_cont : Continuous H :=
        Differentiable.continuous fun x => (hH_diff x).differentiableAt
      have hH_win_cont : Continuous (fun T : ℝ => H (T + 1) - H T) :=
        (hH_cont.comp (continuous_id.add (continuous_const (y := (1 : ℝ))))).sub hH_cont
      exact hH_win_cont.continuousOn.congr fun T _ => by
        dsimp only
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by linarith)]
        have hadj := integral_add_adjacent_intervals (a := U) (b := T) (c := T + 1)
          ((hh_cont g).intervalIntegrable (μ := volume) _ _)
          ((hh_cont g).intervalIntegrable (μ := volume) _ _)
        dsimp [H]; linarith only [hadj]
    exact hcont_win.integrableOn_compact isCompact_Icc
  have hint_rhs : IntegrableOn
      (fun T : ℝ => 2 * (∫ γ in Icc T (T + 1), h_fn f₀ γ) + (∫ γ in Icc T (T + 1), h_fn f₁ γ))
      (Icc U (2 * U)) volume :=
    ((hwin_int f₀).const_mul 2).add (hwin_int f₁)
  have hmono_U := setIntegral_mono_on hsup_int hint_rhs measurableSet_Icc hptw_T
  change (∫ T in Icc U (2 * U), supFn T) ≤
    ∫ T in Icc U (2 * U),
      (2 * (∫ γ in Icc T (T + 1), h_fn f₀ γ) + (∫ γ in Icc T (T + 1), h_fn f₁ γ)) at hmono_U
  rw [MeasureTheory.integral_add ((hwin_int f₀).const_mul 2) (hwin_int f₁),
    MeasureTheory.integral_const_mul] at hmono_U
  have hslid₀ := integral_Icc_unitWindow_integral_le (hh_cont f₀) (hh_nn f₀) hU_pos.le
  have hslid₁ := integral_Icc_unitWindow_integral_le (hh_cont f₁) (hh_nn f₁) hU_pos.le
  -- Bound `∫ u in Icc U (2 * U + 1), h_fn g u` by covering with `W₁ = 3 * U / 4` and `W₂ = U + 1`
  have hcov_dyad : ∀ (g : CompactTest) {Kg : ℝ}, 0 < Kg →
      (∀ n' : ℕ, linearThetaStage (2 * ((3 / 4 : ℝ) * U)) ≤ n' →
        (n' : ℝ) ≤ 10 * ((3 / 4 : ℝ) * U) + 15 →
        (1 / ((3 / 4 : ℝ) * U)) *
          (∫ γ in Icc ((3 / 4 : ℝ) * U) (2 * ((3 / 4 : ℝ) * U)),
            polynomialThetaSourceMomentReading (sourceTwist γ g) (c * Real.log γ) 1 n') ≤
          Kg * Real.log ((3 / 4 : ℝ) * U)) →
      (∀ n' : ℕ, linearThetaStage (2 * (U + 1)) ≤ n' →
        (n' : ℝ) ≤ 10 * (U + 1) + 15 →
        (1 / (U + 1)) *
          (∫ γ in Icc (U + 1) (2 * (U + 1)),
            polynomialThetaSourceMomentReading (sourceTwist γ g) (c * Real.log γ) 1 n') ≤
          Kg * Real.log (U + 1)) →
      (∫ u in Icc U (2 * U + 1), h_fn g u) ≤ 6 * Kg * U * Real.log U := by
    intro g Kg hKg hbd1 hbd2
    let W₁ : ℝ := (3 / 4 : ℝ) * U
    let W₂ : ℝ := U + 1
    have hW₁_pos : 0 < W₁ := by dsimp [W₁]; positivity
    have hW₂_pos : 0 < W₂ := by dsimp [W₂]; positivity
    have hn_hi_2U : (n : ℝ) ≤ 4 * U + 9 := by
      have hb := (linearThetaStage_bounds (by linarith only [hU16] : 1 ≤ 2 * U + 2)).2
      dsimp [n]; linarith only [hb]
    have hn1_lo : linearThetaStage (2 * W₁) ≤ n :=
      linearThetaStage_mono (by dsimp [W₁]; positivity) (by dsimp [W₁]; linarith only [hU16])
    have hn1_hi : (n : ℝ) ≤ 10 * W₁ + 15 := by dsimp [W₁]; linarith only [hn_hi_2U, hU16]
    have hn2_lo : linearThetaStage (2 * W₂) ≤ n := by
      have : 2 * W₂ = 2 * U + 2 := by dsimp [W₂]; ring
      rw [this]
    have hn2_hi : (n : ℝ) ≤ 10 * W₂ + 15 := by dsimp [W₂]; linarith only [hn_hi_2U, hU16]
    have hi1 := hbd1 n hn1_lo hn1_hi
    have hi2 := hbd2 n hn2_lo hn2_hi
    have hm1 := mul_le_mul_of_nonneg_left hi1 hW₁_pos.le
    have hlhs1 : W₁ * ((1 / W₁) * ∫ γ in Icc W₁ (2 * W₁),
        polynomialThetaSourceMomentReading (sourceTwist γ g) (c * Real.log γ) 1 n) =
        ∫ γ in Icc W₁ (2 * W₁),
          polynomialThetaSourceMomentReading (sourceTwist γ g) (c * Real.log γ) 1 n := by
      field_simp [hW₁_pos.ne']
    rw [hlhs1] at hm1
    have hm2 := mul_le_mul_of_nonneg_left hi2 hW₂_pos.le
    have hlhs2 : W₂ * ((1 / W₂) * ∫ γ in Icc W₂ (2 * W₂),
        polynomialThetaSourceMomentReading (sourceTwist γ g) (c * Real.log γ) 1 n) =
        ∫ γ in Icc W₂ (2 * W₂),
          polynomialThetaSourceMomentReading (sourceTwist γ g) (c * Real.log γ) 1 n := by
      field_simp [hW₂_pos.ne']
    rw [hlhs2] at hm2
    have hsplit_u : (∫ u in Icc U (2 * U + 1), h_fn g u) =
        (∫ u in Icc U ((3 / 2 : ℝ) * U), h_fn g u) +
          (∫ u in Icc ((3 / 2 : ℝ) * U) (2 * U + 1), h_fn g u) := by
      simp_rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      rw [← intervalIntegral.integral_of_le (by linarith only [hU16] : U ≤ 2 * U + 1),
        ← intervalIntegral.integral_of_le (by linarith only [hU16] : U ≤ (3 / 2 : ℝ) * U),
        ← intervalIntegral.integral_of_le (by linarith only [hU16] : (3 / 2 : ℝ) * U ≤ 2 * U + 1)]
      exact (integral_add_adjacent_intervals
        ((hh_cont g).intervalIntegrable (μ := volume) _ _)
        ((hh_cont g).intervalIntegrable (μ := volume) _ _)).symm
    have hsub1 : (∫ u in Icc U ((3 / 2 : ℝ) * U), h_fn g u) ≤ ∫ u in Icc W₁ (2 * W₁), h_fn g u :=
      setIntegral_mono_set ((hh_cont g).continuousOn.integrableOn_compact isCompact_Icc)
        (Eventually.of_forall (hh_nn g))
        (Icc_subset_Icc (by dsimp [W₁]; linarith only [hU16])
          (by dsimp [W₁]; linarith only [hU16])).eventuallyLE
    have hsub2 : (∫ u in Icc ((3 / 2 : ℝ) * U) (2 * U + 1), h_fn g u) ≤
        ∫ u in Icc W₂ (2 * W₂), h_fn g u :=
      setIntegral_mono_set ((hh_cont g).continuousOn.integrableOn_compact isCompact_Icc)
        (Eventually.of_forall (hh_nn g))
        (Icc_subset_Icc (by dsimp [W₂]; linarith only [hU16])
          (by dsimp [W₂]; linarith only [hU16])).eventuallyLE
    have heq1 : (∫ u in Icc W₁ (2 * W₁), h_fn g u) =
        ∫ γ in Icc W₁ (2 * W₁),
          polynomialThetaSourceMomentReading (sourceTwist γ g) (c * Real.log γ) 1 n :=
      setIntegral_congr_fun measurableSet_Icc fun γ hγ => by
        dsimp only [h_fn]
        rw [max_eq_right (by dsimp [W₁] at hγ; linarith only [hU16, hγ.1])]
    have heq2 : (∫ u in Icc W₂ (2 * W₂), h_fn g u) =
        ∫ γ in Icc W₂ (2 * W₂),
          polynomialThetaSourceMomentReading (sourceTwist γ g) (c * Real.log γ) 1 n :=
      setIntegral_congr_fun measurableSet_Icc fun γ hγ => by
        dsimp only [h_fn]
        rw [max_eq_right (by dsimp [W₂] at hγ; linarith only [hU16, hγ.1])]
    have hb_W1 : W₁ * (Kg * Real.log W₁) ≤ Kg * U * Real.log U := by
      have hl1 : Real.log W₁ ≤ Real.log U :=
        Real.log_le_log hW₁_pos (by dsimp [W₁]; linarith only [hU16])
      have hw1_le : W₁ ≤ U := by dsimp [W₁]; linarith only [hU16]
      have hl1_nn : 0 ≤ Real.log W₁ := Real.log_nonneg (by dsimp [W₁]; linarith only [hU16])
      calc W₁ * (Kg * Real.log W₁) = Kg * (W₁ * Real.log W₁) := by ring
        _ ≤ Kg * (U * Real.log U) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hw1_le hl1 hl1_nn hU_pos.le) hKg.le
        _ = Kg * U * Real.log U := by ring
    have hb_W2 : W₂ * (Kg * Real.log W₂) ≤ 5 * Kg * U * Real.log U := by
      have hl2 : Real.log W₂ ≤ 2 * Real.log U := by
        calc Real.log W₂ ≤ Real.log (2 * U) :=
              Real.log_le_log hW₂_pos (by dsimp [W₂]; linarith only [hU16])
          _ = Real.log 2 + Real.log U := Real.log_mul zero_lt_two.ne' hU_pos.ne'
          _ ≤ 2 * Real.log U := by linarith only [Real.log_two_lt_d9, hlogU_ge2]
      have hw2_le : W₂ ≤ 2 * U := by dsimp [W₂]; linarith only [hU16]
      have hl2_nn : 0 ≤ Real.log W₂ := Real.log_nonneg (by dsimp [W₂]; linarith only [hU16])
      have hextra : 0 ≤ Kg * U * Real.log U := by positivity
      calc W₂ * (Kg * Real.log W₂) = Kg * (W₂ * Real.log W₂) := by ring
        _ ≤ Kg * ((2 * U) * (2 * Real.log U)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hw2_le hl2 hl2_nn (by positivity)) hKg.le
        _ = 4 * (Kg * U * Real.log U) := by ring
        _ ≤ 5 * Kg * U * Real.log U := by linarith only [hextra]
    rw [hsplit_u]
    exact (add_le_add (hsub1.trans (heq1.trans_le (hm1.trans hb_W1)))
      (hsub2.trans (heq2.trans_le (hm2.trans hb_W2)))).trans_eq (by ring)
  have htot₀ := hcov_dyad f₀ hK₀ hw1_0.2 hw2_0.2
  have htot₁ := hcov_dyad f₁ hK₁ hw1_1.2 hw2_1.2
  have hraw : (∫ T in Icc U (2 * U), supFn T) ≤ (12 * K₀ + 6 * K₁) * U * Real.log U := by
    linarith only [hmono_U, hslid₀, hslid₁, htot₀, htot₁]
  have hm := mul_le_mul_of_nonneg_left hraw (by positivity : 0 ≤ 1 / U)
  have hrhs : (1 / U) * ((12 * K₀ + 6 * K₁) * U * Real.log U) =
      (12 * K₀ + 6 * K₁) * Real.log U := by
    field_simp [hU_pos.ne']
  rw [hrhs] at hm
  exact hm.trans (mul_le_mul_of_nonneg_right (by dsimp [K_sup]; linarith)
    (by linarith only [hlogU_ge2]))

/-- Local unit-window part of `heckeDefect (baseTwistTest γ) L` supported on `xiUnitWindowZeros T`. -/
def localWindowHeckeDefect (T γ L : ℝ) : ℝ :=
  ∑ ρ ∈ xiUnitWindowZeros T,
    ((analyticOrderAt xi ρ).toNat : ℝ) * Complex.normSq (tr (twist γ baseBump) ρ) *
      depthKernel L (ρ.re - 1 / 2)

/-- Off-window Lorentzian tail of `heckeDefect (baseTwistTest γ) L` outside `xiUnitWindowZeros T`. -/
def offWindowHeckeDefect (T γ L : ℝ) : ℝ :=
  heckeDefect (baseTwistTest γ) L - localWindowHeckeDefect T γ L

/-- **Single-Window Separation Theorem (`unitWindow_singleWindow_local_vs_offWindow_separation`).**
On any individual unit window `[T, T + 1]`:
1. `heckeDefect (baseTwistTest γ) L = localWindowHeckeDefect T γ L + offWindowHeckeDefect T γ L`
   with `0 ≤ offWindowHeckeDefect T γ L` and `localWindowHeckeDefect T γ L` pinched within
   `[cos(1/4)² * unitWindowDepthCharge T L, exp(1/4) * unitWindowDepthCharge T L]`;
2. `sInf` of `finiteThetaSourceMomentReading` detects `unitWindowDepthCharge T L` from below,
   its gap to the unit-window mean is bounded by `(1/2) * sSup |∂_γ R|`, while `sSup` is separated
   from `unitWindowDepthCharge T L` solely by `offWindowHeckeDefect T γ L` (plus `O(1)` aperture
   error). -/
theorem unitWindow_singleWindow_local_vs_offWindow_separation :
    ∃ E_unif : ℝ, 0 ≤ E_unif ∧
      ∀ (T L : ℝ) (n : ℕ), 1 ≤ n →
        (∀ γ ∈ Icc T (T + 1), |γ| ≤ (n : ℝ) / 2) →
        1 / 4 + |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
        (∀ γ ∈ Icc T (T + 1),
          heckeDefect (baseTwistTest γ) L =
            localWindowHeckeDefect T γ L + offWindowHeckeDefect T γ L ∧
          0 ≤ offWindowHeckeDefect T γ L ∧
          Real.cos (1 / 4 : ℝ) ^ 2 * unitWindowDepthCharge T L ≤ localWindowHeckeDefect T γ L ∧
          localWindowHeckeDefect T γ L ≤ Real.exp (1 / 4) * unitWindowDepthCharge T L) ∧
        Real.cos (1 / 4 : ℝ) ^ 2 * unitWindowDepthCharge T L - E_unif ≤
          sInf ((fun γ => finiteThetaSourceMomentReading (baseTwistTest γ) L 1 n) ''
            Icc T (T + 1)) ∧
        (∫ γ in Icc T (T + 1), finiteThetaSourceMomentReading (baseTwistTest γ) L 1 n) -
            sInf ((fun γ => finiteThetaSourceMomentReading (baseTwistTest γ) L 1 n) ''
              Icc T (T + 1)) ≤
          (1 / 2) * sSup ((fun γ =>
            |deriv (fun τ : ℝ => finiteThetaSourceMomentReading (baseTwistTest τ) L 1 n) γ|) ''
            Icc T (T + 1)) ∧
        sSup ((fun γ => finiteThetaSourceMomentReading (baseTwistTest γ) L 1 n) ''
            Icc T (T + 1)) ≤
          Real.exp (1 / 4) * unitWindowDepthCharge T L +
            sSup ((fun γ => offWindowHeckeDefect T γ L) '' Icc T (T + 1)) + E_unif := by
  obtain ⟨E_unif, hE_nn, hE_bd⟩ := exists_uniform_aperture_heckeDefect_error_bounds
  refine ⟨E_unif, hE_nn, fun T L n hn1 hγ_adm hL_adm => ?_⟩
  classical
  have hmem_c : ∀ z ∈ xiUnitWindowZeros T, z ∈ zetaZeroConfig.carrier := by
    intro z hz
    obtain ⟨hS, _⟩ := mem_xiUnitWindowZeros.mp hz
    obtain ⟨⟨h0, h1, _, _⟩, hxi⟩ := (Set.Finite.mem_toFinset _).mp hS
    exact CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mpr
      ⟨hxi, h0, h1⟩
  let emb : {z // z ∈ xiUnitWindowZeros T} → zetaZeroConfig.carrier :=
    fun z => ⟨z.1, hmem_c z.1 z.2⟩
  have hinj : Function.Injective emb := fun a b h =>
    Subtype.ext (congrArg (fun x : zetaZeroConfig.carrier => (x : ℂ)) h)
  let S_win : Finset zetaZeroConfig.carrier := (xiUnitWindowZeros T).attach.image emb
  have hloc_eq_sum : ∀ γ : ℝ, localWindowHeckeDefect T γ L =
      ∑ ρ ∈ S_win, zetaWeight (baseTwistTest γ) ρ * depthKernel L (zetaDepth ρ) := by
    intro γ
    unfold localWindowHeckeDefect
    rw [Finset.sum_image (fun a _ b _ h => hinj h), ← Finset.sum_attach (xiUnitWindowZeros T)]
    refine Finset.sum_congr rfl fun z _ => ?_
    obtain ⟨hS, _⟩ := mem_xiUnitWindowZeros.mp z.2
    obtain ⟨⟨h0, h1, _, _⟩, _⟩ := (Set.Finite.mem_toFinset _).mp hS
    have hmult : ((analyticOrderAt xi z.1).toNat : ℝ) = (zetaZeroConfig.mult z.1 : ℝ) := by
      change _ = ((analyticOrderAt riemannZeta z.1).toNat : ℝ)
      exact congrArg (fun k : ℕ => (k : ℝ))
        (congrArg ENat.toNat (xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨h0, h1⟩))
    have hzd : zetaDepth (emb z) = z.1.re - 1 / 2 := rfl
    have hzw : zetaWeight (baseTwistTest γ) (emb z) =
        ((analyticOrderAt xi z.1).toNat : ℝ) * Complex.normSq (tr (twist γ baseBump) z.1) := by
      change (zetaZeroConfig.mult z.1 : ℝ) * Complex.normSq (tr (twist γ baseBump) z.1) = _
      rw [hmult]
    rw [hzw, hzd]
  have hspec : ∀ γ ∈ Icc T (T + 1),
      heckeDefect (baseTwistTest γ) L =
        localWindowHeckeDefect T γ L + offWindowHeckeDefect T γ L ∧
      0 ≤ offWindowHeckeDefect T γ L ∧
      Real.cos (1 / 4 : ℝ) ^ 2 * unitWindowDepthCharge T L ≤ localWindowHeckeDefect T γ L ∧
      localWindowHeckeDefect T γ L ≤ Real.exp (1 / 4) * unitWindowDepthCharge T L := by
    intro γ hγ
    have hsplit := ((summable_heckeDefect (baseTwistTest γ) L).sum_add_tsum_compl (s := S_win)).symm
    change heckeDefect (baseTwistTest γ) L = _ at hsplit
    rw [← hloc_eq_sum γ] at hsplit
    have hoff_eq : offWindowHeckeDefect T γ L =
        ∑' ρ : ↥(S_win : Set zetaZeroConfig.carrier)ᶜ,
          zetaWeight (baseTwistTest γ) ρ.1 * depthKernel L (zetaDepth ρ.1) := by
      unfold offWindowHeckeDefect; linarith only [hsplit]
    have hoff_nn : 0 ≤ offWindowHeckeDefect T γ L := by
      rw [hoff_eq]
      exact tsum_nonneg fun ρ =>
        mul_nonneg (zetaWeight_nonneg _ _) (depthKernel_nonneg _ _)
    have hloc_lo : Real.cos (1 / 4 : ℝ) ^ 2 * unitWindowDepthCharge T L ≤
        localWindowHeckeDefect T γ L := by
      unfold unitWindowDepthCharge localWindowHeckeDefect
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun ρ hρ => ?_
      obtain ⟨hS, him_ge⟩ := mem_xiUnitWindowZeros.mp hρ
      obtain ⟨⟨_, _, _, him_lt⟩, _⟩ := (Set.Finite.mem_toFinset _).mp hS
      have him_abs : |ρ.im - γ| ≤ 1 := abs_le.mpr ⟨by linarith [hγ.2], by linarith [hγ.1]⟩
      have hcos_le : Real.cos (1 / 4 : ℝ) ^ 2 ≤ Complex.normSq (tr (twist γ baseBump) ρ) :=
        cos_quarter_mul_sq_le_normSq_tr_twist_baseBump (A := 1) zero_le_one
          (by linarith [Real.pi_gt_three]) him_abs
      calc Real.cos (1 / 4 : ℝ) ^ 2 *
              (((analyticOrderAt xi ρ).toNat : ℝ) * depthKernel L (ρ.re - 1 / 2))
          = ((analyticOrderAt xi ρ).toNat : ℝ) * Real.cos (1 / 4 : ℝ) ^ 2 *
              depthKernel L (ρ.re - 1 / 2) := by ring
        _ ≤ ((analyticOrderAt xi ρ).toNat : ℝ) * Complex.normSq (tr (twist γ baseBump) ρ) *
              depthKernel L (ρ.re - 1 / 2) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcos_le (Nat.cast_nonneg _)) (depthKernel_nonneg _ _)
    have hloc_hi : localWindowHeckeDefect T γ L ≤
        Real.exp (1 / 4) * unitWindowDepthCharge T L := by
      unfold unitWindowDepthCharge localWindowHeckeDefect
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun ρ hρ => ?_
      obtain ⟨hS, _⟩ := mem_xiUnitWindowZeros.mp hρ
      obtain ⟨⟨h0, h1, _, _⟩, _⟩ := (Set.Finite.mem_toFinset _).mp hS
      have hre_abs : |ρ.re - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      have hexp_le : Complex.normSq (tr (twist γ baseBump) ρ) ≤ Real.exp (1 / 4) := by
        rw [Complex.normSq_eq_norm_sq]
        refine (pow_le_pow_left₀ (norm_nonneg _)
          (norm_tr_twist_baseBump_le_exp γ hre_abs) 2).trans_eq ?_
        rw [← Real.exp_nat_mul]; norm_num
      calc ((analyticOrderAt xi ρ).toNat : ℝ) * Complex.normSq (tr (twist γ baseBump) ρ) *
              depthKernel L (ρ.re - 1 / 2)
          ≤ ((analyticOrderAt xi ρ).toNat : ℝ) * Real.exp (1 / 4) *
              depthKernel L (ρ.re - 1 / 2) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hexp_le (Nat.cast_nonneg _)) (depthKernel_nonneg _ _)
        _ = Real.exp (1 / 4) *
              (((analyticOrderAt xi ρ).toNat : ℝ) * depthKernel L (ρ.re - 1 / 2)) := by ring
    exact ⟨by unfold offWindowHeckeDefect; ring, hoff_nn, hloc_lo, hloc_hi⟩
  -- Continuity of `R` and `offWindowHeckeDefect` on `Icc T (T + 1)`
  let R : ℝ → ℝ := fun γ => finiteThetaSourceMomentReading (baseTwistTest γ) L 1 n
  have hR_eq : R = fun γ => finiteThetaSourceMomentReading (sourceTwist γ baseBumpTest) L 1 n :=
    funext fun γ => by dsimp [R]; rw [sourceTwist_baseBumpTest_eq]
  have hR_diff : Differentiable ℝ R := by
    rw [hR_eq]
    exact differentiable_finiteThetaSourceMomentReading_sourceTwist baseBumpTest L 1 n
  have hR'_cont : Continuous (deriv R) := by
    rw [hR_eq]
    exact (differentiable_deriv_finiteThetaSourceMomentReading_sourceTwist
      baseBumpTest L 1 n).continuous
  -- Minimum lower bound
  have hmin_lo : Real.cos (1 / 4 : ℝ) ^ 2 * unitWindowDepthCharge T L - E_unif ≤
      sInf (R '' Icc T (T + 1)) := by
    obtain ⟨⟨γ_min, hγ_min, hmin_eq, _⟩, _, _⟩ :=
      exists_unitWindow_sInf_eq_and_le_mean_le_sSup T hR_diff.continuous.continuousOn
    rw [hmin_eq]
    have herr := (hE_bd n hn1 L γ_min (hγ_adm γ_min hγ_min) hL_adm).1
    obtain ⟨hdec, hoff_nn, hloc_lo, _⟩ := hspec γ_min hγ_min
    dsimp [R]
    linarith only [(abs_le.mp herr).1, hdec, hoff_nn, hloc_lo]
  -- Mean minus min bound
  have hmean_sub : (∫ γ in Icc T (T + 1), R γ) - sInf (R '' Icc T (T + 1)) ≤
      (1 / 2) * sSup ((fun γ => |deriv R γ|) '' Icc T (T + 1)) := by
    let M₁ : ℝ := sSup ((fun γ => |deriv R γ|) '' Icc T (T + 1))
    have hbdd1 : BddAbove ((fun γ => |deriv R γ|) '' Icc T (T + 1)) :=
      (isCompact_Icc.image hR'_cont.abs).bddAbove
    have hM₁_nn : 0 ≤ M₁ :=
      (abs_nonneg (deriv R T)).trans (le_csSup hbdd1 ⟨T, ⟨le_rfl, by linarith⟩, rfl⟩)
    exact unitWindow_mean_sub_min_le_half_sup_deriv T hM₁_nn hR_diff hR'_cont
      fun γ hγ => le_csSup hbdd1 ⟨γ, hγ, rfl⟩
  -- Supremum upper bound
  have hsup_hi : sSup (R '' Icc T (T + 1)) ≤
      Real.exp (1 / 4) * unitWindowDepthCharge T L +
        sSup ((fun γ => offWindowHeckeDefect T γ L) '' Icc T (T + 1)) + E_unif := by
    have hoff_cont : Continuous (fun γ : ℝ => offWindowHeckeDefect T γ L) := by
      unfold offWindowHeckeDefect localWindowHeckeDefect
      have hhd_c : Continuous (fun γ : ℝ => heckeDefect (baseTwistTest γ) L) := by
        have heq : (fun γ : ℝ => heckeDefect (baseTwistTest γ) L) =
            fun γ : ℝ => heckeDefect (sourceTwist γ baseBumpTest) L :=
          funext fun γ => by rw [sourceTwist_baseBumpTest_eq]
        rw [heq]
        exact Continuous.comp
          (g := fun p : ℝ × ℝ => heckeDefect (sourceTwist p.1 baseBumpTest) p.2)
          (f := fun γ : ℝ => (γ, L))
          (continuous_heckeDefect_sourceTwist_pair baseBumpTest (by norm_num)
            abs_le_quarter_of_baseBumpTest_ne_zero)
          (continuous_id.prodMk (continuous_const (y := L)))
      have hloc_c : Continuous (fun γ : ℝ =>
          ∑ ρ ∈ xiUnitWindowZeros T,
            ((analyticOrderAt xi ρ).toNat : ℝ) * Complex.normSq (tr (twist γ baseBump) ρ) *
              depthKernel L (ρ.re - 1 / 2)) := by
        refine continuous_finsetSum _ fun ρ _ => ?_
        have htr_c : Continuous (fun γ : ℝ => Complex.normSq (tr (twist γ baseBump) ρ)) := by
          have heq : (fun γ : ℝ => Complex.normSq (tr (twist γ baseBump) ρ)) =
              fun γ : ℝ => Complex.normSq (tr (sourceTwist γ baseBumpTest).1 ρ) := rfl
          rw [heq]
          exact Complex.continuous_normSq.comp
            (Continuous.comp
              (g := fun p : ℝ × ℂ => tr (sourceTwist p.1 baseBumpTest).1 p.2)
              (f := fun γ : ℝ => (γ, ρ))
              (continuous_tr_sourceTwist_pair baseBumpTest)
              (continuous_id.prodMk (continuous_const (y := ρ))))
        exact ((continuous_const (y := ((analyticOrderAt xi ρ).toNat : ℝ))).mul htr_c).mul
          (continuous_const (y := depthKernel L (ρ.re - 1 / 2)))
      exact hhd_c.sub hloc_c
    have hoff_bdd : BddAbove ((fun γ => offWindowHeckeDefect T γ L) '' Icc T (T + 1)) :=
      (isCompact_Icc.image hoff_cont).bddAbove
    have hne : (R '' Icc T (T + 1)).Nonempty := ⟨R T, T, ⟨le_rfl, by linarith⟩, rfl⟩
    refine csSup_le hne ?_
    rintro _ ⟨γ, hγ, rfl⟩
    have herr := (hE_bd n hn1 L γ (hγ_adm γ hγ) hL_adm).1
    obtain ⟨hdec, _, _, hloc_hi⟩ := hspec γ hγ
    have hoff_le : offWindowHeckeDefect T γ L ≤
        sSup ((fun u => offWindowHeckeDefect T u L) '' Icc T (T + 1)) :=
      le_csSup hoff_bdd ⟨γ, hγ, rfl⟩
    dsimp [R]
    linarith only [(abs_le.mp herr).2, hdec, hloc_hi, hoff_le]
  exact ⟨hspec, hmin_lo, hmean_sub, hsup_hi⟩

/-- **Finite-Off-Line Separation Theorem (`finiteOffLine_not_rh_unitWindow_separation`).**
Under `FiniteOffLine ∧ ¬RiemannHypothesis`:
1. At **every fixed logarithmic scale** `c ∈ (0, 2]`, the entire unit-window `C²`-jet supremum of
   `polynomialThetaSourceMomentReading (baseTwistTest ·) (c log T) 1 (linearThetaStage (T + 1))`
   converges to `0` as `T → ∞` (in particular, unit-window `sInf`, `mean`, `sSup`, and `C²`-jet are
   all bounded `o(1)` without implying `RiemannHypothesis`);
2. Across **dyadic scales** `L_k(T) = 2^k c₀ log T` (`c₀ > 0`), all four unit-window quantities
   (`sInf`, `mean`, `sSup`, and `C²`-jet `sSup` of `finiteThetaSourceMomentReading` at
   `apertureStage L_k(T) T`) are unbounded. -/
theorem finiteOffLine_not_rh_unitWindow_separation
    (hF : FiniteOffLine) (hnotRH : ¬ RiemannHypothesis) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    (∀ c : ℝ, 0 < c → c ≤ 2 →
      Tendsto (fun T : ℝ =>
        sSup ((fun γ =>
          let P := fun τ : ℝ => polynomialThetaSourceMomentReading (baseTwistTest τ)
            (c * Real.log T) 1 (linearThetaStage (T + 1))
          P γ + |deriv P γ| + |deriv (deriv P) γ|) '' Icc T (T + 1)))
        atTop (𝓝 0)) ∧
    (∀ C : ℝ, ∃ k : ℕ, ∃ T : ℝ, 2 ≤ T ∧
      C < sInf ((fun γ => finiteThetaSourceMomentReading (baseTwistTest γ)
        ((2 : ℝ) ^ k * c₀ * Real.log T) 1
        (apertureStage ((2 : ℝ) ^ k * c₀ * Real.log T) T)) '' Icc T (T + 1))) ∧
    (∀ C : ℝ, ∃ k : ℕ, ∃ T : ℝ, 2 ≤ T ∧
      C < (∫ γ in Icc T (T + 1), finiteThetaSourceMomentReading (baseTwistTest γ)
        ((2 : ℝ) ^ k * c₀ * Real.log T) 1
        (apertureStage ((2 : ℝ) ^ k * c₀ * Real.log T) T))) ∧
    (∀ C : ℝ, ∃ k : ℕ, ∃ T : ℝ, 2 ≤ T ∧
      C < sSup ((fun γ => finiteThetaSourceMomentReading (baseTwistTest γ)
        ((2 : ℝ) ^ k * c₀ * Real.log T) 1
        (apertureStage ((2 : ℝ) ^ k * c₀ * Real.log T) T)) '' Icc T (T + 1))) ∧
    (∀ C : ℝ, ∃ k : ℕ, ∃ T : ℝ, 2 ≤ T ∧
      C < sSup ((fun γ =>
        let R := fun τ : ℝ => finiteThetaSourceMomentReading (baseTwistTest τ)
          ((2 : ℝ) ^ k * c₀ * Real.log T) 1
          (apertureStage ((2 : ℝ) ^ k * c₀ * Real.log T) T)
        R γ + |deriv R γ| + |deriv (deriv R) γ|) '' Icc T (T + 1))) := by
  have htfae := riemannHypothesis_unitWindow_min_mean_max_finiteTheta_tfae hc₀
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Part 1: Fixed-`c` `C²`-jet supremum tends to `0` as `T → ∞`
    intro c hc0 hc2
    let f₀ := baseBumpTest
    let f₁ := momentCompactTest 1 baseBumpTest
    let f₂ := momentCompactTest 2 baseBumpTest
    have hs₀ := abs_le_quarter_of_baseBumpTest_ne_zero
    have hs₁ := abs_le_of_momentCompactTest_ne_zero 1 baseBumpTest hs₀
    have hs₂ := abs_le_of_momentCompactTest_ne_zero 2 baseBumpTest hs₀
    obtain ⟨D₀, hD₀, hd₀⟩ := exists_heckeDefect_compactTest_le_div_sq_of_finiteOffLine hF f₀ hs₀ hc0 hc2
    obtain ⟨D₁, hD₁, hd₁⟩ := exists_heckeDefect_compactTest_le_div_sq_of_finiteOffLine hF f₁ hs₁ hc0 hc2
    obtain ⟨D₂, hD₂, hd₂⟩ := exists_heckeDefect_compactTest_le_div_sq_of_finiteOffLine hF f₂ hs₂ hc0 hc2
    obtain ⟨C₀, hC₀, hp₀⟩ := exists_compactTest_polynomialReading_sub_heckeDefect_le_log_div f₀ hs₀
    obtain ⟨C₁, hC₁, hp₁⟩ := exists_compactTest_polynomialReading_sub_heckeDefect_le_log_div f₁ hs₁
    obtain ⟨C₂, hC₂, hp₂⟩ := exists_compactTest_polynomialReading_sub_heckeDefect_le_log_div f₂ hs₂
    let K_jet : ℝ := 3 * (D₀ + C₀) + 3 * (D₁ + C₁) + (D₂ + C₂) + 1
    have hK_pos : 0 < K_jet := by dsimp [K_jet]; positivity
    rw [Metric.tendsto_atTop]
    intro ε hε
    let T_tar : ℝ := max 4 (8 * (2 * K_jet / ε) ^ 2 + 1)
    refine ⟨T_tar, fun T hT => ?_⟩
    have hT4 : 4 ≤ T := (le_max_left _ _).trans hT
    have hT_big : 8 * (2 * K_jet / ε) ^ 2 + 1 ≤ T := (le_max_right _ _).trans hT
    have hT_pos : 0 < T := by linarith only [hT4]
    let L := c * Real.log T
    let n := linearThetaStage (T + 1)
    let P := fun τ : ℝ => polynomialThetaSourceMomentReading (baseTwistTest τ) L 1 n
    let J := fun γ : ℝ => P γ + |deriv P γ| + |deriv (deriv P) γ|
    have hJ_bdd : BddAbove (J '' Icc T (T + 1)) :=
      (isCompact_Icc.image (continuous_baseTwist_polyTheta_c2Jet L n)).bddAbove
    have hJ_nn_T : 0 ≤ J T := by
      have hp_nn : 0 ≤ P T := polynomialThetaSourceMomentReading_nonneg _ _ _ _
      dsimp [J]; linarith only [hp_nn, abs_nonneg (deriv P T), abs_nonneg (deriv (deriv P) T)]
    have hsup_nn : 0 ≤ sSup (J '' Icc T (T + 1)) :=
      hJ_nn_T.trans (le_csSup hJ_bdd ⟨T, ⟨le_rfl, by linarith⟩, rfl⟩)
    have hsup_le : sSup (J '' Icc T (T + 1)) ≤ K_jet * (Real.log (2 * T) / T) := by
      have hne : (J '' Icc T (T + 1)).Nonempty := ⟨J T, T, ⟨le_rfl, by linarith⟩, rfl⟩
      refine csSup_le hne ?_
      rintro _ ⟨γ, hγ, rfl⟩
      have hγ_ge2 : 2 ≤ γ := by linarith only [hT4, hγ.1]
      have hγ_pos : 0 < γ := by linarith only [hγ_ge2]
      have hγ_le_2T : γ ≤ 2 * T := by linarith only [hT4, hγ.2]
      have hL0 : 0 ≤ L := mul_nonneg hc0.le (Real.log_nonneg (by linarith only [hT4]))
      have hL2 : L ≤ 2 * Real.log γ :=
        (mul_le_mul_of_nonneg_right hc2 (Real.log_nonneg (by linarith only [hT4]))).trans
          (mul_le_mul_of_nonneg_left (Real.log_le_log hT_pos hγ.1) zero_le_two)
      have hn_lo : linearThetaStage γ ≤ n :=
        linearThetaStage_mono (by linarith only [hγ_ge2]) hγ.2
      have hn_hi : (n : ℝ) ≤ 10 * γ + 15 := by
        have hb := (linearThetaStage_bounds (by linarith only [hT4] : 1 ≤ T + 1)).2
        dsimp [n]; linarith only [hb, hγ.1, hT4]
      have hlog2T_ge1 : 1 ≤ Real.log (2 * T) := by
        have h2 := Real.log_two_gt_d9
        have h8_eq : (2 : ℝ) ^ (3 : ℕ) = 8 := by norm_num
        have h8 : Real.log ((2 : ℝ) ^ (3 : ℕ)) ≤ Real.log (2 * T) :=
          Real.log_le_log (by norm_num) (by linarith only [h8_eq, hT4])
        rw [Real.log_pow] at h8; push_cast at h8; linarith only [h2, h8]
      have hinv_sq : 1 / T ^ 2 ≤ Real.log (2 * T) / T := by
        have h1 : 1 / T ^ 2 ≤ 1 / T :=
          div_le_div_of_nonneg_left zero_le_one hT_pos (by nlinarith only [hT4])
        exact h1.trans (div_le_div_of_nonneg_right hlog2T_ge1 hT_pos.le)
      have hlog_div_γ : Real.log γ / γ ≤ Real.log (2 * T) / T :=
        (div_le_div_of_nonneg_right (Real.log_le_log hγ_pos hγ_le_2T) hγ_pos.le).trans
          (div_le_div_of_nonneg_left (by linarith only [hlog2T_ge1]) hT_pos hγ.1)
      have hb_poly : ∀ (g : CompactTest) {Dg Cg : ℝ}, 0 < Dg → 0 < Cg →
          heckeDefect (sourceTwist γ g) L ≤ Dg / T ^ 2 →
          |polynomialThetaSourceMomentReading (sourceTwist γ g) L 1 n -
              heckeDefect (sourceTwist γ g) L| ≤ Cg * Real.log γ / γ →
          polynomialThetaSourceMomentReading (sourceTwist γ g) L 1 n ≤
            (Dg + Cg) * (Real.log (2 * T) / T) := by
        intro g Dg Cg hDg hCg hhd hdiff
        have h1 := (le_abs_self _).trans hdiff
        have h2 : Dg / T ^ 2 ≤ Dg * (Real.log (2 * T) / T) := by
          rw [div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_left hinv_sq hDg.le
        have h3 : Cg * Real.log γ / γ ≤ Cg * (Real.log (2 * T) / T) := by
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left hlog_div_γ hCg.le
        linarith only [h1, h2, h3, hhd]
      have hv₀ := hb_poly f₀ hD₀ hC₀ (hd₀ T (by linarith only [hT4]) γ hγ)
        (hp₀ γ L n hγ_ge2 hL0 hL2 hn_lo hn_hi)
      have hv₁ := hb_poly f₁ hD₁ hC₁ (hd₁ T (by linarith only [hT4]) γ hγ)
        (hp₁ γ L n hγ_ge2 hL0 hL2 hn_lo hn_hi)
      have hv₂ := hb_poly f₂ hD₂ hC₂ (hd₂ T (by linarith only [hT4]) γ hγ)
        (hp₂ γ L n hγ_ge2 hL0 hL2 hn_lo hn_hi)
      have hjet := baseTwist_polyTheta_c2Jet_le L n γ
      have hextra : 0 ≤ Real.log (2 * T) / T := div_nonneg (by linarith only [hlog2T_ge1]) hT_pos.le
      dsimp only [J, P, f₀, f₁, f₂, K_jet] at hjet hv₀ hv₁ hv₂ ⊢
      linarith only [hjet, hv₀, hv₁, hv₂, hextra]
    have hlog_small : K_jet * (Real.log (2 * T) / T) < ε := by
      let y : ℝ := Real.log (2 * T)
      have hy_nn : 0 ≤ y := Real.log_nonneg (by linarith only [hT4])
      have hy_exp : (y / 2) ^ 2 ≤ 2 * T := by
        have h1 : y / 2 ≤ Real.exp (y / 2) :=
          (by linarith : y / 2 ≤ y / 2 + 1).trans (Real.add_one_le_exp (y / 2))
        have h2 := pow_le_pow_left₀ (by positivity) h1 2
        have h3 : Real.exp (y / 2) ^ 2 = 2 * T := by
          rw [sq, ← Real.exp_add, add_halves]
          exact Real.exp_log (by positivity)
        exact h2.trans_eq h3
      have hy_sq : y ^ 2 ≤ 8 * T := by linarith only [hy_exp]
      have htar_lt : 8 * T < (ε * T / (2 * K_jet)) ^ 2 := by
        have h1 : 8 * (2 * K_jet / ε) ^ 2 < T := by linarith only [hT_big]
        have h2 := mul_lt_mul_of_pos_right h1 (by positivity : 0 < (ε / (2 * K_jet)) ^ 2 * T)
        have hlhs : 8 * (2 * K_jet / ε) ^ 2 * ((ε / (2 * K_jet)) ^ 2 * T) = 8 * T := by
          field_simp [hK_pos.ne', hε.ne']
        have hrhs : T * ((ε / (2 * K_jet)) ^ 2 * T) = (ε * T / (2 * K_jet)) ^ 2 := by
          field_simp [hK_pos.ne']
        rwa [hlhs, hrhs] at h2
      have hy_lt : y < ε * T / (2 * K_jet) := by
        by_contra hge
        have hsq := pow_le_pow_left₀ (by positivity) (not_lt.mp hge) 2
        linarith only [hy_sq, htar_lt, hsq]
      have hm := (lt_div_iff₀ (by positivity : 0 < 2 * K_jet)).mp hy_lt
      have hm2 := (div_lt_iff₀ hT_pos).mpr (by linarith only [hm, hε] : y * K_jet < (ε / 2) * T)
      have hlhs : K_jet * (y / T) = y * K_jet / T := by ring
      dsimp [y] at hlhs hm2
      linarith only [hlhs, hm2, hε]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hsup_nn]
    exact hsup_le.trans_lt hlog_small
  · -- Part 2a: Dyadic `sInf` unbounded
    intro C
    by_contra hall; push Not at hall
    have h10 := htfae.out 1 0 rfl rfl
    exact hnotRH (h10.mp ⟨C, hall⟩)
  · -- Part 2b: Dyadic mean unbounded
    intro C
    by_contra hall; push Not at hall
    have h20 := htfae.out 2 0 rfl rfl
    exact hnotRH (h20.mp ⟨C, hall⟩)
  · -- Part 2c: Dyadic `sSup` unbounded
    intro C
    by_contra hall; push Not at hall
    have h30 := htfae.out 3 0 rfl rfl
    exact hnotRH (h30.mp ⟨C, hall⟩)
  · -- Part 2d: Dyadic `C²`-jet `sSup` unbounded
    intro C
    by_contra hall; push Not at hall
    have h40 := htfae.out 4 0 rfl rfl
    exact hnotRH (h40.mp ⟨C, hall⟩)

end GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect

end

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.abs_deriv_finiteThetaSourceMomentReading_le
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.abs_deriv_deriv_finiteThetaSourceMomentReading_le
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.abs_deriv_polynomialThetaSourceMomentReading_le
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.abs_deriv_deriv_polynomialThetaSourceMomentReading_le
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.unitWindow_mean_sub_min_le_half_sup_deriv
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.unitWindow_mean_sub_interior_min_le_sixth_sup_deriv2
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.riemannHypothesis_unitWindow_min_mean_max_finiteTheta_tfae
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.polynomialTheta_unitWindow_min_mean_max_log_tfae
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_dyadicMean_unitWindow_sup_polynomialTheta_le_log_up_to_half
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.unitWindow_singleWindow_local_vs_offWindow_separation
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.finiteOffLine_not_rh_unitWindow_separation

import GaloisForLFunctions.RHTower.SuzukiLimitingLogFormCoercivity
import GaloisForLFunctions.RHTower.SuzukiRestrictedWeilSmoothBound

/-!
# Quantitative prime-free scaled coercivity

For `0 < a < (log 2)/2`, Suzuki's fixed-interval formula (4.5) has no prime-translation terms.
This module formalizes that exact empty-prime window and replaces the paper's pointwise `O(a)`
remainder in (5.1) by a uniform quadratic-form estimate.  Combined with the explicit limiting-form
gap `1/24`, it yields a coercivity coefficient tending to `+∞` as `a → 0+`.

This is the exact prime-free right-hand side of Suzuki's scaled formula.  Identification with the
closed finite-aperture operator still requires the change-of-variables/form-closure bridge.
-/

open MeasureTheory Set intervalIntegral Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Apertures lying in both the prime-free range and the unit curvature-control range. -/
structure SuzukiPrimeFreeSmallAperture where
  val : ℝ
  pos : 0 < val
  two_mul_le_one : 2 * val ≤ 1
  two_mul_lt_log_two : 2 * val < Real.log 2

instance : Coe SuzukiPrimeFreeSmallAperture ℝ := ⟨SuzukiPrimeFreeSmallAperture.val⟩

/-- The visible prime-power layer is literally empty below the first logarithmic threshold. -/
theorem suzukiRestrictedWeilIndices_eq_empty (a : SuzukiPrimeFreeSmallAperture) :
    suzukiRestrictedWeilIndices a.val = ∅ := by
  have hexp : Real.exp (2 * a.val) < (2 : ℝ) := by
    calc
      Real.exp (2 * a.val) < Real.exp (Real.log 2) :=
        Real.exp_lt_exp.mpr a.two_mul_lt_log_two
      _ = 2 := Real.exp_log (by norm_num)
  have hfloor : ⌊Real.exp (2 * a.val)⌋₊ < 2 :=
    (Nat.floor_lt (Real.exp_pos _).le).2 (by exact_mod_cast hexp)
  unfold suzukiRestrictedWeilIndices RHTower.suzukiVisibleWeilIndices
  exact Finset.Icc_eq_empty (Nat.not_le_of_lt hfloor)

/-- Canonical bound for the exact continuous source curvature on `[-1,1]`. -/
def suzukiOriginCurvatureUnitBound : ℝ :=
  Classical.choose exists_suzukiOriginRemainderCurvature_bound

theorem suzukiOriginCurvatureUnitBound_spec :
    0 ≤ suzukiOriginCurvatureUnitBound ∧
      ∀ t : ℝ, |t| ≤ 1 →
        |suzukiOriginRemainderCurvature t| ≤ suzukiOriginCurvatureUnitBound :=
  Classical.choose_spec exists_suzukiOriginRemainderCurvature_bound

/-- Exact real remainder quadratic form in Suzuki's fixed-interval formula (4.5). -/
def suzukiScaledRemainderQuadraticReal
    (a : SuzukiPrimeFreeSmallAperture) (u : SuzukiRestrictedWeilCore 1) : ℝ :=
  ∫ x in (-1 : ℝ)..1,
    (∫ y in (-1 : ℝ)..1,
      suzukiOriginRemainderCurvature (a.val * (x - y)) * u y) * u x

/-- Uniform Schur estimate for the scaled source remainder.  This strengthens the paper's
fixed-vector `O(a)` statement to an operator-form bound. -/
theorem suzukiScaledRemainderQuadraticReal_abs_le
    (a : SuzukiPrimeFreeSmallAperture) (u : SuzukiRestrictedWeilCore 1) :
    |suzukiScaledRemainderQuadraticReal a u| ≤
      2 * suzukiOriginCurvatureUnitBound *
        ∫ x in (-1 : ℝ)..1, u x ^ 2 := by
  have hk : Continuous (fun t : ℝ =>
      suzukiOriginRemainderCurvature (a.val * t)) :=
    continuous_suzukiOriginRemainderCurvature.comp (continuous_const.mul continuous_id)
  have hkernel : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |suzukiOriginRemainderCurvature (a.val * (x - y))| ≤
        suzukiOriginCurvatureUnitBound := by
    intro x hx y hy
    apply suzukiOriginCurvatureUnitBound_spec.2
    have hxy : |x - y| ≤ (2 : ℝ) := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    rw [abs_mul, abs_of_pos a.pos]
    nlinarith [a.two_mul_le_one, abs_nonneg (x - y)]
  have h := iteratedKernelQuadratic_abs_le (a := (1 : ℝ)) (C := suzukiOriginCurvatureUnitBound)
    (by norm_num) hk u.continuous suzukiOriginCurvatureUnitBound_spec.1 hkernel
  simpa [suzukiScaledRemainderQuadraticReal] using h

/-- Exact real prime-free numerator from Suzuki (4.5), before division by `L²` mass. -/
def suzukiPrimeFreeScaledRealForm
    (a : SuzukiPrimeFreeSmallAperture) (u : SuzukiRestrictedWeilCore 1) : ℝ :=
  (-Real.log a.val - (2 * suzukiWeilArchimedeanConstant + 1)) *
      (∫ x in (-1 : ℝ)..1, u x ^ 2) +
    suzukiFinitePartEnergy 1 u -
    a.val * suzukiScaledRemainderQuadraticReal a u

def suzukiSmallScaleCoercivityCoefficient (a : ℝ) : ℝ :=
  -Real.log a - (2 * suzukiWeilArchimedeanConstant + 1) + (1 / 24 : ℝ) -
    2 * a * suzukiOriginCurvatureUnitBound

/-- Uniform real coercivity for Suzuki's prime-free scaled numerator. -/
theorem suzukiPrimeFreeScaledRealForm_coercive
    (a : SuzukiPrimeFreeSmallAperture) (u : SuzukiRestrictedWeilCore 1) :
    suzukiSmallScaleCoercivityCoefficient a.val *
        (∫ x in (-1 : ℝ)..1, u x ^ 2) ≤
      suzukiPrimeFreeScaledRealForm a u := by
  let E : ℝ := ∫ x in (-1 : ℝ)..1, u x ^ 2
  have hE : 0 ≤ E := intervalIntegral.integral_nonneg (by norm_num)
    (fun x _ => sq_nonneg _)
  have hL := suzukiLimitingLogForm_real_coercive u
  have hR := suzukiScaledRemainderQuadraticReal_abs_le a u
  have hRupper : suzukiScaledRemainderQuadraticReal a u ≤
      2 * suzukiOriginCurvatureUnitBound * E :=
    (le_abs_self _).trans hR
  unfold suzukiPrimeFreeScaledRealForm suzukiSmallScaleCoercivityCoefficient
  change _ ≤ (-Real.log a.val - (2 * suzukiWeilArchimedeanConstant + 1)) * E +
    suzukiFinitePartEnergy 1 u - a.val * suzukiScaledRemainderQuadraticReal a u
  change (1 / 24 : ℝ) * E ≤ suzukiFinitePartEnergy 1 u at hL
  nlinarith [mul_le_mul_of_nonneg_left hRupper a.pos.le]

/-- Complex prime-free numerator on the literal test-function space. -/
def suzukiPrimeFreeScaledForm
    (a : SuzukiPrimeFreeSmallAperture) (u : SuzukiRestrictedWeilComplexTest 1) : ℝ :=
  suzukiPrimeFreeScaledRealForm a
      (suzukiRestrictedWeilRealTestToCore suzukiUnitAperture u.realPart) +
    suzukiPrimeFreeScaledRealForm a
      (suzukiRestrictedWeilRealTestToCore suzukiUnitAperture u.imagPart)

/-- Uniform complex coercivity, with the exact source normalization. -/
theorem suzukiPrimeFreeScaledForm_coercive
    (a : SuzukiPrimeFreeSmallAperture) (u : SuzukiRestrictedWeilComplexTest 1) :
    suzukiSmallScaleCoercivityCoefficient a.val *
        suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture u ≤
      suzukiPrimeFreeScaledForm a u := by
  let ur := suzukiRestrictedWeilRealTestToCore suzukiUnitAperture u.realPart
  let ui := suzukiRestrictedWeilRealTestToCore suzukiUnitAperture u.imagPart
  have hr := suzukiPrimeFreeScaledRealForm_coercive a ur
  have hi := suzukiPrimeFreeScaledRealForm_coercive a ui
  rw [suzukiRestrictedWeilComplexIntervalEnergy_eq]
  unfold suzukiPrimeFreeScaledForm
  change suzukiSmallScaleCoercivityCoefficient a.val *
      ((∫ x in (-1 : ℝ)..1, ur x ^ 2) + ∫ x in (-1 : ℝ)..1, ui x ^ 2) ≤
    suzukiPrimeFreeScaledRealForm a ur + suzukiPrimeFreeScaledRealForm a ui
  linarith

/-- The quantitative coefficient diverges to `+∞`; this is the uniform version of Suzuki (5.1). -/
theorem tendsto_suzukiSmallScaleCoercivityCoefficient :
    Tendsto suzukiSmallScaleCoercivityCoefficient (𝓝[>] 0) atTop := by
  have hlog : Tendsto (fun a : ℝ => -Real.log a) (𝓝[>] 0) atTop := by
    have h := Filter.tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
    simpa [Function.comp_def] using h
  have herror : Tendsto (fun a : ℝ =>
      -(2 * suzukiWeilArchimedeanConstant + 1) + (1 / 24 : ℝ) -
        2 * a * suzukiOriginCurvatureUnitBound) (𝓝[>] 0)
      (𝓝 (-(2 * suzukiWeilArchimedeanConstant + 1) + (1 / 24 : ℝ))) := by
    have hc : Continuous (fun a : ℝ =>
        -(2 * suzukiWeilArchimedeanConstant + 1) + (1 / 24 : ℝ) -
          2 * a * suzukiOriginCurvatureUnitBound) := by fun_prop
    have h0 : Tendsto (fun a : ℝ =>
        -(2 * suzukiWeilArchimedeanConstant + 1) + (1 / 24 : ℝ) -
          2 * a * suzukiOriginCurvatureUnitBound) (𝓝 (0 : ℝ))
        (𝓝 (-(2 * suzukiWeilArchimedeanConstant + 1) + (1 / 24 : ℝ) -
          2 * 0 * suzukiOriginCurvatureUnitBound)) := hc.continuousAt
    have h : Tendsto (fun a : ℝ =>
        -(2 * suzukiWeilArchimedeanConstant + 1) + (1 / 24 : ℝ) -
          2 * a * suzukiOriginCurvatureUnitBound) (𝓝[>] 0)
        (𝓝 (-(2 * suzukiWeilArchimedeanConstant + 1) + (1 / 24 : ℝ) -
          2 * 0 * suzukiOriginCurvatureUnitBound)) :=
      h0.mono_left inf_le_left
    simpa using h
  have hsum := hlog.atTop_add herror
  convert hsum using 1
  ext a
  unfold suzukiSmallScaleCoercivityCoefficient
  ring

theorem eventually_suzukiSmallScaleCoercivityCoefficient_pos :
    ∀ᶠ a in 𝓝[>] (0 : ℝ), 0 < suzukiSmallScaleCoercivityCoefficient a :=
  tendsto_suzukiSmallScaleCoercivityCoefficient.eventually (eventually_gt_atTop 0)

/-- The quantified small-aperture range is nonempty and contains a scale with strictly positive
uniform coercivity coefficient. -/
theorem exists_suzukiCoercivePrimeFreeSmallAperture :
    ∃ a : SuzukiPrimeFreeSmallAperture,
      0 < suzukiSmallScaleCoercivityCoefficient a.val := by
  have hpos : ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a := self_mem_nhdsWithin
  have hhalf : ∀ᶠ a : ℝ in 𝓝[>] 0, a < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono inf_le_left
  have hlog : ∀ᶠ a : ℝ in 𝓝[>] 0, a < Real.log 2 / 2 :=
    (eventually_lt_nhds (div_pos (Real.log_pos (by norm_num)) (by norm_num))).filter_mono
      inf_le_left
  have hall : ∀ᶠ a : ℝ in 𝓝[>] 0,
      0 < a ∧ a < 1 / 2 ∧ a < Real.log 2 / 2 ∧
        0 < suzukiSmallScaleCoercivityCoefficient a := by
    filter_upwards [hpos, hhalf, hlog,
      eventually_suzukiSmallScaleCoercivityCoefficient_pos] with a ha ha1 ha2 hc
    exact ⟨ha, ha1, ha2, hc⟩
  obtain ⟨a, ha, ha1, ha2, hc⟩ := hall.exists
  exact ⟨⟨a, ha, by nlinarith, by nlinarith⟩, hc⟩

end GaloisForLFunctions.RHTower

import GaloisForLFunctions.RHTower.Suzuki.SuzukiRestrictedWeilSemibounded
import Mathlib.Analysis.Distribution.TestFunction

/-!
# Suzuki's exact real and complex aperture test cores

Mathlib's test-function space gives the literal vector space `C_c^infinity(-a,a)` used by Suzuki.
Compact support inside the open aperture supplies a strict inner support radius, so every real test
maps canonically into the source core used by the four-block estimates. The complex quadratic form
is the sum of its real and imaginary source forms, exactly as for any real symmetric distribution,
and inherits the same unconditional semibound with complex `L²` energy.
-/

open MeasureTheory Set intervalIntegral
open scoped Distributions

noncomputable section

namespace GaloisForLFunctions.RHTower

def suzukiRestrictedWeilApertureOpen (a : ℝ) : TopologicalSpace.Opens ℝ :=
  ⟨Ioo (-a) a, isOpen_Ioo⟩

abbrev SuzukiRestrictedWeilRealTest (a : ℝ) := 𝓓(suzukiRestrictedWeilApertureOpen a, ℝ)
abbrev SuzukiRestrictedWeilComplexTest (a : ℝ) := 𝓓(suzukiRestrictedWeilApertureOpen a, ℂ)

private theorem exists_suzukiRestrictedWeilTest_supportRadius
    (a : RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilRealTest a.1) :
    ∃ r : ℝ, 0 ≤ r ∧ r < a.1 ∧ Function.support u ⊆ Icc (-r) r := by
  by_cases hempty : (tsupport u).Nonempty
  · obtain ⟨x₀, hx₀, hmax⟩ := u.hasCompactSupport.exists_isMaxOn hempty
      continuous_abs.continuousOn
    refine ⟨|x₀|, abs_nonneg _, ?_, ?_⟩
    · have hopen := u.tsupport_subset hx₀
      change x₀ ∈ Ioo (-a.1) a.1 at hopen
      exact (abs_lt).2 hopen
    · intro x hx
      have hxt : x ∈ tsupport u := subset_closure hx
      have habs : |x| ≤ |x₀| := hmax hxt
      exact (abs_le).1 habs
  · refine ⟨0, le_rfl, a.property, ?_⟩
    intro x hx
    exact False.elim (hempty ⟨x, subset_closure hx⟩)

def suzukiRestrictedWeilRealTestToCore
    (a : RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilRealTest a.1) :
    SuzukiRestrictedWeilCore a.1 where
  toFun := u
  smooth := u.contDiff
  supportRadius := Classical.choose (exists_suzukiRestrictedWeilTest_supportRadius a u)
  supportRadius_nonneg := (Classical.choose_spec (exists_suzukiRestrictedWeilTest_supportRadius a u)).1
  supportRadius_lt_aperture := (Classical.choose_spec (exists_suzukiRestrictedWeilTest_supportRadius a u)).2.1
  support_subset := (Classical.choose_spec (exists_suzukiRestrictedWeilTest_supportRadius a u)).2.2

@[simp] theorem suzukiRestrictedWeilRealTestToCore_apply
    (a : RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilRealTest a.1) (x : ℝ) :
    suzukiRestrictedWeilRealTestToCore a u x = u x := rfl

def SuzukiRestrictedWeilComplexTest.realPart {a : ℝ} (u : SuzukiRestrictedWeilComplexTest a) : SuzukiRestrictedWeilRealTest a where
  toFun x := (u x).re
  contDiff' := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => Complex.reCLM (u x))
    simpa only [Function.comp_def] using Complex.reCLM.contDiff.comp u.contDiff
  hasCompactSupport' := u.hasCompactSupport.mono (by
    intro x hx hzero
    exact hx (congrArg Complex.re hzero))
  tsupport_subset' := by
    apply (closure_mono ?_).trans u.tsupport_subset
    intro x hx hzero
    exact hx (congrArg Complex.re hzero)

def SuzukiRestrictedWeilComplexTest.imagPart {a : ℝ} (u : SuzukiRestrictedWeilComplexTest a) : SuzukiRestrictedWeilRealTest a where
  toFun x := (u x).im
  contDiff' := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => Complex.imCLM (u x))
    simpa only [Function.comp_def] using Complex.imCLM.contDiff.comp u.contDiff
  hasCompactSupport' := u.hasCompactSupport.mono (by
    intro x hx hzero
    exact hx (congrArg Complex.im hzero))
  tsupport_subset' := by
    apply (closure_mono ?_).trans u.tsupport_subset
    intro x hx hzero
    exact hx (congrArg Complex.im hzero)

def suzukiRestrictedWeilComplexQuadraticForm
    (a : RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilComplexTest a.1) : ℝ :=
  let ur := suzukiRestrictedWeilRealTestToCore a u.realPart
  let ui := suzukiRestrictedWeilRealTestToCore a u.imagPart
  suzukiRestrictedWeilForm a.1 ur ur + suzukiRestrictedWeilForm a.1 ui ui

def suzukiRestrictedWeilComplexIntervalEnergy
    (a : RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilComplexTest a.1) : ℝ :=
  ∫ x in (-a.1)..a.1, ‖u x‖ ^ (2 : ℕ)

theorem suzukiRestrictedWeilComplexIntervalEnergy_eq
    (a : RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilComplexTest a.1) :
    suzukiRestrictedWeilComplexIntervalEnergy a u =
      (∫ x in (-a.1)..a.1, (u x).re ^ (2 : ℕ)) +
        ∫ x in (-a.1)..a.1, (u x).im ^ (2 : ℕ) := by
  unfold suzukiRestrictedWeilComplexIntervalEnergy
  have hre : IntervalIntegrable (fun x : ℝ => (u x).re ^ (2 : ℕ)) volume (-a.1) a.1 :=
    ((Complex.continuous_re.comp u.continuous).pow 2).intervalIntegrable _ _
  have him : IntervalIntegrable (fun x : ℝ => (u x).im ^ (2 : ℕ)) volume (-a.1) a.1 :=
    ((Complex.continuous_im.comp u.continuous).pow 2).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add hre him]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

theorem suzukiRestrictedWeilComplexQuadraticForm_lowerBound
    (a : RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilComplexTest a.1) :
    -(suzukiRestrictedWeilLowerBoundConstant a.1 * suzukiRestrictedWeilComplexIntervalEnergy a u) ≤
      suzukiRestrictedWeilComplexQuadraticForm a u := by
  let ur := suzukiRestrictedWeilRealTestToCore a u.realPart
  let ui := suzukiRestrictedWeilRealTestToCore a u.imagPart
  have hr := suzukiRestrictedWeilForm_lowerBound a ur
  have hi := suzukiRestrictedWeilForm_lowerBound a ui
  rw [suzukiRestrictedWeilComplexIntervalEnergy_eq]
  unfold suzukiRestrictedWeilComplexQuadraticForm
  change -(suzukiRestrictedWeilLowerBoundConstant a.1 *
      ((∫ x in (-a.1)..a.1, ur x ^ (2 : ℕ)) + ∫ x in (-a.1)..a.1, ui x ^ (2 : ℕ))) ≤ _
  linarith

end GaloisForLFunctions.RHTower


import GaloisForLFunctions.RHTower.Suzuki.SuzukiDirichletScrewFactorization
import GaloisForLFunctions.RHTower.Suzuki.SuzukiRestrictedWeilSourceForm
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewSourceNormalization

/-!
# Suzuki equation (2.5) as an operator identity

The source equation (2.5) is a double real interval integral.  The 2026 factorization theorem,
however, needs the same statement for the literal Hilbert-space operator `G_a`.  This module
closes that interface: a real strict-interior smooth test is differentiated into the exact
zero-mean `L²` coordinate, and the pairing of Suzuki's compressed screw operator is proved equal
to the source-locked four-block Weil form.
-/

open Complex MeasureTheory Set
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

private theorem integral_subtype_Icc_eq_intervalIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {b c : ℝ} (hbc : b ≤ c) (F : ℝ → E) :
    (∫ x : Set.Icc b c, F (x : ℝ) ∂volume) = ∫ x in b..c, F x := by
  calc
    (∫ x : Set.Icc b c, F (x : ℝ) ∂volume) =
        ∫ x in Set.Icc b c, F x :=
      MeasureTheory.integral_subtype measurableSet_Icc F
    _ = ∫ x in Set.Ioc b c, F x := MeasureTheory.integral_Icc_eq_integral_Ioc
    _ = ∫ x in b..c, F x := by rw [intervalIntegral.integral_of_le hbc]

/-- Complexification of a real source core is still smooth. -/
theorem suzukiRestrictedWeilCore_contDiff_ofReal
    {a : ℝ} (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (u x : ℂ)) := by
  change ContDiff ℝ (⊤ : ℕ∞) (Complex.ofRealCLM ∘ u)
  exact Complex.ofRealCLM.contDiff.comp u.smooth

/-- Complexification does not enlarge the compact support of a real source core. -/
theorem suzukiRestrictedWeilCore_hasCompactSupport_ofReal
    {a : ℝ} (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a) :
    HasCompactSupport (fun x : ℝ => (u x : ℂ)) := by
  apply u.hasCompactSupport.mono
  intro x hx hu
  apply hx
  change ((u.toFun x : ℝ) : ℂ) = 0
  exact_mod_cast hu

/-- Complexification of a source core remains strictly inside its aperture. -/
theorem suzukiRestrictedWeilCore_tsupport_ofReal_subset_aperture
    (a : SuzukiPositiveAperture)
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a.1) :
    tsupport (fun x : ℝ => (u x : ℂ)) ⊆ Ioo (-a.1) a.1 := by
  have hsupp : Function.support (fun x : ℝ => (u x : ℂ)) ⊆
      Icc (-u.supportRadius) u.supportRadius := by
    intro x hx
    apply u.support_subset
    intro hu
    apply hx
    change ((u.toFun x : ℝ) : ℂ) = 0
    exact_mod_cast hu
  have hclosed : tsupport (fun x : ℝ => (u x : ℂ)) ⊆
      Icc (-u.supportRadius) u.supportRadius :=
    closure_minimal hsupp isClosed_Icc
  intro x hx
  have hxr := hclosed hx
  have hrlt : u.supportRadius < a.1 := u.supportRadius_lt_aperture
  change -a.1 < x ∧ x < a.1
  constructor <;> linarith [hxr.1, hxr.2, hrlt]

/-- Classical derivative commutes pointwise with complexification on the smooth real core. -/
theorem deriv_suzukiRestrictedWeilCore_ofReal
    {a : ℝ} (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a) (x : ℝ) :
    deriv (fun y : ℝ => (u y : ℂ)) x = ((deriv u.toFun x : ℝ) : ℂ) := by
  exact ((u.smooth.differentiable (by simp) x).hasDerivAt.ofReal_comp).deriv

/-- Exact zero-mean interval derivative of a real source core. -/
def suzukiRestrictedWeilCoreDerivativeZeroMean
    (a : SuzukiPositiveAperture)
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a.1) :
    SuzukiApertureZeroMean a :=
  suzukiSmoothDerivativeZeroMean a (fun x : ℝ => (u x : ℂ))
    (suzukiRestrictedWeilCore_contDiff_ofReal u)
    (suzukiRestrictedWeilCore_hasCompactSupport_ofReal u)
    (suzukiRestrictedWeilCore_tsupport_ofReal_subset_aperture a u)

theorem suzukiRestrictedWeilCoreDerivativeZeroMean_coeFn
    (a : SuzukiPositiveAperture)
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a.1) :
    ((suzukiRestrictedWeilCoreDerivativeZeroMean a u : SuzukiApertureZeroMean a) :
        SuzukiApertureInterval a.1 → ℂ) =ᵐ[volume]
      fun x => ((deriv u.toFun (x : ℝ) : ℝ) : ℂ) := by
  have h := suzukiSmoothDerivativeCoordinate_coeFn a
    (fun x : ℝ => (u x : ℂ))
    (suzukiRestrictedWeilCore_contDiff_ofReal u)
    (suzukiRestrictedWeilCore_hasCompactSupport_ofReal u)
  filter_upwards [h] with x hx
  change
    (suzukiSmoothDerivativeCoordinate a (fun x : ℝ => (u x : ℂ))
        (suzukiRestrictedWeilCore_contDiff_ofReal u)
        (suzukiRestrictedWeilCore_hasCompactSupport_ofReal u)) x = _
  rw [hx, deriv_suzukiRestrictedWeilCore_ofReal]

/-- Raw screw convolution on the exact zero-mean derivative coordinate is the literal source
double integral in equation (2.5). -/
theorem suzukiRawScrewIntervalForm_coreDerivative_eq_equationTwoFive
    (a : SuzukiPositiveAperture)
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a.1) :
    suzukiRawScrewIntervalForm a.1
        (suzukiRestrictedWeilCoreDerivativeZeroMean a u :
          SuzukiApertureIntervalL2 a.1)
        (suzukiRestrictedWeilCoreDerivativeZeroMean a u :
          SuzukiApertureIntervalL2 a.1) =
      ((∫ x in (-a.1)..a.1, ∫ y in (-a.1)..a.1,
        GaloisForLFunctions.RHTower.suzukiSourceScrew (x - y) *
          deriv u.toFun y * deriv u.toFun x : ℝ) : ℂ) := by
  let f : SuzukiApertureZeroMean a :=
    suzukiRestrictedWeilCoreDerivativeZeroMean a u
  have hf := suzukiRestrictedWeilCoreDerivativeZeroMean_coeFn a u
  unfold suzukiRawScrewIntervalForm
  change (∫ x : SuzukiApertureInterval a.1,
      ∫ y : SuzukiApertureInterval a.1,
        suzukiScrewG ((x : ℝ) - (y : ℝ)) *
          (f : SuzukiApertureIntervalL2 a.1) y *
          (starRingEnd ℂ) ((f : SuzukiApertureIntervalL2 a.1) x)) = _
  calc
    (∫ x : SuzukiApertureInterval a.1,
        ∫ y : SuzukiApertureInterval a.1,
          suzukiScrewG ((x : ℝ) - (y : ℝ)) *
            (f : SuzukiApertureIntervalL2 a.1) y *
            (starRingEnd ℂ) ((f : SuzukiApertureIntervalL2 a.1) x)) =
      ∫ x : SuzukiApertureInterval a.1,
        ∫ y : SuzukiApertureInterval a.1,
            (GaloisForLFunctions.RHTower.suzukiSourceScrew
              ((x : ℝ) - (y : ℝ)) : ℂ) *
            ((deriv u.toFun (y : ℝ) : ℝ) : ℂ) *
              ((deriv u.toFun (x : ℝ) : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [hf] with x hx
        apply integral_congr_ae
        filter_upwards [hf] with y hy
        rw [suzukiScrewG_eq_sourceScrew, hx, hy, Complex.conj_ofReal]
    _ = ∫ x in (-a.1)..a.1, ∫ y in (-a.1)..a.1,
          (GaloisForLFunctions.RHTower.suzukiSourceScrew (x - y) : ℂ) *
            ((deriv u.toFun y : ℝ) : ℂ) * ((deriv u.toFun x : ℝ) : ℂ) := by
        have hbounds : (-a.1 : ℝ) ≤ a.1 := by linarith [a.property]
        have hinner (x : SuzukiApertureInterval a.1) :
            (∫ y : SuzukiApertureInterval a.1,
              (GaloisForLFunctions.RHTower.suzukiSourceScrew
                  ((x : ℝ) - (y : ℝ)) : ℂ) *
                ((deriv u.toFun (y : ℝ) : ℝ) : ℂ) *
                  ((deriv u.toFun (x : ℝ) : ℝ) : ℂ)) =
              ∫ y in (-a.1)..a.1,
                (GaloisForLFunctions.RHTower.suzukiSourceScrew
                  ((x : ℝ) - y) : ℂ) *
                ((deriv u.toFun y : ℝ) : ℂ) *
                  ((deriv u.toFun (x : ℝ) : ℝ) : ℂ) := by
          change (∫ y : Set.Icc (-a.1) a.1,
              (GaloisForLFunctions.RHTower.suzukiSourceScrew
                  ((x : ℝ) - (y : ℝ)) : ℂ) *
                ((deriv u.toFun (y : ℝ) : ℝ) : ℂ) *
                  ((deriv u.toFun (x : ℝ) : ℝ) : ℂ)) = _
          exact integral_subtype_Icc_eq_intervalIntegral (E := ℂ) hbounds
            (fun y : ℝ =>
              (GaloisForLFunctions.RHTower.suzukiSourceScrew
                  ((x : ℝ) - y) : ℂ) *
                ((deriv u.toFun y : ℝ) : ℂ) *
                  ((deriv u.toFun (x : ℝ) : ℝ) : ℂ))
        simp_rw [hinner]
        change (∫ x : Set.Icc (-a.1) a.1,
            ∫ y in (-a.1)..a.1,
              (GaloisForLFunctions.RHTower.suzukiSourceScrew
                  ((x : ℝ) - y) : ℂ) *
                ((deriv u.toFun y : ℝ) : ℂ) *
                  ((deriv u.toFun (x : ℝ) : ℝ) : ℂ)) = _
        exact integral_subtype_Icc_eq_intervalIntegral (E := ℂ) hbounds
          (fun x : ℝ => ∫ y in (-a.1)..a.1,
            (GaloisForLFunctions.RHTower.suzukiSourceScrew (x - y) : ℂ) *
              ((deriv u.toFun y : ℝ) : ℂ) *
                ((deriv u.toFun x : ℝ) : ℂ))
    _ = ((∫ x in (-a.1)..a.1, ∫ y in (-a.1)..a.1,
          GaloisForLFunctions.RHTower.suzukiSourceScrew (x - y) *
            deriv u.toFun y * deriv u.toFun x : ℝ) : ℂ) := by
        calc
          (∫ x in (-a.1)..a.1, ∫ y in (-a.1)..a.1,
              (GaloisForLFunctions.RHTower.suzukiSourceScrew (x - y) : ℂ) *
                ((deriv u.toFun y : ℝ) : ℂ) *
                  ((deriv u.toFun x : ℝ) : ℂ)) =
            ∫ x in (-a.1)..a.1,
              ((∫ y in (-a.1)..a.1,
                GaloisForLFunctions.RHTower.suzukiSourceScrew (x - y) *
                  deriv u.toFun y * deriv u.toFun x : ℝ) : ℂ) := by
              apply intervalIntegral.integral_congr
              intro x _
              change (∫ y in (-a.1)..a.1,
                  (GaloisForLFunctions.RHTower.suzukiSourceScrew (x - y) : ℂ) *
                    ((deriv u.toFun y : ℝ) : ℂ) *
                      ((deriv u.toFun x : ℝ) : ℂ)) =
                ((∫ y in (-a.1)..a.1,
                  GaloisForLFunctions.RHTower.suzukiSourceScrew (x - y) *
                    deriv u.toFun y * deriv u.toFun x : ℝ) : ℂ)
              calc
                _ = ∫ y in (-a.1)..a.1,
                    ((GaloisForLFunctions.RHTower.suzukiSourceScrew (x - y) *
                      deriv u.toFun y * deriv u.toFun x : ℝ) : ℂ) := by
                      apply intervalIntegral.integral_congr
                      intro y _
                      norm_cast
                _ = _ := intervalIntegral.integral_ofReal
          _ = ((∫ x in (-a.1)..a.1, ∫ y in (-a.1)..a.1,
                GaloisForLFunctions.RHTower.suzukiSourceScrew (x - y) *
                  deriv u.toFun y * deriv u.toFun x : ℝ) : ℂ) :=
            intervalIntegral.integral_ofReal

/-- **Suzuki 2026, equation (2.5), operator form.**  The quadratic pairing of the literal
compressed screw operator on a real smooth Dirichlet derivative equals the exact arithmetic
four-block restricted Weil form. -/
theorem inner_suzukiScrewZeroMeanOperator_coreDerivative_eq_restrictedWeilForm
    (a : SuzukiPositiveAperture)
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a.1) :
    inner ℂ (suzukiRestrictedWeilCoreDerivativeZeroMean a u)
        (suzukiScrewZeroMeanOperator a
          (suzukiRestrictedWeilCoreDerivativeZeroMean a u)) =
      (GaloisForLFunctions.RHTower.suzukiRestrictedWeilForm a.1 u u : ℂ) := by
  rw [inner_suzukiScrewZeroMeanOperator_eq_raw,
    suzukiRawScrewIntervalForm_coreDerivative_eq_equationTwoFive,
    GaloisForLFunctions.RHTower.suzuki_equation_two_five]

end RHTower

end

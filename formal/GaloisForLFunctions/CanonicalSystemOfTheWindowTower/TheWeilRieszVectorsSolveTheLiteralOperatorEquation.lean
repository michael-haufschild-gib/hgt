import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLocalWeilKernelIsHermiteBiehler

/-!
# The literal operator equation for Weil evaluation vectors

The completed Riesz identity holds against the whole form domain. The
Friedrichs representation theorem therefore places its physical source in the
restricted operator domain. Its image is the compact exponential representing
Fourier evaluation, with an explicit essential bound.
-/

open MeasureTheory Set Filter Complex
open scoped InnerProductSpace
noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact
open _root_.RHTower GaloisForLFunctions.HTGeometry
attribute [local instance] Measure.Subtype.measureSpace

/-- The literal compact exponential forcing for Fourier evaluation. -/
def evaluationForcing (a : SuzukiPositiveAperture) (z : ℂ) : suzukiApertureHilbert a :=
  suzukiApertureL2Equiv a (suzukiTaSpectralExponentialL2 a (star z))

theorem eval_eq_inner_evaluationForcing (a : PrecontactAperture) (z : ℂ)
    (x : WeilHilbertBeforeContact a) :
    eval a z x = inner ℂ (evaluationForcing a.1 z)
      (ccmArchimedeanFormToAperture a.1 (toForm a x)) := by
  change inner ℂ (suzukiTaSpectralExponentialL2 a.1 (star z))
      ((suzukiApertureL2Equiv a.1).symm
        (ccmArchimedeanFormToAperture a.1 (toForm a x))) = _
  have h := (suzukiApertureL2Equiv a.1).inner_map_map
    (suzukiTaSpectralExponentialL2 a.1 (star z))
    ((suzukiApertureL2Equiv a.1).symm
      (ccmArchimedeanFormToAperture a.1 (toForm a x)))
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

/-- The completed Riesz vector represents the literal restricted Weil operator equation. -/
theorem evalVector_represents_operator (a : PrecontactAperture) (z : ℂ)
    (u : CCMArchimedeanFormDomain a.1) :
    ccmRestrictedWeilForm a.1 (toForm a (evalVector a z)) u =
      inner ℂ (evaluationForcing a.1 z) (ccmArchimedeanFormToAperture a.1 u) := by
  have h := inner_evalVector a z ((toForm a).symm u)
  rw [inner_eq_weil, LinearEquiv.apply_symm_apply, eval_eq_inner_evaluationForcing,
    LinearEquiv.apply_symm_apply] at h
  exact h

/-- Fourier Riesz vectors lie in the physical operator domain, with explicit exponential image. -/
theorem evalVector_operator_domain_and_apply (a : PrecontactAperture) (z : ℂ) :
    ∃ hmem : ccmArchimedeanFormToAperture a.1 (toForm a (evalVector a z)) ∈
        (ccmRestrictedWeilOperator a.1).domain,
      ccmRestrictedWeilOperator a.1
        ⟨ccmArchimedeanFormToAperture a.1 (toForm a (evalVector a z)), hmem⟩ =
          evaluationForcing a.1 z := by
  exact boundedPerturbedFriedrichsOperator_mem_domain_of_represents
    (ccmArchimedeanFormToAperture a.1) (ccmRestrictedWeilBoundedRemainder a.1)
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a.1)
    (ccmArchimedeanFormToAperture_injective a.1) (denseRange_ccmArchimedeanFormToAperture a.1)
    (toForm a (evalVector a z)) (evaluationForcing a.1 z)
    (evalVector_represents_operator a z)

theorem evaluationForcing_coeFn (a : SuzukiPositiveAperture) (z : ℂ) :
    (((evaluationForcing a z : suzukiApertureHilbert a) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      (Icc (-a.1) a.1).indicator (fun x : ℝ => Complex.exp (-I * star z * (x : ℂ))) := by
  change (suzukiApertureZeroExtendL2 (suzukiTaSpectralExponentialL2 a (star z)) : ℝ → ℂ) =ᵐ[volume] _
  refine (suzukiApertureZeroExtendL2_coeFn _).trans ?_
  apply ae_of_ae_restrict_of_ae_restrict_compl (Icc (-a.1) a.1)
  · rw [ae_restrict_iff_subtype measurableSet_Icc]
    filter_upwards [suzukiApertureRepresentative_ae (suzukiTaSpectralExponentialL2 a (star z)),
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
        (suzukiTaSpectralExponentialContinuous a (star z))] with x hr hc
    rw [suzukiApertureZeroExtend_apply, hr]
    change (suzukiTaSpectralExponentialL2 a (star z) : SuzukiApertureInterval a.1 → ℂ) x = _ at hc
    rw [hc, indicator_of_mem x.property]
    rfl
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc.compl] with x hx
    have hx' : x ∉ Icc (-a.1) a.1 := hx
    rw [suzukiApertureZeroExtend_eq_zero_of_notMem _ hx', indicator_of_notMem hx']

/-- The exact operator forcing is bounded on the physical aperture. -/
theorem evaluationForcing_bounded (a : SuzukiPositiveAperture) (z : ℂ) :
    ∀ᵐ x ∂volume, ‖(evaluationForcing a z : SoninL2) x‖ ≤ Real.exp (a.1 * |z.im|) := by
  filter_upwards [evaluationForcing_coeFn a z] with x hx
  rw [hx]
  by_cases ha : x ∈ Icc (-a.1) a.1
  · rw [indicator_of_mem ha, Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hr : (-I * star z * (x : ℂ)).re = -(z.im * x) := by
      change (-I * (starRingEnd ℂ) z * (x : ℂ)).re = -(z.im * x)
      simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, neg_zero, zero_mul,
        Complex.neg_im, Complex.I_im, neg_one_mul, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      ring
    rw [hr]
    calc
      _ ≤ |z.im * x| := neg_le_abs _
      _ = |z.im| * |x| := abs_mul _ _
      _ ≤ |z.im| * a.1 := mul_le_mul_of_nonneg_left (abs_le.mpr ha) (abs_nonneg _)
      _ = _ := mul_comm _ _
  · rw [indicator_of_notMem ha, norm_zero]
    exact (Real.exp_pos _).le

#print axioms evalVector_operator_domain_and_apply
#print axioms evaluationForcing_coeFn
#print axioms evaluationForcing_bounded

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact

import GaloisForLFunctions.RHTower.SuzukiLimitingLogMixedReality
import GaloisForLFunctions.RHTower.SuzukiSmallApertureGroundAsymptotic
import GaloisForLFunctions.RHTower.CCMArchimedeanBoundaryLayerFormCore
import GaloisForLFunctions.RHTower.SuzukiHlogLaurentFormCore

/-!
# Exact identification of Suzuki's limiting ground energy

This module identifies the variational constant μ₁ from Suzuki (2026), Theorem 1.4—defined
as the infimum over literal complex C_c^∞(-1,1) tests—with the bottom eigenvalue of the complete
closed compact-resolvent limiting logarithmic operator. It proves mixed-form reality on the real
core, exact complexification, density of the literal test core in the closed form domain, both
variational inequalities, and the final equality without attainment or density hypotheses.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

theorem suzukiLimitingLogClosedForm_realCore_mixed_im_eq_zero
    (u v : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    (suzukiLimitingLogClosedForm
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u)
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture v)).im = 0 := by
  let qu := suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u
  let qv := suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture v
  have hWeil := ccmRestrictedWeilForm_realCore_mixed_im_eq_zero
    suzukiLimitingUnitAperture u v
  have hprime :=
    inner_suzukiLimitingIntervalPrimeOperator_realCore_mixed_im_eq_zero u v
  have hmass := inner_suzukiLimitingCoreIntervalVector_mixed_im_eq_zero u v
  have horigin :=
    inner_suzukiLimitingOriginKernelOperator_realCore_mixed_im_eq_zero u v
  rw [inner_suzukiLimitingLogClosedForm_eq_weil_add_corrections]
  rw [suzukiWeilIntervalForm_eq_ccmRestrictedWeilForm]
  rw [← suzukiLimitingCoreIntervalVector_eq_limitingFormEmbedding u,
    ← suzukiLimitingCoreIntervalVector_eq_limitingFormEmbedding v]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, hWeil, hprime, hmass, horigin]
  ring

theorem star_suzukiLimitingLogClosedForm_swap
    (u v : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    star (suzukiLimitingLogClosedForm u v) =
      suzukiLimitingLogClosedForm v u := by
  have hB := suzukiLimitingLogBoundedRemainder_isSelfAdjoint.isSymmetric
    (suzukiLimitingLogFormEmbedding v)
    (suzukiLimitingLogFormEmbedding u)
  unfold suzukiLimitingLogClosedForm
  change (starRingEnd ℂ) (inner ℂ u v +
      inner ℂ (suzukiLimitingLogBoundedRemainder
        (suzukiLimitingLogFormEmbedding u))
        (suzukiLimitingLogFormEmbedding v)) = _
  rw [map_add, inner_conj_symm v u,
    inner_conj_symm (suzukiLimitingLogFormEmbedding v)
      (suzukiLimitingLogBoundedRemainder
        (suzukiLimitingLogFormEmbedding u))]
  exact congrArg (fun z => inner ℂ v u + z) hB.symm

theorem suzukiLimitingLogClosedForm_realCore_mixed_symm
    (u v : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    suzukiLimitingLogClosedForm
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u)
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture v) =
    suzukiLimitingLogClosedForm
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture v)
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u) := by
  rw [← star_suzukiLimitingLogClosedForm_swap]
  exact Complex.conj_eq_iff_im.mpr
    (suzukiLimitingLogClosedForm_realCore_mixed_im_eq_zero v u)

theorem suzukiLimitingLogClosedForm_add_left
    (u v w : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    suzukiLimitingLogClosedForm (u + v) w =
      suzukiLimitingLogClosedForm u w + suzukiLimitingLogClosedForm v w := by
  simp only [suzukiLimitingLogClosedForm, map_add, inner_add_left]
  ring

theorem suzukiLimitingLogClosedForm_add_right
    (u v w : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    suzukiLimitingLogClosedForm u (v + w) =
      suzukiLimitingLogClosedForm u v + suzukiLimitingLogClosedForm u w := by
  simp only [suzukiLimitingLogClosedForm, map_add, inner_add_right]
  ring

theorem suzukiLimitingLogClosedForm_smul_left
    (c : ℂ) (u v : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    suzukiLimitingLogClosedForm (c • u) v =
      star c * suzukiLimitingLogClosedForm u v := by
  have hinner : inner ℂ (c • u) v = star c * inner ℂ u v := by
    exact inner_smul_left u v c
  unfold suzukiLimitingLogClosedForm
  rw [map_smul, map_smul, inner_smul_left, hinner]
  rw [starRingEnd_apply]
  ring

theorem suzukiLimitingLogClosedForm_smul_right
    (c : ℂ) (u v : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    suzukiLimitingLogClosedForm u (c • v) =
      c * suzukiLimitingLogClosedForm u v := by
  have hinner : inner ℂ u (c • v) = c * inner ℂ u v := by
    exact inner_smul_right u v c
  unfold suzukiLimitingLogClosedForm
  rw [map_smul, inner_smul_right, hinner]
  ring

theorem suzukiLimitingLogClosedForm_real_add_I_imag
    (u v : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    let qu := suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u
    let qv := suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture v
    suzukiLimitingLogClosedForm (qu + I • qv) (qu + I • qv) =
      suzukiLimitingLogClosedForm qu qu + suzukiLimitingLogClosedForm qv qv := by
  dsimp only
  let qu := suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u
  let qv := suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture v
  have hsymm : suzukiLimitingLogClosedForm qu qv =
      suzukiLimitingLogClosedForm qv qu :=
    suzukiLimitingLogClosedForm_realCore_mixed_symm u v
  simp only [suzukiLimitingLogClosedForm_add_left,
    suzukiLimitingLogClosedForm_add_right,
    suzukiLimitingLogClosedForm_smul_left,
    suzukiLimitingLogClosedForm_smul_right]
  change suzukiLimitingLogClosedForm qu qu +
      star I * suzukiLimitingLogClosedForm qv qu +
      I * (suzukiLimitingLogClosedForm qu qv +
        star I * suzukiLimitingLogClosedForm qv qv) =
    suzukiLimitingLogClosedForm qu qu + suzukiLimitingLogClosedForm qv qv
  have hI : star I = -I := Complex.conj_I
  rw [hI]
  rw [hsymm]
  ring_nf
  rw [Complex.I_sq]
  ring

def suzukiComplexTestInteriorSource
    (u : SuzukiRestrictedWeilComplexTest 1) :
    CCMComplexSmoothInteriorSource suzukiLimitingUnitAperture where
  toFun := u
  smooth := u.contDiff'
  hasCompactSupport := u.hasCompactSupport'
  tsupport_subset := u.tsupport_subset'

theorem suzukiComplexTestInteriorSource_toRestrictedWeilComplexTest
    (u : SuzukiRestrictedWeilComplexTest 1) :
    (suzukiComplexTestInteriorSource u).toRestrictedWeilComplexTest = u := by
  rfl

def suzukiLimitingComplexCoreFormVector
    (u : SuzukiRestrictedWeilComplexTest 1) :
    CCMArchimedeanFormDomain suzukiLimitingUnitAperture :=
  (suzukiComplexTestInteriorSource u).toCCMFormVector

theorem suzukiLimitingComplexCoreFormVector_eq_real_add_I_imag
    (u : SuzukiRestrictedWeilComplexTest 1) :
    suzukiLimitingComplexCoreFormVector u =
      suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture
        (suzukiRestrictedWeilRealTestToCore
          GaloisForLFunctions.RHTower.suzukiUnitAperture u.realPart) +
      I • suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture
        (suzukiRestrictedWeilRealTestToCore
          GaloisForLFunctions.RHTower.suzukiUnitAperture u.imagPart) := by
  exact (suzukiComplexTestInteriorSource u).toCCMFormVector_eq_real_add_I_imag

theorem suzukiLimitingLogClosedForm_complexCore_re_eq
    (u : SuzukiRestrictedWeilComplexTest 1) :
    (suzukiLimitingLogClosedForm
      (suzukiLimitingComplexCoreFormVector u)
      (suzukiLimitingComplexCoreFormVector u)).re =
        GaloisForLFunctions.RHTower.suzukiLimitingLogForm u := by
  let ur := suzukiRestrictedWeilRealTestToCore
    GaloisForLFunctions.RHTower.suzukiUnitAperture u.realPart
  let ui := suzukiRestrictedWeilRealTestToCore
    GaloisForLFunctions.RHTower.suzukiUnitAperture u.imagPart
  rw [suzukiLimitingComplexCoreFormVector_eq_real_add_I_imag]
  rw [suzukiLimitingLogClosedForm_real_add_I_imag]
  rw [suzukiLimitingLogClosedForm_core_eq_weilFinitePartBlock,
    suzukiLimitingLogClosedForm_core_eq_weilFinitePartBlock]
  have hr := suzukiWeilFinitePartBlock_eq_energy suzukiLimitingUnitAperture ur
  have hi := suzukiWeilFinitePartBlock_eq_energy suzukiLimitingUnitAperture ui
  dsimp only [suzukiLimitingUnitAperture] at hr hi
  rw [Complex.add_re, Complex.ofReal_re, Complex.ofReal_re, hr, hi]
  rfl

theorem norm_sq_suzukiLimitingLogFormEmbedding_complexCore
    (u : SuzukiRestrictedWeilComplexTest 1) :
    ‖suzukiLimitingLogFormEmbedding
      (suzukiLimitingComplexCoreFormVector u)‖ ^ 2 =
        suzukiRestrictedWeilComplexIntervalEnergy
          GaloisForLFunctions.RHTower.suzukiUnitAperture u := by
  change suzukiWeilIntervalFormMass suzukiLimitingUnitAperture
      (suzukiComplexTestInteriorSource u).toCCMFormVector = _
  rw [suzukiWeilIntervalFormMass_complexSmooth_eq]
  rfl

/-- Strict-interior smooth complex source vectors inside the complete limiting form domain. -/
def suzukiLimitingComplexSmoothCore :
    Set (CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :=
  Set.range suzukiLimitingComplexCoreFormVector

theorem dense_suzukiLimitingComplexSmoothCore :
    Dense suzukiLimitingComplexSmoothCore := by
  apply
    (denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector
      suzukiLimitingUnitAperture).mono
  rintro _ ⟨u, rfl⟩
  exact ⟨u.toRestrictedWeilComplexTest, rfl⟩

theorem suzukiLimitingLogGroundEnergy_mul_complexCore_norm_sq_le
    (u : SuzukiRestrictedWeilComplexTest 1) :
    suzukiLimitingLogGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding
          (suzukiLimitingComplexCoreFormVector u)‖ ^ 2 ≤
      (suzukiLimitingLogClosedForm
        (suzukiLimitingComplexCoreFormVector u)
        (suzukiLimitingComplexCoreFormVector u)).re := by
  by_cases hq : suzukiLimitingComplexCoreFormVector u = 0
  · rw [hq, map_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    simp [suzukiLimitingLogClosedForm]
  · have hJne : suzukiLimitingLogFormEmbedding
        (suzukiLimitingComplexCoreFormVector u) ≠ 0 := by
      intro h
      apply hq
      apply suzukiLimitingLogFormEmbedding_injective
      simpa using h
    have henergy : 0 < suzukiRestrictedWeilComplexIntervalEnergy
        GaloisForLFunctions.RHTower.suzukiUnitAperture u := by
      rw [← norm_sq_suzukiLimitingLogFormEmbedding_complexCore]
      exact pow_pos (norm_pos_iff.mpr hJne) 2
    have hfloor := isGLB_suzukiLimitingLogRayleighSet.1
      ⟨u, henergy, rfl⟩
    rw [le_div_iff₀ henergy] at hfloor
    rw [norm_sq_suzukiLimitingLogFormEmbedding_complexCore,
      suzukiLimitingLogClosedForm_complexCore_re_eq]
    exact hfloor

/-- Suzuki's test-function ground value is a lower bound on the entire closed form domain. -/
theorem suzukiLimitingLogGroundEnergy_mul_formNorm_sq_le
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    suzukiLimitingLogGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2 ≤
      (suzukiLimitingLogClosedForm q q).re := by
  exact dense_suzukiLimitingComplexSmoothCore.induction
    (fun _ hcore => by
      rcases hcore with ⟨u, rfl⟩
      exact suzukiLimitingLogGroundEnergy_mul_complexCore_norm_sq_le u)
    (isClosed_le (by fun_prop) (by
      unfold suzukiLimitingLogClosedForm
      have hdiag : Continuous (fun x :
          CCMArchimedeanFormDomain suzukiLimitingUnitAperture =>
          inner ℂ x x) :=
        (continuous_id : Continuous (fun x :
          CCMArchimedeanFormDomain suzukiLimitingUnitAperture => x)).inner
            (𝕜 := ℂ) continuous_id
      have hJ := suzukiLimitingLogFormEmbedding.continuous
      have hBJ := suzukiLimitingLogBoundedRemainder.continuous.comp hJ
      exact Complex.continuous_re.comp
        (hdiag.add (hBJ.inner (𝕜 := ℂ) hJ)))) q

theorem suzukiLimitingLogOperatorGroundEnergy_le_logGroundEnergy :
    suzukiLimitingLogOperatorGroundEnergy ≤
      suzukiLimitingLogGroundEnergy := by
  apply isGLB_suzukiLimitingLogRayleighSet.2
  rintro r ⟨u, henergy, rfl⟩
  rw [le_div_iff₀ henergy]
  rw [← norm_sq_suzukiLimitingLogFormEmbedding_complexCore,
    ← suzukiLimitingLogClosedForm_complexCore_re_eq]
  exact suzukiLimitingLogOperatorGroundEnergy_mul_formNorm_sq_le
    (suzukiLimitingComplexCoreFormVector u)

/-- Every vector in the represented operator domain has its canonical complete form-domain lift. -/
theorem suzukiLimitingLogOperator_exists_formLift
    (x : suzukiLimitingLogOperator.domain) :
    ∃ q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture,
      suzukiLimitingLogFormEmbedding q = (x : SuzukiApertureIntervalL2 1) ∧
      suzukiLimitingLogClosedForm q q =
        inner ℂ (suzukiLimitingLogOperator x)
          (x : SuzukiApertureIntervalL2 1) := by
  let J := suzukiLimitingLogFormEmbedding
  let B := suzukiLimitingLogBoundedRemainder
  let C := boundedPerturbedFormCovariance J B
    suzukiLimitingLogBoundedRemainder_isSelfAdjoint
  have hCinj : Function.Injective C :=
    boundedPerturbedFormCovariance_injective J B
      suzukiLimitingLogBoundedRemainder_isSelfAdjoint
      suzukiLimitingLogFormEmbedding_injective
      denseRange_suzukiLimitingLogFormEmbedding
  have hxrange : (x : SuzukiApertureIntervalL2 1) ∈ C.range := by
    simpa only [J, B, C, suzukiLimitingLogOperator,
      boundedPerturbedFriedrichsOperator_domain,
      closedDenseInverse_domain] using x.property
  obtain ⟨y, hy⟩ := hxrange
  have hmem : C y ∈ suzukiLimitingLogOperator.domain := by
    change C y ∈ (closedDenseInverse C).domain
    exact (closedDenseInverse_apply_C C hCinj y).1
  let xc : suzukiLimitingLogOperator.domain := ⟨C y, hmem⟩
  let q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture :=
    boundedPerturbedFormRieszInv J B
      suzukiLimitingLogBoundedRemainder_isSelfAdjoint (J.adjoint y)
  have hrep := boundedPerturbedFriedrichsOperator_represents_form
    J B suzukiLimitingLogBoundedRemainder_isSelfAdjoint
      suzukiLimitingLogFormEmbedding_injective
      denseRange_suzukiLimitingLogFormEmbedding y q
  change (xc : SuzukiApertureIntervalL2 1) = J q ∧
    inner ℂ (suzukiLimitingLogOperator xc) (J q) =
      inner ℂ q q + inner ℂ (B (J q)) (J q) at hrep
  have hxc : xc = x := Subtype.ext hy
  refine ⟨q, ?_, ?_⟩
  · rw [← hrep.1, hxc]
  · change inner ℂ q q + inner ℂ (B (J q)) (J q) = _
    rw [← hrep.2, hxc]
    congr 1

theorem suzukiLimitingLogGroundEnergy_le_operatorGroundEnergy :
    suzukiLimitingLogGroundEnergy ≤
      suzukiLimitingLogOperatorGroundEnergy := by
  obtain ⟨x, hxne, hx⟩ := suzukiLimitingLogOperator_exists_groundEigenstate
  obtain ⟨q, hq, hform⟩ := suzukiLimitingLogOperator_exists_formLift x
  have hfloor := suzukiLimitingLogGroundEnergy_mul_formNorm_sq_le q
  have hnorm : 0 < ‖(x : SuzukiApertureIntervalL2 1)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hxne) 2
  have hinner :
      (inner ℂ (suzukiLimitingLogOperator x)
        (x : SuzukiApertureIntervalL2 1)).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖(x : SuzukiApertureIntervalL2 1)‖ ^ 2 := by
    rw [hx, inner_smul_left]
    rw [show (starRingEnd ℂ)
      (suzukiLimitingLogOperatorGroundEnergy : ℂ) =
        (suzukiLimitingLogOperatorGroundEnergy : ℂ) by
          exact Complex.conj_ofReal _]
    rw [inner_self_eq_norm_sq_to_K]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    simp [pow_two, Complex.mul_re]
  rw [hq, hform, hinner] at hfloor
  nlinarith

/-- Exact identification of Suzuki's `mu₁`: test-function infimum equals bottom eigenvalue of the
closed compact-resolvent limiting operator. -/
theorem suzukiLimitingLogOperatorGroundEnergy_eq_logGroundEnergy :
    suzukiLimitingLogOperatorGroundEnergy =
      suzukiLimitingLogGroundEnergy :=
  le_antisymm suzukiLimitingLogOperatorGroundEnergy_le_logGroundEnergy
    suzukiLimitingLogGroundEnergy_le_operatorGroundEnergy

end RHTower


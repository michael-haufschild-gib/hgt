import GaloisForLFunctions.RHTower.CCMRestrictedWeilFriedrichsOperator
import GaloisForLFunctions.RHTower.SuzukiApertureL2Equivalence

/-!
# Suzuki's restricted Weil operator on the literal interval

Connes--Consani's exact restricted Weil form was constructed on the physical zero-extended
aperture subspace of `L²(ℝ)`.  Suzuki's 2026 operator `A_a`, however, is stated on the literal
Hilbert space `L²(-a,a)`.  The zero-extension unitary transports both the form embedding and its
bounded self-adjoint remainder to that interval.  Applying the same Friedrichs construction then
gives the literal interval operator, with its exact source quadratic form, self-adjointness, and
compact resolvent.

No abstract form premise is introduced: the form domain is the already constructed exact
Riemann--Siegel weighted domain, and the bounded term is the explicit polar-plus-finite-prime
remainder transported through the interval/zero-extension unitary.
-/

open MeasureTheory Set
open scoped ENNReal InnerProduct BigOperators

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-! ## Exact interval form data -/

def suzukiApertureToPhysicalCLM (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 →L[ℂ] suzukiApertureHilbert a :=
  (suzukiApertureL2Equiv a).toContinuousLinearEquiv.toContinuousLinearMap

def suzukiPhysicalToApertureCLM (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →L[ℂ] SuzukiApertureIntervalL2 a.1 :=
  (suzukiApertureL2Equiv a).symm.toContinuousLinearEquiv.toContinuousLinearMap

noncomputable instance instNontrivialSuzukiApertureIntervalL2
    (a : SuzukiPositiveAperture) : Nontrivial (SuzukiApertureIntervalL2 a.1) :=
  Equiv.nontrivial (suzukiApertureL2Equiv a).toEquiv

/-- Exact CCM form embedding, now landing in the literal interval `L²(-a,a)`. -/
def suzukiWeilIntervalFormEmbedding (a : SuzukiPositiveAperture) :
    CCMArchimedeanFormDomain a →L[ℂ] SuzukiApertureIntervalL2 a.1 :=
  suzukiPhysicalToApertureCLM a ∘L ccmArchimedeanFormToAperture a

/-- Explicit polar-plus-finite-prime remainder transported to the literal interval. -/
def suzukiWeilIntervalBoundedRemainder (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 →L[ℂ] SuzukiApertureIntervalL2 a.1 :=
  suzukiPhysicalToApertureCLM a ∘L
    ccmRestrictedWeilBoundedRemainder a ∘L suzukiApertureToPhysicalCLM a

theorem suzukiWeilIntervalFormEmbedding_injective (a : SuzukiPositiveAperture) :
    Function.Injective (suzukiWeilIntervalFormEmbedding a) := by
  intro u v huv
  apply ccmArchimedeanFormToAperture_injective a
  exact (suzukiApertureL2Equiv a).symm.injective huv

theorem denseRange_suzukiWeilIntervalFormEmbedding (a : SuzukiPositiveAperture) :
    DenseRange (suzukiWeilIntervalFormEmbedding a) := by
  have hunitary : DenseRange (suzukiPhysicalToApertureCLM a) :=
    (suzukiApertureL2Equiv a).symm.surjective.denseRange
  have h := hunitary.comp (denseRange_ccmArchimedeanFormToAperture a)
    (suzukiPhysicalToApertureCLM a).continuous
  simpa only [suzukiWeilIntervalFormEmbedding, ContinuousLinearMap.coe_comp] using h

theorem isCompactOperator_suzukiWeilIntervalFormEmbedding
    (a : SuzukiPositiveAperture) :
    IsCompactOperator (suzukiWeilIntervalFormEmbedding a) := by
  exact (isCompactOperator_ccmArchimedeanFormToAperture a).clm_comp
    (suzukiPhysicalToApertureCLM a)

theorem suzukiWeilIntervalBoundedRemainder_isSelfAdjoint
    (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (suzukiWeilIntervalBoundedRemainder a) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  have hphysical :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)
  intro f g
  let e := suzukiApertureL2Equiv a
  change inner ℂ (e.symm (ccmRestrictedWeilBoundedRemainder a (e f))) g =
    inner ℂ f (e.symm (ccmRestrictedWeilBoundedRemainder a (e g)))
  calc
    inner ℂ (e.symm (ccmRestrictedWeilBoundedRemainder a (e f))) g =
        inner ℂ (e.symm (ccmRestrictedWeilBoundedRemainder a (e f)))
          (e.symm (e g)) := by rw [e.symm_apply_apply]
    _ = inner ℂ (ccmRestrictedWeilBoundedRemainder a (e f)) (e g) :=
      e.symm.inner_map_map _ _
    _ = inner ℂ (e f) (ccmRestrictedWeilBoundedRemainder a (e g)) :=
      hphysical (e f) (e g)
    _ = inner ℂ (e.symm (e f))
        (e.symm (ccmRestrictedWeilBoundedRemainder a (e g))) :=
      (e.symm.inner_map_map _ _).symm
    _ = inner ℂ f
        (e.symm (ccmRestrictedWeilBoundedRemainder a (e g))) := by
      rw [e.symm_apply_apply]

/-- Exact restricted Weil sesquilinear form on literal interval coordinates. -/
def suzukiWeilIntervalForm (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) : ℂ :=
  inner ℂ u v +
    inner ℂ
      (suzukiWeilIntervalBoundedRemainder a
        (suzukiWeilIntervalFormEmbedding a u))
      (suzukiWeilIntervalFormEmbedding a v)

/-- Unitary transport changes coordinates but not the exact restricted Weil form. -/
theorem suzukiWeilIntervalForm_eq_ccmRestrictedWeilForm
    (a : SuzukiPositiveAperture) (u v : CCMArchimedeanFormDomain a) :
    suzukiWeilIntervalForm a u v = ccmRestrictedWeilForm a u v := by
  let e := suzukiApertureL2Equiv a
  change inner ℂ u v +
      inner ℂ
        (e.symm (ccmRestrictedWeilBoundedRemainder a
          (e (e.symm (ccmArchimedeanFormToAperture a u)))))
        (e.symm (ccmArchimedeanFormToAperture a v)) = _
  rw [e.apply_symm_apply]
  rw [e.symm.inner_map_map]
  rfl

/-- The interval form has the literal archimedean--polar--prime source diagonal. -/
theorem suzukiWeilIntervalForm_self_re_eq_source
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    (suzukiWeilIntervalForm a u u).re =
      ccmRestrictedWeilSourceQuadratic a u := by
  rw [suzukiWeilIntervalForm_eq_ccmRestrictedWeilForm,
    ccmRestrictedWeilForm_self_re_eq_source]

/-! ## Suzuki's literal interval operator `A_a` -/

/-- Suzuki's `A_a` on `L²(-a,a)`, obtained from the exact restricted Weil form. -/
def suzukiWeilFriedrichsOperator (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 →ₗ.[ℂ] SuzukiApertureIntervalL2 a.1 :=
  boundedPerturbedFriedrichsOperator
    (suzukiWeilIntervalFormEmbedding a)
    (suzukiWeilIntervalBoundedRemainder a)
    (suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a)

/-- Shifted covariance for Suzuki's exact interval form. -/
def suzukiWeilIntervalCovariance (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 →L[ℂ] SuzukiApertureIntervalL2 a.1 :=
  boundedPerturbedFormCovariance
    (suzukiWeilIntervalFormEmbedding a)
    (suzukiWeilIntervalBoundedRemainder a)
    (suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a)

theorem suzukiWeilIntervalCovariance_injective (a : SuzukiPositiveAperture) :
    Function.Injective (suzukiWeilIntervalCovariance a) := by
  exact boundedPerturbedFormCovariance_injective
    (suzukiWeilIntervalFormEmbedding a)
    (suzukiWeilIntervalBoundedRemainder a)
    (suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a)
    (suzukiWeilIntervalFormEmbedding_injective a)
    (denseRange_suzukiWeilIntervalFormEmbedding a)

theorem suzukiWeilIntervalCovariance_isPositive (a : SuzukiPositiveAperture) :
    ContinuousLinearMap.IsPositive (suzukiWeilIntervalCovariance a) := by
  exact boundedPerturbedFormCovariance_isPositive
    (suzukiWeilIntervalFormEmbedding a)
    (suzukiWeilIntervalBoundedRemainder a)
    (suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a)

theorem suzukiWeilIntervalCovariance_isCompact (a : SuzukiPositiveAperture) :
    IsCompactOperator (suzukiWeilIntervalCovariance a) := by
  exact boundedPerturbedFormCovariance_isCompact
    (suzukiWeilIntervalFormEmbedding a)
    (suzukiWeilIntervalBoundedRemainder a)
    (suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a)
    (isCompactOperator_suzukiWeilIntervalFormEmbedding a)

theorem norm_suzukiWeilIntervalCovariance_pos (a : SuzukiPositiveAperture) :
    0 < ‖suzukiWeilIntervalCovariance a‖ := by
  have hne : suzukiWeilIntervalCovariance a ≠ 0 := by
    intro hzero
    obtain ⟨z, hz⟩ := exists_ne
      (0 : SuzukiApertureIntervalL2 a.1)
    apply hz
    apply suzukiWeilIntervalCovariance_injective a
    simp [hzero]
  exact (norm_pos_iff (E := SuzukiApertureIntervalL2 a.1 →L[ℂ]
    SuzukiApertureIntervalL2 a.1)).mpr hne

/-- Bottom spectral value of Suzuki's literal interval operator. -/
def suzukiWeilIntervalGroundEnergy (a : SuzukiPositiveAperture) : ℝ :=
  ‖suzukiWeilIntervalCovariance a‖⁻¹ -
    boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a)

/-- Suzuki's bottom spectral value is attained by a genuine nonzero interval eigenstate. -/
theorem suzukiWeilFriedrichsOperator_exists_groundEigenstate
    (a : SuzukiPositiveAperture) :
    ∃ x : (suzukiWeilFriedrichsOperator a).domain,
      (x : SuzukiApertureIntervalL2 a.1) ≠ 0 ∧
        suzukiWeilFriedrichsOperator a x =
          (suzukiWeilIntervalGroundEnergy a : ℂ) •
            (x : SuzukiApertureIntervalL2 a.1) := by
  let C := suzukiWeilIntervalCovariance a
  let mu : ℝ := ‖C‖
  have hCinj : Function.Injective C :=
    suzukiWeilIntervalCovariance_injective a
  have hmu : 0 < mu := norm_suzukiWeilIntervalCovariance_pos a
  obtain ⟨e, hene, he⟩ :=
    boundedPerturbedFormCovariance_exists_norm_eigenvector
      (suzukiWeilIntervalFormEmbedding a)
      (suzukiWeilIntervalBoundedRemainder a)
      (suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a)
      (suzukiWeilIntervalFormEmbedding_injective a)
      (denseRange_suzukiWeilIntervalFormEmbedding a)
      (isCompactOperator_suzukiWeilIntervalFormEmbedding a)
  change C e = (mu : ℂ) • e at he
  have hmuC : (mu : ℂ) ≠ 0 := by exact_mod_cast hmu.ne'
  let z : SuzukiApertureIntervalL2 a.1 := (mu : ℂ)⁻¹ • e
  have hCz : C z = e := by
    change C ((mu : ℂ)⁻¹ • e) = e
    rw [map_smul, he, smul_smul, inv_mul_cancel₀ hmuC, one_smul]
  have hedom : e ∈ (closedDenseInverse C).domain := by
    rw [closedDenseInverse_domain]
    exact ⟨z, hCz⟩
  let x : (suzukiWeilFriedrichsOperator a).domain :=
    ⟨e, by
      change e ∈ (closedDenseInverse C).domain
      exact hedom⟩
  refine ⟨x, hene, ?_⟩
  have hinvZ := (closedDenseInverse_apply_C C hCinj z).2
  have hinv : closedDenseInverse C ⟨e, hedom⟩ = z := by
    let Cz : (closedDenseInverse C).domain :=
      ⟨C z, (closedDenseInverse_apply_C C hCinj z).1⟩
    have heq : (⟨e, hedom⟩ : (closedDenseInverse C).domain) = Cz :=
      Subtype.ext hCz.symm
    rw [heq]
    exact hinvZ
  change boundedPerturbedFriedrichsOperator
      (suzukiWeilIntervalFormEmbedding a)
      (suzukiWeilIntervalBoundedRemainder a)
      (suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a) x = _
  rw [boundedPerturbedFriedrichsOperator_apply]
  change closedDenseInverse C ⟨e, hedom⟩ -
      (boundedPerturbedFormShift
        (suzukiWeilIntervalBoundedRemainder a) : ℂ) • e = _
  rw [hinv]
  change (mu : ℂ)⁻¹ • e -
      (boundedPerturbedFormShift
        (suzukiWeilIntervalBoundedRemainder a) : ℂ) • e = _
  unfold suzukiWeilIntervalGroundEnergy
  change (mu : ℂ)⁻¹ • e -
      (boundedPerturbedFormShift
        (suzukiWeilIntervalBoundedRemainder a) : ℂ) • e =
    ((mu⁻¹ - boundedPerturbedFormShift
      (suzukiWeilIntervalBoundedRemainder a) : ℝ) : ℂ) • e
  push_cast
  module

/-- Exact ground energy is the quadratic-form floor on the full interval form domain. -/
theorem suzukiWeilIntervalGroundEnergy_mul_formNorm_sq_le_source
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    suzukiWeilIntervalGroundEnergy a *
          ‖suzukiWeilIntervalFormEmbedding a u‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a u := by
  have hfloor := boundedPerturbedForm_ground_mul_norm_sq_le
    (suzukiWeilIntervalFormEmbedding a)
    (suzukiWeilIntervalBoundedRemainder a)
    (suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a)
    (suzukiWeilIntervalFormEmbedding_injective a)
    (denseRange_suzukiWeilIntervalFormEmbedding a)
    u
  change suzukiWeilIntervalGroundEnergy a *
      ‖suzukiWeilIntervalFormEmbedding a u‖ ^ 2 ≤
    (suzukiWeilIntervalForm a u u).re at hfloor
  rwa [suzukiWeilIntervalForm_self_re_eq_source] at hfloor


/-- Suzuki's restricted Weil operator on the literal interval is self-adjoint. -/
theorem suzukiWeilFriedrichsOperator_isSelfAdjoint
    (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (suzukiWeilFriedrichsOperator a) := by
  exact boundedPerturbedFriedrichsOperator_isSelfAdjoint
    (suzukiWeilIntervalFormEmbedding a)
    (suzukiWeilIntervalBoundedRemainder a)
    (suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a)
    (suzukiWeilIntervalFormEmbedding_injective a)
    (denseRange_suzukiWeilIntervalFormEmbedding a)

/-- Explicit compact resolvent point for Suzuki's interval operator. -/
theorem suzukiWeilFriedrichsOperator_hasCompactResolventAt_negShift
    (a : SuzukiPositiveAperture) :
    LinearPMap.HasCompactResolventAt
      (suzukiWeilFriedrichsOperator a)
      (-(boundedPerturbedFormShift
        (suzukiWeilIntervalBoundedRemainder a) : ℂ)) := by
  exact boundedPerturbedFriedrichsOperator_hasCompactResolventAt_negShift
    (suzukiWeilIntervalFormEmbedding a)
    (suzukiWeilIntervalBoundedRemainder a)
    (suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a)
    (suzukiWeilIntervalFormEmbedding_injective a)
    (denseRange_suzukiWeilIntervalFormEmbedding a)
    (isCompactOperator_suzukiWeilIntervalFormEmbedding a)

/-- Exact first-representation theorem for Suzuki's source form in interval coordinates. -/
theorem suzukiWeilFriedrichsOperator_represents_form
    (a : SuzukiPositiveAperture)
    (y : SuzukiApertureIntervalL2 a.1)
    (v : CCMArchimedeanFormDomain a) :
    let C := boundedPerturbedFormCovariance
      (suzukiWeilIntervalFormEmbedding a)
      (suzukiWeilIntervalBoundedRemainder a)
      (suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a)
    let x : (suzukiWeilFriedrichsOperator a).domain :=
      ⟨C y, by
        change C y ∈ (closedDenseInverse C).domain
        exact (closedDenseInverse_apply_C C
          (boundedPerturbedFormCovariance_injective
            (suzukiWeilIntervalFormEmbedding a)
            (suzukiWeilIntervalBoundedRemainder a)
            (suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a)
            (suzukiWeilIntervalFormEmbedding_injective a)
            (denseRange_suzukiWeilIntervalFormEmbedding a)) y).1⟩
    let u := boundedPerturbedFormRieszInv
      (suzukiWeilIntervalFormEmbedding a)
      (suzukiWeilIntervalBoundedRemainder a)
      (suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a)
      ((suzukiWeilIntervalFormEmbedding a).adjoint y)
    (x : SuzukiApertureIntervalL2 a.1) =
        suzukiWeilIntervalFormEmbedding a u ∧
      inner ℂ (suzukiWeilFriedrichsOperator a x)
          (suzukiWeilIntervalFormEmbedding a v) =
        suzukiWeilIntervalForm a u v := by
  exact boundedPerturbedFriedrichsOperator_represents_form
    (suzukiWeilIntervalFormEmbedding a)
    (suzukiWeilIntervalBoundedRemainder a)
    (suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a)
    (suzukiWeilIntervalFormEmbedding_injective a)
    (denseRange_suzukiWeilIntervalFormEmbedding a)
    y v

end RHTower

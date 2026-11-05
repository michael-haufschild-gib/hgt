import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheApertureFlowNeverStalls
import GaloisForLFunctions.WindowVisibilityLaw.OnsetApertureAndPositivityDictionary
import GaloisForLFunctions.RHTower.CHMDGraphNormIsTheWeilFormNormOnAnAperture
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilExactFiniteSchur

/-!
# The unshifted Weil Hilbert space before contact

At every positive aperture strictly below the actual onset, the ground energy `μ` is positive.
Writing the literal form as `Q(u) = ‖u‖² + Re⟨BJu,Ju⟩` gives
`‖u‖² ≤ (1 + ‖B‖/μ) Q(u)`. Consequently the unshifted Weil form is a complete Hilbert
inner product on the archimedean form domain, with its original dense smooth source core.
-/

open Complex Set Filter Topology
open scoped InnerProduct

noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

open _root_.RHTower SquareRootThreshold WindowVisibilityLaw
open ArithmeticContinuationAndCriticalEnergy Zeta23

/-- Positive apertures strictly below the onset of the actual zeta configuration. -/
abbrev PrecontactAperture :=
  {a : SuzukiPositiveAperture // (a.1 : EReal) < onsetAperture zetaZeroConfig}

/-- The pre-contact parameter space contains the explicit aperture `181/500`. -/
def basePrecontactAperture : PrecontactAperture :=
  ⟨⟨181 / 500, by norm_num⟩,
    (EReal.coe_lt_coe_iff.mpr
      ArithmeticIncidencePositivity.enlargedWeilFloorAperture_bounds.1).trans_le
        enlargedWeilFloorAperture_le_onsetAperture_zeta⟩

/-- Strict decrease of ground energy turns the onset interval into a strict Rayleigh floor. -/
theorem precontact_groundEnergy_pos (a : PrecontactAperture) :
    0 < ccmRestrictedWeilGroundEnergy a.1 := by
  by_cases hRH : RiemannHypothesis
  · exact riemannHypothesis_iff_ccmRestrictedWeilGroundEnergy_pos.mp hRH a.1
  have ha : (a.1.1 : EReal) < (zetaContactAperture : EReal) :=
    lt_of_lt_of_eq a.2 (onsetAperture_zeta_eq_contact_of_not_rh hRH)
  have hab : a.1 < ⟨zetaContactAperture, zetaContactAperture_pos hRH⟩ :=
    EReal.coe_lt_coe_iff.mp ha
  exact lt_of_eq_of_lt (ccmRestrictedWeilGroundEnergy_contact_eq_zero hRH).symm
    (strictAnti_ccmRestrictedWeilGroundEnergy hab)

/-- Explicit comparison of the closed-form norm with the unshifted Weil norm. -/
def precontactNormFactor (a : PrecontactAperture) : ℝ :=
  1 + ‖ccmRestrictedWeilBoundedRemainder a.1‖ / ccmRestrictedWeilGroundEnergy a.1

theorem one_le_precontactNormFactor (a : PrecontactAperture) :
    1 ≤ precontactNormFactor a := by
  exact le_add_of_nonneg_right
    (div_nonneg (norm_nonneg (ccmRestrictedWeilBoundedRemainder a.1))
      (precontact_groundEnergy_pos a).le)

theorem formNorm_sq_le_precontactFactor_mul_weil (a : PrecontactAperture)
    (u : CCMArchimedeanFormDomain a.1) :
    ‖u‖ ^ 2 ≤ precontactNormFactor a * (ccmRestrictedWeilForm a.1 u u).re := by
  have hfloor := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a.1 u
  rw [← ccmRestrictedWeilForm_self_re_eq_source] at hfloor
  have hmass : ‖ccmArchimedeanFormToAperture a.1 u‖ ^ 2 ≤
      (ccmRestrictedWeilForm a.1 u u).re / ccmRestrictedWeilGroundEnergy a.1 :=
    (le_div_iff₀ (precontact_groundEnergy_pos a)).mpr (by simpa [mul_comm] using hfloor)
  have hB := (abs_le.mp (abs_re_inner_boundedRemainder_le a.1 u)).1
  calc
    ‖u‖ ^ 2 ≤ (ccmRestrictedWeilForm a.1 u u).re +
        ‖ccmRestrictedWeilBoundedRemainder a.1‖ *
          ‖ccmArchimedeanFormToAperture a.1 u‖ ^ 2 := by
      rw [re_ccmRestrictedWeilForm_self]
      linarith only [hB]
    _ ≤ (ccmRestrictedWeilForm a.1 u u).re +
        ‖ccmRestrictedWeilBoundedRemainder a.1‖ *
          ((ccmRestrictedWeilForm a.1 u u).re / ccmRestrictedWeilGroundEnergy a.1) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hmass
        (norm_nonneg (ccmRestrictedWeilBoundedRemainder a.1)))
    _ = precontactNormFactor a * (ccmRestrictedWeilForm a.1 u u).re := by
      unfold precontactNormFactor
      ring

/-- The actual form domain equipped with the unshifted Weil inner product. -/
def WeilHilbertBeforeContact (a : PrecontactAperture) : Type := CCMArchimedeanFormDomain a.1

namespace WeilHilbertBeforeContact

variable (a : PrecontactAperture)

instance instAddCommGroup : AddCommGroup (WeilHilbertBeforeContact a) :=
  inferInstanceAs (AddCommGroup (CCMArchimedeanFormDomain a.1))

instance instModule : Module ℂ (WeilHilbertBeforeContact a) :=
  inferInstanceAs (Module ℂ (CCMArchimedeanFormDomain a.1))

/-- Algebraic identity to the original closed-form domain. -/
def toForm : WeilHilbertBeforeContact a ≃ₗ[ℂ] CCMArchimedeanFormDomain a.1 :=
  LinearEquiv.refl ℂ _

instance core : InnerProductSpace.Core ℂ (WeilHilbertBeforeContact a) where
  inner x y := inner ℂ (ccmRestrictedWeilZeroFormOperator a.1 (toForm a x)) (toForm a y)
  conj_inner_symm x y := by
    calc
      _ = inner ℂ (toForm a x) (ccmRestrictedWeilZeroFormOperator a.1 (toForm a y)) :=
        inner_conj_symm (𝕜 := ℂ) (E := CCMArchimedeanFormDomain a.1) _ _
      _ = _ := ((ContinuousLinearMap.isSelfAdjoint_iff'.mpr
        (ccmRestrictedWeilZeroFormOperator_adjoint a.1)).isSymmetric
          (toForm a x) (toForm a y)).symm
  re_inner_nonneg x := by
    change 0 ≤ (inner ℂ (ccmRestrictedWeilZeroFormOperator a.1 (toForm a x)) (toForm a x)).re
    rw [inner_ccmRestrictedWeilZeroFormOperator, ccmRestrictedWeilForm_self_re_eq_source]
    exact (mul_nonneg (precontact_groundEnergy_pos a).le (sq_nonneg _)).trans
      (ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a.1 (toForm a x))
  add_left x y z := by
    simp only [map_add, inner_add_left]
  smul_left x y c := by
    simp only [map_smul, inner_smul_left (E := CCMArchimedeanFormDomain a.1)]
  definite x hx := by
    have h := formNorm_sq_le_precontactFactor_mul_weil a (toForm a x)
    rw [← inner_ccmRestrictedWeilZeroFormOperator, hx] at h
    have hz : ‖toForm a x‖ ^ 2 = 0 :=
      le_antisymm (by simpa using h) (sq_nonneg _)
    apply (toForm a).injective
    simpa only [map_zero] using norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

instance instNormedAddCommGroup : NormedAddCommGroup (WeilHilbertBeforeContact a) :=
  (core a).toNormedAddCommGroup

instance instInnerProductSpace : InnerProductSpace ℂ (WeilHilbertBeforeContact a) :=
  InnerProductSpace.ofCore _

/-- The Hilbert inner product is exactly the literal Weil form, with no mass shift. -/
theorem inner_eq_weil (x y : WeilHilbertBeforeContact a) :
    inner ℂ x y = ccmRestrictedWeilForm a.1 (toForm a x) (toForm a y) :=
  inner_ccmRestrictedWeilZeroFormOperator a.1 _ _

theorem norm_sq_eq_weil (x : WeilHilbertBeforeContact a) :
    ‖x‖ ^ 2 = (ccmRestrictedWeilForm a.1 (toForm a x) (toForm a x)).re := by
  exact (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) x).trans
    (congrArg Complex.re (inner_eq_weil a x x))

theorem toForm_norm_le (x : WeilHilbertBeforeContact a) :
    ‖toForm a x‖ ≤ precontactNormFactor a * ‖x‖ := by
  have h := formNorm_sq_le_precontactFactor_mul_weil a (toForm a x)
  rw [← norm_sq_eq_weil] at h
  have hC := one_le_precontactNormFactor a
  have hCC : precontactNormFactor a ≤ precontactNormFactor a ^ 2 := by
    nlinarith only [hC]
  have hs := h.trans (mul_le_mul_of_nonneg_right hCC (sq_nonneg ‖x‖))
  have hn := norm_nonneg (toForm a x)
  have hx := norm_nonneg x
  have hr := mul_nonneg (le_trans zero_le_one hC) hx
  exact (sq_le_sq₀ hn hr).mp (by simpa only [mul_pow] using hs)

theorem norm_le_toForm (x : WeilHilbertBeforeContact a) :
    ‖x‖ ≤ (‖ccmRestrictedWeilZeroFormOperator a.1‖ + 1) * ‖toForm a x‖ := by
  have hsq : ‖x‖ ^ 2 ≤ ‖ccmRestrictedWeilZeroFormOperator a.1‖ * ‖toForm a x‖ ^ 2 := by
    rw [norm_sq_eq_weil, ← inner_ccmRestrictedWeilZeroFormOperator]
    calc
      _ ≤ ‖inner ℂ (ccmRestrictedWeilZeroFormOperator a.1 (toForm a x)) (toForm a x)‖ :=
        Complex.re_le_norm _
      _ ≤ ‖ccmRestrictedWeilZeroFormOperator a.1 (toForm a x)‖ * ‖toForm a x‖ :=
        norm_inner_le_norm (𝕜 := ℂ) (E := CCMArchimedeanFormDomain a.1) _ _
      _ ≤ (‖ccmRestrictedWeilZeroFormOperator a.1‖ * ‖toForm a x‖) * ‖toForm a x‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = _ := by ring
  have hK := norm_nonneg (ccmRestrictedWeilZeroFormOperator a.1)
  have hKK : ‖ccmRestrictedWeilZeroFormOperator a.1‖ ≤
      (‖ccmRestrictedWeilZeroFormOperator a.1‖ + 1) ^ 2 := by nlinarith only [hK]
  have hs := hsq.trans (mul_le_mul_of_nonneg_right hKK (sq_nonneg ‖toForm a x‖))
  have hx := norm_nonneg x
  have hr : 0 ≤ (‖ccmRestrictedWeilZeroFormOperator a.1‖ + 1) * ‖toForm a x‖ :=
    mul_nonneg (by linarith only [hK]) (norm_nonneg _)
  exact (sq_le_sq₀ hx hr).mp (by simpa only [mul_pow] using hs)

def toFormCLM : WeilHilbertBeforeContact a →L[ℂ] CCMArchimedeanFormDomain a.1 :=
  LinearMap.mkContinuous (toForm a).toLinearMap (precontactNormFactor a) (toForm_norm_le a)

def fromFormCLM : CCMArchimedeanFormDomain a.1 →L[ℂ] WeilHilbertBeforeContact a :=
  LinearMap.mkContinuous (toForm a).symm.toLinearMap
    (‖ccmRestrictedWeilZeroFormOperator a.1‖ + 1) (fun x => norm_le_toForm a ((toForm a).symm x))

@[simp] theorem toForm_fromForm (x : CCMArchimedeanFormDomain a.1) :
    toForm a (fromFormCLM a x) = x := rfl

@[simp] theorem fromForm_toForm (x : WeilHilbertBeforeContact a) :
    fromFormCLM a (toForm a x) = x := rfl

/-- The exact Weil and archimedean form topologies coincide before contact. -/
def equivForm : WeilHilbertBeforeContact a ≃L[ℂ] CCMArchimedeanFormDomain a.1 where
  toLinearEquiv := toForm a
  continuous_toFun := (toFormCLM a).continuous
  continuous_invFun := (fromFormCLM a).continuous

instance instCompleteSpace : CompleteSpace (WeilHilbertBeforeContact a) := by
  let e : WeilHilbertBeforeContact a ≃ᵤ CCMArchimedeanFormDomain a.1 :=
    { (equivForm a).toEquiv with
      uniformContinuous_toFun := (toFormCLM a).uniformContinuous
      uniformContinuous_invFun := (fromFormCLM a).uniformContinuous }
  exact e.completeSpace_iff.mpr inferInstance

/-- The unchanged smooth compact core is dense for the exact Weil norm. -/
theorem denseRange_smoothCore :
    DenseRange (fun u : CCMComplexSmoothInteriorSource a.1 =>
      fromFormCLM a u.toCCMFormVector) :=
  (equivForm a).symm.surjective.denseRange.comp
    (denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector a.1)
    (fromFormCLM a).continuous

/-- Physical mass is controlled by the exact Weil norm and the actual ground energy. -/
theorem groundEnergy_mul_mass_le (x : WeilHilbertBeforeContact a) :
    ccmRestrictedWeilGroundEnergy a.1 *
      ‖ccmArchimedeanFormToAperture a.1 (toForm a x)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [norm_sq_eq_weil, ccmRestrictedWeilForm_self_re_eq_source]
  exact ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a.1 _

/-- Increasing the aperture preserves the exact Weil norm. -/
def inclusion {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) :
    WeilHilbertBeforeContact a →ₗᵢ[ℂ] WeilHilbertBeforeContact b where
  toFun x := fromFormCLM b (apertureExt hab (toForm a x))
  map_add' x y := by simp only [map_add, apertureExt_add]
  map_smul' c x := by simp only [map_smul, apertureExt_smul, RingHom.id_apply]
  norm_map' x := by
    have heq : ‖fromFormCLM b (apertureExt hab (toForm a x))‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [norm_sq_eq_weil, norm_sq_eq_weil, toForm_fromForm]
      exact congrArg Complex.re (apertureForm_ext _root_.RHTower.WeilDeletion.literalFamily
        hab (toForm a x) (toForm a x))
    exact le_antisymm
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp heq.le)
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp heq.ge)

theorem toForm_inclusion {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1)
    (x : WeilHilbertBeforeContact a) :
    toForm b (inclusion hab x) = apertureExt hab (toForm a x) := rfl

theorem inclusion_self (x : WeilHilbertBeforeContact a) : inclusion le_rfl x = x := by
  apply (toForm a).injective
  rw [toForm_inclusion]
  apply Subtype.ext
  exact apertureExt_val le_rfl (toForm a x)

theorem inclusion_trans {a b c : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) (hbc : b.1.1 ≤ c.1.1) (x : WeilHilbertBeforeContact a) :
    inclusion hbc (inclusion hab x) = inclusion (hab.trans hbc) x := by
  apply (toForm c).injective
  rw [toForm_inclusion, toForm_inclusion, toForm_inclusion]
  apply Subtype.ext
  rw [apertureExt_val, apertureExt_val, apertureExt_val]

end WeilHilbertBeforeContact

#print axioms precontact_groundEnergy_pos
#print axioms basePrecontactAperture
#print axioms WeilHilbertBeforeContact.inner_eq_weil
#print axioms WeilHilbertBeforeContact.instCompleteSpace
#print axioms WeilHilbertBeforeContact.denseRange_smoothCore
#print axioms WeilHilbertBeforeContact.inclusion

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower

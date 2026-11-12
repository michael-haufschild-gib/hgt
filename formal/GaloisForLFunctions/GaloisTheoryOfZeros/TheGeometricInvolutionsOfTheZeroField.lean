import GaloisForLFunctions.GaloisTheoryOfZeros.TheRealWidthFieldOfTheZeros

/-!
# The geometric involutions and their fixed fields

Whenever functional-equation reflection lifts, it fixes exactly the centered
zero field. Composing it with ordinary conjugation fixes the Gaussian extension
of the even-width field. Their common fixed field is the even-width field itself.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower
open scoped IntermediateField
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- The unique source-field lift of functional-equation reflection. -/
def sourceFunctionalReflection (hi : I ∉ fullFibreZeroExtension) :
    gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension :=
  (gaussianGaloisProduct hi).symm (1,-1)

private theorem sourceFunctionalReflection_coordinates (hi : I ∉ fullFibreZeroExtension) :
    gaussianActionCoordinates (sourceFunctionalReflection hi) = (1,-1) :=
  (gaussianGaloisProduct hi).apply_symm_apply (1,-1)

private theorem centered_gaussian_map_coe (a : fullFibreZeroExtension) :
    (algebraMap fullFibreZeroExtension gaussianZeroExtension a : ℂ) = (a : ℂ) :=
  (IsScalarTower.algebraMap_apply fullFibreZeroExtension gaussianZeroExtension ℂ a).symm

private theorem gaussian_conjugation_coe (z : gaussianZeroExtension) :
    (gaussianZeroConjugation z : ℂ) = (starRingEnd ℂ) (z : ℂ) := rfl

/-- Functional-equation reflection fixes the whole centered field. -/
theorem sourceFunctionalReflection_base (hi : I ∉ fullFibreZeroExtension)
    (a : fullFibreZeroExtension) :
    sourceFunctionalReflection hi (algebraMap fullFibreZeroExtension gaussianZeroExtension a) =
      algebraMap fullFibreZeroExtension gaussianZeroExtension a := by
  have h : (sourceFunctionalReflection hi).restrictNormal fullFibreZeroExtension = 1 :=
    congrArg Prod.fst (sourceFunctionalReflection_coordinates hi)
  rw [← AlgEquiv.restrictNormal_commutes, h]
  rfl

theorem sourceFunctionalReflection_unit (hi : I ∉ fullFibreZeroExtension) :
    sourceFunctionalReflection hi gaussianUnit = -gaussianUnit := by
  have h := gaussianActionCoordinates_unit (sourceFunctionalReflection hi)
  rw [sourceFunctionalReflection_coordinates] at h
  simpa only [Units.val_neg,Units.val_one,Int.cast_neg,Int.cast_one,neg_one_mul] using h

/-- The product coordinate acts as the actual functional equation on every original zero. -/
theorem sourceFunctionalReflection_original (hi : I ∉ fullFibreZeroExtension) (q : XiZeroCopy) :
    sourceFunctionalReflection hi (originalZeroInGaussianExtension q) =
      1-originalZeroInGaussianExtension q := by
  have hq : sourceFunctionalReflection hi (centeredZeroInGaussianExtension q) =
      centeredZeroInGaussianExtension q :=
    sourceFunctionalReflection_base hi (centeredZeroInFibreExtension q)
  rw [originalZeroInGaussianExtension,map_add,map_div₀,map_one,map_ofNat,map_mul,
    sourceFunctionalReflection_unit,hq]
  ring

/-- Functional-equation reflection is central whenever it exists. -/
theorem sourceFunctionalReflection_central (hi : I ∉ fullFibreZeroExtension)
    (τ : gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension) :
    sourceFunctionalReflection hi * τ = τ * sourceFunctionalReflection hi := by
  apply (gaussianGaloisProduct hi).injective
  change gaussianActionCoordinates (sourceFunctionalReflection hi*τ) =
    gaussianActionCoordinates (τ*sourceFunctionalReflection hi)
  rw [map_mul,map_mul,sourceFunctionalReflection_coordinates]
  apply Prod.ext
  · exact (one_mul _).trans (mul_one _).symm
  · exact mul_comm _ _

/-- Functional-equation reflection has order two. -/
theorem sourceFunctionalReflection_square (hi : I ∉ fullFibreZeroExtension) :
    sourceFunctionalReflection hi * sourceFunctionalReflection hi = 1 := by
  apply (gaussianGaloisProduct hi).injective
  change gaussianActionCoordinates (sourceFunctionalReflection hi*sourceFunctionalReflection hi) =
    gaussianActionCoordinates 1
  rw [map_mul,map_one,sourceFunctionalReflection_coordinates]
  simp

/-- Reflection across the critical line fixes the Gaussian unit. -/
def sourceLineReflection (hi : I ∉ fullFibreZeroExtension) :
    gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension :=
  gaussianZeroConjugation * sourceFunctionalReflection hi

theorem sourceLineReflection_unit (hi : I ∉ fullFibreZeroExtension) :
    sourceLineReflection hi gaussianUnit = gaussianUnit := by
  change gaussianZeroConjugation (sourceFunctionalReflection hi gaussianUnit) = gaussianUnit
  rw [sourceFunctionalReflection_unit,map_neg]
  apply Subtype.ext
  change -(starRingEnd ℂ) I = I
  simp

/-- The second involution is the actual reflection across the critical line. -/
theorem sourceLineReflection_original (hi : I ∉ fullFibreZeroExtension) (q : XiZeroCopy) :
    sourceLineReflection hi (originalZeroInGaussianExtension q) =
      1-gaussianZeroConjugation (originalZeroInGaussianExtension q) := by
  change gaussianZeroConjugation
    (sourceFunctionalReflection hi (originalZeroInGaussianExtension q)) = _
  rw [sourceFunctionalReflection_original,map_sub,map_one]

private theorem gaussian_repr_lift (z : gaussianZeroExtension) (a b : fullFibreZeroExtension)
    (hab : (z : ℂ) = (a : ℂ)+(b : ℂ)*I) :
    z = algebraMap fullFibreZeroExtension gaussianZeroExtension a +
      algebraMap fullFibreZeroExtension gaussianZeroExtension b * gaussianUnit := by
  apply Subtype.ext
  change (z : ℂ) = (algebraMap fullFibreZeroExtension gaussianZeroExtension a : ℂ) +
    (algebraMap fullFibreZeroExtension gaussianZeroExtension b : ℂ)*I
  rw [centered_gaussian_map_coe,centered_gaussian_map_coe]
  exact hab

private theorem sourceFunctionalReflection_formula (hi : I ∉ fullFibreZeroExtension)
    (z : gaussianZeroExtension) (a b : fullFibreZeroExtension)
    (hab : (z : ℂ) = (a : ℂ)+(b : ℂ)*I) :
    (sourceFunctionalReflection hi z : ℂ) = (a : ℂ)-(b : ℂ)*I := by
  have he : sourceFunctionalReflection hi z =
      algebraMap fullFibreZeroExtension gaussianZeroExtension a -
        algebraMap fullFibreZeroExtension gaussianZeroExtension b*gaussianUnit := by
    rw [gaussian_repr_lift z a b hab,map_add,map_mul,sourceFunctionalReflection_base,
      sourceFunctionalReflection_base,sourceFunctionalReflection_unit]
    ring
  have h := congrArg (fun x : gaussianZeroExtension => (x : ℂ)) he
  change (sourceFunctionalReflection hi z : ℂ) =
    (algebraMap fullFibreZeroExtension gaussianZeroExtension a : ℂ) -
      (algebraMap fullFibreZeroExtension gaussianZeroExtension b : ℂ)*I at h
  rwa [centered_gaussian_map_coe,centered_gaussian_map_coe] at h

private theorem sourceLineReflection_formula (hi : I ∉ fullFibreZeroExtension)
    (z : gaussianZeroExtension) (a b : fullFibreZeroExtension)
    (hab : (z : ℂ) = (a : ℂ)+(b : ℂ)*I) :
    (sourceLineReflection hi z : ℂ) =
      (starRingEnd ℂ) (a : ℂ)+(starRingEnd ℂ) (b : ℂ)*I := by
  change (gaussianZeroConjugation (sourceFunctionalReflection hi z) : ℂ) = _
  rw [gaussian_conjugation_coe,sourceFunctionalReflection_formula hi z a b hab]
  simp only [map_sub,map_mul,conj_I,mul_neg,sub_neg_eq_add]

/-- The fixed field of functional-equation reflection is the entire centered zero field. -/
theorem sourceFunctionalReflection_fixed_iff (hi : I ∉ fullFibreZeroExtension)
    (z : gaussianZeroExtension) :
    sourceFunctionalReflection hi z = z ↔ (z : ℂ) ∈ fullFibreZeroExtension := by
  constructor
  · intro hz
    obtain ⟨a,b,hab⟩ := gaussian_element_repr z
    have he := sourceFunctionalReflection_formula hi z a b hab
    rw [hz,hab] at he
    have hbI : (b : ℂ)*I = 0 := by linear_combination (1/2:ℂ)*he
    have hb : (b : ℂ) = 0 := (mul_eq_zero.mp hbI).resolve_right I_ne_zero
    rw [hab,hb,zero_mul,add_zero]
    exact a.property
  · intro hz
    let a : fullFibreZeroExtension := ⟨z,hz⟩
    have he : algebraMap fullFibreZeroExtension gaussianZeroExtension a = z := by
      apply Subtype.ext
      exact centered_gaussian_map_coe a
    rw [← he,sourceFunctionalReflection_base]

/-- Reflection across the critical line fixes exactly the Gaussian extension of all even widths. -/
theorem sourceLineReflection_fixed_iff (hi : I ∉ fullFibreZeroExtension)
    (z : gaussianZeroExtension) :
    sourceLineReflection hi z = z ↔ (z : ℂ) ∈ evenWidthField⟮I⟯ := by
  constructor
  · intro hz
    obtain ⟨a,b,hab⟩ := gaussian_element_repr z
    have he := sourceLineReflection_formula hi z a b hab
    rw [hz,hab] at he
    have hr := congrArg Complex.re he
    have hm := congrArg Complex.im he
    simp only [add_re,mul_re,conj_re,conj_im,I_re,I_im,mul_zero,mul_one,
      zero_sub,neg_neg] at hr
    simp only [add_im,mul_im,conj_re,conj_im,I_re,I_im,mul_zero,mul_one,
      add_zero] at hm
    have ha : (a : ℂ).im = 0 := by linarith only [hm]
    have hb : (b : ℂ).im = 0 := by linarith only [hr]
    have haE : (a : ℂ) ∈ evenWidthField := by
      change (a : ℂ) ∈ evenWidthField.toSubfield
      rw [evenWidthField_eq_real_part]
      refine ⟨a.property,(a : ℂ).re,?_⟩
      apply Complex.ext <;> simp [ha]
    have hbE : (b : ℂ) ∈ evenWidthField := by
      change (b : ℂ) ∈ evenWidthField.toSubfield
      rw [evenWidthField_eq_real_part]
      refine ⟨b.property,(b : ℂ).re,?_⟩
      apply Complex.ext <;> simp [hb]
    rw [hab]
    exact (evenWidthField⟮I⟯).add_mem
      ((evenWidthField⟮I⟯).algebraMap_mem (⟨a,haE⟩ : evenWidthField))
      ((evenWidthField⟮I⟯).mul_mem
        ((evenWidthField⟮I⟯).algebraMap_mem (⟨b,hbE⟩ : evenWidthField))
        (IntermediateField.mem_adjoin_simple_self evenWidthField I))
  · intro hz
    obtain ⟨a,b,hab⟩ := HTGeometry.exists_repr_of_mem_adjoin_sqrt
      (show I*I = algebraMap evenWidthField ℂ (-1) by rw [I_mul_I,map_neg,map_one]) hz
    change (z : ℂ) = (a : ℂ)+(b : ℂ)*I at hab
    let aL : fullFibreZeroExtension := ⟨a,evenWidthField_le_zeroExtension a.property⟩
    let bL : fullFibreZeroExtension := ⟨b,evenWidthField_le_zeroExtension b.property⟩
    obtain ⟨ar,har⟩ := evenWidthField_le_real a.property
    obtain ⟨br,hbr⟩ := evenWidthField_le_real b.property
    apply Subtype.ext
    rw [sourceLineReflection_formula hi z aL bL hab]
    change (starRingEnd ℂ) (a : ℂ)+(starRingEnd ℂ) (b : ℂ)*I = (z : ℂ)
    rw [hab,← har,← hbr]
    simp

private theorem gaussian_conjugation_fixed_iff_real (z : gaussianZeroExtension) :
    gaussianZeroConjugation z = z ↔ (z : ℂ) ∈ Complex.ofRealHom.fieldRange := by
  constructor
  · intro h
    have him := congrArg (fun x : gaussianZeroExtension => (x : ℂ).im) h
    change -(z : ℂ).im = (z : ℂ).im at him
    have hz : (z : ℂ).im = 0 := by linarith only [him]
    refine ⟨(z : ℂ).re,?_⟩
    apply Complex.ext <;> simp [hz]
  · rintro ⟨r,hr⟩
    apply Subtype.ext
    rw [gaussian_conjugation_coe,← hr]
    simp

/-- The common fixed field of ordinary conjugation and functional-equation reflection is the even-width field. -/
theorem source_geometric_common_fixed (hi : I ∉ fullFibreZeroExtension)
    (z : gaussianZeroExtension) :
    (sourceFunctionalReflection hi z = z ∧ gaussianZeroConjugation z = z) ↔
      (z : ℂ) ∈ evenWidthField := by
  rw [sourceFunctionalReflection_fixed_iff,gaussian_conjugation_fixed_iff_real]
  change _ ↔ (z : ℂ) ∈ evenWidthField.toSubfield
  rw [evenWidthField_eq_real_part]
  rfl

private def signInvolutionHom {G : Type*} [Group G] (g : G) (hg : g*g = 1) : ℤˣ →* G where
  toFun ε := if ε = 1 then 1 else g
  map_one' := by simp
  map_mul' ε η := by
    have hn : (-1 : ℤˣ) ≠ 1 := by
      intro h
      have he := congrArg (fun u : ℤˣ => (u : ℤ)) h
      norm_num at he
    rcases Int.units_eq_one_or ε with rfl | rfl <;>
      rcases Int.units_eq_one_or η with rfl | rfl <;> simp [hn,hg]

private theorem signInvolutionHom_neg_one {G : Type*} [Group G] (g : G) (hg : g*g = 1) :
    signInvolutionHom g hg (-1) = g := by
  have hn : (-1 : ℤˣ) ≠ 1 := by
    intro h
    have he := congrArg (fun u : ℤˣ => (u : ℤ)) h
    norm_num at he
  change (if (-1 : ℤˣ) = 1 then 1 else g) = g
  rw [if_neg hn]

private theorem signInvolutionHom_injective {G : Type*} [Group G]
    (g : G) (hg : g*g = 1) (hne : g ≠ 1) :
    Function.Injective (signInvolutionHom g hg) := by
  intro ε η he
  rcases Int.units_eq_one_or ε with rfl | rfl <;>
    rcases Int.units_eq_one_or η with rfl | rfl <;>
    simp only [map_one,signInvolutionHom_neg_one] at he ⊢
  · exact False.elim (hne he.symm)
  · exact False.elim (hne he)

private theorem centered_conjugation_square :
    fullFibreZeroConjugation * fullFibreZeroConjugation = 1 := by
  apply AlgEquiv.ext
  intro z
  apply Subtype.ext
  change (starRingEnd ℂ) ((starRingEnd ℂ) (z : ℂ)) = (z : ℂ)
  simp

private theorem centered_conjugation_ne_one (q : XiZeroCopy) (hq : zeroWidth q ≠ 0) :
    fullFibreZeroConjugation ≠ 1 := by
  intro he
  have h := DFunLike.congr_fun he (centeredZeroInFibreExtension q)
  have him := congrArg (fun z : fullFibreZeroExtension => (z : ℂ).im) h
  change -(xiSpectralPoint q).im = (xiSpectralPoint q).im at him
  have hz : (xiSpectralPoint q).im = 0 := by linarith only [him]
  exact hq (by simp only [zeroWidth,hz,ofReal_zero])

/-- The two geometric sign coordinates act on the full Gaussian zero field. -/
def sourceGeometricKleinFour (hi : I ∉ fullFibreZeroExtension) :
    ℤˣ × ℤˣ →* (gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension) where
  toFun p := (gaussianGaloisProduct hi).symm
    (signInvolutionHom fullFibreZeroConjugation centered_conjugation_square p.1,p.2)
  map_one' := by
    change (gaussianGaloisProduct hi).symm
      (signInvolutionHom fullFibreZeroConjugation centered_conjugation_square (1 : ℤˣ),
        (1 : ℤˣ)) = 1
    rw [map_one]
    exact (gaussianGaloisProduct hi).symm.map_one
  map_mul' p r := by
    change (gaussianGaloisProduct hi).symm
      (signInvolutionHom fullFibreZeroConjugation centered_conjugation_square (p.1*r.1),p.2*r.2) = _
    rw [map_mul]
    exact (gaussianGaloisProduct hi).symm.map_mul
      (signInvolutionHom fullFibreZeroConjugation centered_conjugation_square p.1,p.2)
      (signInvolutionHom fullFibreZeroConjugation centered_conjugation_square r.1,r.2)

private theorem sourceGeometricKleinFour_coordinates (hi : I ∉ fullFibreZeroExtension) (p : ℤˣ×ℤˣ) :
    gaussianActionCoordinates (sourceGeometricKleinFour hi p) =
      (signInvolutionHom fullFibreZeroConjugation centered_conjugation_square p.1,p.2) :=
  (gaussianGaloisProduct hi).apply_symm_apply _

/-- A nonzero width makes the geometric sign action a faithful Klein four action. -/
theorem sourceGeometricKleinFour_injective (hi : I ∉ fullFibreZeroExtension)
    (q : XiZeroCopy) (hq : zeroWidth q ≠ 0) :
    Function.Injective (sourceGeometricKleinFour hi) := by
  intro p r he
  have hc := congrArg gaussianActionCoordinates he
  rw [sourceGeometricKleinFour_coordinates,sourceGeometricKleinFour_coordinates] at hc
  apply Prod.ext
  · exact signInvolutionHom_injective fullFibreZeroConjugation centered_conjugation_square
      (centered_conjugation_ne_one q hq) (congrArg Prod.fst hc)
  · exact congrArg (fun x :
      (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) × ℤˣ => x.2) hc

/-- All geometric sign actions are central in the full infinite source Galois group. -/
theorem sourceGeometricKleinFour_central (hi : I ∉ fullFibreZeroExtension) (p : ℤˣ×ℤˣ)
    (τ : gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension) :
    sourceGeometricKleinFour hi p * τ = τ * sourceGeometricKleinFour hi p := by
  apply (gaussianGaloisProduct hi).injective
  change gaussianActionCoordinates (sourceGeometricKleinFour hi p*τ) =
    gaussianActionCoordinates (τ*sourceGeometricKleinFour hi p)
  rw [map_mul,map_mul,sourceGeometricKleinFour_coordinates]
  apply Prod.ext
  · change (if p.1 = 1 then 1 else fullFibreZeroConjugation) *
      (gaussianActionCoordinates τ).1 =
        (gaussianActionCoordinates τ).1*(if p.1 = 1 then 1 else fullFibreZeroConjugation)
    split_ifs
    · simp only [one_mul,mul_one]
    · exact (fullFibreZeroConjugation_central (gaussianActionCoordinates τ).1).symm
  · exact mul_comm _ _

/-- The Gaussian sign alone is functional-equation reflection. -/
theorem sourceGeometricKleinFour_functional (hi : I ∉ fullFibreZeroExtension) :
    sourceGeometricKleinFour hi (1,-1) = sourceFunctionalReflection hi := by
  change (gaussianGaloisProduct hi).symm
    (signInvolutionHom fullFibreZeroConjugation centered_conjugation_square 1,-1) = _
  rw [map_one]
  rfl

/-- Reversing both geometric signs is ordinary complex conjugation. -/
theorem sourceGeometricKleinFour_conjugation (hi : I ∉ fullFibreZeroExtension) :
    sourceGeometricKleinFour hi (-1,-1) = gaussianZeroConjugation := by
  apply (gaussianGaloisProduct hi).injective
  change gaussianActionCoordinates (sourceGeometricKleinFour hi (-1,-1)) =
    gaussianActionCoordinates gaussianZeroConjugation
  rw [sourceGeometricKleinFour_coordinates,gaussian_conjugation_coordinates,
    signInvolutionHom_neg_one]

/-- The centered conjugation sign alone is reflection across the critical line. -/
theorem sourceGeometricKleinFour_line (hi : I ∉ fullFibreZeroExtension) :
    sourceGeometricKleinFour hi (-1,1) = sourceLineReflection hi := by
  have hp : ((-1,1) : ℤˣ×ℤˣ) = (-1,-1)*(1,-1) := by simp
  rw [hp,map_mul,sourceGeometricKleinFour_conjugation,sourceGeometricKleinFour_functional]
  rfl

/-- Reflection across the critical line is central whenever its source-field lift exists. -/
theorem sourceLineReflection_central (hi : I ∉ fullFibreZeroExtension)
    (τ : gaussianZeroExtension ≃ₐ[fullFibreSourceField] gaussianZeroExtension) :
    sourceLineReflection hi * τ = τ * sourceLineReflection hi := by
  rw [← sourceGeometricKleinFour_line]
  exact sourceGeometricKleinFour_central hi (-1,1) τ

end GaloisForLFunctions.GaloisTheoryOfZeros

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.sourceFunctionalReflection_original
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.sourceFunctionalReflection_central
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.sourceFunctionalReflection_fixed_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.sourceLineReflection_fixed_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.source_geometric_common_fixed

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.sourceGeometricKleinFour_injective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.sourceGeometricKleinFour_central

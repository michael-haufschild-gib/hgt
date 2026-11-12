import GaloisForLFunctions.GaloisTheoryOfZeros.TheRealWidthFieldOfTheZeros
import Mathlib.FieldTheory.IntermediateField.Algebraic

/-!
# The biquadratic diagram of a nonzero width

The full Gaussian zero field has degree two or four over the entire even-width
field. In the degree-four case its three quadratic subfields are the real width
field, the centered zero field, and the Gaussian extension of the even field.
-/

noncomputable section
set_option autoImplicit false
open Complex Polynomial RHTower
open scoped IntermediateField BigOperators
namespace GaloisForLFunctions.GaloisTheoryOfZeros

private theorem field_finrank_congr {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    {A B : IntermediateField K Ω} (h : A = B) : Module.finrank K A = Module.finrank K B :=
  congrArg (fun N : IntermediateField K Ω => Module.finrank K N) h

private theorem field_finrank_restrict {K L Ω : Type*} [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    (A : IntermediateField L Ω) :
    Module.finrank K (A.restrictScalars K) = Module.finrank K A := rfl

private theorem two_quadratic_steps_degree_four (K A B : Type*)
    [Field K] [Field A] [Field B] [Algebra K A] [Algebra A B]
    [Algebra K B] [IsScalarTower K A B]
    (hA : Module.finrank K A = 2) (hB : Module.finrank A B = 2) :
    Module.finrank K B = 4 := by
  rw [← Module.finrank_mul_finrank K A B,hA,hB]

/-- Every quadratic complex subfield has a nonbase generator whose square lies in the base. -/
theorem quadratic_subfield_square_generator (E : Subfield ℂ)
    (N : IntermediateField E ℂ) (hN : Module.finrank E N = 2) :
    ∃ r : ℂ, r ∈ N ∧ r ∉ E ∧ r*r ∈ E ∧ N = E⟮r⟯ := by
  letI : Algebra.IsQuadraticExtension E N :=
    { toFree := inferInstance
      finrank_eq_two' := hN }
  have hNbot : N ≠ ⊥ := by
    intro h
    have h1 : Module.finrank E N = 1 := IntermediateField.finrank_eq_one_iff.mpr h
    omega
  obtain ⟨z,hzN,hzbot⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hNbot)
  let x : N := ⟨z,hzN⟩
  have hxrange : x ∉ (algebraMap E N).range := by
    rintro ⟨a,ha⟩
    have he : (a : ℂ) = z := congrArg (fun w : N => (w : ℂ)) ha
    exact hzbot (IntermediateField.mem_bot.mpr ⟨a,he⟩)
  have hint : IsIntegral E x := Algebra.IsIntegral.isIntegral x
  have hd : (minpoly E x).natDegree = 2 := by
    apply le_antisymm
    · calc
        _ ≤ Module.finrank E N := minpoly.natDegree_le x
        _ = 2 := hN
    · exact (minpoly.two_le_natDegree_iff hint).mpr hxrange
  let b : E := (minpoly E x).coeff 1
  let d : E := (minpoly E x).coeff 0
  have hc2 : (minpoly E x).coeff 2 = 1 := by
    have h := minpoly.monic hint
    change (minpoly E x).coeff (minpoly E x).natDegree = 1 at h
    rwa [hd] at h
  have hpoly : minpoly E x = X^2+C b*X+C d := by
    calc
      _ = ∑ k ∈ Finset.range ((minpoly E x).natDegree+1),
          C ((minpoly E x).coeff k)*X^k := (minpoly E x).as_sum_range_C_mul_X_pow
      _ = _ := by
        rw [hd]
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
          pow_zero, pow_one, mul_one, hc2, C_1, one_mul]
        dsimp only [b,d]
        ring
  have hval : x*x+algebraMap E N b*x+algebraMap E N d = 0 := by
    have h := minpoly.aeval E x
    rw [hpoly] at h
    simpa only [map_add, map_mul, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C, pow_two] using h
  let r : N := 2*x+algebraMap E N b
  have hrsq : r*r = algebraMap E N (b*b-4*d) := by
    dsimp only [r]
    simp only [map_sub,map_mul,map_ofNat]
    linear_combination 4*hval
  have hrval : (r : ℂ) = 2*z+(b : ℂ) := rfl
  have hrnot : (r : ℂ) ∉ E := by
    intro hrE
    have hz : z = ((r : ℂ)-(b : ℂ))/2 := by rw [hrval]; ring
    apply hzbot
    refine IntermediateField.mem_bot.mpr ⟨⟨z,?_⟩,rfl⟩
    rw [hz]
    exact E.div_mem (E.sub_mem hrE b.property) (natCast_mem E 2)
  have hrsqC : (r : ℂ)*(r : ℂ) = ((b*b-4*d : E) : ℂ) :=
    congrArg (fun w : N => (w : ℂ)) hrsq
  have hrsqmem : (r : ℂ)*(r : ℂ) ∈ E := by
    rw [hrsqC]
    exact (b*b-4*d).property
  have hrbot : (r : ℂ) ∉ (⊥ : IntermediateField E ℂ) := by
    intro h
    obtain ⟨a,ha⟩ := IntermediateField.mem_bot.mp h
    exact hrnot (ha ▸ a.property)
  have hdeg : Module.finrank E E⟮(r : ℂ)⟯ = 2 :=
    HTGeometry.finrank_adjoin_eq_two
      (show (r : ℂ)*(r : ℂ) = algebraMap E ℂ (⟨_,hrsqmem⟩ : E) from rfl) hrbot
  have hle : E⟮(r : ℂ)⟯ ≤ N := IntermediateField.adjoin_simple_le_iff.mpr r.property
  exact ⟨r,r.property,hrnot,hrsqmem,
    (IntermediateField.eq_of_le_of_finrank_eq hle (hdeg.trans hN.symm)).symm⟩

/-- A square root over the base in a quadratic extension lies on one of its two coordinate lines. -/
theorem quadratic_square_root_line (E : Subfield ℂ) {d z : ℂ}
    (hdd : d*d ∈ E) (hd : d ∉ E) (hz : z ∈ E⟮d⟯) (hzz : z*z ∈ E) :
    z ∈ E ∨ ∃ b : E, z = (b : ℂ)*d := by
  obtain ⟨a,b,hab⟩ := HTGeometry.exists_repr_of_mem_adjoin_sqrt
    (show d*d = algebraMap E ℂ (⟨d*d,hdd⟩ : E) from rfl) hz
  change z = (a : ℂ)+(b : ℂ)*d at hab
  have hab0 : (a : ℂ)*(b : ℂ) = 0 := by
    by_contra habne
    have hcne : 2*((a : ℂ)*(b : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) habne
    have hsolve : d = (z*z-((a : ℂ)*(a : ℂ)+(b : ℂ)*(b : ℂ)*(d*d))) /
        (2*((a : ℂ)*(b : ℂ))) := by
      apply (eq_div_iff hcne).mpr
      rw [hab]
      ring
    apply hd
    rw [hsolve]
    exact E.div_mem
      (E.sub_mem hzz (E.add_mem (E.mul_mem a.property a.property)
        (E.mul_mem (E.mul_mem b.property b.property) hdd)))
      (E.mul_mem (natCast_mem E 2) (E.mul_mem a.property b.property))
  rcases mul_eq_zero.mp hab0 with ha | hb
  · exact Or.inr ⟨b,by rw [hab,ha,zero_add]⟩
  · left
    rw [hab,hb,zero_mul,add_zero]
    exact a.property

/-- Scaling a generator by a nonzero base element does not change its field. -/
private theorem adjoin_nonzero_base_mul (E : Subfield ℂ) (a : E) (ha : (a : ℂ) ≠ 0) (z : ℂ) :
    E⟮(a : ℂ)*z⟯ = E⟮z⟯ := by
  apply le_antisymm
  · apply IntermediateField.adjoin_simple_le_iff.mpr
    exact (E⟮z⟯).mul_mem ((E⟮z⟯).algebraMap_mem a)
      (IntermediateField.mem_adjoin_simple_self E z)
  · apply IntermediateField.adjoin_simple_le_iff.mpr
    have he : z = (a : ℂ)*z/(a : ℂ) := by
      apply (eq_div_iff ha).mpr
      exact mul_comm _ _
    have haMem : (a : ℂ) ∈ E⟮(a : ℂ)*z⟯ :=
      (E⟮(a : ℂ)*z⟯).algebraMap_mem a
    have hm : (a : ℂ)*z/(a : ℂ) ∈ E⟮(a : ℂ)*z⟯ :=
      (E⟮(a : ℂ)*z⟯).div_mem
        (IntermediateField.mem_adjoin_simple_self E ((a : ℂ)*z)) haMem
    rwa [← he] at hm

/-- The full Gaussian zero field viewed over the even-width field. -/
def evenGaussianZeroExtension : IntermediateField evenWidthField ℂ :=
  IntermediateField.extendScalars (evenWidthField_le_zeroExtension.trans zeroExtension_le_gaussian)

/-- Adjoining one signed width to the entire even-width field. -/
def widthAnchorExtension (q : XiZeroCopy) : IntermediateField evenWidthField ℂ :=
  evenWidthField⟮zeroWidth q⟯

private theorem widthAnchorExtension_le_real (q : XiZeroCopy) :
    (widthAnchorExtension q).toSubfield ≤ Complex.ofRealHom.fieldRange := by
  rw [widthAnchorExtension, IntermediateField.adjoin_toSubfield]
  apply Subfield.closure_le.mpr
  rintro z (⟨a,rfl⟩ | hz)
  · exact evenWidthField_le_real a.property
  · have he : z = zeroWidth q := Set.mem_singleton_iff.mp hz
    rw [he]
    exact ⟨(xiSpectralPoint q).im,rfl⟩

private theorem gaussian_adjoin_degree_two {K : Type*} [Field K] [Algebra K ℂ]
    (hK : ∀ a : K, (algebraMap K ℂ a).im = 0) :
    Module.finrank K K⟮I⟯ = 2 := by
  apply HTGeometry.finrank_adjoin_eq_two
    (show I*I = algebraMap K ℂ (-1) by rw [I_mul_I,map_neg,map_one])
  intro hi
  obtain ⟨a,ha⟩ := IntermediateField.mem_bot.mp hi
  have h := hK a
  rw [ha,I_im] at h
  exact one_ne_zero h

/-- A width absent from the even field and the Gaussian unit give a degree-four tower. -/
theorem width_biquadratic_tower_degree (q : XiZeroCopy) (hq : zeroWidth q ∉ evenWidthField) :
    Module.finrank evenWidthField (widthAnchorExtension q)⟮I⟯ = 4 := by
  have hA : Module.finrank evenWidthField (widthAnchorExtension q) = 2 :=
    (realWidthField_anchor_quadratic q hq).2
  have hI : Module.finrank (widthAnchorExtension q) (widthAnchorExtension q)⟮I⟯ = 2 := by
    apply gaussian_adjoin_degree_two
    intro a
    obtain ⟨r,hr⟩ := widthAnchorExtension_le_real q a.property
    change (a : ℂ).im = 0
    rw [← hr]
    rfl
  exact two_quadratic_steps_degree_four evenWidthField (widthAnchorExtension q)
    (widthAnchorExtension q)⟮I⟯ hA hI

/-- The two quadratic generators exhaust the entire infinite Gaussian zero field. -/
theorem evenGaussianZeroExtension_eq_width_tower (q : XiZeroCopy) (hq : zeroWidth q ≠ 0) :
    evenGaussianZeroExtension =
      ((widthAnchorExtension q)⟮I⟯).restrictScalars evenWidthField := by
  let D : IntermediateField evenWidthField ℂ :=
    ((widthAnchorExtension q)⟮I⟯).restrictScalars evenWidthField
  have hFA : realWidthField.toSubfield = (widthAnchorExtension q).toSubfield := by
    have h := congrArg IntermediateField.toSubfield (realWidthField_eq_width_anchor q hq)
    exact h
  have hFD : realWidthField.toSubfield ≤ D.toSubfield := by
    rw [hFA]
    intro z hz
    exact IntermediateField.algebraMap_mem ((widthAnchorExtension q)⟮I⟯)
      (⟨z,hz⟩ : widthAnchorExtension q)
  have hMD : gaussianZeroExtension.toSubfield ≤ D.toSubfield := by
    rw [gaussianZeroExtension_eq_realWidth_adjoin]
    change (realWidthField⟮I⟯).toSubfield ≤ D.toSubfield
    rw [IntermediateField.adjoin_toSubfield]
    apply Subfield.closure_le.mpr
    rintro z (⟨a,rfl⟩ | hz)
    · exact hFD a.property
    · have he : z = I := Set.mem_singleton_iff.mp hz
      rw [he]
      exact IntermediateField.mem_adjoin_simple_self (widthAnchorExtension q) I
  have hDM : D.toSubfield ≤ gaussianZeroExtension.toSubfield := by
    change ((widthAnchorExtension q)⟮I⟯).toSubfield ≤ gaussianZeroExtension.toSubfield
    rw [IntermediateField.adjoin_toSubfield]
    apply Subfield.closure_le.mpr
    rintro z (⟨a,rfl⟩ | hz)
    · apply realWidthField_le_gaussian
      change (a : ℂ) ∈ realWidthField.toSubfield
      rw [hFA]
      exact a.property
    · have he : z = I := Set.mem_singleton_iff.mp hz
      rw [he]
      exact gaussianUnit.property
  apply le_antisymm
  · exact hMD
  · exact hDM

/-- A width absent from the even products forces relative degree four for the full zero field. -/
theorem evenGaussianZeroExtension_finrank_four (q : XiZeroCopy)
    (hq : zeroWidth q ∉ evenWidthField) :
    Module.finrank evenWidthField evenGaussianZeroExtension = 4 := by
  have hq0 : zeroWidth q ≠ 0 := by
    intro h
    exact hq (by rw [h]; exact evenWidthField.zero_mem)
  exact (field_finrank_congr (evenGaussianZeroExtension_eq_width_tower q hq0)).trans
    ((field_finrank_restrict ((widthAnchorExtension q)⟮I⟯)).trans
      (width_biquadratic_tower_degree q hq))

private theorem width_nonzero_of_not_mem (q : XiZeroCopy) (hq : zeroWidth q ∉ evenWidthField) :
    zeroWidth q ≠ 0 := by
  intro h
  exact hq (by rw [h]; exact evenWidthField.zero_mem)

/-- All base-field square roots in the full zero field lie on the four biquadratic lines. -/
theorem evenSquareRootLines (q : XiZeroCopy) (hq : zeroWidth q ∉ evenWidthField)
    (z : gaussianZeroExtension) (hz : (z : ℂ)*(z : ℂ) ∈ evenWidthField) :
    (z : ℂ) ∈ evenWidthField ∨
      (∃ a : evenWidthField, (z : ℂ) = (a : ℂ)*zeroWidth q) ∨
      (∃ a : evenWidthField, (z : ℂ) = (a : ℂ)*I) ∨
      (∃ a : evenWidthField, (z : ℂ) = (a : ℂ)*(I*zeroWidth q)) := by
  have hline (x : realWidthField) (hxx : (x : ℂ)*(x : ℂ) ∈ evenWidthField) :
      (x : ℂ) ∈ evenWidthField ∨ ∃ a : evenWidthField, (x : ℂ) = (a : ℂ)*zeroWidth q := by
    have hx : (x : ℂ) ∈ evenWidthField⟮zeroWidth q⟯ := by
      have hmem (u : ℂ) : u ∈ realWidthField ↔ u ∈ evenWidthField⟮zeroWidth q⟯ := by
        rw [realWidthField_eq_width_anchor q (width_nonzero_of_not_mem q hq)]
        rfl
      exact (hmem (x : ℂ)).mp x.property
    exact quadratic_square_root_line evenWidthField.toSubfield
      (zeroWidth_mul_mem_evenWidthField q q) hq hx hxx
  obtain ⟨a,b,hab⟩ := gaussian_element_realWidth_repr z
  obtain ⟨ar,har⟩ := realWidthField_le_real a.property
  obtain ⟨br,hbr⟩ := realWidthField_le_real b.property
  obtain ⟨r,hr⟩ := evenWidthField_le_real hz
  have him : ((z : ℂ)*(z : ℂ)).im = 0 := by rw [← hr]; rfl
  rw [hab,← har,← hbr] at him
  have hab0 : (a : ℂ)*(b : ℂ) = 0 := by
    have him' : ar*br+br*ar = 0 := by simpa [Complex.mul_im] using him
    have hp : 2*(ar*br) = 0 := by nlinarith only [him']
    have hp0 : ar*br = 0 := (mul_eq_zero.mp hp).resolve_left (by norm_num)
    rw [← har,← hbr,← map_mul,hp0,map_zero]
  rcases mul_eq_zero.mp hab0 with ha | hb
  · have hzb : (z : ℂ) = (b : ℂ)*I := by simpa only [ha,zero_add] using hab
    have hbb : (b : ℂ)*(b : ℂ) = -((z : ℂ)*(z : ℂ)) := by
      rw [hzb]
      calc
        _ = -((b : ℂ)*(b : ℂ)*(I*I)) := by rw [I_mul_I]; ring
        _ = _ := by ring
    have hbbE : (b : ℂ)*(b : ℂ) ∈ evenWidthField := by
      rw [hbb]
      exact evenWidthField.neg_mem hz
    rcases hline b hbbE with hbE | ⟨k,hk⟩
    · exact Or.inr (Or.inr (Or.inl ⟨⟨b,hbE⟩,hzb⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨k,by rw [hzb,hk]; ring⟩))
  · have hza : (z : ℂ) = (a : ℂ) := by simpa only [hb,zero_mul,add_zero] using hab
    have haaE : (a : ℂ)*(a : ℂ) ∈ evenWidthField := by rwa [hza] at hz
    rcases hline a haaE with haE | ⟨k,hk⟩
    · exact Or.inl (by rw [hza]; exact haE)
    · exact Or.inr (Or.inl ⟨k,hza.trans hk⟩)

/-- Every quadratic subfield of the entire Gaussian zero field is one of the three geometric fields. -/
theorem quadratic_subfield_classification (q : XiZeroCopy)
    (hq : zeroWidth q ∉ evenWidthField) (N : IntermediateField evenWidthField ℂ)
    (hNM : N ≤ evenGaussianZeroExtension) (hN : Module.finrank evenWidthField N = 2) :
    N = evenWidthField⟮zeroWidth q⟯ ∨ N = evenWidthField⟮I⟯ ∨
      N = evenWidthField⟮I*zeroWidth q⟯ := by
  obtain ⟨r,hrN,hrE,hrr,hNr⟩ :=
    quadratic_subfield_square_generator evenWidthField.toSubfield N hN
  have hrM : r ∈ gaussianZeroExtension := hNM hrN
  have hscale (a : evenWidthField) (u : ℂ) (he : r = (a : ℂ)*u) :
      N = evenWidthField⟮u⟯ := by
    have ha : (a : ℂ) ≠ 0 := by
      intro ha0
      apply hrE
      rw [he,ha0,zero_mul]
      exact evenWidthField.zero_mem
    rw [hNr,he]
    exact adjoin_nonzero_base_mul evenWidthField.toSubfield a ha u
  rcases evenSquareRootLines q hq ⟨r,hrM⟩ hrr with h | ⟨a,ha⟩ | ⟨a,ha⟩ | ⟨a,ha⟩
  · exact False.elim (hrE h)
  · exact Or.inl (hscale a (zeroWidth q) ha)
  · exact Or.inr (Or.inl (hscale a I ha))
  · exact Or.inr (Or.inr (hscale a (I*zeroWidth q) ha))

private theorem gaussian_adjoin_real_mem (E : Subfield ℂ)
    (hE : E ≤ Complex.ofRealHom.fieldRange) {z : ℂ}
    (hz : z ∈ E⟮I⟯) (hzreal : z ∈ Complex.ofRealHom.fieldRange) : z ∈ E := by
  obtain ⟨a,b,hab⟩ := HTGeometry.exists_repr_of_mem_adjoin_sqrt
    (show I*I = algebraMap E ℂ (-1) by rw [I_mul_I,map_neg,map_one]) hz
  change z = (a : ℂ)+(b : ℂ)*I at hab
  obtain ⟨ar,har⟩ := hE a.property
  obtain ⟨br,hbr⟩ := hE b.property
  obtain ⟨r,hr⟩ := hzreal
  have him := congrArg Complex.im hab
  rw [← har,← hbr,← hr] at him
  have hb : br = 0 := by simpa using him.symm
  rw [← hbr,hb,map_zero,zero_mul,add_zero] at hab
  rw [hab]
  exact a.property

private theorem imaginary_width_not_real (q : XiZeroCopy) (hq : zeroWidth q ≠ 0) :
    I*zeroWidth q ∉ Complex.ofRealHom.fieldRange := by
  rintro ⟨r,hr⟩
  have h := congrArg Complex.im hr
  have hw : (xiSpectralPoint q).im = 0 := by simpa [zeroWidth] using h.symm
  exact hq (by simp only [zeroWidth,hw,ofReal_zero])

/-- The degree-two subfields are exactly three distinct fields, all inside the full Gaussian field. -/
theorem biquadratic_quadratic_fields (q : XiZeroCopy) (hq : zeroWidth q ∉ evenWidthField) :
    let A := evenWidthField⟮zeroWidth q⟯
    let B := evenWidthField⟮I⟯
    let C := evenWidthField⟮I*zeroWidth q⟯
    A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
      ∀ N : IntermediateField evenWidthField ℂ,
        (N ≤ evenGaussianZeroExtension ∧ Module.finrank evenWidthField N = 2) ↔
          N = A ∨ N = B ∨ N = C := by
  dsimp only
  have hq0 := width_nonzero_of_not_mem q hq
  have hδB : zeroWidth q ∉ evenWidthField⟮I⟯ := by
    intro h
    exact hq (gaussian_adjoin_real_mem evenWidthField.toSubfield evenWidthField_le_real h
      ⟨(xiSpectralPoint q).im,rfl⟩)
  have hAB : evenWidthField⟮zeroWidth q⟯ ≠ evenWidthField⟮I⟯ := by
    intro he
    apply hδB
    rw [← he]
    exact IntermediateField.mem_adjoin_simple_self evenWidthField (zeroWidth q)
  have hAC : evenWidthField⟮zeroWidth q⟯ ≠ evenWidthField⟮I*zeroWidth q⟯ := by
    intro he
    have hm : I*zeroWidth q ∈ widthAnchorExtension q := by
      change I*zeroWidth q ∈ evenWidthField⟮zeroWidth q⟯
      rw [he]
      exact IntermediateField.mem_adjoin_simple_self evenWidthField (I*zeroWidth q)
    exact imaginary_width_not_real q hq0 (widthAnchorExtension_le_real q hm)
  have hBC : evenWidthField⟮I⟯ ≠ evenWidthField⟮I*zeroWidth q⟯ := by
    intro he
    have hm : I*zeroWidth q ∈ evenWidthField⟮I⟯ := by
      rw [he]
      exact IntermediateField.mem_adjoin_simple_self evenWidthField (I*zeroWidth q)
    apply hδB
    have hd : zeroWidth q = (I*zeroWidth q)/I := by
      apply (eq_div_iff I_ne_zero).mpr
      exact mul_comm _ _
    rw [hd]
    exact (evenWidthField⟮I⟯).div_mem hm
      (IntermediateField.mem_adjoin_simple_self evenWidthField I)
  refine ⟨hAB,hAC,hBC,fun N => ⟨fun h => quadratic_subfield_classification q hq N h.1 h.2,?_⟩⟩
  rintro (rfl | rfl | rfl)
  · refine ⟨IntermediateField.adjoin_simple_le_iff.mpr ?_,
      (realWidthField_anchor_quadratic q hq).2⟩
    exact realWidthField_le_gaussian (zeroWidth_mem_realWidthField q)
  · refine ⟨IntermediateField.adjoin_simple_le_iff.mpr gaussianUnit.property,?_⟩
    apply gaussian_adjoin_degree_two
    intro a
    obtain ⟨r,hr⟩ := evenWidthField_le_real a.property
    change (a : ℂ).im = 0
    rw [← hr]
    rfl
  · refine ⟨IntermediateField.adjoin_simple_le_iff.mpr ?_,?_⟩
    · rw [← zeroImaginaryOffset_eq]
      exact zeroExtension_le_gaussian (zeroImaginaryOffset_mem q)
    · have h := (zeroExtension_width_anchor_quadratic q hq0).2
      rwa [zeroImaginaryOffset_eq] at h

/-- If widths already lie in their even field, only the Gaussian quadratic step remains. -/
theorem evenGaussian_eq_adjoin_of_realWidth_eq (h : realWidthField = evenWidthField) :
    evenGaussianZeroExtension = evenWidthField⟮I⟯ := by
  ext z
  change z ∈ gaussianZeroExtension ↔ z ∈ evenWidthField⟮I⟯
  rw [gaussianZeroExtension_eq_realWidth_adjoin,h]
  rfl

/-- Above the entire even-width field, the Gaussian zero field is always quadratic or biquadratic. -/
theorem gaussian_even_width_dichotomy :
    (realWidthField = evenWidthField ∧
      evenGaussianZeroExtension = evenWidthField⟮I⟯ ∧
      Module.finrank evenWidthField evenGaussianZeroExtension = 2) ∨
    (∃ q : XiZeroCopy, zeroWidth q ∉ evenWidthField ∧
      Module.finrank evenWidthField evenGaussianZeroExtension = 4) := by
  classical
  by_cases he : realWidthField = evenWidthField
  · refine Or.inl ⟨he,evenGaussian_eq_adjoin_of_realWidth_eq he,?_⟩
    apply (field_finrank_congr (evenGaussian_eq_adjoin_of_realWidth_eq he)).trans
    apply gaussian_adjoin_degree_two
    intro a
    obtain ⟨r,hr⟩ := evenWidthField_le_real a.property
    change (a : ℂ).im = 0
    rw [← hr]
    rfl
  · have hex : ∃ q : XiZeroCopy, zeroWidth q ∉ evenWidthField := by
      by_contra h
      push Not at h
      have hle : realWidthField ≤ evenWidthField := by
        apply IntermediateField.adjoin_le_iff.mpr
        rintro z ⟨q,rfl⟩
        exact h q
      exact he (le_antisymm hle evenWidthField_le_realWidthField)
    obtain ⟨q,hq⟩ := hex
    exact Or.inr ⟨q,hq,evenGaussianZeroExtension_finrank_four q hq⟩

/-- The complete Gaussian zero field has relative degree exactly two or four over its even widths. -/
theorem gaussian_even_width_degree :
    Module.finrank evenWidthField evenGaussianZeroExtension = 2 ∨
      Module.finrank evenWidthField evenGaussianZeroExtension = 4 := by
  rcases gaussian_even_width_dichotomy with ⟨_,_,h⟩ | ⟨q,_,h⟩
  · exact Or.inl h
  · exact Or.inr h

end GaloisForLFunctions.GaloisTheoryOfZeros

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.evenGaussianZeroExtension_finrank_four
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.quadratic_subfield_classification

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.biquadratic_quadratic_fields

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.gaussian_even_width_dichotomy

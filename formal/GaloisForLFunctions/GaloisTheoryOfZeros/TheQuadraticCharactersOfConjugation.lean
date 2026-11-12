import GaloisForLFunctions.GaloisTheoryOfZeros.TheDescentOfTheGlobalWidthSquareClass

/-!
# Quadratic characters that detect centered conjugation

Every continuous quadratic character detecting conjugation acts on a nonzero
purely imaginary source square root. Such a character exists exactly when the
whole width restriction splits and some width is nonzero. Restriction and a
detecting character give the full Galois group as a topological direct product,
with conjugation in its independent sign factor.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower
open scoped IntermediateField
namespace GaloisForLFunctions.GaloisTheoryOfZeros

private theorem sign_cast_injective {L : Type*} [Field L] [CharZero L] :
    Function.Injective (fun u : ℤˣ => ((u : ℤ) : L)) := by
  intro u v h
  apply Units.ext
  exact Int.cast_injective h

private def sourceRootSignValue {K L : Type*} [Field K] [Field L] [Algebra K L]
    (b : L) (σ : L ≃ₐ[K] L) : ℤˣ := by
  classical
  exact if σ b = b then 1 else -1

private theorem sourceRootSignValue_action {K L : Type*} [Field K] [Field L] [Algebra K L]
    (b : L) (a : K) (hs : b^2 = algebraMap K L a) (σ : L ≃ₐ[K] L) :
    σ b = ((sourceRootSignValue b σ : ℤ) : L)*b := by
  classical
  have hsq : (σ b)^2 = b^2 := by
    rw [← map_pow,hs,σ.commutes]
  by_cases h : σ b = b
  · rw [sourceRootSignValue,if_pos h,Units.val_one,Int.cast_one,one_mul]
    exact h
  · have hn := (sq_eq_sq_iff_eq_or_eq_neg.mp hsq).resolve_left h
    rw [sourceRootSignValue,if_neg h,Units.val_neg,Units.val_one,
      Int.cast_neg,Int.cast_one,neg_one_mul]
    exact hn

/-- The sign by which a source automorphism acts on a nonzero source square root. -/
def sourceRootSign {K L : Type*} [Field K] [Field L] [CharZero L] [Algebra K L]
    (b : L) (a : K) (hs : b^2 = algebraMap K L a) (hb : b ≠ 0) :
    (L ≃ₐ[K] L) →* ℤˣ where
  toFun := sourceRootSignValue b
  map_one' := by simp [sourceRootSignValue]
  map_mul' σ τ := by
    apply sign_cast_injective (L := L)
    apply mul_right_cancel₀ hb
    calc
      ((sourceRootSignValue b (σ*τ) : ℤ) : L)*b = (σ*τ) b :=
        (sourceRootSignValue_action b a hs (σ*τ)).symm
      _ = σ (τ b) := rfl
      _ = σ (((sourceRootSignValue b τ : ℤ) : L)*b) :=
        congrArg σ (sourceRootSignValue_action b a hs τ)
      _ = (((sourceRootSignValue b σ*sourceRootSignValue b τ : ℤˣ) : ℤ) : L)*b := by
        rw [map_mul,map_intCast,sourceRootSignValue_action b a hs σ]
        simp only [Units.val_mul,Int.cast_mul]
        ring

/-- The quadratic character acts on its defining radical by its sign. -/
theorem sourceRootSign_action {K L : Type*} [Field K] [Field L] [CharZero L] [Algebra K L]
    (b : L) (a : K) (hs : b^2 = algebraMap K L a) (hb : b ≠ 0) (σ : L ≃ₐ[K] L) :
    σ b = ((sourceRootSign b a hs hb σ : ℤ) : L)*b :=
  sourceRootSignValue_action b a hs σ

/-- The character kernel is the stabilizer of its radical. -/
theorem sourceRootSign_eq_one_iff {K L : Type*} [Field K] [Field L] [CharZero L] [Algebra K L]
    (b : L) (a : K) (hs : b^2 = algebraMap K L a) (hb : b ≠ 0) (σ : L ≃ₐ[K] L) :
    sourceRootSign b a hs hb σ = 1 ↔ σ b = b := by
  classical
  change (if σ b = b then (1 : ℤˣ) else -1) = 1 ↔ σ b = b
  by_cases h : σ b = b
  · simp [h]
  · simp only [h,ite_false,iff_false]
    intro he
    have hi := congrArg (fun u : ℤˣ => (u : ℤ)) he
    norm_num at hi

/-- A source square-root character is continuous for the full Krull topology. -/
theorem sourceRootSign_continuous {K L : Type*} [Field K] [Field L] [CharZero L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (b : L) (a : K) (hs : b^2 = algebraMap K L a) (hb : b ≠ 0) :
    Continuous (sourceRootSign b a hs hb) := by
  apply continuous_of_continuousAt_one (sourceRootSign b a hs hb)
  have hfix : ∀ᶠ σ in nhds (1 : L ≃ₐ[K] L), σ b = b :=
    (stabilizer_isOpen_of_isIntegral (K := K) (L := L) b).mem_nhds (Subgroup.one_mem _)
  have h : ∀ᶠ σ in nhds (1 : L ≃ₐ[K] L), sourceRootSign b a hs hb σ = 1 :=
    hfix.mono fun σ hσ => (sourceRootSign_eq_one_iff b a hs hb σ).mpr hσ
  change Filter.Tendsto (sourceRootSign b a hs hb) _ (nhds (sourceRootSign b a hs hb 1))
  rw [map_one]
  exact tendsto_const_nhds.congr' (h.mono fun σ hσ => hσ.symm)

private theorem centered_conjugation_involutive (b : fullFibreZeroExtension) :
    fullFibreZeroConjugation (fullFibreZeroConjugation b) = b := by
  apply Subtype.ext
  exact star_star (b : ℂ)

private theorem centered_conjugation_commutes
    (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension)
    (b : fullFibreZeroExtension) :
    σ (fullFibreZeroConjugation b) = fullFibreZeroConjugation (σ b) :=
  congrArg (fun τ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension => τ b)
    (fullFibreZeroConjugation_central σ)

/-- Every continuous character detecting conjugation has an explicit imaginary eigenradical. -/
theorem centered_character_has_radical
    (χ : (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) →* ℤˣ)
    (hχ : Continuous χ) (hc : χ fullFibreZeroConjugation = -1) :
    ∃ b : fullFibreZeroExtension, b ≠ 0 ∧ fullFibreZeroConjugation b = -b ∧
      (∃ a : fullFibreSourceField, b^2 = algebraMap fullFibreSourceField fullFibreZeroExtension a) ∧
      ∀ σ, σ b = ((χ σ : ℤ) : fullFibreZeroExtension)*b := by
  letI : IsGalois fullFibreSourceField fullFibreZeroExtension := ⟨⟩
  let H : ClosedSubgroup
      (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) :=
    ⟨χ.ker,isClosed_singleton.preimage hχ⟩
  let D : IntermediateField fullFibreSourceField fullFibreZeroExtension :=
    IntermediateField.fixedField H.toSubgroup
  have hnot : fullFibreZeroConjugation ∉ D.fixingSubgroup := by
    rw [show D.fixingSubgroup = H.toSubgroup from InfiniteGalois.fixingSubgroup_fixedField H]
    intro h
    have he : χ fullFibreZeroConjugation = 1 := h
    rw [hc] at he
    have hi := congrArg (fun u : ℤˣ => (u : ℤ)) he
    norm_num at hi
  obtain ⟨d,hd,hcd⟩ : ∃ d : fullFibreZeroExtension, d ∈ D ∧
      fullFibreZeroConjugation d ≠ d := by
    by_contra! h
    exact hnot ((IntermediateField.mem_fixingSubgroup_iff _ _).mpr h)
  let b := d-fullFibreZeroConjugation d
  have hb : b ≠ 0 := by
    exact sub_ne_zero.mpr hcd.symm
  have hcb : fullFibreZeroConjugation b = -b := by
    dsimp only [b]
    rw [map_sub,centered_conjugation_involutive]
    ring
  have hker (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension)
      (hσ : χ σ = 1) : σ b = b := by
    have hσd : σ d = d := (IntermediateField.mem_fixedField_iff _ _).mp hd σ hσ
    dsimp only [b]
    rw [map_sub,centered_conjugation_commutes,hσd]
  have heigen (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) :
      σ b = ((χ σ : ℤ) : fullFibreZeroExtension)*b := by
    rcases Int.units_eq_one_or (χ σ) with hplus | hminus
    · rw [hplus,Units.val_one,Int.cast_one,one_mul]
      exact hker σ hplus
    · have hσc : χ (σ*fullFibreZeroConjugation) = 1 := by
        rw [map_mul,hminus,hc]; simp
      have he := hker (σ*fullFibreZeroConjugation) hσc
      change σ (fullFibreZeroConjugation b) = b at he
      rw [hcb,map_neg] at he
      rw [hminus,Units.val_neg,Units.val_one,Int.cast_neg,Int.cast_one,neg_one_mul]
      exact neg_eq_iff_eq_neg.mp he
  have hfixed : ∀ σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension,
      σ (b^2) = b^2 := by
    intro σ
    rw [map_pow,heigen]
    rcases Int.units_eq_one_or (χ σ) with h | h <;>
      rw [h] <;> norm_num
  exact ⟨b,hb,hcb,(InfiniteGalois.mem_range_algebraMap_iff_fixed (b^2)).mpr hfixed |>.imp
    (fun a ha => ha.symm),heigen⟩

/-- Eigenradicals for one character differ by a nonzero source scalar. -/
theorem centered_character_radical_unique
    (χ : (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) →* ℤˣ)
    (b d : fullFibreZeroExtension) (hb : b ≠ 0) (hd : d ≠ 0)
    (he : ∀ σ, σ b = ((χ σ : ℤ) : fullFibreZeroExtension)*b)
    (hf : ∀ σ, σ d = ((χ σ : ℤ) : fullFibreZeroExtension)*d) :
    ∃ a : fullFibreSourceFieldˣ,
      d = algebraMap fullFibreSourceField fullFibreZeroExtension (a : fullFibreSourceField)*b := by
  letI : IsGalois fullFibreSourceField fullFibreZeroExtension := ⟨⟩
  have hfix : ∀ σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension,
      σ (d/b) = d/b := by
    intro σ
    rw [map_div₀,hf,he]
    rcases Int.units_eq_one_or (χ σ) with h | h <;> rw [h] <;> norm_num
  obtain ⟨a,ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (d/b)).mpr hfix
  have ha0 : a ≠ 0 := by
    intro h
    rw [h,map_zero] at ha
    exact (div_ne_zero hd hb) ha.symm
  refine ⟨Units.mk0 a ha0,?_⟩
  change d = algebraMap fullFibreSourceField fullFibreZeroExtension a*b
  rw [ha,div_mul_cancel₀ _ hb]

private theorem fixing_simple_eq_stabilizer {K L : Type*} [Field K] [Field L] [Algebra K L]
    (b : L) : (K⟮b⟯).fixingSubgroup = MulAction.stabilizer (L ≃ₐ[K] L) b := by
  apply le_antisymm
  · intro σ hσ
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ b
      (IntermediateField.mem_adjoin_simple_self K b)
  · apply (IntermediateField.le_iff_le _ _).mp
    apply IntermediateField.adjoin_simple_le_iff.mpr
    rw [IntermediateField.mem_fixedField_iff]
    exact fun σ hσ => hσ

/-- The fixed field of a source square-root character is its entire radical extension. -/
theorem sourceRootSign_fixedField {K L : Type*} [Field K] [Field L] [CharZero L] [Algebra K L]
    [IsGalois K L] (b : L) (a : K) (hs : b^2 = algebraMap K L a) (hb : b ≠ 0) :
    IntermediateField.fixedField (sourceRootSign b a hs hb).ker = K⟮b⟯ := by
  have hker : (sourceRootSign b a hs hb).ker = (K⟮b⟯).fixingSubgroup := by
    rw [fixing_simple_eq_stabilizer]
    ext σ
    exact sourceRootSign_eq_one_iff b a hs hb σ
  rw [hker,InfiniteGalois.fixedField_fixingSubgroup]

/-- The action on one nonzero radical determines its sign character uniquely. -/
theorem sourceRootSign_eq_of_action {K L : Type*} [Field K] [Field L] [CharZero L] [Algebra K L]
    (b : L) (a : K) (hs : b^2 = algebraMap K L a) (hb : b ≠ 0)
    (χ : (L ≃ₐ[K] L) →* ℤˣ) (he : ∀ σ, σ b = ((χ σ : ℤ) : L)*b) :
    sourceRootSign b a hs hb = χ := by
  apply MonoidHom.ext
  intro σ
  apply sign_cast_injective (L := L)
  apply mul_right_cancel₀ hb
  exact (sourceRootSign_action b a hs hb σ).symm.trans (he σ)

/-- A detecting character cuts out exactly an imaginary quadratic source field. -/
theorem centered_character_quadratic_field
    (χ : (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) →* ℤˣ)
    (hχ : Continuous χ) (hc : χ fullFibreZeroConjugation = -1) :
    ∃ (b : fullFibreZeroExtension) (a : fullFibreSourceField), b ≠ 0 ∧
      fullFibreZeroConjugation b = -b ∧ b^2 = algebraMap fullFibreSourceField fullFibreZeroExtension a ∧
      IntermediateField.fixedField χ.ker = fullFibreSourceField⟮b⟯ ∧
      Module.finrank fullFibreSourceField fullFibreSourceField⟮b⟯ = 2 := by
  letI : IsGalois fullFibreSourceField fullFibreZeroExtension := ⟨⟩
  obtain ⟨b,hb,hcb,⟨a,hs⟩,he⟩ := centered_character_has_radical χ hχ hc
  refine ⟨b,a,hb,hcb,hs,?_,?_⟩
  · rw [← sourceRootSign_eq_of_action b a hs hb χ he]
    exact sourceRootSign_fixedField b a hs hb
  · apply HTGeometry.finrank_adjoin_eq_two (by simpa only [pow_two] using hs)
    rintro ⟨d,hd⟩
    have hfix : fullFibreZeroConjugation b = b := by
      rw [← hd]
      exact fullFibreZeroConjugation.commutes d
    have hb0 : b = 0 := by
      have hh : b = -b := hfix.symm.trans hcb
      linear_combination (1/2 : fullFibreZeroExtension)*hh
    exact hb hb0

private def centeredWidthOffset (q : XiZeroCopy) : fullFibreZeroExtension :=
  ⟨zeroImaginaryOffset q,zeroImaginaryOffset_mem q⟩

private theorem centeredWidthOffset_conjugation (q : XiZeroCopy) :
    fullFibreZeroConjugation (centeredWidthOffset q) = -centeredWidthOffset q := by
  apply Subtype.ext
  change (starRingEnd ℂ) (zeroImaginaryOffset q) = -zeroImaginaryOffset q
  rw [zeroImaginaryOffset_eq]
  simp only [zeroWidth,map_mul,Complex.conj_ofReal,Complex.conj_I,neg_mul]

private theorem centeredWidthOffset_ne_zero (q : XiZeroCopy) (hq : zeroWidth q ≠ 0) :
    centeredWidthOffset q ≠ 0 := by
  intro h
  have he := congrArg (fun b : fullFibreZeroExtension => (b : ℂ)) h
  change zeroImaginaryOffset q = 0 at he
  rw [zeroImaginaryOffset_eq] at he
  exact (mul_ne_zero I_ne_zero hq) he

private theorem centeredWidthOffset_sq (q : XiZeroCopy) :
    zeroImaginaryOffset q ^ 2 = -(zeroWidth q ^ 2) := by
  rw [zeroImaginaryOffset_eq,mul_pow]
  have hi : I^2 = -1 := by simpa only [pow_two] using I_mul_I
  rw [hi,neg_one_mul]

private theorem real_of_conj_eq (z : ℂ) (hz : (starRingEnd ℂ) z = z) :
    z ∈ Complex.ofRealHom.fieldRange := by
  have him := congrArg Complex.im hz
  change -z.im = z.im at him
  refine ⟨z.re,?_⟩
  apply Complex.ext
  · rfl
  · change 0 = z.im
    linarith only [him]

/-- Ratios of imaginary anti-invariants lie in the exact even-width field. -/
theorem centered_imaginary_ratio_mem_even
    (b d : fullFibreZeroExtension)
    (hb : fullFibreZeroConjugation b = -b) (hd : fullFibreZeroConjugation d = -d) :
    (b : ℂ)/(d : ℂ) ∈ evenWidthField := by
  change (b : ℂ)/(d : ℂ) ∈ evenWidthField.toSubfield
  rw [evenWidthField_eq_real_part]
  refine ⟨fullFibreZeroExtension.div_mem b.property d.property,real_of_conj_eq _ ?_⟩
  have hbC : (starRingEnd ℂ) (b : ℂ) = -(b : ℂ) :=
    congrArg (fun z : fullFibreZeroExtension => (z : ℂ)) hb
  have hdC : (starRingEnd ℂ) (d : ℂ) = -(d : ℂ) :=
    congrArg (fun z : fullFibreZeroExtension => (z : ℂ)) hd
  rw [map_div₀,hbC,hdC,neg_div_neg_eq]

/-- A nonzero imaginary source square root descends every nonzero width square. -/
theorem widthSquareDescends_of_imaginary_source_root
    (b : fullFibreZeroExtension) (hb : b ≠ 0)
    (hc : fullFibreZeroConjugation b = -b)
    (a : fullFibreSourceField) (hs : b^2 = algebraMap fullFibreSourceField fullFibreZeroExtension a)
    (q : XiZeroCopy) (hq : zeroWidth q ≠ 0) : WidthSquareDescends q := by
  have hbC : (b : ℂ) ≠ 0 := fun h => hb (Subtype.ext h)
  have hoC : zeroImaginaryOffset q ≠ 0 :=
    fun h => centeredWidthOffset_ne_zero q hq (Subtype.ext h)
  have hsC : (b : ℂ)^2 = (a : ℂ) :=
    congrArg (fun z : fullFibreZeroExtension => (z : ℂ)) hs
  have ha : a ≠ 0 := by
    intro h
    rw [h,map_zero] at hs
    exact (pow_ne_zero 2 hb) hs
  let v := (b : ℂ)/zeroImaginaryOffset q
  have hv : v ≠ 0 := div_ne_zero hbC hoC
  have hvE : v ∈ evenWidthField :=
    centered_imaginary_ratio_mem_even b (centeredWidthOffset q) hc
      (centeredWidthOffset_conjugation q)
  let u : evenWidthInReal :=
    ⟨⟨v⁻¹,evenWidthField_le_realWidthField (evenWidthField.inv_mem hvE)⟩,
      evenWidthField.inv_mem hvE⟩
  have hu : u ≠ 0 := by
    intro h
    exact (inv_ne_zero hv) (congrArg (fun z : evenWidthInReal => ((z : realWidthField) : ℂ)) h)
  refine ⟨Units.mk0 (-a) (neg_ne_zero.mpr ha),Units.mk0 u hu,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change zeroWidth q^2 = -(a : ℂ)*(((b : ℂ)/zeroImaginaryOffset q)⁻¹)^2
  rw [← hsC,inv_div]
  calc
    zeroWidth q^2 = -(zeroImaginaryOffset q)^2 := by rw [centeredWidthOffset_sq,neg_neg]
    _ = -((b : ℂ)^2)*(zeroImaginaryOffset q/(b : ℂ))^2 := by field_simp

/-- Descent produces a purely imaginary square root of a nonzero source element inside the full zero field. -/
theorem imaginary_source_root_of_widthSquareDescends
    (q : XiZeroCopy) (hq : zeroWidth q ≠ 0) (hd : WidthSquareDescends q) :
    ∃ (b : fullFibreZeroExtension) (a : fullFibreSourceField), b ≠ 0 ∧
      fullFibreZeroConjugation b = -b ∧
      b^2 = algebraMap fullFibreSourceField fullFibreZeroExtension a := by
  obtain ⟨a,u,hu⟩ := hd
  let v : fullFibreZeroExtension :=
    ⟨(((u : evenWidthInReal) : realWidthField) : ℂ),
      evenWidthField_le_zeroExtension (u : evenWidthInReal).property⟩
  have hv : v ≠ 0 := by
    intro h
    apply u.ne_zero
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : fullFibreZeroExtension => (z : ℂ)) h
  have hcv : fullFibreZeroConjugation v = v := by
    apply Subtype.ext
    obtain ⟨r,hr⟩ := evenWidthField_le_real (u : evenWidthInReal).property
    change (starRingEnd ℂ) (v : ℂ) = (v : ℂ)
    rw [show (v : ℂ) = (r : ℂ) from hr.symm]
    exact Complex.conj_ofReal r
  let b := centeredWidthOffset q/v
  refine ⟨b,-(a : fullFibreSourceField),div_ne_zero (centeredWidthOffset_ne_zero q hq) hv,?_,?_⟩
  · dsimp only [b]
    rw [map_div₀,centeredWidthOffset_conjugation,hcv,neg_div]
  · have he := congrArg (fun z : evenWidthInReal => ((z : realWidthField) : ℂ)) hu
    change zeroWidth q^2 = ((a : fullFibreSourceField) : ℂ)*(v : ℂ)^2 at he
    apply Subtype.ext
    change (zeroImaginaryOffset q/(v : ℂ))^2 = -((a : fullFibreSourceField) : ℂ)
    rw [div_pow,centeredWidthOffset_sq,he]
    apply (div_eq_iff (pow_ne_zero 2 (fun h => hv (Subtype.ext h)))).mpr
    ring

private theorem nonzero_width_of_imaginary_element
    (b : fullFibreZeroExtension) (hb : b ≠ 0) (hc : fullFibreZeroConjugation b = -b) :
    ∃ q : XiZeroCopy, zeroWidth q ≠ 0 := by
  by_contra! h
  have hr : ∀ q : XiZeroCopy, (xiSpectralPoint q).im = 0 := by
    intro q
    have he := h q
    change ((xiSpectralPoint q).im : ℂ) = 0 at he
    exact_mod_cast he
  have hLK : fullFibreZeroExtension.toSubfield = fullFibreSourceField := by
    rw [fullFibreZeroExtension_toSubfield]
    exact (fullFibreSourceField_eq_zeroClosure_iff.mpr hr).symm
  let a : fullFibreSourceField :=
    ⟨b,(congrArg (fun E : Subfield ℂ => (b : ℂ) ∈ E) hLK).mp b.property⟩
  have hfix : fullFibreZeroConjugation b = b := fullFibreZeroConjugation.commutes a
  have hb0 : b = 0 := by
    have he : b = -b := hfix.symm.trans hc
    linear_combination (1/2 : fullFibreZeroExtension)*he
  exact hb hb0

/-- All continuous quadratic characters detect conjugation exactly in the descended, nonreal regime. -/
theorem centered_conjugation_quadratic_detection :
    (∃ χ : (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) →* ℤˣ,
      Continuous χ ∧ χ fullFibreZeroConjugation = -1) ↔
      WidthRestrictionSplits ∧ ∃ q : XiZeroCopy, zeroWidth q ≠ 0 := by
  constructor
  · rintro ⟨χ,hχ,hc⟩
    obtain ⟨b,hb,hcb,⟨a,hs⟩,_⟩ := centered_character_has_radical χ hχ hc
    obtain ⟨q,hq⟩ := nonzero_width_of_imaginary_element b hb hcb
    exact ⟨(widthRestrictionSplits_iff_descends q hq).mpr
      (widthSquareDescends_of_imaginary_source_root b hb hcb a hs q hq),q,hq⟩
  · rintro ⟨hs,q,hq⟩
    obtain ⟨b,a,hb,hcb,hba⟩ := imaginary_source_root_of_widthSquareDescends q hq
      ((widthRestrictionSplits_iff_descends q hq).mp hs)
    refine ⟨sourceRootSign b a hba hb,sourceRootSign_continuous b a hba hb,?_⟩
    have hnot : sourceRootSign b a hba hb fullFibreZeroConjugation ≠ 1 := by
      intro h
      have he := (sourceRootSign_eq_one_iff b a hba hb fullFibreZeroConjugation).mp h
      have hb0 : b = 0 := by
        rw [hcb] at he
        linear_combination (-1/2 : fullFibreZeroExtension)*he
      exact hb hb0
    exact (Int.units_eq_one_or _).resolve_left hnot

/-- Nonsplitting makes every continuous quadratic character blind to centered conjugation. -/
theorem centered_quadratic_characters_blind_of_not_split
    (hn : ¬ WidthRestrictionSplits)
    (χ : (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) →* ℤˣ)
    (hχ : Continuous χ) : χ fullFibreZeroConjugation = 1 := by
  rcases Int.units_eq_one_or (χ fullFibreZeroConjugation) with h | h
  · exact h
  · exact False.elim (hn (centered_conjugation_quadratic_detection.mp ⟨χ,hχ,h⟩).1)

/-- The maximal real subfield, internal to the entire centered zero extension. -/
def evenWidthInCentered : IntermediateField fullFibreSourceField fullFibreZeroExtension :=
  evenWidthField.comap (IntermediateField.val fullFibreZeroExtension)

/-- The internal real subfield is the concrete field of all even width products. -/
def evenWidthInCenteredEquiv : evenWidthInCentered ≃ₐ[fullFibreSourceField] evenWidthField :=
  HTGeometry.comapValEquiv evenWidthField_le_zeroExtension

instance evenWidthInCentered_normal : Normal fullFibreSourceField evenWidthInCentered :=
  Normal.of_algEquiv evenWidthInCenteredEquiv.symm

/-- Restriction of the full centered Galois action to its maximal real subfield. -/
def centeredEvenRestriction :
    (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) →*
      (evenWidthInCentered ≃ₐ[fullFibreSourceField] evenWidthInCentered) :=
  AlgEquiv.restrictNormalHom evenWidthInCentered

/-- Conjugation fixes the entire even-width field. -/
theorem centeredEvenRestriction_conjugation :
    centeredEvenRestriction fullFibreZeroConjugation = 1 := by
  apply AlgEquiv.ext
  intro z
  apply Subtype.ext
  have hcomm := AlgEquiv.restrictNormal_commutes fullFibreZeroConjugation evenWidthInCentered z
  refine hcomm.trans ?_
  apply Subtype.ext
  obtain ⟨r,hr⟩ := evenWidthField_le_real z.property
  change (r : ℂ) = ((z : fullFibreZeroExtension) : ℂ) at hr
  change (starRingEnd ℂ) ((z : fullFibreZeroExtension) : ℂ) = ((z : fullFibreZeroExtension) : ℂ)
  rw [← hr]
  exact Complex.conj_ofReal r

/-- Every nonzero imaginary element generates the full centered field over its real part. -/
theorem centered_imaginary_adjoin_top (b : fullFibreZeroExtension) (hb : b ≠ 0)
    (hc : fullFibreZeroConjugation b = -b) : evenWidthInCentered⟮b⟯ = ⊤ := by
  let H : IntermediateField evenWidthInCentered fullFibreZeroExtension := evenWidthInCentered⟮b⟯
  have hroot (q : XiZeroCopy) : centeredZeroInFibreExtension q ∈ H := by
    let r : evenWidthInCentered :=
      ⟨centeredWidthOffset q/b,
        centered_imaginary_ratio_mem_even (centeredWidthOffset q) b
          (centeredWidthOffset_conjugation q) hc⟩
    have hoff : centeredWidthOffset q ∈ H := by
      have he : centeredWidthOffset q = algebraMap evenWidthInCentered fullFibreZeroExtension r*b :=
        (div_mul_cancel₀ _ hb).symm
      rw [he]
      exact H.mul_mem (H.algebraMap_mem r) (IntermediateField.mem_adjoin_simple_self _ _)
    let t : fullFibreSourceField :=
      ⟨((xiSpectralPoint q).re : ℂ),ordinate_mem_fullFibreSourceField q⟩
    have ht : algebraMap fullFibreSourceField fullFibreZeroExtension t ∈ H := by
      rw [IsScalarTower.algebraMap_apply fullFibreSourceField evenWidthInCentered fullFibreZeroExtension]
      exact H.algebraMap_mem _
    have he : centeredZeroInFibreExtension q =
        algebraMap fullFibreSourceField fullFibreZeroExtension t+centeredWidthOffset q := by
      apply Subtype.ext
      change xiSpectralPoint q = ((xiSpectralPoint q).re : ℂ)+zeroImaginaryOffset q
      rw [zeroImaginaryOffset]
      ring
    rw [he]
    exact H.add_mem ht hoff
  have hle : fullFibreZeroExtension ≤
      (H.restrictScalars fullFibreSourceField).map (IntermediateField.val fullFibreZeroExtension) := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro z ⟨q,rfl⟩
    exact ⟨centeredZeroInFibreExtension q,hroot q,rfl⟩
  apply top_unique
  intro z _
  obtain ⟨a,ha,he⟩ := hle z.property
  have haz : a = z := Subtype.ext he
  rwa [haz] at ha

/-- Restriction and a quadratic character provide coordinates on the full centered Galois group. -/
def centeredQuadraticCoordinates
    (χ : (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) →* ℤˣ) :
    (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) →*
      ((evenWidthInCentered ≃ₐ[fullFibreSourceField] evenWidthInCentered) × ℤˣ) :=
  centeredEvenRestriction.prod χ

/-- A character detecting conjugation gives exact direct-product coordinates on the entire zero extension. -/
theorem centeredQuadraticCoordinates_bijective
    (χ : (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) →* ℤˣ)
    (hχ : Continuous χ) (hc : χ fullFibreZeroConjugation = -1) :
    Function.Bijective (centeredQuadraticCoordinates χ) := by
  letI : IsGalois fullFibreSourceField fullFibreZeroExtension := ⟨⟩
  obtain ⟨b,hb,hcb,_,he⟩ := centered_character_has_radical χ hχ hc
  have hgen : evenWidthInCentered ⊔ fullFibreSourceField⟮b⟯ = ⊤ := by
    have h := congrArg (fun A : IntermediateField evenWidthInCentered fullFibreZeroExtension =>
      A.restrictScalars fullFibreSourceField) (centered_imaginary_adjoin_top b hb hcb)
    rw [IntermediateField.restrictScalars_adjoin_eq_sup] at h
    exact h
  constructor
  · apply (MonoidHom.ker_eq_bot_iff (centeredQuadraticCoordinates χ)).mp
    apply le_antisymm _ bot_le
    intro σ hσ
    have hp : centeredEvenRestriction σ = 1 ∧ χ σ = 1 :=
      ⟨congrArg Prod.fst hσ,congrArg Prod.snd hσ⟩
    have hE : σ ∈ evenWidthInCentered.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker]
      exact hp.1
    have hD : σ ∈ (fullFibreSourceField⟮b⟯).fixingSubgroup := by
      have hfix : σ b = b := by rw [he,hp.2,Units.val_one,Int.cast_one,one_mul]
      rw [fixing_simple_eq_stabilizer]
      exact hfix
    have hf : σ ∈ (evenWidthInCentered ⊔ fullFibreSourceField⟮b⟯).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hE,hD⟩
    rwa [hgen,IntermediateField.fixingSubgroup_top] at hf
  · rintro ⟨σ,u⟩
    obtain ⟨τ,hτ⟩ := AlgEquiv.restrictNormalHom_surjective fullFibreZeroExtension σ
    have hτ' : centeredEvenRestriction τ = σ := hτ
    by_cases h : χ τ = u
    · exact ⟨τ,Prod.ext hτ' h⟩
    · refine ⟨τ*fullFibreZeroConjugation,Prod.ext ?_ ?_⟩
      · change centeredEvenRestriction (τ*fullFibreZeroConjugation) = σ
        rw [map_mul,centeredEvenRestriction_conjugation,mul_one,hτ']
      · change χ (τ*fullFibreZeroConjugation) = u
        rw [map_mul,hc]
        rcases Int.units_eq_one_or (χ τ) with ht | ht <;>
          rcases Int.units_eq_one_or u with hu | hu <;> simp_all

/-- The direct-product coordinates preserve the full Krull topology. -/
theorem centeredQuadraticCoordinates_continuous
    (χ : (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) →* ℤˣ)
    (hχ : Continuous χ) : Continuous (centeredQuadraticCoordinates χ) :=
  (InfiniteGalois.restrictNormalHom_continuous evenWidthInCentered).prodMk hχ

/-- A detecting character splits the entire centered Galois group as its real action times the conjugation sign. -/
def centeredQuadraticGaloisEquiv
    (χ : (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) →* ℤˣ)
    (hχ : Continuous χ) (hc : χ fullFibreZeroConjugation = -1) :
    (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) ≃*
      ((evenWidthInCentered ≃ₐ[fullFibreSourceField] evenWidthInCentered) × ℤˣ) :=
  MulEquiv.ofBijective (centeredQuadraticCoordinates χ) (centeredQuadraticCoordinates_bijective χ hχ hc)

/-- The group splitting is also a homeomorphism, with no finiteness of the total field. -/
def centeredQuadraticGaloisHomeomorph
    (χ : (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) →* ℤˣ)
    (hχ : Continuous χ) (hc : χ fullFibreZeroConjugation = -1) :
    (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) ≃ₜ
      ((evenWidthInCentered ≃ₐ[fullFibreSourceField] evenWidthInCentered) × ℤˣ) := by
  letI : IsGalois fullFibreSourceField fullFibreZeroExtension := ⟨⟩
  letI : IsGalois fullFibreSourceField evenWidthInCentered := ⟨⟩
  exact Continuous.homeoOfEquivCompactToT2
    (f := (centeredQuadraticGaloisEquiv χ hχ hc).toEquiv)
    (centeredQuadraticCoordinates_continuous χ hχ)

/-- Centered conjugation occupies exactly the independent sign factor. -/
theorem centeredQuadraticGaloisEquiv_conjugation
    (χ : (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) →* ℤˣ)
    (hχ : Continuous χ) (hc : χ fullFibreZeroConjugation = -1) :
    centeredQuadraticGaloisEquiv χ hχ hc fullFibreZeroConjugation = (1,-1) :=
  Prod.ext centeredEvenRestriction_conjugation hc

end GaloisForLFunctions.GaloisTheoryOfZeros
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.sourceRootSign_continuous
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.centered_character_has_radical
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.centered_character_radical_unique

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.sourceRootSign_fixedField
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.centered_character_quadratic_field
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.centered_imaginary_ratio_mem_even
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthSquareDescends_of_imaginary_source_root
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.imaginary_source_root_of_widthSquareDescends
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.centered_conjugation_quadratic_detection
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.centered_quadratic_characters_blind_of_not_split

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.centered_imaginary_adjoin_top
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.centeredQuadraticCoordinates_bijective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.centeredQuadraticGaloisHomeomorph
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.centeredQuadraticGaloisEquiv_conjugation

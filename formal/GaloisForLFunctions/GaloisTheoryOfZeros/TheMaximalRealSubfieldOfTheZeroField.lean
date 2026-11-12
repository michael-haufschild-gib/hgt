import GaloisForLFunctions.GaloisTheoryOfZeros.TheFieldOfCompleteFibreTraces
import GaloisForLFunctions.HTGeometry.QuadraticRepresentation
import GaloisForLFunctions.HTGeometry.AdjoinInsert
import GaloisForLFunctions.HTGeometry.IntermediateFieldComap
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Subgroup.Center

/-!
# The maximal real subfield of the centered zero field

Pairwise products of signed zero widths generate exactly the maximal real
subfield of the entire centered zero field. This field is normal over the
complete-fibre source. If a width is nonzero, its imaginary offset generates
a quadratic presentation of the whole centered field over that real part.

If some width is nonzero, the field of signed widths is either the even-product
field or a real quadratic extension of it. The first case occurs precisely when the centered
zero field already contains the Gaussian unit. No location or simplicity
hypothesis is imposed on the zero divisor.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower
open scoped IntermediateField

namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- Signed real width in the centered spectral coordinate. -/
def zeroWidth (q : XiZeroCopy) : ℂ := ((xiSpectralPoint q).im : ℂ)

/-- The imaginary displacement from the source-field ordinate. -/
def zeroImaginaryOffset (q : XiZeroCopy) : ℂ :=
  xiSpectralPoint q - ((xiSpectralPoint q).re : ℂ)

theorem zeroImaginaryOffset_eq (q : XiZeroCopy) :
    zeroImaginaryOffset q = I * zeroWidth q := by
  apply Complex.ext <;> simp [zeroImaginaryOffset, zeroWidth]

theorem zeroImaginaryOffset_mem (q : XiZeroCopy) :
    zeroImaginaryOffset q ∈ fullFibreZeroExtension :=
  fullFibreZeroExtension.sub_mem (centeredZeroInFibreExtension q).property
    (fullFibreZeroExtension.algebraMap_mem
      ⟨((xiSpectralPoint q).re : ℂ), ordinate_mem_fullFibreSourceField q⟩)

/-- The field of all pairwise signed-width products over the complete-fibre source. -/
def evenWidthField : IntermediateField fullFibreSourceField ℂ :=
  IntermediateField.adjoin fullFibreSourceField
    (Set.range fun qr : XiZeroCopy × XiZeroCopy => zeroWidth qr.1 * zeroWidth qr.2)

theorem zeroWidth_mul_mem_evenWidthField (q r : XiZeroCopy) :
    zeroWidth q * zeroWidth r ∈ evenWidthField :=
  IntermediateField.subset_adjoin _ _ ⟨(q,r), rfl⟩

/-- Width products lie in the actual centered zero field. -/
theorem evenWidthField_le_zeroExtension : evenWidthField ≤ fullFibreZeroExtension := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨⟨q,r⟩, rfl⟩
  have he : zeroWidth q * zeroWidth r =
      -(zeroImaginaryOffset q * zeroImaginaryOffset r) := by
    rw [zeroImaginaryOffset_eq, zeroImaginaryOffset_eq]
    calc
      _ = -(I*I*(zeroWidth q*zeroWidth r)) := by rw [I_mul_I]; ring
      _ = _ := by ring
  change zeroWidth q * zeroWidth r ∈ fullFibreZeroExtension
  rw [he]
  exact fullFibreZeroExtension.neg_mem (fullFibreZeroExtension.mul_mem
    (zeroImaginaryOffset_mem q) (zeroImaginaryOffset_mem r))

/-- The complete even-width field is real. -/
theorem evenWidthField_le_real :
    evenWidthField.toSubfield ≤ Complex.ofRealHom.fieldRange := by
  rw [evenWidthField, IntermediateField.adjoin_toSubfield]
  apply Subfield.closure_le.mpr
  rintro z (⟨k, rfl⟩ | ⟨⟨q,r⟩, rfl⟩)
  · exact fullFibreSourceField_le_real k.property
  · exact ⟨(xiSpectralPoint q).im*(xiSpectralPoint r).im, by
      simp only [map_mul]; rfl⟩

private theorem ordinate_mem_evenWidthField (q : XiZeroCopy) :
    ((xiSpectralPoint q).re : ℂ) ∈ evenWidthField :=
  evenWidthField.algebraMap_mem
    ⟨((xiSpectralPoint q).re : ℂ), ordinate_mem_fullFibreSourceField q⟩

private theorem width_anchor_formula (q₀ q : XiZeroCopy) (hq₀ : zeroWidth q₀ ≠ 0) :
    zeroImaginaryOffset q =
      (zeroWidth q₀*zeroWidth q / (zeroWidth q₀*zeroWidth q₀)) * zeroImaginaryOffset q₀ := by
  rw [zeroImaginaryOffset_eq, zeroImaginaryOffset_eq]
  field_simp [hq₀]

/-- Any nonzero imaginary offset generates the entire centered field over the width products. -/
theorem zeroExtension_eq_width_anchor (q₀ : XiZeroCopy) (hq₀ : zeroWidth q₀ ≠ 0) :
    fullFibreZeroExtension =
      (evenWidthField⟮zeroImaginaryOffset q₀⟯).restrictScalars fullFibreSourceField := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro z ⟨q, rfl⟩
    have hc : zeroWidth q₀*zeroWidth q / (zeroWidth q₀*zeroWidth q₀) ∈ evenWidthField :=
      evenWidthField.div_mem (zeroWidth_mul_mem_evenWidthField q₀ q)
        (zeroWidth_mul_mem_evenWidthField q₀ q₀)
    have ht : ((xiSpectralPoint q).re : ℂ) ∈
        evenWidthField⟮zeroImaginaryOffset q₀⟯ :=
      IntermediateField.algebraMap_mem (evenWidthField⟮zeroImaginaryOffset q₀⟯)
        (⟨_, ordinate_mem_evenWidthField q⟩ : evenWidthField)
    have hcoef : zeroWidth q₀*zeroWidth q / (zeroWidth q₀*zeroWidth q₀) ∈
        evenWidthField⟮zeroImaginaryOffset q₀⟯ :=
      IntermediateField.algebraMap_mem (evenWidthField⟮zeroImaginaryOffset q₀⟯)
        (⟨_, hc⟩ : evenWidthField)
    have hoff : zeroImaginaryOffset q ∈ evenWidthField⟮zeroImaginaryOffset q₀⟯ := by
      rw [width_anchor_formula q₀ q hq₀]
      exact IntermediateField.mul_mem _ hcoef (IntermediateField.mem_adjoin_simple_self _ _)
    have he : xiSpectralPoint q = ((xiSpectralPoint q).re : ℂ)+zeroImaginaryOffset q := by
      dsimp only [zeroImaginaryOffset]
      ring
    rw [he]
    exact IntermediateField.add_mem _ ht hoff
  · rw [IntermediateField.restrictScalars_adjoin_eq_sup]
    apply sup_le evenWidthField_le_zeroExtension
    apply IntermediateField.adjoin_simple_le_iff.mpr
    exact zeroImaginaryOffset_mem q₀

private theorem width_anchor_square (q₀ : XiZeroCopy) :
    zeroImaginaryOffset q₀ * zeroImaginaryOffset q₀ =
      algebraMap evenWidthField ℂ
        (⟨-(zeroWidth q₀*zeroWidth q₀),
          evenWidthField.neg_mem (zeroWidth_mul_mem_evenWidthField q₀ q₀)⟩ : evenWidthField) := by
  change zeroImaginaryOffset q₀ * zeroImaginaryOffset q₀ = -(zeroWidth q₀*zeroWidth q₀)
  rw [zeroImaginaryOffset_eq]
  calc
    _ = I*I*(zeroWidth q₀*zeroWidth q₀) := by ring
    _ = _ := by rw [I_mul_I]; ring

/-- The pairwise width products generate exactly the maximal real subfield of the zero field. -/
theorem evenWidthField_eq_real_part :
    evenWidthField.toSubfield =
      fullFibreZeroExtension.toSubfield ⊓ Complex.ofRealHom.fieldRange := by
  apply le_antisymm
  · exact fun z hz => ⟨evenWidthField_le_zeroExtension hz, evenWidthField_le_real hz⟩
  · intro z hz
    classical
    by_cases hall : ∀ q : XiZeroCopy, zeroWidth q = 0
    · have hreal : ∀ q : XiZeroCopy, (xiSpectralPoint q).im = 0 := by
        intro q
        have h := hall q
        change ((xiSpectralPoint q).im : ℂ) = 0 at h
        exact_mod_cast h
      have hK := fullFibreSourceField_eq_zeroClosure_iff.mpr hreal
      have hzK : z ∈ fullFibreSourceField := by
        rw [hK, ← fullFibreZeroExtension_toSubfield]
        exact hz.1
      exact evenWidthField.algebraMap_mem ⟨z, hzK⟩
    · push Not at hall
      obtain ⟨q₀, hq₀⟩ := hall
      have hzA : z ∈ evenWidthField⟮zeroImaginaryOffset q₀⟯ := by
        have hzL : z ∈ fullFibreZeroExtension := hz.1
        rw [zeroExtension_eq_width_anchor q₀ hq₀] at hzL
        exact hzL
      obtain ⟨a, b, hab⟩ := HTGeometry.exists_repr_of_mem_adjoin_sqrt
        (width_anchor_square q₀) hzA
      obtain ⟨ar, har⟩ := evenWidthField_le_real a.property
      obtain ⟨br, hbr⟩ := evenWidthField_le_real b.property
      obtain ⟨zr, hzr⟩ := hz.2
      have him := congrArg Complex.im hab
      rw [zeroImaginaryOffset_eq] at him
      change z.im = (a : ℂ).im + ((b : ℂ).re * (I*zeroWidth q₀).im +
        (b : ℂ).im * (I*zeroWidth q₀).re) at him
      rw [← har, ← hbr, ← hzr] at him
      have hb0 : br = 0 := by
        have hw0 : (xiSpectralPoint q₀).im ≠ 0 := by
          intro h
          apply hq₀
          simp [zeroWidth, h]
        have hp : br * (xiSpectralPoint q₀).im = 0 := by
          simpa [zeroWidth] using him.symm
        exact (mul_eq_zero.mp hp).resolve_right hw0
      have hb : (b : ℂ) = 0 := by rw [← hbr, hb0]; rfl
      change z = (a : ℂ)+(b : ℂ)*zeroImaginaryOffset q₀ at hab
      rw [hb, zero_mul, add_zero] at hab
      rw [hab]
      exact a.property

/-- The subgroup generated by conjugation on the entire centered zero field. -/
def centeredConjugationSubgroup : Subgroup
    (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) :=
  Subgroup.zpowers fullFibreZeroConjugation

instance centeredConjugationSubgroup_normal : centeredConjugationSubgroup.Normal := by
  have hc : fullFibreZeroConjugation ∈ Subgroup.center
      (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) := by
    apply Subgroup.mem_center_iff.mpr
    intro σ
    exact fullFibreZeroConjugation_central σ
  have hH : centeredConjugationSubgroup ≤ Subgroup.center
      (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) :=
    Subgroup.zpowers_le.mpr hc
  refine ⟨fun a ha b => ?_⟩
  have hcomm := Subgroup.mem_center_iff.mp (hH ha) b
  simpa [hcomm] using ha

/-- The explicit width-product field is the fixed field of centered conjugation. -/
theorem evenWidthField_comap_eq_fixedField :
    evenWidthField.comap (IntermediateField.val fullFibreZeroExtension) =
      IntermediateField.fixedField centeredConjugationSubgroup := by
  ext z
  rw [IntermediateField.mem_fixedField_iff]
  change (z : ℂ) ∈ evenWidthField.toSubfield ↔ _
  rw [evenWidthField_eq_real_part]
  constructor
  · intro hz
    obtain ⟨r, hr⟩ := hz.2
    have hc : fullFibreZeroConjugation z = z := by
      apply Subtype.ext
      change (starRingEnd ℂ) (z : ℂ) = (z : ℂ)
      rw [← hr]
      simp
    have hsub : centeredConjugationSubgroup ≤ MulAction.stabilizer
        (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) z :=
      Subgroup.zpowers_le.mpr hc
    intro σ hσ
    exact hsub hσ
  · intro h
    have hc := h fullFibreZeroConjugation (Subgroup.mem_zpowers _)
    have him := congrArg (fun x : fullFibreZeroExtension => (x : ℂ).im) hc
    change -(z : ℂ).im = (z : ℂ).im at him
    refine ⟨z.property, (z : ℂ).re, ?_⟩
    apply Complex.ext
    · rfl
    · change 0 = (z : ℂ).im
      linarith only [him]

/-- The maximal real subfield is normal over the complete-fibre source field. -/
instance evenWidthField_normal : Normal fullFibreSourceField evenWidthField := by
  letI : IsGalois fullFibreSourceField fullFibreZeroExtension := ⟨⟩
  have hn : Normal fullFibreSourceField
      (IntermediateField.fixedField centeredConjugationSubgroup) := inferInstance
  rw [← evenWidthField_comap_eq_fixedField] at hn
  letI := hn
  exact Normal.of_algEquiv (HTGeometry.comapValEquiv evenWidthField_le_zeroExtension)

private theorem offset_not_mem_evenWidthField (q : XiZeroCopy) (hq : zeroWidth q ≠ 0) :
    zeroImaginaryOffset q ∉ evenWidthField := by
  intro h
  obtain ⟨x, hx⟩ := evenWidthField_le_real h
  have him := congrArg Complex.im hx
  rw [zeroImaginaryOffset_eq] at him
  have hw : (xiSpectralPoint q).im = 0 := by simpa [zeroWidth] using him.symm
  exact hq (by simp [zeroWidth, hw])

/-- A nonzero imaginary offset gives a genuinely quadratic presentation of the entire field. -/
theorem zeroExtension_width_anchor_quadratic (q : XiZeroCopy) (hq : zeroWidth q ≠ 0) :
    fullFibreZeroExtension =
        (evenWidthField⟮zeroImaginaryOffset q⟯).restrictScalars fullFibreSourceField ∧
      Module.finrank evenWidthField evenWidthField⟮zeroImaginaryOffset q⟯ = 2 := by
  refine ⟨zeroExtension_eq_width_anchor q hq, ?_⟩
  apply HTGeometry.finrank_adjoin_eq_two (width_anchor_square q)
  intro h
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp h
  apply offset_not_mem_evenWidthField q hq
  exact ha ▸ a.property

/-- The entire zero extension is real and trivial over the source, or quadratic over its real part. -/
theorem centered_zero_field_dichotomy :
    fullFibreZeroExtension.toSubfield = fullFibreSourceField ∨
      ∃ q : XiZeroCopy, zeroWidth q ≠ 0 ∧
        fullFibreZeroExtension =
          (evenWidthField⟮zeroImaginaryOffset q⟯).restrictScalars fullFibreSourceField ∧
        Module.finrank evenWidthField evenWidthField⟮zeroImaginaryOffset q⟯ = 2 := by
  classical
  by_cases hall : ∀ q : XiZeroCopy, zeroWidth q = 0
  · left
    rw [fullFibreZeroExtension_toSubfield]
    symm
    apply fullFibreSourceField_eq_zeroClosure_iff.mpr
    intro q
    have h := hall q
    change ((xiSpectralPoint q).im : ℂ) = 0 at h
    exact_mod_cast h
  · right
    push Not at hall
    obtain ⟨q, hq⟩ := hall
    exact ⟨q, hq, zeroExtension_width_anchor_quadratic q hq⟩

/-- The real field generated by every signed width over the source field. -/
def realWidthField : IntermediateField fullFibreSourceField ℂ :=
  IntermediateField.adjoin fullFibreSourceField (Set.range zeroWidth)

theorem zeroWidth_mem_realWidthField (q : XiZeroCopy) : zeroWidth q ∈ realWidthField :=
  IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩

theorem evenWidthField_le_realWidthField : evenWidthField ≤ realWidthField := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨⟨q,r⟩, rfl⟩
  exact realWidthField.mul_mem (zeroWidth_mem_realWidthField q) (zeroWidth_mem_realWidthField r)

theorem realWidthField_le_real :
    realWidthField.toSubfield ≤ Complex.ofRealHom.fieldRange := by
  rw [realWidthField, IntermediateField.adjoin_toSubfield]
  apply Subfield.closure_le.mpr
  rintro z (⟨k, rfl⟩ | ⟨q, rfl⟩)
  · exact fullFibreSourceField_le_real k.property
  · exact ⟨(xiSpectralPoint q).im, rfl⟩

/-- One nonzero signed width generates all widths over their pairwise products. -/
theorem realWidthField_eq_width_anchor (q₀ : XiZeroCopy) (hq₀ : zeroWidth q₀ ≠ 0) :
    realWidthField = (evenWidthField⟮zeroWidth q₀⟯).restrictScalars fullFibreSourceField := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro z ⟨q, rfl⟩
    have hp : zeroWidth q₀*zeroWidth q ∈ evenWidthField⟮zeroWidth q₀⟯ :=
      IntermediateField.algebraMap_mem (evenWidthField⟮zeroWidth q₀⟯)
        (⟨_, zeroWidth_mul_mem_evenWidthField q₀ q⟩ : evenWidthField)
    have he : zeroWidth q = (zeroWidth q₀*zeroWidth q)/zeroWidth q₀ := by
      apply (eq_div_iff hq₀).mpr
      exact mul_comm _ _
    change zeroWidth q ∈ evenWidthField⟮zeroWidth q₀⟯
    rw [he]
    exact (evenWidthField⟮zeroWidth q₀⟯).div_mem hp
      (IntermediateField.mem_adjoin_simple_self evenWidthField (zeroWidth q₀))
  · rw [IntermediateField.restrictScalars_adjoin_eq_sup]
    apply sup_le evenWidthField_le_realWidthField
    exact IntermediateField.adjoin_simple_le_iff.mpr (zeroWidth_mem_realWidthField q₀)

/-- The width field is quadratic over the even products when the anchor is absent from them. -/
theorem realWidthField_anchor_quadratic (q : XiZeroCopy) (hq : zeroWidth q ∉ evenWidthField) :
    realWidthField = (evenWidthField⟮zeroWidth q⟯).restrictScalars fullFibreSourceField ∧
      Module.finrank evenWidthField evenWidthField⟮zeroWidth q⟯ = 2 := by
  have hq0 : zeroWidth q ≠ 0 := by
    intro h
    exact hq (by rw [h]; exact evenWidthField.zero_mem)
  refine ⟨realWidthField_eq_width_anchor q hq0, ?_⟩
  have hs : zeroWidth q*zeroWidth q = algebraMap evenWidthField ℂ
      (⟨zeroWidth q*zeroWidth q, zeroWidth_mul_mem_evenWidthField q q⟩ : evenWidthField) := rfl
  apply HTGeometry.finrank_adjoin_eq_two hs
  intro h
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp h
  exact hq (ha ▸ a.property)

/-- The Gaussian unit belongs to the centered field exactly when a nonzero width lies in its real part. -/
theorem gaussianUnit_mem_zeroExtension_iff_width_mem (q : XiZeroCopy) (hq : zeroWidth q ≠ 0) :
    I ∈ fullFibreZeroExtension ↔ zeroWidth q ∈ evenWidthField := by
  constructor
  · intro hi
    have hiA : I ∈ evenWidthField⟮zeroImaginaryOffset q⟯ := by
      rw [zeroExtension_eq_width_anchor q hq] at hi
      exact hi
    obtain ⟨a, b, hab⟩ := HTGeometry.exists_repr_of_mem_adjoin_sqrt
      (width_anchor_square q) hiA
    obtain ⟨ar, har⟩ := evenWidthField_le_real a.property
    obtain ⟨br, hbr⟩ := evenWidthField_le_real b.property
    have him := congrArg Complex.im hab
    rw [zeroImaginaryOffset_eq] at him
    change 1 = (a : ℂ).im + ((b : ℂ).re*(I*zeroWidth q).im +
      (b : ℂ).im*(I*zeroWidth q).re) at him
    rw [← har, ← hbr] at him
    have hr : br*(xiSpectralPoint q).im = 1 := by
      simpa [zeroWidth] using him.symm
    have hp : (b : ℂ)*zeroWidth q = 1 := by
      rw [← hbr]
      apply Complex.ext
      · simpa [zeroWidth] using hr
      · simp [zeroWidth]
    have hb : (b : ℂ) ≠ 0 := by
      intro h
      rw [h, zero_mul] at hp
      exact zero_ne_one hp
    have hw : zeroWidth q = (b : ℂ)⁻¹ := by
      apply mul_left_cancel₀ hb
      rw [hp, mul_inv_cancel₀ hb]
    rw [hw]
    exact evenWidthField.inv_mem b.property
  · intro hw
    have he : I = zeroImaginaryOffset q / zeroWidth q := by
      exact (eq_div_iff hq).mpr (zeroImaginaryOffset_eq q).symm
    rw [he]
    exact fullFibreZeroExtension.div_mem (zeroImaginaryOffset_mem q)
      (evenWidthField_le_zeroExtension hw)

/-- A nonzero anchor already in the even field makes every signed width belong to it. -/
theorem realWidthField_eq_even_iff (q : XiZeroCopy) (hq : zeroWidth q ≠ 0) :
    realWidthField = evenWidthField ↔ zeroWidth q ∈ evenWidthField := by
  constructor
  · intro h
    rw [← h]
    exact zeroWidth_mem_realWidthField q
  · intro hw
    apply le_antisymm _ evenWidthField_le_realWidthField
    rw [realWidthField_eq_width_anchor q hq,
      IntermediateField.restrictScalars_adjoin_eq_sup]
    exact sup_le le_rfl (IntermediateField.adjoin_simple_le_iff.mpr hw)

/-- For a nonzero width, adjoining all signed widths collapses exactly when the zero field contains `i`. -/
theorem realWidthField_eq_even_iff_gaussianUnit (q : XiZeroCopy) (hq : zeroWidth q ≠ 0) :
    realWidthField = evenWidthField ↔ I ∈ fullFibreZeroExtension := by
  rw [realWidthField_eq_even_iff q hq, gaussianUnit_mem_zeroExtension_iff_width_mem q hq]

/-- Above the even field the entire width field is trivial or genuinely quadratic. -/
theorem realWidthField_anchor_dichotomy (q : XiZeroCopy) (hq : zeroWidth q ≠ 0) :
    realWidthField = evenWidthField ∨
      (realWidthField = (evenWidthField⟮zeroWidth q⟯).restrictScalars fullFibreSourceField ∧
        Module.finrank evenWidthField evenWidthField⟮zeroWidth q⟯ = 2) := by
  classical
  by_cases hw : zeroWidth q ∈ evenWidthField
  · exact Or.inl ((realWidthField_eq_even_iff q hq).mpr hw)
  · exact Or.inr (realWidthField_anchor_quadratic q hw)

end GaloisForLFunctions.GaloisTheoryOfZeros

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroExtension_eq_width_anchor
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.evenWidthField_eq_real_part
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.evenWidthField_normal
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.centered_zero_field_dichotomy
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.realWidthField_anchor_quadratic
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.gaussianUnit_mem_zeroExtension_iff_width_mem
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.realWidthField_anchor_dichotomy

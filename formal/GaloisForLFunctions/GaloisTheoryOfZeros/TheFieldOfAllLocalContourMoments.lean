import GaloisForLFunctions.RHTower.XiArithmeticSourceMomentTorelli
import GaloisForLFunctions.RHTower.XiWeilCauchyCoreMultiplicity
import Mathlib.Algebra.Field.Subfield.Basic

/-!
# The field of all local contour moments

First moments of the continued prime–archimedean source, taken over every
admissible rational rectangle, generate exactly the field of all centered ξ
zeros. A rational isolating rectangle recovers a zero from its first trace
by dividing by its positive integer multiplicity. Higher moments add no field
elements; zeroth moments generate only the prime field.

Consequently an ambient field automorphism fixes all first contour moments
exactly when it fixes every centered zero. This statement covers the entire
divisor and requires no continuity of the automorphism.
-/

noncomputable section
open Complex RHTower
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- Rational coordinates for a contour in the centered spectral plane. -/
structure RationalContour where
  left : ℚ
  right : ℚ
  bottom : ℚ
  top : ℚ

def RationalContour.lowerCorner (R : RationalContour) : ℂ :=
  ⟨R.left, R.bottom⟩

def RationalContour.upperCorner (R : RationalContour) : ℂ :=
  ⟨R.right, R.top⟩

/-- A nondegenerate rectangle whose boundary lies in the continued source domain. -/
def RationalContour.Admissible (R : RationalContour) : Prop :=
  R.lowerCorner.re < R.upperCorner.re ∧ R.lowerCorner.im < R.upperCorner.im ∧
  (∀ x ∈ Set.uIcc R.lowerCorner.re R.upperCorner.re,
    XiExplicitAdmissible ((x : ℂ) + R.lowerCorner.im * I)) ∧
  (∀ x ∈ Set.uIcc R.lowerCorner.re R.upperCorner.re,
    XiExplicitAdmissible ((x : ℂ) + R.upperCorner.im * I)) ∧
  (∀ y ∈ Set.uIcc R.lowerCorner.im R.upperCorner.im,
    XiExplicitAdmissible ((R.upperCorner.re : ℂ) + y * I)) ∧
  (∀ y ∈ Set.uIcc R.lowerCorner.im R.upperCorner.im,
    XiExplicitAdmissible ((R.lowerCorner.re : ℂ) + y * I))

/-- A literal continued-source contour moment, before identifying its residues. -/
def RationalContour.moment (R : RationalContour) (k : ℕ) : ℂ :=
  xiArithmeticSourceRectangleMoment R.lowerCorner R.upperCorner k

/-- The residue identity counts every enclosed zero occurrence. -/
theorem RationalContour.moment_eq (R : RationalContour) (hR : R.Admissible) (k : ℕ) :
    R.moment k = ∑ q ∈ xiZeroCopyClosedRectangle R.lowerCorner R.upperCorner,
      xiSpectralPoint q ^ k := by
  rcases hR with ⟨hre, him, hbot, htop, hright, hleft⟩
  exact xiArithmeticSourceRectangleMoment_eq_zeroPowerSum hre him hbot htop hright hleft k

/-- Rational admissible contours isolate any chosen support point, retaining all its copies. -/
theorem exists_isolating_rationalContour (q₀ : XiZeroCopy) :
    ∃ R : RationalContour, R.Admissible ∧
      ∀ q : XiZeroCopy,
        q ∈ xiZeroCopyClosedRectangle R.lowerCorner R.upperCorner ↔ q.1 = q₀.1 := by
  obtain ⟨d, hd0, hd⟩ := exists_pos_le_norm_xiSpectralPoint_sub_support q₀.1
  let a := xiSpectralPointSupport q₀.1
  have ha : xiSpectralPoint q₀ = a := xiSpectralPoint_eq_support q₀
  have haim : -1/2 < a.im ∧ a.im < 1/2 := by
    rw [← ha]
    exact xiSpectralPoint_im_mem_openHalf q₀
  obtain ⟨e, he0, hed, heup, helo⟩ : ∃ e : ℝ, 0 < e ∧
      e ≤ d/4 ∧ e ≤ (1/2-a.im)/2 ∧ e ≤ (a.im+1/2)/2 := by
    refine ⟨min (d/4) (min ((1/2-a.im)/2) ((a.im+1/2)/2)), ?_, ?_, ?_, ?_⟩
    · exact lt_min (by positivity) (lt_min (by linarith [haim.2]) (by linarith [haim.1]))
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨l, hla, hal⟩ := exists_rat_btwn (by linarith : a.re-e < a.re)
  obtain ⟨r, har, hra⟩ := exists_rat_btwn (by linarith : a.re < a.re+e)
  obtain ⟨b, hba, hab⟩ := exists_rat_btwn (by linarith : a.im-e < a.im)
  obtain ⟨t, hat, hta⟩ := exists_rat_btwn (by linarith : a.im < a.im+e)
  have hlr : (l : ℝ) < r := hal.trans har
  have hbt : (b : ℝ) < t := hab.trans hat
  have hsmall {z : ℂ} (hl : (l : ℝ) ≤ z.re) (hr : z.re ≤ r)
      (hb : (b : ℝ) ≤ z.im) (ht : z.im ≤ t) : ‖z-a‖ < d := by
    have hre : |z.re-a.re| < e := abs_lt.mpr ⟨by linarith, by linarith⟩
    have him : |z.im-a.im| < e := abs_lt.mpr ⟨by linarith, by linarith⟩
    have hn := Complex.norm_le_abs_re_add_abs_im (z-a)
    simp only [Complex.sub_re, Complex.sub_im] at hn
    linarith
  have hisolated {z : ℂ} (hl : (l : ℝ) ≤ z.re) (hr : z.re ≤ r)
      (hb : (b : ℝ) ≤ z.im) (ht : z.im ≤ t) (hz : XiC z = 0) : z = a := by
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z).mp hz
    by_cases hs : q.1 = q₀.1
    · rw [← hq, xiSpectralPoint_eq_support, hs]
    · have hbound := hd q hs
      rw [hq] at hbound
      exact False.elim ((not_le_of_gt (hsmall hl hr hb ht)) hbound)
  have hadm (x y : ℝ) (hl : (l : ℝ) ≤ x) (hr : x ≤ r)
      (hb : (b : ℝ) ≤ y) (ht : y ≤ t)
      (hedge : x = l ∨ x = r ∨ y = b ∨ y = t) :
      XiExplicitAdmissible ((x : ℂ) + y*I) := by
    apply XiExplicitAdmissible_of_im_lt_half_of_ne_one_of_XiC_ne_zero
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add]
      linarith [haim.2]
    · intro h
      have hreal := congrArg Complex.re h
      norm_num at hreal
      linarith [haim.1]
    · intro hz
      have heq := hisolated (z := (x : ℂ) + y*I)
        (by simpa using hl) (by simpa using hr) (by simpa using hb) (by simpa using ht) hz
      have hxe : x = a.re := by simpa using congrArg Complex.re heq
      have hye : y = a.im := by simpa using congrArg Complex.im heq
      rcases hedge with hedge | hedge | hedge | hedge <;> linarith
  let R : RationalContour := ⟨l, r, b, t⟩
  refine ⟨R, ⟨hlr, hbt, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    change x ∈ Set.uIcc (l : ℝ) r at hx
    rw [Set.uIcc_of_le hlr.le] at hx
    exact hadm x b hx.1 hx.2 le_rfl hbt.le (Or.inr (Or.inr (Or.inl rfl)))
  · intro x hx
    change x ∈ Set.uIcc (l : ℝ) r at hx
    rw [Set.uIcc_of_le hlr.le] at hx
    exact hadm x t hx.1 hx.2 hbt.le le_rfl (Or.inr (Or.inr (Or.inr rfl)))
  · intro y hy
    change y ∈ Set.uIcc (b : ℝ) t at hy
    rw [Set.uIcc_of_le hbt.le] at hy
    exact hadm r y hlr.le le_rfl hy.1 hy.2 (Or.inr (Or.inl rfl))
  · intro y hy
    change y ∈ Set.uIcc (b : ℝ) t at hy
    rw [Set.uIcc_of_le hbt.le] at hy
    exact hadm l y le_rfl hlr.le hy.1 hy.2 (Or.inl rfl)
  · intro q
    rw [mem_xiZeroCopyClosedRectangle, Complex.mem_reProdIm]
    change ((xiSpectralPoint q).re ∈ Set.uIcc (l : ℝ) r ∧
      (xiSpectralPoint q).im ∈ Set.uIcc (b : ℝ) t) ↔ q.1 = q₀.1
    rw [Set.uIcc_of_le hlr.le, Set.uIcc_of_le hbt.le]
    constructor
    · rintro ⟨⟨hl, hr⟩, ⟨hb, ht⟩⟩
      apply xiSpectralPointSupport_injective
      simpa only [xiSpectralPoint_eq_support] using
        hisolated hl hr hb ht (XiC_xiSpectralPoint_eq_zero q)
    · intro hq
      have heq : xiSpectralPoint q = a := by rw [xiSpectralPoint_eq_support, hq]
      rw [heq]
      exact ⟨⟨hal.le, har.le⟩, ⟨hab.le, hat.le⟩⟩



/-- The subfield generated by the entire centered zero carrier. -/
def centeredZeroField : Subfield ℂ := Subfield.closure (Set.range xiSpectralPoint)

/-- Only first source moments of admissible rational rectangles are admitted. -/
def firstContourField : Subfield ℂ :=
  Subfield.closure {z | ∃ R : RationalContour, R.Admissible ∧ z = R.moment 1}

/-- All nonnegative power moments of the same rational contour family. -/
def fullContourField : Subfield ℂ :=
  Subfield.closure {z | ∃ R : RationalContour, R.Admissible ∧ ∃ k : ℕ, z = R.moment k}

/-- Each centered zero is a nonzero rational multiple of one first source moment. -/
theorem exists_firstContourMoment_recovers (q₀ : XiZeroCopy) :
    ∃ R : RationalContour, R.Admissible ∧ ∃ m : ℕ, 0 < m ∧
      R.moment 1 = (m : ℂ) * xiSpectralPoint q₀ := by
  classical
  obtain ⟨R, hR, hiso⟩ := exists_isolating_rationalContour q₀
  let T := xiZeroCopyClosedRectangle R.lowerCorner R.upperCorner
  refine ⟨R, hR, T.card, Finset.card_pos.mpr ⟨q₀, (hiso q₀).mpr rfl⟩, ?_⟩
  rw [R.moment_eq hR]
  calc
    (∑ q ∈ T, xiSpectralPoint q ^ 1) = ∑ _q ∈ T, xiSpectralPoint q₀ := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [pow_one, xiSpectralPoint_eq_support, (hiso q).mp hq,
        ← xiSpectralPoint_eq_support q₀]
    _ = (T.card : ℂ) * xiSpectralPoint q₀ := by
      rw [Finset.sum_const, nsmul_eq_mul]

private theorem firstContourField_le_full : firstContourField ≤ fullContourField := by
  apply Subfield.closure_mono
  rintro z ⟨R, hR, rfl⟩
  exact ⟨R, hR, 1, rfl⟩

private theorem fullContourField_le_zero : fullContourField ≤ centeredZeroField := by
  apply Subfield.closure_le.mpr
  rintro z ⟨R, hR, k, rfl⟩
  rw [R.moment_eq hR]
  apply Subfield.sum_mem
  intro q _
  exact centeredZeroField.pow_mem (Subfield.subset_closure ⟨q, rfl⟩) k

private theorem centeredZeroField_le_first : centeredZeroField ≤ firstContourField := by
  apply Subfield.closure_le.mpr
  rintro z ⟨q, rfl⟩
  obtain ⟨R, hR, m, hm, heq⟩ := exists_firstContourMoment_recovers q
  have hmem : R.moment 1 ∈ firstContourField := Subfield.subset_closure ⟨R, hR, rfl⟩
  rw [heq] at hmem
  have hinv : (m : ℂ)⁻¹ ∈ firstContourField :=
    firstContourField.inv_mem (natCast_mem firstContourField m)
  have hprod := firstContourField.mul_mem hinv hmem
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  change xiSpectralPoint q ∈ firstContourField
  simpa only [← mul_assoc, inv_mul_cancel₀ hm0, one_mul] using hprod

/-- First moments already generate the entire zero field, with no height cutoff. -/
theorem firstContourField_eq_centeredZeroField : firstContourField = centeredZeroField :=
  le_antisymm (firstContourField_le_full.trans fullContourField_le_zero)
    centeredZeroField_le_first

/-- Higher power moments add no field elements once every rational contour is admitted. -/
theorem fullContourField_eq_centeredZeroField : fullContourField = centeredZeroField :=
  le_antisymm fullContourField_le_zero
    (centeredZeroField_le_first.trans firstContourField_le_full)




/-- The field generated by all contour counts alone. -/
def zerothContourField : Subfield ℂ :=
  Subfield.closure {z | ∃ R : RationalContour, R.Admissible ∧ z = R.moment 0}

/-- Counts remain in the prime field; first moments recover the zero field. -/
theorem zerothContourField_eq_bot : zerothContourField = ⊥ := by
  apply le_antisymm _ bot_le
  apply Subfield.closure_le.mpr
  rintro z ⟨R, hR, rfl⟩
  rw [R.moment_eq hR]
  simp only [pow_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact natCast_mem (⊥ : Subfield ℂ) _



/-- Fixing all local first traces is exactly fixing every centered zero.
No continuity of the ambient field automorphism is needed. -/
theorem fixes_firstContourMoments_iff (σ : ℂ ≃+* ℂ) :
    (∀ R : RationalContour, R.Admissible → σ (R.moment 1) = R.moment 1) ↔
      ∀ q : XiZeroCopy, σ (xiSpectralPoint q) = xiSpectralPoint q := by
  constructor
  · intro h q
    obtain ⟨R, hR, m, hm, heq⟩ := exists_firstContourMoment_recovers q
    have hfix := h R hR
    rw [heq, map_mul, map_natCast] at hfix
    exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hm.ne') hfix
  · intro h R hR
    rw [R.moment_eq hR]
    simp only [pow_one, map_sum, h]

/-- Once first traces are fixed, every higher local trace is fixed as well. -/
theorem fixes_allContourMoments_iff_first (σ : ℂ ≃+* ℂ) :
    (∀ R : RationalContour, R.Admissible → ∀ k, σ (R.moment k) = R.moment k) ↔
      ∀ R : RationalContour, R.Admissible → σ (R.moment 1) = R.moment 1 := by
  constructor
  · intro h R hR
    exact h R hR 1
  · intro h R hR k
    have hfix := (fixes_firstContourMoments_iff σ).mp h
    rw [R.moment_eq hR]
    simp only [map_sum, map_pow, hfix]


end GaloisForLFunctions.GaloisTheoryOfZeros

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.firstContourField_eq_centeredZeroField
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.fullContourField_eq_centeredZeroField
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.fixes_firstContourMoments_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zerothContourField_eq_bot

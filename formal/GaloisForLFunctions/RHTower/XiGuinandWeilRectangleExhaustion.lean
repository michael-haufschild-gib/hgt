import GaloisForLFunctions.RHTower.XiGuinandWeilRectanglePeeling
import Mathlib.Order.Interval.Set.Infinite

/-!
# Cofinal admissible rectangles for the centered Xi divisor

Every centered Xi spectral point has imaginary coordinate strictly between `-1/2` and `1/2`.
Given any finite packet of multiplicity copies, this module constructs a rectangle containing the
packet strictly in its interior whose whole boundary is admissible for the continued
prime--archimedean explicit formula.

The construction uses only finite avoidance.  A raw compact rectangle contains finitely many Xi
zeros; the final left, right, and top coordinates are selected from open intervals while avoiding
the finite sets of their real and imaginary coordinates.  The bottom edge is fixed below the Xi
strip.  Thus the admissible rectangles are cofinal among finite divisor packets.
-/

open Complex Filter intervalIntegral Set

namespace RHTower

noncomputable section

/-- The imaginary centered spectral coordinate is `1/2 - Re ρ`. -/
theorem xiSpectralPoint_im_eq (q : XiZeroCopy) :
    (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
  rw [xiSpectralPoint]
  simp [Complex.mul_im]

/-- Every centered Xi divisor point lies in the open horizontal strip
`-1/2 < Im z < 1/2`. -/
theorem xiSpectralPoint_im_mem_openHalf (q : XiZeroCopy) :
    (-1 / 2 : ℝ) < (xiSpectralPoint q).im ∧
      (xiSpectralPoint q).im < 1 / 2 := by
  rw [xiSpectralPoint_im_eq]
  have h := xi_divisor_support_re_mem_open_unit q.1
  constructor <;> linarith

/-- Every zero of `XiC` lies in the same open horizontal strip. -/
theorem xiC_zero_im_mem_openHalf {z : ℂ} (hz : XiC z = 0) :
    (-1 / 2 : ℝ) < z.im ∧ z.im < 1 / 2 := by
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z).mp hz
  rw [← hq]
  exact xiSpectralPoint_im_mem_openHalf q

/-- Boundary admissibility follows from lying below the top of the centered Xi strip, avoiding the
completed point `1`, and avoiding the centered Xi divisor. -/
theorem XiExplicitAdmissible_of_im_lt_half_of_ne_one_of_XiC_ne_zero
    {z : ℂ} (him : z.im < 1 / 2)
    (hne_one : (1 / 2 + z * I) ≠ 1) (hXi : XiC z ≠ 0) :
    XiExplicitAdmissible z := by
  have hre : 0 < (1 / 2 + z * I).re := by
    simp [Complex.mul_re]
    linarith
  refine ⟨hre, hne_one, ?_⟩
  have hs0 : (1 / 2 + z * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hG := Gammaℝ_ne_zero_of_re_pos hre
  intro hzeta
  apply hXi
  change xi (1 / 2 + z * I) = 0
  rw [xi_eq_archFactor_mul_zeta hs0 hne_one hG, hzeta, mul_zero]

private theorem exists_Ioo_not_mem_finset {a b : ℝ} (hab : a < b) (F : Finset ℝ) :
    ∃ x ∈ Set.Ioo a b, x ∉ F := by
  have hinf : (Set.Ioo a b).Infinite := Set.Ioo_infinite hab
  have hdiff : (Set.Ioo a b \ (F : Set ℝ)).Infinite := hinf.sdiff F.finite_toSet
  obtain ⟨x, hxI, hxF⟩ := hdiff.nonempty
  exact ⟨x, hxI, by simpa using hxF⟩

/-- **Cofinal admissible rectangle selection.**  Every finite packet of multiplicity-exact Xi
divisor copies lies strictly inside some positively oriented rectangle on whose four edges every
base point is admissible for the continued Guinand--Weil formula. -/
theorem exists_admissible_rectangle_containing_xiZeroCopy_finset
    (t : Finset XiZeroCopy) :
    ∃ z₁ z₂ : ℂ,
      z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
      (∀ q ∈ t, z₁.re < (xiSpectralPoint q).re ∧
        (xiSpectralPoint q).re < z₂.re ∧
        z₁.im < (xiSpectralPoint q).im ∧
        (xiSpectralPoint q).im < z₂.im) ∧
      (∀ x ∈ uIcc z₁.re z₂.re,
        XiExplicitAdmissible ((x : ℂ) + z₁.im * I)) ∧
      (∀ x ∈ uIcc z₁.re z₂.re,
        XiExplicitAdmissible ((x : ℂ) + z₂.im * I)) ∧
      (∀ y ∈ uIcc z₁.im z₂.im,
        XiExplicitAdmissible ((z₂.re : ℂ) + y * I)) ∧
      (∀ y ∈ uIcc z₁.im z₂.im,
        XiExplicitAdmissible ((z₁.re : ℂ) + y * I)) := by
  classical
  let R : ℝ := 1 + ∑ q ∈ t, ‖xiSpectralPoint q‖
  have hR : 0 < R := by
    dsimp only [R]
    have : 0 ≤ ∑ q ∈ t, ‖xiSpectralPoint q‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  let y₀ : ℝ := if ht : t.Nonempty then
      t.sup' ht (fun q => (xiSpectralPoint q).im) else 0
  have hy₀lt : y₀ < 1 / 2 := by
    dsimp only [y₀]
    split_ifs with ht
    · rw [Finset.sup'_lt_iff]
      exact fun q _ => (xiSpectralPoint_im_mem_openHalf q).2
    · norm_num
  have hy₀lower : -1 / 2 < y₀ := by
    dsimp only [y₀]
    split_ifs with ht
    · obtain ⟨q, hq⟩ := ht
      exact (xiSpectralPoint_im_mem_openHalf q).1.trans_le
        (Finset.le_sup' (fun q => (xiSpectralPoint q).im) hq)
    · norm_num
  let raw₁ : ℂ := ((-R - 1 : ℝ) : ℂ) + (-1 : ℝ) * I
  let raw₂ : ℂ := ((R + 1 : ℝ) : ℂ) + (1 / 2 : ℝ) * I
  let Z : Finset ℂ := xiCClosedRectangleZeros raw₁ raw₂
  let Fre : Finset ℝ := Z.image Complex.re
  let Fim : Finset ℝ := Z.image Complex.im
  obtain ⟨y₂, hy₂I, hy₂avoid⟩ := exists_Ioo_not_mem_finset hy₀lt Fim
  obtain ⟨x₁, hx₁I, hx₁avoid⟩ :=
    exists_Ioo_not_mem_finset (by linarith : -R - 1 < -R) Fre
  obtain ⟨x₂, hx₂I, hx₂avoid⟩ :=
    exists_Ioo_not_mem_finset (by linarith : R < R + 1) Fre
  have hy₂lo := hy₂I.1
  have hy₂hi := hy₂I.2
  have hx₁lo := hx₁I.1
  have hx₁hi := hx₁I.2
  have hx₂lo := hx₂I.1
  have hx₂hi := hx₂I.2
  let z₁ : ℂ := (x₁ : ℂ) + (-3 / 4 : ℝ) * I
  let z₂ : ℂ := (x₂ : ℂ) + y₂ * I
  have hz₁re : z₁.re = x₁ := by simp [z₁]
  have hz₁im : z₁.im = -3 / 4 := by simp [z₁]
  have hz₂re : z₂.re = x₂ := by simp [z₂]
  have hz₂im : z₂.im = y₂ := by simp [z₂]
  have hre : z₁.re < z₂.re := by
    rw [hz₁re, hz₂re]
    linarith [hx₁hi, hx₂lo, hR]
  have him : z₁.im < z₂.im := by
    rw [hz₁im, hz₂im]
    linarith [hy₂lo, hy₀lower]
  have hpacket : ∀ q ∈ t, z₁.re < (xiSpectralPoint q).re ∧
      (xiSpectralPoint q).re < z₂.re ∧ z₁.im < (xiSpectralPoint q).im ∧
      (xiSpectralPoint q).im < z₂.im := by
    intro q hq
    have hsum : ‖xiSpectralPoint q‖ ≤ ∑ r ∈ t, ‖xiSpectralPoint r‖ :=
      Finset.single_le_sum (fun r _ => norm_nonneg (xiSpectralPoint r)) hq
    have habs := Complex.abs_re_le_norm (xiSpectralPoint q)
    have hqreL : -R < (xiSpectralPoint q).re := by
      dsimp only [R]
      have hneg := neg_le_neg (le_trans (neg_le_abs _) (le_trans habs hsum))
      linarith
    have hqreR : (xiSpectralPoint q).re < R := by
      dsimp only [R]
      have := le_trans (le_abs_self _) (le_trans habs hsum)
      linarith
    have hqimTop : (xiSpectralPoint q).im ≤ y₀ := by
      dsimp only [y₀]
      rw [dif_pos ⟨q, hq⟩]
      exact Finset.le_sup' (fun r => (xiSpectralPoint r).im) hq
    rw [hz₁re, hz₂re, hz₁im, hz₂im]
    exact ⟨by linarith [hx₁hi], by linarith [hx₂lo],
      by linarith [(xiSpectralPoint_im_mem_openHalf q).1], by linarith [hy₂lo]⟩
  have hraw_mem {z : ℂ} (hreZ : -R - 1 ≤ z.re) (hreZ' : z.re ≤ R + 1)
      (himZ : (-1 : ℝ) ≤ z.im) (himZ' : z.im ≤ 1 / 2) :
      z ∈ (uIcc raw₁.re raw₂.re ×ℂ uIcc raw₁.im raw₂.im) := by
    apply Complex.mem_reProdIm.mpr
    have hrraw : raw₁.re ≤ raw₂.re := by simp [raw₁, raw₂]; linarith [hR]
    have hiraw : raw₁.im ≤ raw₂.im := by simp [raw₁, raw₂]; norm_num
    rw [uIcc_of_le hrraw, uIcc_of_le hiraw]
    constructor
    · constructor
      · simp [raw₁]
        linarith
      · simp [raw₂]
        linarith
    · constructor
      · simpa [raw₁] using himZ
      · simpa [raw₂, div_eq_mul_inv] using himZ'
  have hzero_mem_Z {z : ℂ}
      (hraw : z ∈ (uIcc raw₁.re raw₂.re ×ℂ uIcc raw₁.im raw₂.im))
      (hz : XiC z = 0) : z ∈ Z :=
    mem_xiCClosedRectangleZeros.mpr ⟨hraw, hz⟩
  have hbot0 : ∀ x ∈ uIcc z₁.re z₂.re,
      XiC ((x : ℂ) + z₁.im * I) ≠ 0 := by
    intro x _ hzero
    have hs := xiC_zero_im_mem_openHalf hzero
    have hsim : (((x : ℂ) + z₁.im * I).im) = -3 / 4 := by simp [hz₁im]
    rw [hsim] at hs
    norm_num at hs
  have htop0 : ∀ x ∈ uIcc z₁.re z₂.re,
      XiC ((x : ℂ) + z₂.im * I) ≠ 0 := by
    intro x hx hzero
    have hxI : x₁ ≤ x ∧ x ≤ x₂ := by
      rw [uIcc_of_le hre.le] at hx
      simpa [hz₁re, hz₂re] using hx
    have hraw : ((x : ℂ) + z₂.im * I) ∈
        (uIcc raw₁.re raw₂.re ×ℂ uIcc raw₁.im raw₂.im) := by
      apply hraw_mem <;> simp [hz₂im] <;>
        linarith [hxI.1, hxI.2, hx₁lo, hx₂hi, hy₂lo, hy₂hi, hy₀lower]
    have hzZ := hzero_mem_Z hraw hzero
    apply hy₂avoid
    exact Finset.mem_image.mpr ⟨(x : ℂ) + z₂.im * I, hzZ, by simp [hz₂im]⟩
  have hright0 : ∀ y ∈ uIcc z₁.im z₂.im,
      XiC ((z₂.re : ℂ) + y * I) ≠ 0 := by
    intro y hy hzero
    have hyI : -3 / 4 ≤ y ∧ y ≤ y₂ := by
      rw [uIcc_of_le him.le] at hy
      simpa [hz₁im, hz₂im] using hy
    have hraw : ((z₂.re : ℂ) + y * I) ∈
        (uIcc raw₁.re raw₂.re ×ℂ uIcc raw₁.im raw₂.im) := by
      apply hraw_mem <;> simp [hz₂re] <;>
        linarith [hyI.1, hyI.2, hx₂lo, hx₂hi, hy₂hi]
    have hzZ := hzero_mem_Z hraw hzero
    apply hx₂avoid
    exact Finset.mem_image.mpr ⟨(z₂.re : ℂ) + y * I, hzZ, by simp [hz₂re]⟩
  have hleft0 : ∀ y ∈ uIcc z₁.im z₂.im,
      XiC ((z₁.re : ℂ) + y * I) ≠ 0 := by
    intro y hy hzero
    have hyI : -3 / 4 ≤ y ∧ y ≤ y₂ := by
      rw [uIcc_of_le him.le] at hy
      simpa [hz₁im, hz₂im] using hy
    have hraw : ((z₁.re : ℂ) + y * I) ∈
        (uIcc raw₁.re raw₂.re ×ℂ uIcc raw₁.im raw₂.im) := by
      apply hraw_mem <;> simp [hz₁re] <;>
        linarith [hyI.1, hyI.2, hx₁lo, hx₁hi, hy₂hi]
    have hzZ := hzero_mem_Z hraw hzero
    apply hx₁avoid
    exact Finset.mem_image.mpr ⟨(z₁.re : ℂ) + y * I, hzZ, by simp [hz₁re]⟩
  have hne_one_of_re_ne_zero {z : ℂ} (hzre : z.re ≠ 0) :
      (1 / 2 + z * I) ≠ 1 := by
    intro h
    have himEq := congrArg Complex.im h
    simp [Complex.mul_im] at himEq
    exact hzre himEq
  have hne_one_of_im_ne {z : ℂ} (hzim : z.im ≠ -1 / 2) :
      (1 / 2 + z * I) ≠ 1 := by
    intro h
    have hreEq := congrArg Complex.re h
    simp [Complex.mul_re] at hreEq
    apply hzim
    linarith
  have hbotAdm : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I) := by
    intro x hx
    apply XiExplicitAdmissible_of_im_lt_half_of_ne_one_of_XiC_ne_zero
    · simp [hz₁im]; norm_num
    · apply hne_one_of_im_ne
      simp [hz₁im]
      norm_num
    · exact hbot0 x hx
  have htopAdm : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I) := by
    intro x hx
    apply XiExplicitAdmissible_of_im_lt_half_of_ne_one_of_XiC_ne_zero
    · simp [hz₂im]
      simpa [div_eq_mul_inv] using hy₂hi
    · apply hne_one_of_im_ne
      simp [hz₂im]
      linarith [hy₂lo, hy₀lower]
    · exact htop0 x hx
  have hrightAdm : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I) := by
    intro y hy
    have hyI : -3 / 4 ≤ y ∧ y ≤ y₂ := by
      rw [uIcc_of_le him.le] at hy
      simpa [hz₁im, hz₂im] using hy
    apply XiExplicitAdmissible_of_im_lt_half_of_ne_one_of_XiC_ne_zero
    · simp
      linarith [hyI.2, hy₂hi]
    · apply hne_one_of_re_ne_zero
      simp [hz₂re]
      linarith [hx₂lo, hR]
    · exact hright0 y hy
  have hleftAdm : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I) := by
    intro y hy
    have hyI : -3 / 4 ≤ y ∧ y ≤ y₂ := by
      rw [uIcc_of_le him.le] at hy
      simpa [hz₁im, hz₂im] using hy
    apply XiExplicitAdmissible_of_im_lt_half_of_ne_one_of_XiC_ne_zero
    · simp
      linarith [hyI.2, hy₂hi]
    · apply hne_one_of_re_ne_zero
      simp [hz₁re]
      linarith [hx₁hi, hR]
    · exact hleft0 y hy
  exact ⟨z₁, z₂, hre, him, hpacket,
    hbotAdm, htopAdm, hrightAdm, hleftAdm⟩

end

end RHTower

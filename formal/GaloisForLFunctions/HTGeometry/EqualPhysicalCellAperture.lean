import GaloisForLFunctions.HTGeometry.CenteredIndicatorHilbert
import GaloisForLFunctions.HTGeometry.FiniteHilbertDispersion
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators
open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A half-open physical cell of length `c`, starting at `s`. -/
def equalPhysicalCell (c s : ℝ) : Set ℝ := Ioc s (s + c)

theorem measurableSet_equalPhysicalCell (c s : ℝ) :
    MeasurableSet (equalPhysicalCell c s) :=
  measurableSet_Ioc

theorem volume_equalPhysicalCell {c s : ℝ} (hc : 0 ≤ c) :
    (volume : Measure ℝ) (equalPhysicalCell c s) = ENNReal.ofReal c := by
  rw [equalPhysicalCell, Real.volume_Ioc]
  congr 1
  ring

theorem volumeReal_equalPhysicalCell {c s : ℝ} (hc : 0 ≤ c) :
    (volume : Measure ℝ).real (equalPhysicalCell c s) = c := by
  rw [Measure.real, volume_equalPhysicalCell hc, ENNReal.toReal_ofReal hc]

theorem volumeReal_equalPhysicalCell_inter (c s t : ℝ) :
    (volume : Measure ℝ).real (equalPhysicalCell c s ∩ equalPhysicalCell c t) =
      max (c - |s - t|) 0 := by
  rcases le_total s t with hst | hts
  · have hinter : equalPhysicalCell c s ∩ equalPhysicalCell c t = Ioc t (s + c) := by
      ext x
      simp only [equalPhysicalCell, mem_inter_iff, mem_Ioc]
      constructor
      · rintro ⟨⟨_, hxs⟩, htx, _⟩
        exact ⟨htx, hxs⟩
      · rintro ⟨htx, hxs⟩
        exact ⟨⟨lt_of_le_of_lt hst htx, hxs⟩, ⟨htx, by linarith⟩⟩
    rw [hinter, Real.volume_real_Ioc, abs_of_nonpos (sub_nonpos.mpr hst)]
    congr 1
    ring
  · have hinter : equalPhysicalCell c s ∩ equalPhysicalCell c t = Ioc s (t + c) := by
      ext x
      simp only [equalPhysicalCell, mem_inter_iff, mem_Ioc]
      constructor
      · rintro ⟨⟨hsx, _⟩, ⟨_, hxt⟩⟩
        exact ⟨hsx, hxt⟩
      · rintro ⟨hsx, hxt⟩
        exact ⟨⟨hsx, by linarith⟩, ⟨lt_of_le_of_lt hts hsx, hxt⟩⟩
    rw [hinter, Real.volume_real_Ioc, abs_of_nonneg (sub_nonneg.mpr hts)]
    congr 1
    ring

theorem max_sub_abs_eq_sub_min (c h : ℝ) (hh : 0 ≤ h) :
    max (c - h) 0 = c - min h c := by
  rcases le_total h c with hle | hle
  · rw [min_eq_left hle, max_eq_left (sub_nonneg.mpr hle)]
  · rw [min_eq_right hle, max_eq_right (sub_nonpos.mpr hle)]
    ring

theorem volumeReal_equalPhysicalCell_inter_eq_sub_min
    (c s t : ℝ) :
    (volume : Measure ℝ).real (equalPhysicalCell c s ∩ equalPhysicalCell c t) =
      c - min |s - t| c := by
  rw [volumeReal_equalPhysicalCell_inter, max_sub_abs_eq_sub_min c |s - t| (abs_nonneg _)]

/-- Centered carrier of a physical cell in the aperture `(0,A]`. -/
def equalPhysicalCellCarrier (A c s : ℝ) : Lp ℝ 2 (volume : Measure ℝ) :=
  centeredIndicatorOn (volume : Measure ℝ) (Ioc 0 A) (equalPhysicalCell c s)
    measurableSet_Ioc (by simp [Real.volume_Ioc])
    (measurableSet_equalPhysicalCell c s) (by simp [equalPhysicalCell, Real.volume_Ioc])

theorem equalPhysicalCell_subset_aperture
    {A c s : ℝ} (hc : 0 < c) (hs0 : 0 ≤ s) (hsA : s ≤ A - c) :
    equalPhysicalCell c s ⊆ Ioc 0 A := by
  intro x hx
  rcases hx with ⟨hsx, hxc⟩
  exact ⟨lt_of_le_of_lt hs0 hsx, by linarith⟩

/-- `(AH11)`: exact Gram law for equal moving cells. -/
theorem real_inner_equalPhysicalCellCarrier
    {A c s t : ℝ} (hA : 0 < A) (hc : 0 < c)
    (hs0 : 0 ≤ s) (hsA : s ≤ A - c)
    (ht0 : 0 ≤ t) (htA : t ≤ A - c) :
    inner ℝ (equalPhysicalCellCarrier A c s) (equalPhysicalCellCarrier A c t) =
      c * (A - c) / A - min |s - t| c := by
  rw [equalPhysicalCellCarrier, equalPhysicalCellCarrier,
    real_inner_centeredIndicatorOn volume (Ioc 0 A)
      (equalPhysicalCell c s) (equalPhysicalCell c t)
      measurableSet_Ioc (by simp [Real.volume_Ioc])
      (measurableSet_equalPhysicalCell c s) (by simp [equalPhysicalCell, Real.volume_Ioc])
      (measurableSet_equalPhysicalCell c t) (by simp [equalPhysicalCell, Real.volume_Ioc])
      (equalPhysicalCell_subset_aperture hc hs0 hsA)
      (equalPhysicalCell_subset_aperture hc ht0 htA)
      (by simpa [Real.volume_real_Ioc] using hA)]
  rw [volumeReal_equalPhysicalCell_inter_eq_sub_min,
    volumeReal_equalPhysicalCell hc.le, volumeReal_equalPhysicalCell hc.le,
    Real.volume_real_Ioc, sub_zero, max_eq_left hA.le]
  field_simp [hA.ne']
  ring

/-- Exact common squared radius `D = c(A-c)/A`. -/
theorem norm_sq_equalPhysicalCellCarrier
    {A c s : ℝ} (hA : 0 < A) (hc : 0 < c)
    (hs0 : 0 ≤ s) (hsA : s ≤ A - c) :
    ‖equalPhysicalCellCarrier A c s‖ ^ 2 = c * (A - c) / A := by
  rw [← real_inner_self_eq_norm_sq,
    real_inner_equalPhysicalCellCarrier hA hc hs0 hsA hs0 hsA]
  simp [hc.le]

/-- `(AH10)`: squared Hilbert distance is twice the truncated displacement. -/
theorem norm_sub_sq_equalPhysicalCellCarrier
    {A c s t : ℝ} (hA : 0 < A) (hc : 0 < c)
    (hs0 : 0 ≤ s) (hsA : s ≤ A - c)
    (ht0 : 0 ≤ t) (htA : t ≤ A - c) :
    ‖equalPhysicalCellCarrier A c s - equalPhysicalCellCarrier A c t‖ ^ 2 =
      2 * min |s - t| c := by
  rw [norm_sub_sq_real,
    norm_sq_equalPhysicalCellCarrier hA hc hs0 hsA,
    norm_sq_equalPhysicalCellCarrier hA hc ht0 htA,
    real_inner_equalPhysicalCellCarrier hA hc hs0 hsA ht0 htA]
  ring

/-- `(AH12)`: exact normalized barycenter energy of equal physical cells. -/
theorem norm_sq_sum_equalPhysicalCellCarrier
    {ι : Type*} (S : Finset ι) (weight start : ι → ℝ)
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c)
    (hstart0 : ∀ i ∈ S, 0 ≤ start i)
    (hstartA : ∀ i ∈ S, start i ≤ A - c)
    (hweight : ∑ i ∈ S, weight i = 1) :
    ‖∑ i ∈ S, weight i • equalPhysicalCellCarrier A c (start i)‖ ^ 2 =
      c * (A - c) / A -
        ∑ i ∈ S, ∑ j ∈ S, weight i * weight j * min |start i - start j| c := by
  rw [finite_weighted_hilbert_dispersion]
  rw [hweight]
  have hradius :
      (∑ i ∈ S, weight i * ‖equalPhysicalCellCarrier A c (start i)‖ ^ 2) =
        c * (A - c) / A := by
    calc
      ∑ i ∈ S, weight i * ‖equalPhysicalCellCarrier A c (start i)‖ ^ 2 =
          ∑ i ∈ S, weight i * (c * (A - c) / A) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [norm_sq_equalPhysicalCellCarrier hA hc (hstart0 i hi) (hstartA i hi)]
      _ = (∑ i ∈ S, weight i) * (c * (A - c) / A) := by
            rw [Finset.sum_mul]
      _ = c * (A - c) / A := by rw [hweight, one_mul]
  rw [hradius]
  have hdisp :
      (∑ i ∈ S, ∑ j ∈ S,
        weight i * weight j *
          ‖equalPhysicalCellCarrier A c (start i) -
            equalPhysicalCellCarrier A c (start j)‖ ^ 2) =
        2 * ∑ i ∈ S, ∑ j ∈ S,
          weight i * weight j * min |start i - start j| c := by
    calc
      ∑ i ∈ S, ∑ j ∈ S,
          weight i * weight j *
            ‖equalPhysicalCellCarrier A c (start i) -
              equalPhysicalCellCarrier A c (start j)‖ ^ 2 =
          ∑ i ∈ S, ∑ j ∈ S,
            2 * (weight i * weight j * min |start i - start j| c) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              rw [norm_sub_sq_equalPhysicalCellCarrier hA hc
                (hstart0 i hi) (hstartA i hi) (hstart0 j hj) (hstartA j hj)]
              ring
      _ = 2 * ∑ i ∈ S, ∑ j ∈ S,
          weight i * weight j * min |start i - start j| c := by
            simp_rw [Finset.mul_sum]
  rw [hdisp]
  ring

end
end GaloisForLFunctions.HTGeometry

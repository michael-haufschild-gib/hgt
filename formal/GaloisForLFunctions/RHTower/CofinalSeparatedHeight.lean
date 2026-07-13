import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real

/-!
# Quantitative finite avoidance on a cofinal real interval

A finite set of forbidden horizontal coordinates cannot occupy a whole dyadic interval after each
coordinate is thickened by intervals whose total length is smaller than that interval.  This is
the height-selection lemma needed for the rectangular Xi contour: it supplies an admissible
vertical line together with an explicit separation radius, rather than mere non-incidence.
-/

open MeasureTheory Set

namespace RHTower

/-- If the total length of equal-radius neighbourhoods of a finite set is less than `T`, then
some point of `(T,2T)` stays at least that radius from every forbidden coordinate. -/
theorem exists_Ioo_two_mul_separated_from_finset
    (F : Finset ℝ) {T delta : ℝ} (hT : 0 < T) (hdelta : 0 ≤ delta)
    (hsmall : 2 * F.card * delta < T) :
    ∃ R ∈ Ioo T (2 * T), ∀ x ∈ F, delta ≤ |R - x| := by
  classical
  let U : Set ℝ := ⋃ x ∈ F, Ioo (x - delta) (x + delta)
  have hmeasureU : volume.real U ≤ 2 * F.card * delta := by
    calc
      volume.real U ≤ ∑ x ∈ F, volume.real (Ioo (x - delta) (x + delta)) :=
        measureReal_biUnion_finset_le F fun x => Ioo (x - delta) (x + delta)
      _ = ∑ _x ∈ F, 2 * delta := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Measure.real, Real.volume_Ioo,
          ENNReal.toReal_ofReal (by linarith : 0 ≤ x + delta - (x - delta))]
        ring
      _ = 2 * F.card * delta := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
  have hmeasureIoo : volume.real (Ioo T (2 * T)) = T := by
    rw [Measure.real, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * T - T)]
    ring
  have hUfin : volume U ≠ ⊤ := by
    apply ne_of_lt
    refine (measure_biUnion_finset_le F
      fun x => Ioo (x - delta) (x + delta)).trans_lt ?_
    exact ENNReal.sum_lt_top.mpr fun x _ => by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top
  have hnotSubset : ¬Ioo T (2 * T) ⊆ U := by
    intro hsubset
    have hmono : volume.real (Ioo T (2 * T)) ≤ volume.real U :=
      measureReal_mono hsubset hUfin
    rw [hmeasureIoo] at hmono
    linarith
  obtain ⟨R, hRIoo, hRU⟩ := Set.not_subset.mp hnotSubset
  refine ⟨R, hRIoo, fun x hx => ?_⟩
  have hnot : R ∉ Ioo (x - delta) (x + delta) := by
    intro hmem
    apply hRU
    exact mem_iUnion₂.mpr ⟨x, hx, hmem⟩
  rw [mem_Ioo, not_and_or] at hnot
  by_cases hxR : x ≤ R
  · rw [abs_of_nonneg (sub_nonneg.mpr hxR)]
    rcases hnot with hleft | hright <;> linarith
  · have hRx : R ≤ x := le_of_not_ge hxR
    rw [abs_of_nonpos (sub_nonpos.mpr hRx)]
    rcases hnot with hleft | hright <;> linarith

end RHTower

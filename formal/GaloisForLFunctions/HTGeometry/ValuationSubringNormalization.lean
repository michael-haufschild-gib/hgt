import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Projective normalization over a valuation subring

A finite vector over a field, containing the coordinate `1`, can be normalized in any valuation
subring.  If its distinguished affine coordinate has nonzero residue, the normalization scale is a
unit and every original coordinate already belongs to the valuation subring.
-/

namespace GaloisForLFunctions.HTGeometry

/-- A finite vector containing `1` admits a normalization in any valuation subring, with one
normalized coordinate equal to `1`. -/
theorem exists_valuationSubring_normalization
    {L : Type*} [Field L] (O : ValuationSubring L)
    {ι : Type*} [Finite ι] [Nonempty ι]
    (v : ι → L) (hone : ∃ i, v i = 1) :
    ∃ (c : L) (_ : c ≠ 0) (w : ι → O) (i₀ : ι),
      v i₀ = c ∧
      (∀ i, O.valuation (v i) ≤ O.valuation c) ∧
      (∀ i, (w i : L) = v i / c) ∧
      w i₀ = 1 := by
  classical
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max (fun i => O.valuation (v i))
  let c := v i₀
  have hvc : O.valuation c ≠ 0 := by
    obtain ⟨j, hj⟩ := hone
    have hle := hi₀ j
    rw [hj, map_one] at hle
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hle)
  have hc : c ≠ 0 := (Valuation.ne_zero_iff O.valuation).mp hvc
  have hint : ∀ i, O.valuation (v i / c) ≤ 1 := by
    intro i
    rw [Valuation.map_div]
    exact (div_le_one₀ (pos_iff_ne_zero.mpr hvc)).2 (hi₀ i)
  let w : ι → O := fun i =>
    ⟨v i / c, (O.valuation_le_one_iff _).mp (hint i)⟩
  have hw : ∀ i, (w i : L) = v i / c := fun _ => rfl
  have hwi₀ : w i₀ = 1 := by
    apply Subtype.ext
    simp [w, c, hc]
  exact ⟨c, hc, w, i₀, rfl, hi₀, hw, hwi₀⟩

/-- If the distinguished affine coordinate remains nonzero in the residue field, every original
coordinate belongs to the valuation subring. -/
theorem valuationSubring_all_mem_of_normalized_coordinate
    {L : Type*} [Field L] (O : ValuationSubring L)
    {ι : Type*} [Finite ι] [Nonempty ι]
    {v : ι → L} {a : ι} (ha : v a = 1)
    {c : L} (_hc : c ≠ 0) {w : ι → O}
    (hmax : ∀ i, O.valuation (v i) ≤ O.valuation c)
    (hw : ∀ i, (w i : L) = v i / c)
    (ha0 : IsLocalRing.residue O (w a) ≠ 0) :
    ∀ i, v i ∈ O := by
  have hwunit : IsUnit (w a) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit (w a)).mp ha0
  have hwval : O.valuation (w a : L) = 1 :=
    (O.valuation_eq_one_iff (w a)).mp hwunit
  have hcval : O.valuation c = 1 := by
    have h := congrArg O.valuation (hw a)
    rw [ha, Valuation.map_div, map_one] at h
    rw [hwval] at h
    rw [one_div] at h
    exact inv_eq_one.mp h.symm
  intro i
  rw [← O.valuation_le_one_iff]
  simpa [hcval] using hmax i

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.RHTower.MobiusBoundaryOppositeSignTransport

/-!
# Exceptional-fallback threshold for Möbius cube transport

An almost-all short-displacement theorem can be combined with a pointwise fallback only if the
exceptional-set saving compensates for every exponent by which the fallback exceeds the critical
square-root scale.  This file isolates the exact finite budget and exponent threshold.

No Möbius cancellation estimate is assumed here.  Arithmetic inputs must separately bound the
exceptional set and provide the two displacement estimates.
-/

open scoped BigOperators

namespace RHTower

/-- Split a finite displacement budget exactly into ordinary and exceptional centers. -/
theorem sum_displacement_le_good_add_exceptional
    {ι : Type*} [DecidableEq ι]
    (s exceptional : Finset ι) (d : ι → ℝ) (goodGap fallbackGap : ℝ)
    (hgood : ∀ i ∈ s, i ∉ exceptional → d i ≤ goodGap)
    (hfallback : ∀ i ∈ s, i ∈ exceptional → d i ≤ fallbackGap) :
    ∑ i ∈ s, d i ≤
      ((s \ exceptional).card : ℝ) * goodGap +
        ((s ∩ exceptional).card : ℝ) * fallbackGap := by
  calc
    ∑ i ∈ s, d i =
        (∑ i ∈ s ∩ exceptional, d i) + ∑ i ∈ s \ exceptional, d i :=
      (Finset.sum_inter_add_sum_sdiff s exceptional d).symm
    _ ≤ ((s ∩ exceptional).card : ℝ) * fallbackGap +
        ((s \ exceptional).card : ℝ) * goodGap := by
      apply add_le_add
      · rw [← nsmul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_le_sum fun i hi =>
          hfallback i (Finset.mem_inter.mp hi).1 (Finset.mem_inter.mp hi).2
      · rw [← nsmul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_le_sum fun i hi =>
          hgood i (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hi).2
    _ = ((s \ exceptional).card : ℝ) * goodGap +
        ((s ∩ exceptional).card : ℝ) * fallbackGap := add_comm _ _

/-- A fallback exponent `θ` with exceptional-density saving `κ` reaches the critical half exactly
when `κ` pays the full excess `θ - 1/2`. -/
theorem exceptionalFallback_strictHalf_iff
    (fallbackExponent exceptionalSaving : ℝ) :
    fallbackExponent - exceptionalSaving ≤ (1 / 2 : ℝ) ↔
      fallbackExponent ≤ exceptionalSaving + (1 / 2 : ℝ) := by
  constructor <;> intro h <;> linarith

/-- Required-saving form of the exceptional-fallback threshold. -/
theorem exceptionalFallback_strictHalf_iff_requiredSaving
    (fallbackExponent exceptionalSaving : ℝ) :
    fallbackExponent - exceptionalSaving ≤ (1 / 2 : ℝ) ↔
      fallbackExponent - (1 / 2 : ℝ) ≤ exceptionalSaving := by
  constructor <;> intro h <;> linarith

/-- If the available exceptional saving is smaller than the fallback excess, strict-half cost is
impossible for this hybrid budget. -/
theorem exceptionalFallback_not_strictHalf
    {fallbackExponent exceptionalSaving : ℝ}
    (hshort : exceptionalSaving <
      fallbackExponent - (1 / 2 : ℝ)) :
    ¬ fallbackExponent - exceptionalSaving ≤ (1 / 2 : ℝ) := by
  intro h
  linarith

/-- For a cofactor fallback of exponent `1/2 + η`, global exceptional cardinality alone can make
the Hall padding dominate only when `η > 1/2 - κ`, while strict-half cost needs `η < κ`.
Such an exponent exists exactly beyond the quarter-saving threshold. -/
theorem exists_cofactorExponent_globalHall_and_strictHalf_iff
    (exceptionalSaving : ℝ) :
    (∃ η : ℝ,
      (1 / 2 : ℝ) - exceptionalSaving < η ∧ η < exceptionalSaving) ↔
      (1 / 4 : ℝ) < exceptionalSaving := by
  constructor
  · rintro ⟨η, hHall, hcost⟩
    linarith
  · intro hquarter
    exact ⟨(1 / 4 : ℝ), by linarith, hquarter⟩

end RHTower

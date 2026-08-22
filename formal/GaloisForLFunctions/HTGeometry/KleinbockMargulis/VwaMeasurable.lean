/-
# The very well approximable vectors form a Borel set

Rational accuracy losses suffice in the definition, and for a fixed loss the denominators achieving
it are unbounded exactly when, past every threshold, one denominator brings the vector within the
prescribed distance of the integer lattice.  That is a countable intersection of countable unions of
closed conditions.

Main results:
* `vwa_iff_exists_nat` — rational accuracy losses suffice.
* `measurableSet_vwa` — **the exceptional set of the Diophantine exponent is Borel**.
-/
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.Transference
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

variable {n : ℕ}

/-- The set of denominators achieving the sharpened simultaneous approximation. -/
def vwaSet (y : Fin n → ℝ) (ε : ℝ) : Set ℕ :=
  {q : ℕ | 1 ≤ q ∧ ∃ p : Fin n → ℤ, ∀ i,
    |(q : ℝ) * y i - (p i : ℝ)| ≤ (q : ℝ) ^ (-((n : ℝ))⁻¹ - ε)}

theorem vwa_iff_exists_pos (y : Fin n → ℝ) :
    VWA y ↔ ∃ ε : ℝ, 0 < ε ∧ (vwaSet y ε).Infinite := Iff.rfl

/-- Rational accuracy losses suffice. -/
theorem vwa_iff_exists_nat (y : Fin n → ℝ) :
    VWA y ↔ ∃ N : ℕ, (vwaSet y (1 / ((N : ℝ) + 1))).Infinite := by
  constructor
  · rintro ⟨ε, hε, hinf⟩
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨N, hinf.mono ?_⟩
    rintro q ⟨hq1, p, hp⟩
    refine ⟨hq1, p, fun i => le_trans (hp i) ?_⟩
    refine Real.rpow_le_rpow_of_exponent_le ?_ (by linarith [hN.le])
    exact_mod_cast hq1
  · rintro ⟨N, hinf⟩
    exact ⟨1 / ((N : ℝ) + 1), by positivity, hinf⟩

theorem measurableSet_vwaSet_infinite (ε : ℝ) :
    MeasurableSet {y : Fin n → ℝ | (vwaSet y ε).Infinite} := by
  have hEq : {y : Fin n → ℝ | (vwaSet y ε).Infinite}
      = ⋂ M : ℕ, ⋃ q : ℕ, ⋃ (_ : M < q),
          {y : Fin n → ℝ | 1 ≤ q ∧ ∃ p : Fin n → ℤ, ∀ i,
            |(q : ℝ) * y i - (p i : ℝ)| ≤ (q : ℝ) ^ (-((n : ℝ))⁻¹ - ε)} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro hinf M
      obtain ⟨q, hq, hMq⟩ := hinf.exists_gt M
      exact ⟨q, hMq, hq⟩
    · intro h
      refine Set.infinite_of_not_bddAbove ?_
      rintro ⟨M, hM⟩
      obtain ⟨q, hMq, hq⟩ := h M
      have : q ≤ M := hM hq
      omega
  rw [hEq]
  refine MeasurableSet.iInter fun M => MeasurableSet.iUnion fun q =>
    MeasurableSet.iUnion fun _ => ?_
  by_cases hq : 1 ≤ q
  · have hset : {y : Fin n → ℝ | 1 ≤ q ∧ ∃ p : Fin n → ℤ, ∀ i,
          |(q : ℝ) * y i - (p i : ℝ)| ≤ (q : ℝ) ^ (-((n : ℝ))⁻¹ - ε)}
        = ⋃ p : Fin n → ℤ, ⋂ i : Fin n,
            {y : Fin n → ℝ | |(q : ℝ) * y i - (p i : ℝ)| ≤ (q : ℝ) ^ (-((n : ℝ))⁻¹ - ε)} := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, hq, true_and]
    rw [hset]
    refine MeasurableSet.iUnion fun p => MeasurableSet.iInter fun i => ?_
    exact measurableSet_le (by fun_prop) measurable_const
  · have hempty : {y : Fin n → ℝ | 1 ≤ q ∧ ∃ p : Fin n → ℤ, ∀ i,
          |(q : ℝ) * y i - (p i : ℝ)| ≤ (q : ℝ) ^ (-((n : ℝ))⁻¹ - ε)} = ∅ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hq h.1
    rw [hempty]
    exact MeasurableSet.empty

/-- **The very well approximable vectors form a Borel set.** -/
theorem measurableSet_vwa : MeasurableSet {y : Fin n → ℝ | VWA y} := by
  have hEq : {y : Fin n → ℝ | VWA y}
      = ⋃ N : ℕ, {y : Fin n → ℝ | (vwaSet y (1 / ((N : ℝ) + 1))).Infinite} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    exact vwa_iff_exists_nat y
  rw [hEq]
  exact MeasurableSet.iUnion fun N => measurableSet_vwaSet_infinite _

end GaloisForLFunctions.HTGeometry.KleinbockMargulis

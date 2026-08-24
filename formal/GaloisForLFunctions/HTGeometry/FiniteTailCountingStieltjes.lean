import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Finite tail counts as atomic Stieltjes measures

A finite multiplicity-labelled family of real locations defines a decreasing tail-count step
function.  Its negative Stieltjes increment on `(a, b]` is exactly the counting measure of the
locations in that interval.  This is the finite, dependency-closed form needed whenever one tail
of an otherwise infinite divisor is known to be finite.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal Classical

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [Fintype α]

/-- Number of multiplicity-labelled locations strictly above a real threshold. -/
def finiteTailCount (location : α → ℝ) (t : ℝ) : ℕ :=
  (Finset.univ.filter fun x => t < location x).card

/-- Atomic counting measure of a finite multiplicity-labelled real family. -/
def finiteTailAtomicMeasure (location : α → ℝ) : Measure ℝ :=
  ∑ x ∈ (Finset.univ : Finset α), Measure.dirac (location x)

/-- Tail counts decrease with the threshold. -/
theorem finiteTailCount_antitone (location : α → ℝ) :
    Antitone (finiteTailCount location) := by
  intro a b hab
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact hab.trans_lt hx

/-- Exact finite Stieltjes law: atomic mass on `(a,b]` is the drop in the strict tail count. -/
theorem finiteTailAtomicMeasure_Ioc_eq_tailCount_sub
    (location : α → ℝ) {a b : ℝ} (hab : a ≤ b) :
    finiteTailAtomicMeasure location (Ioc a b) =
      (finiteTailCount location a - finiteTailCount location b : ℕ) := by
  let A := Finset.univ.filter fun x : α => a < location x
  let B := Finset.univ.filter fun x : α => b < location x
  let J := Finset.univ.filter fun x : α => a < location x ∧ location x ≤ b
  have hBA : B ⊆ A := by
    intro x hx
    simp only [B, A, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hab.trans_lt hx
  have hsdiff : A \ B = J := by
    ext x
    simp only [A, B, J, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_univ, true_and, not_lt]
  have hinter : B ∩ A = B := Finset.inter_eq_left.mpr hBA
  rw [finiteTailAtomicMeasure, Measure.finsetSum_apply]
  simp only [Measure.dirac_apply' _ measurableSet_Ioc]
  simp only [Set.indicator, Pi.one_apply]
  simp [finiteTailCount]
  change (J.card : ℝ≥0∞) = (A.card : ℝ≥0∞) - (B.card : ℝ≥0∞)
  rw [← hsdiff, Finset.card_sdiff, hinter, ENNReal.natCast_sub]

/-- The atom at one location has multiplicity equal to the size of its labelled fibre. -/
theorem finiteTailAtomicMeasure_singleton
    (location : α → ℝ) (t : ℝ) :
    finiteTailAtomicMeasure location {t} =
      ((Finset.univ.filter fun x : α => location x = t).card : ℕ) := by
  rw [finiteTailAtomicMeasure, Measure.finsetSum_apply]
  simp only [Measure.dirac_apply' _ (measurableSet_singleton t)]
  simp only [Set.indicator, Pi.one_apply]
  simp

end GaloisForLFunctions.HTGeometry

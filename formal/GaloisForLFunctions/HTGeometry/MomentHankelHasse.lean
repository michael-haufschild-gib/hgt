import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.StieltjesSemidefiniteCriterion

/-!
# Hasse principles for moment and Hankel positivity

Strict Hamburger positivity is equivalent to strict positivity of every finite Hankel block.
Stieltjes measure realization is equivalent to semidefiniteness of every finite ordinary and
shifted Hankel block.  Global failure is therefore detected by one finite matrix obstruction.
-/

namespace HTGeometry

open MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Strict positivity of a moment form is a Hasse predicate over finite Hankel blocks. -/
def positiveMomentFormHassePredicate : HassePredicate (ℕ → ℝ) ℕ where
  global s := PositiveMomentForm s
  atPlace n s := (momentHankelMatrix s n).PosDef
  local_global s := positiveMomentForm_iff_momentHankelMatrix_posDef (s := s)

/-- Failure of strict moment positivity occurs on one finite Hankel block. -/
theorem not_positiveMomentForm_iff_exists_hankel_not_posDef (s : ℕ → ℝ) :
    ¬ PositiveMomentForm s ↔ ∃ n : ℕ, ¬ (momentHankelMatrix s n).PosDef :=
  positiveMomentFormHassePredicate.not_global_iff_exists_local_not s

/-- Stieltjes realization is a Hasse predicate over ordinary and shifted finite Hankel blocks. -/
def stieltjesMomentHassePredicate : HassePredicate (ℕ → ℝ) (Sum ℕ ℕ) where
  global s := ∃ mu : Measure ℝ, IsFiniteMeasure mu ∧ HasStieltjesMoments s mu
  atPlace place s := Sum.elim
    (fun n => (momentHankelMatrix s n).PosSemidef)
    (fun n => (shiftedMomentHankelMatrix s n).PosSemidef) place
  local_global s := by
    rw [stieltjesMomentSequence_iff_hankel_posSemidef]
    constructor
    · rintro ⟨hordinary, hshifted⟩ place
      cases place with
      | inl n => exact hordinary n
      | inr n => exact hshifted n
    · intro h
      exact ⟨fun n => h (Sum.inl n), fun n => h (Sum.inr n)⟩

/-- Failure of global Stieltjes realization has one finite ordinary or shifted Hankel obstruction. -/
theorem no_stieltjesMomentSequence_iff_exists_finite_hankel_obstruction (s : ℕ → ℝ) :
    (¬ ∃ mu : Measure ℝ, IsFiniteMeasure mu ∧ HasStieltjesMoments s mu) ↔
      (∃ n : ℕ, ¬ (momentHankelMatrix s n).PosSemidef) ∨
      ∃ n : ℕ, ¬ (shiftedMomentHankelMatrix s n).PosSemidef := by
  rw [show (¬ ∃ mu : Measure ℝ, IsFiniteMeasure mu ∧ HasStieltjesMoments s mu) ↔
      ¬ stieltjesMomentHassePredicate.global s by rfl]
  rw [stieltjesMomentHassePredicate.not_global_iff_exists_local_not]
  constructor
  · rintro ⟨place, hplace⟩
    cases place with
    | inl n => exact Or.inl ⟨n, hplace⟩
    | inr n => exact Or.inr ⟨n, hplace⟩
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · exact ⟨Sum.inl n, hn⟩
    · exact ⟨Sum.inr n, hn⟩

end


end HTGeometry

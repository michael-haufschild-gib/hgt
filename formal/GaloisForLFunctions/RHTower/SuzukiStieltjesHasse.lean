import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.RHTower.SuzukiStieltjesCriterion

/-!
# Suzuki Stieltjes Hasse principle for RH

The corrected Suzuki criterion makes RH a predicate-level Hasse principle over finite ordinary and
shifted Hankel blocks of the literal Suzuki moment sequence.  False RH is therefore equivalent to
one finite positive-semidefiniteness obstruction.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- RH as the complete family of Suzuki ordinary and shifted finite Hankel conditions. -/
def suzukiStieltjesHassePredicate : HassePredicate Unit (Sum ℕ ℕ) where
  global _ := RiemannHypothesis
  atPlace place _ := Sum.elim
    (fun n => (HTGeometry.momentHankelMatrix suzukiStieltjesMoment n).PosSemidef)
    (fun n => (HTGeometry.shiftedMomentHankelMatrix suzukiStieltjesMoment n).PosSemidef)
    place
  local_global _ := by
    rw [riemannHypothesis_iff_suzukiStieltjes_hankel_posSemidef]
    constructor
    · rintro ⟨hordinary, hshifted⟩ place
      cases place with
      | inl n => exact hordinary n
      | inr n => exact hshifted n
    · intro h
      exact ⟨fun n => h (Sum.inl n), fun n => h (Sum.inr n)⟩

/-- False RH is exactly failure of one finite ordinary or shifted Suzuki Hankel block. -/
theorem not_riemannHypothesis_iff_exists_suzuki_finite_hankel_obstruction :
    ¬ RiemannHypothesis ↔
      (∃ n : ℕ,
        ¬ (HTGeometry.momentHankelMatrix suzukiStieltjesMoment n).PosSemidef) ∨
      ∃ n : ℕ,
        ¬ (HTGeometry.shiftedMomentHankelMatrix suzukiStieltjesMoment n).PosSemidef := by
  rw [show (¬ RiemannHypothesis) ↔ ¬ suzukiStieltjesHassePredicate.global () by rfl]
  rw [suzukiStieltjesHassePredicate.not_global_iff_exists_local_not]
  constructor
  · rintro ⟨place, hplace⟩
    cases place with
    | inl n => exact Or.inl ⟨n, hplace⟩
    | inr n => exact Or.inr ⟨n, hplace⟩
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · exact ⟨Sum.inl n, hn⟩
    · exact ⟨Sum.inr n, hn⟩

end RHTower

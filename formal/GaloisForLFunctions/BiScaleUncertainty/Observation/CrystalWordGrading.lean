import GaloisForLFunctions.HTGeometry.ProjectiveHorizonCatalanObservationMatroid

/-!
# Crystal-word gradings of reciprocal observation histories

The modified-major-index identity of Dombos--Jang,
arXiv:2611.17443, Proposition `rev_maj`, is a telescoping law for
binary words. Applied to the corpus's Dyck encoding, it shifts the
generating polynomial of length-`n` histories by exactly `q^(n+1)`.
-/

open scoped BigOperators
open DyckStep
namespace GaloisForLFunctions.BiScaleUncertainty.Observation
open GaloisForLFunctions.HTGeometry

/-- Weighted descents, including the terminal descent to a dummy up-step. -/
def modifiedMajorFrom : ℕ → List DyckStep → ℕ
  | _, [] => 0
  | _, [U] => 0
  | k, [D] => k
  | k, a :: b :: w =>
    (if a = D ∧ b = U then k else 0) + modifiedMajorFrom (k + 1) (b :: w)

/-- Sum of ascent positions, with no terminal correction. -/
def comajorFrom : ℕ → List DyckStep → ℕ
  | _, [] => 0
  | _, [_] => 0
  | k, a :: b :: w =>
    (if a = U ∧ b = D then k else 0) + comajorFrom (k + 1) (b :: w)

/-- An offset leaves only the initial down-step as a boundary term. -/
theorem modifiedMajorFrom_balance (w : List DyckStep) (k : ℕ) :
    modifiedMajorFrom (k + 1) w = comajorFrom (k + 1) w + w.count D +
      (if w.head? = some D then k else 0) := by
  induction w generalizing k with
  | nil => simp [modifiedMajorFrom, comajorFrom]
  | cons a w ih =>
    cases w with
    | nil => cases a <;> simp [modifiedMajorFrom, comajorFrom]
    | cons b w =>
      have h := ih (k + 1)
      cases a <;> cases b <;>
        simp [modifiedMajorFrom, comajorFrom, List.count_cons] at h ⊢ <;> omega

/-- The two statistics differ by exactly the number of down-steps. -/
theorem modifiedMajor_eq_comajor_add_count (w : List DyckStep) :
    modifiedMajorFrom 1 w = comajorFrom 1 w + w.count D := by
  simpa only [Nat.zero_add, ite_self, Nat.add_zero] using modifiedMajorFrom_balance w 0

/-- The Dyck specialization of the binary-word grading shift. -/
theorem dyck_modifiedMajor_eq (p : DyckWord) :
    modifiedMajorFrom 1 p.toList = comajorFrom 1 p.toList + p.semilength := by
  rw [modifiedMajor_eq_comajor_add_count, p.semilength_eq_count_D]

/-- A reciprocal history contributes one more down-step than its original length. -/
theorem reciprocal_modifiedMajor_eq (p : ReciprocalObservationWord) :
    modifiedMajorFrom 1 p.toDyckWord.toList =
      comajorFrom 1 p.toDyckWord.toList + (p.toList.length + 1) := by
  rw [dyck_modifiedMajor_eq, reciprocalObservationWord_toDyckWord_semilength]

variable {R : Type*} [CommSemiring R]

/-- Exact regrading of each observation history, over any commutative coefficient semiring. -/
theorem reciprocal_crystal_weight (q : R) (p : ReciprocalObservationWord) :
    q ^ modifiedMajorFrom 1 p.toDyckWord.toList =
      q ^ (p.toList.length + 1) * q ^ comajorFrom 1 p.toDyckWord.toList := by
  rw [reciprocal_modifiedMajor_eq, pow_add, mul_comm]

/-- The entire fixed-length generating polynomial acquires one common grading factor. -/
theorem reciprocal_crystal_generating_shift (q : R) (n : ℕ) :
    (∑ p : {p : ReciprocalObservationWord // p.toList.length = n},
      q ^ modifiedMajorFrom 1 p.1.toDyckWord.toList) =
      q ^ (n + 1) *
        ∑ p : {p : ReciprocalObservationWord // p.toList.length = n},
          q ^ comajorFrom 1 p.1.toDyckWord.toList := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [reciprocal_crystal_weight, p.2]

/-- Forgetting the grading recovers the existing Catalan count exactly. -/
theorem reciprocal_crystal_generating_one (n : ℕ) :
    (∑ p : {p : ReciprocalObservationWord // p.toList.length = n},
      (1 : R) ^ modifiedMajorFrom 1 p.1.toDyckWord.toList) = (catalan (n + 1) : R) := by
  simp only [one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    card_reciprocalObservationWord_length_eq_catalan]

#print axioms modifiedMajor_eq_comajor_add_count
#print axioms reciprocal_crystal_generating_shift
#print axioms reciprocal_crystal_generating_one

end GaloisForLFunctions.BiScaleUncertainty.Observation

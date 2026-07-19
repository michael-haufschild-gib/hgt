import GaloisForLFunctions.HTGeometry.RectangularKreinInertia
import Mathlib.InformationTheory.Hamming

/-!
# The sign chamber grading is a Hamming distance

The coordinate walls `c j = 0` cut a real coefficient space into open orthants, and the chambers are
the sign patterns.  The count of negative coordinates — which is the negative Krein index of the
associated Pick kernel — is exactly the Hamming distance of the chamber's sign pattern from the
all-positive pattern.

That identification is combinatorial and independent of any measure: it says the chamber grading is
the graph distance in the sign hypercube, where adjacency is a single coordinate flip.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Classical

/-- The number of negative coordinates of a real coefficient vector. -/
def negCount {d : ℕ} (c : Fin d → ℝ) : ℕ :=
  (Finset.univ.filter fun j => c j < 0).card

/-- The sign pattern of a coefficient vector, as a point of the chamber hypercube. -/
def signPattern {d : ℕ} (c : Fin d → ℝ) : Fin d → Bool :=
  fun j => decide (c j < 0)

/-- The all-positive chamber. -/
def positiveChamber (d : ℕ) : Fin d → Bool := fun _ => false

/-- **The chamber grading is the Hamming distance from the positive chamber.**  The number of
negative coordinates equals the graph distance of the sign pattern from the all-positive pattern in
the sign hypercube. -/
theorem negCount_eq_hammingDist {d : ℕ} (c : Fin d → ℝ) :
    negCount c = hammingDist (signPattern c) (positiveChamber d) := by
  classical
  rw [negCount, hammingDist]
  congr 1
  ext j
  simp [signPattern, positiveChamber]

/-- A coefficient vector lies in the positive chamber exactly when no coordinate is negative. -/
theorem signPattern_eq_positiveChamber_iff {d : ℕ} (c : Fin d → ℝ) :
    signPattern c = positiveChamber d ↔ ∀ j, 0 ≤ c j := by
  constructor
  · intro h j
    have := congrFun h j
    simp only [signPattern, positiveChamber, decide_eq_false_iff_not, not_lt] at this
    exact this
  · intro h
    funext j
    simp only [signPattern, positiveChamber, decide_eq_false_iff_not, not_lt]
    exact h j

/-- **The positive chamber is exactly the zero of the grading.** -/
theorem negCount_eq_zero_iff {d : ℕ} (c : Fin d → ℝ) :
    negCount c = 0 ↔ ∀ j, 0 ≤ c j := by
  rw [negCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h j
    exact not_lt.1 (h (Finset.mem_univ j))
  · intro h j _
    exact not_lt.2 (h j)

/-- The grading is bounded by the ambient dimension. -/
theorem negCount_le {d : ℕ} (c : Fin d → ℝ) : negCount c ≤ d := by
  rw [negCount]
  calc (Finset.univ.filter fun j => c j < 0).card
      ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_filter_le _ _
    _ = d := by simp

end

end GaloisForLFunctions.HTGeometry

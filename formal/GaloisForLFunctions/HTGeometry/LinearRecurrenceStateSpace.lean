import GaloisForLFunctions.HTGeometry.FiniteFieldStateSpaceHankelRank
import Mathlib.Algebra.LinearRecurrence

/-!
# Linear recurrences as finite state-space observations

Every solution of an order-`d` linear recurrence has the canonical `d`-coordinate sliding-window
state.  Mathlib's `LinearRecurrence.tupleSucc` is its transition map.  Taking the matrix of that
map and reporting the first coordinate gives an explicit state-space realization of the original
sequence.  Consequently every finite-order recurrent observation has singular Hankel block in
size `d+1`.

This supplies the converse direction needed to connect the corpus with finite-memory system
identification, linear recurrent neural networks, weighted automata, finite Markov observation
models, and sampled physical response laws.
-/

open scoped BigOperators Matrix

namespace HTGeometry

noncomputable section

/-- The length-`order` observation window beginning at label `n`. -/
def linearRecurrenceWindow {K : Type*} [CommSemiring K]
    (E : LinearRecurrence K) (u : ℕ → K) (n : ℕ) : Fin E.order → K :=
  fun i ↦ u (n + (i : ℕ))

/-- The recurrence transition advances the complete observation window by one label. -/
theorem linearRecurrence_tupleSucc_window
    {K : Type*} [CommSemiring K] (E : LinearRecurrence K) {u : ℕ → K}
    (hu : E.IsSolution u) (n : ℕ) :
    E.tupleSucc (linearRecurrenceWindow E u n) =
      linearRecurrenceWindow E u (n + 1) := by
  ext i
  rw [LinearRecurrence.tupleSucc]
  dsimp [linearRecurrenceWindow]
  split_ifs with hi
  · congr 1
    omega
  · have hilast : (i : ℕ) + 1 = E.order := by omega
    rw [← hu n]
    congr 1
    omega

/-- Iterating the recurrence transition from the initial window gives the window at label `n`. -/
theorem linearRecurrence_tupleSucc_pow_initial
    {K : Type*} [CommSemiring K] (E : LinearRecurrence K) {u : ℕ → K}
    (hu : E.IsSolution u) (n : ℕ) :
    (E.tupleSucc ^ n) (fun i ↦ u (i : ℕ)) =
      linearRecurrenceWindow E u n := by
  induction n with
  | zero =>
      ext i
      change u (i : ℕ) = u (0 + (i : ℕ))
      rw [zero_add]
  | succ n ih =>
      rw [pow_succ']
      change E.tupleSucc ((E.tupleSucc ^ n) (fun i ↦ u (i : ℕ))) = _
      rw [ih, linearRecurrence_tupleSucc_window E hu n]

/-- Companion transition matrix obtained from the canonical recurrence window update. -/
def linearRecurrenceCompanionMatrix {K : Type*} [CommSemiring K]
    (E : LinearRecurrence K) : Matrix (Fin E.order) (Fin E.order) K :=
  LinearMap.toMatrix' E.tupleSucc

/-- Matrix powers of the companion transition act exactly like iterates of `tupleSucc`. -/
theorem linearRecurrenceCompanionMatrix_pow_mulVec
    {K : Type*} [CommSemiring K] (E : LinearRecurrence K)
    (v : Fin E.order → K) (n : ℕ) :
    (linearRecurrenceCompanionMatrix E ^ n) *ᵥ v = (E.tupleSucc ^ n) v := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (linearRecurrenceCompanionMatrix E ^ (n + 1)) *ᵥ v =
            linearRecurrenceCompanionMatrix E *ᵥ
              ((linearRecurrenceCompanionMatrix E ^ n) *ᵥ v) := by
              rw [pow_succ']
              exact (Matrix.mulVec_mulVec v
                (linearRecurrenceCompanionMatrix E)
                (linearRecurrenceCompanionMatrix E ^ n)).symm
        _ = linearRecurrenceCompanionMatrix E *ᵥ ((E.tupleSucc ^ n) v) := by
              rw [ih]
        _ = E.tupleSucc ((E.tupleSucc ^ n) v) := by
              rw [linearRecurrenceCompanionMatrix, LinearMap.toMatrix'_mulVec]
        _ = (E.tupleSucc ^ (n + 1)) v := by
              rw [pow_succ']
              rfl

/-- The coordinate reported by the companion realization. -/
def linearRecurrenceOutput {K : Type*} [CommSemiring K]
    (E : LinearRecurrence K) (horder : E.order ≠ 0) : Fin E.order → K :=
  Pi.single ⟨0, Nat.pos_of_ne_zero horder⟩ 1

/-- **Explicit recurrence realization.**  Reporting the first coordinate of the companion state
recovers the recurrence solution at every observation label. -/
theorem algebraicStateSpaceResponse_linearRecurrence
    {K : Type*} [Field K] (E : LinearRecurrence K) {u : ℕ → K}
    (hu : E.IsSolution u) (horder : E.order ≠ 0) :
    algebraicStateSpaceResponse
        (linearRecurrenceCompanionMatrix E)
        (fun i ↦ u (i : ℕ))
        (linearRecurrenceOutput E horder) = u := by
  funext n
  rw [algebraicStateSpaceResponse,
    linearRecurrenceCompanionMatrix_pow_mulVec,
    linearRecurrence_tupleSucc_pow_initial E hu n]
  simp [linearRecurrenceOutput, linearRecurrenceWindow, single_dotProduct]

/-- Every positive-order recurrence solution has a state-space realization of the same dimension. -/
theorem algebraicStateSpaceDimensionAtMost_of_linearRecurrence
    {K : Type*} [Field K] (E : LinearRecurrence K) {u : ℕ → K}
    (hu : E.IsSolution u) (horder : E.order ≠ 0) :
    AlgebraicStateSpaceDimensionAtMost E.order u := by
  refine ⟨linearRecurrenceCompanionMatrix E,
    (fun i ↦ u (i : ℕ)), linearRecurrenceOutput E horder, ?_⟩
  exact (algebraicStateSpaceResponse_linearRecurrence E hu horder).symm

/-- Every order-`d` recurrence solution has zero leading Hankel determinant in size `d+1`. -/
theorem det_algebraicHankelMatrix_succ_eq_zero_of_linearRecurrence
    {K : Type*} [Field K] (E : LinearRecurrence K) {u : ℕ → K}
    (hu : E.IsSolution u) (horder : E.order ≠ 0) :
    (algebraicHankelMatrix u (E.order + 1)).det = 0 :=
  det_algebraicHankelMatrix_succ_eq_zero_of_stateSpaceDimensionAtMost
    (algebraicStateSpaceDimensionAtMost_of_linearRecurrence E hu horder)

end

end HTGeometry

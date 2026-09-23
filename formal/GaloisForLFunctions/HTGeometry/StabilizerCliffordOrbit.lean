import GaloisForLFunctions.HTGeometry.StabilizerTwoDesign
import GaloisForLFunctions.HTGeometry.TwoReplicaGlobalCliffordTwirlRange

/-!
# The six single-qubit stabilizer states are a Clifford orbit of the computational zero

Each of the six single-qubit stabilizer amplitudes is the first column of an explicit Clifford
matrix: the identity, the square of the `X` quarter turn, and the two quarter turns about `X` and
`Y` together with their inverses.  Acting on the computational zero therefore reaches every
stabilizer state up to a unit phase.
-/

open Matrix

open QuantumAlg

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-- The computational zero state of one qubit. -/
def boolZeroState : Bool → ℂ := fun b => if b then 0 else 1

/-- The six single-qubit stabilizer amplitudes, indexed by `Bool`. -/
def boolStabAmp (t : Fin 6) : Bool → ℂ :=
  fun b => stabAmp rt2inv t (if b then 1 else 0)

theorem mulVec_boolZeroState (M : Matrix Bool Bool ℂ) :
    M *ᵥ boolZeroState = fun x => M x false := by
  funext x
  rw [Matrix.mulVec, dotProduct, Fintype.sum_bool]
  simp [boolZeroState]

/-- Cliffords carrying the computational zero to each of the six stabilizer states. -/
def stabClifford : Fin 6 → QubitTwoDesign.BinaryOctahedral :=
  ![1,
    cliffordQuarterTurnCode 0 * cliffordQuarterTurnCode 0,
    (cliffordQuarterTurnCode 1)⁻¹,
    cliffordQuarterTurnCode 1,
    cliffordQuarterTurnCode 0,
    (cliffordQuarterTurnCode 0)⁻¹]

theorem booleanQubitClifford_quarterTurn_inv_matrix (a : Fin 3) :
    booleanQubitClifford (cliffordQuarterTurnCode a)⁻¹ =
      rt2inv • (1 - Complex.I • finiteQubitPauli a) := by
  rw [← booleanQubitClifford_conjTranspose_eq_inv, booleanQubitClifford_quarterTurn_matrix]
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
    Matrix.conjTranspose_smul, finiteQubitPauli_isHermitian a]
  rw [rt2inv_conj]
  congr 1
  rw [RCLike.star_def, Complex.conj_I]
  module

theorem stabClifford_zero : stabClifford 0 = 1 := rfl
theorem stabClifford_one :
    stabClifford 1 = cliffordQuarterTurnCode 0 * cliffordQuarterTurnCode 0 := rfl
theorem stabClifford_two : stabClifford 2 = (cliffordQuarterTurnCode 1)⁻¹ := rfl
theorem stabClifford_three : stabClifford 3 = cliffordQuarterTurnCode 1 := rfl
theorem stabClifford_four : stabClifford 4 = cliffordQuarterTurnCode 0 := rfl
theorem stabClifford_five : stabClifford 5 = (cliffordQuarterTurnCode 0)⁻¹ := rfl

theorem finiteQubitPauli_zero_apply :
    finiteQubitPauli 0 = fun x y => if x = y then (0 : ℂ) else 1 := by
  rw [finiteQubitPauli]
  simp

theorem finiteQubitPauli_one_apply :
    finiteQubitPauli 1 = fun x y =>
      if x = y then (0 : ℂ) else if x = false then -Complex.I else Complex.I := by
  rw [finiteQubitPauli]
  norm_num

theorem stabClifford_mulVec_zero :
    booleanQubitClifford (stabClifford 0) *ᵥ boolZeroState = boolStabAmp 0 := by
  rw [stabClifford_zero, booleanQubitClifford_one, mulVec_boolZeroState]
  funext b
  cases b <;> simp [boolStabAmp, stabAmp]

theorem stabClifford_mulVec_one :
    booleanQubitClifford (stabClifford 1) *ᵥ boolZeroState =
      Complex.I • boolStabAmp 1 := by
  rw [stabClifford_one, booleanQubitClifford_mul, booleanQubitClifford_quarterTurn_matrix,
    mulVec_boolZeroState]
  funext b
  rw [Matrix.mul_apply, Fintype.sum_bool]
  have hr : rt2inv ^ (2 : ℕ) = 1 / 2 := by
    rw [sq]
    exact rt2inv_mul_self
  cases b
  · simp [finiteQubitPauli_zero_apply, boolStabAmp, stabAmp]
    linear_combination rt2inv ^ (2 : ℕ) * Complex.I_sq
  · simp [finiteQubitPauli_zero_apply, boolStabAmp, stabAmp]
    linear_combination (2 * Complex.I) * hr

theorem stabClifford_mulVec_two :
    booleanQubitClifford (stabClifford 2) *ᵥ boolZeroState = boolStabAmp 2 := by
  rw [stabClifford_two, booleanQubitClifford_quarterTurn_inv_matrix, mulVec_boolZeroState]
  funext b
  cases b <;>
    · simp [finiteQubitPauli_one_apply, boolStabAmp, stabAmp]

theorem stabClifford_mulVec_three :
    booleanQubitClifford (stabClifford 3) *ᵥ boolZeroState = boolStabAmp 3 := by
  rw [stabClifford_three, booleanQubitClifford_quarterTurn_matrix, mulVec_boolZeroState]
  funext b
  cases b <;>
    · simp [finiteQubitPauli_one_apply, boolStabAmp, stabAmp]

theorem stabClifford_mulVec_four :
    booleanQubitClifford (stabClifford 4) *ᵥ boolZeroState = boolStabAmp 4 := by
  rw [stabClifford_four, booleanQubitClifford_quarterTurn_matrix, mulVec_boolZeroState]
  funext b
  cases b <;>
    · simp [finiteQubitPauli_zero_apply, boolStabAmp, stabAmp]

theorem stabClifford_mulVec_five :
    booleanQubitClifford (stabClifford 5) *ᵥ boolZeroState = boolStabAmp 5 := by
  rw [stabClifford_five, booleanQubitClifford_quarterTurn_inv_matrix, mulVec_boolZeroState]
  funext b
  cases b <;>
    · simp [finiteQubitPauli_zero_apply, boolStabAmp, stabAmp]

/-- **The six stabilizer states are Clifford images of the computational zero.** -/
theorem booleanQubitClifford_stabClifford_mulVec (t : Fin 6) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      booleanQubitClifford (stabClifford t) *ᵥ boolZeroState = c • boolStabAmp t := by
  fin_cases t
  · exact ⟨1, by norm_num, by rw [one_smul]; exact stabClifford_mulVec_zero⟩
  · exact ⟨Complex.I, by simp, stabClifford_mulVec_one⟩
  · exact ⟨1, by norm_num, by rw [one_smul]; exact stabClifford_mulVec_two⟩
  · exact ⟨1, by norm_num, by rw [one_smul]; exact stabClifford_mulVec_three⟩
  · exact ⟨1, by norm_num, by rw [one_smul]; exact stabClifford_mulVec_four⟩
  · exact ⟨1, by norm_num, by rw [one_smul]; exact stabClifford_mulVec_five⟩

end GaloisForLFunctions.HTGeometry

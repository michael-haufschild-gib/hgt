import GaloisForLFunctions.RHTower.EulerSquarefreeWickGammaSixBistochasticRecurrence
import GaloisForLFunctions.RHTower.EulerSquarefreeWickInteractionCohomology

/-!
# EWQ diagonal-gauge expectation versus Gamma-six dephasing

The literal simultaneous flip of the two Euler--Wick gauges is an involution.  Its normalized
average is therefore an idempotent conditional expectation, and the raw checkerboard interaction
is fixed by it.  In contrast, the completed Gamma-six channel is idempotent exactly at neutral
horizontal grade.

This separates two operations that can look deceptively similar: reflection-pair normalization is
not an equivariant landing of the literal finite-gauge expectation away from the critical line.
Any route using naturality of those averages must construct that naturality from the arithmetic
source; it cannot obtain it from positivity or coefficient faithfulness alone.
-/

open Complex Matrix
open scoped ComplexOrder MatrixOrder

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The nontrivial involution of the two-point gauge space. -/
def finTwoFlip (x : Fin 2) : Fin 2 :=
  if x = 0 then 1 else 0

@[simp] theorem finTwoFlip_zero : finTwoFlip 0 = 1 := by
  simp [finTwoFlip]

@[simp] theorem finTwoFlip_one : finTwoFlip 1 = 0 := by
  simp [finTwoFlip]

@[simp] theorem finTwoFlip_involutive (x : Fin 2) :
    finTwoFlip (finTwoFlip x) = x := by
  fin_cases x <;> simp

@[simp] theorem finTwoAnchoredSign_flip (x : Fin 2) :
    finTwoAnchoredSign (finTwoFlip x) = -finTwoAnchoredSign x := by
  fin_cases x <;> simp

/-- Simultaneous flip of both independent Euler--Wick residue gauges. -/
def eulerWickTwoGaugeDiagonalFlip (x : Fin 2 × Fin 2) : Fin 2 × Fin 2 :=
  (finTwoFlip x.1, finTwoFlip x.2)

@[simp] theorem eulerWickTwoGaugeDiagonalFlip_involutive (x : Fin 2 × Fin 2) :
    eulerWickTwoGaugeDiagonalFlip (eulerWickTwoGaugeDiagonalFlip x) = x := by
  rcases x with ⟨x, y⟩
  simp [eulerWickTwoGaugeDiagonalFlip]

/-- Haar average over the literal diagonal order-two gauge subgroup. -/
def eulerWickTwoGaugeDiagonalAverage
    (f : Fin 2 × Fin 2 → ℂ) : Fin 2 × Fin 2 → ℂ :=
  fun x => (f x + f (eulerWickTwoGaugeDiagonalFlip x)) / 2

/-- The literal diagonal gauge average is an idempotent conditional expectation. -/
theorem eulerWickTwoGaugeDiagonalAverage_idempotent
    (f : Fin 2 × Fin 2 → ℂ) :
    eulerWickTwoGaugeDiagonalAverage (eulerWickTwoGaugeDiagonalAverage f) =
      eulerWickTwoGaugeDiagonalAverage f := by
  funext x
  simp [eulerWickTwoGaugeDiagonalAverage]
  ring

/-- Raw two-gauge orbit of the four-factor Euler--Wick defect. -/
def eulerWickRawGaugeOrbitObservable (a : Fin 4 → ℂ) :
    Fin 2 × Fin 2 → ℂ :=
  fun x => eulerSquarefreeWickFourDefect
    (eulerSquarefreeWickTwoLegGauge a x.1 x.2)

/-- The joint checkerboard character is invariant under the simultaneous gauge flip. -/
theorem eulerWickRawGaugeOrbitObservable_diagonalFlip
    (a : Fin 4 → ℂ) (x : Fin 2 × Fin 2) :
    eulerWickRawGaugeOrbitObservable a (eulerWickTwoGaugeDiagonalFlip x) =
      eulerWickRawGaugeOrbitObservable a x := by
  rcases x with ⟨x, y⟩
  simp only [eulerWickRawGaugeOrbitObservable,
    eulerWickTwoGaugeDiagonalFlip, eulerSquarefreeWickFourDefect_twoLegGauge,
    finTwoAnchoredSign_flip]
  ring

/-- Diagonal gauge expectation retains the full raw interaction packet. -/
theorem eulerWickTwoGaugeDiagonalAverage_rawGaugeOrbitObservable
    (a : Fin 4 → ℂ) :
    eulerWickTwoGaugeDiagonalAverage (eulerWickRawGaugeOrbitObservable a) =
      eulerWickRawGaugeOrbitObservable a := by
  funext x
  rw [eulerWickTwoGaugeDiagonalAverage]
  rw [eulerWickRawGaugeOrbitObservable_diagonalFlip]
  ring

/-- Two applications of Gamma-six dephasing square its off-diagonal coherence factor. -/
theorem eulerWickGammaSixBalancedDephasing_comp_apply
    (a : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    eulerWickGammaSixBalancedDephasing a
        (eulerWickGammaSixBalancedDephasing a M) i j =
      if i = j then M i j
      else ((eulerWickGammaSixDephasingFactor a : ℂ) ^ 2) * M i j := by
  rw [eulerWickGammaSixBalancedDephasing_apply]
  split_ifs with hij
  · simpa [hij] using eulerWickGammaSixBalancedDephasing_apply a M i j
  · rw [eulerWickGammaSixBalancedDephasing_apply]
    simp [hij]
    ring

/-- Gamma-six dephasing is a conditional expectation exactly at neutral horizontal grade. -/
theorem eulerWickGammaSixBalancedDephasing_idempotent_iff (a : ℝ) :
    (∀ M : Matrix (Fin 2) (Fin 2) ℂ,
      eulerWickGammaSixBalancedDephasing a
          (eulerWickGammaSixBalancedDephasing a M) =
        eulerWickGammaSixBalancedDephasing a M) ↔
      a = 0 := by
  constructor
  · intro hidem
    have h := congrFun (congrFun
      (hidem (eulerWickReplicaPureProjector eulerWickPrimeFiveOddDepth))
      (0 : Fin 2)) (1 : Fin 2)
    rw [eulerWickGammaSixBalancedDephasing_comp_apply] at h
    simp [eulerWickGammaSixBalancedDephasing_apply,
      eulerWickReplicaPureProjector_apply,
      eulerWickQuadraticDepthCharacter_five_odd] at h
    have hkpos := eulerWickGammaSixDephasingFactor_pos a
    have hk : eulerWickGammaSixDephasingFactor a = 1 := by
      have hreal : eulerWickGammaSixDephasingFactor a ^ 2 =
          eulerWickGammaSixDephasingFactor a := by
        exact_mod_cast h
      nlinarith
    exact (eulerWickGammaSixDephasingFactor_eq_one_iff a).1 hk
  · rintro rfl M
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [eulerWickGammaSixBalancedDephasing_apply,
        eulerWickGammaSixDephasingFactor]

/-- Full-channel recurrence is stronger than return of one selected arithmetic state.  Two
applications of the completed depth step return every matrix exactly if and only if the horizontal
Gamma-six grade is neutral.  Thus any source theorem identifying the literal period-two depth clock
with one repeatedly used completion channel cannot hide coherence loss in an unobserved state. -/
theorem eulerWickGammaSixBalancedDepthStep_two_fullReturn_iff (a : ℝ) :
    (∀ M : Matrix (Fin 2) (Fin 2) ℂ,
      eulerWickGammaSixBalancedDepthStep a
          (eulerWickGammaSixBalancedDepthStep a M) = M) ↔
      a = 0 := by
  constructor
  · intro hreturn
    exact (eulerWickGammaSixBalancedDepthStep_two_exactReturn_iff a).1
      (hreturn (eulerWickReplicaPureProjector eulerWickPrimeFiveOddDepth))
  · rintro rfl M
    have hdephase (X : Matrix (Fin 2) (Fin 2) ℂ) :
        eulerWickGammaSixBalancedDephasing 0 X = X := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [eulerWickGammaSixBalancedDephasing_apply,
          eulerWickGammaSixDephasingFactor]
    rw [eulerWickGammaSixBalancedDepthStep, hdephase,
      eulerWickGammaSixBalancedDepthStep, hdephase]
    calc
      eulerWickReplicaPauliZ *
            (eulerWickReplicaPauliZ * M * eulerWickReplicaPauliZ) *
          eulerWickReplicaPauliZ =
          (eulerWickReplicaPauliZ * eulerWickReplicaPauliZ) * M *
            (eulerWickReplicaPauliZ * eulerWickReplicaPauliZ) := by
              simp only [mul_assoc]
      _ = M := by rw [eulerWickReplicaPauliZ_sq]; simp

end

end GaloisForLFunctions.RHTower

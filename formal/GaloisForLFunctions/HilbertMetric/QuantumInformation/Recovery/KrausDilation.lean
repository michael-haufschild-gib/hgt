import GaloisForLFunctions.HilbertMetric.QuantumInformation.Recovery.ReadyBranch
import GaloisForLFunctions.HTGeometry.MatrixQuadraticFormDetermination
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Finite Kraus channels for ready-branch recovery

Stacking a normalized rectangular Kraus family gives the corresponding
recovery isometry, and slicing the matrix of an isometry recovers a
normalized family. Thus the ready-branch Bell-fidelity optimum is
attained among finite Kraus channels.
-/

open Matrix
open scoped BigOperators Matrix

namespace GaloisForLFunctions.HilbertMetric.QuantumInformation.ReadyBranch

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Adjoint transfer for the coordinate pairing on different carriers. -/
theorem cinner_rectangular_mulVec {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix β α ℂ) (x : α → ℂ) (y : β → ℂ) :
    cinner (A *ᵥ x) y = cinner x (Aᴴ *ᵥ y) := by
  change star (A *ᵥ x) ⬝ᵥ y = star x ⬝ᵥ (Aᴴ *ᵥ y)
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec]

/-- The squared norm of the stacked output equals the quadratic form of
the sum of the Kraus Gram matrices. -/
theorem krausStack_cinner {α β κ : Type*} [Fintype α] [Fintype β] [Fintype κ]
    (A : κ → Matrix β α ℂ) (x : α → ℂ) :
    cinner x ((∑ k, (A k)ᴴ * A k) *ᵥ x) =
      (cnormSq (fun p : β × κ => ((A p.2) *ᵥ x) p.1) : ℂ) := by
  classical
  rw [Matrix.sum_mulVec, cinner_sum_right]
  simp_rw [← Matrix.mulVec_mulVec, ← cinner_rectangular_mulVec, cinner_self]
  rw [← Complex.ofReal_sum]
  congr 1
  simp only [cnormSq, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- Kraus completeness is equivalent to norm preservation of the
stacked rectangular operator. -/
theorem krausStack_norm_preserving_iff {α β κ : Type*}
    [Fintype α] [Fintype β] [Fintype κ] [DecidableEq α] (A : κ → Matrix β α ℂ) :
    (∀ x : α → ℂ, cnormSq (fun p : β × κ => ((A p.2) *ᵥ x) p.1) = cnormSq x) ↔
      ∑ k, (A k)ᴴ * A k = 1 := by
  constructor
  · intro h
    apply matrix_eq_of_quadraticForm_eq
    intro x
    change cinner x ((∑ k, (A k)ᴴ * A k) *ᵥ x) = cinner x ((1 : Matrix α α ℂ) *ᵥ x)
    rw [krausStack_cinner, h x, Matrix.one_mulVec, cinner_self]
  · intro h x
    have hc := krausStack_cinner A x
    rw [h, Matrix.one_mulVec, cinner_self] at hc
    exact Complex.ofReal_injective hc.symm

variable {F L K : Type*} [Fintype F] [Fintype L] [Fintype K] [DecidableEq F]

/-- A finite, trace-preserving Kraus family from the available register
to the recovered logical qubit. -/
structure KrausRecovery (F K : Type*) [Fintype F] [Fintype K] [DecidableEq F] where
  operator : K → Matrix Bool (Bool × F) ℂ
  completeness : ∑ k, (operator k)ᴴ * operator k = 1

/-- Stack the Kraus output amplitudes in an auxiliary register. -/
def KrausRecovery.toRecovery (A : KrausRecovery F K) : Recovery F K where
  apply :=
    { toFun := fun x p => (A.operator p.2 *ᵥ x) p.1
      map_add' := fun x y => funext fun p =>
        congrFun (Matrix.mulVec_add (A.operator p.2) x y) p.1
      map_smul' := fun c x => funext fun p =>
        congrFun (Matrix.mulVec_smul (A.operator p.2) c x) p.1 }
  norm_preserving := (krausStack_norm_preserving_iff A.operator).mpr A.completeness

private theorem recovery_matrix_slice (R : Recovery F K) (k : K)
    (x : Bool × F → ℂ) (b : Bool) :
    ((fun row i => R.apply.toMatrix' (row, k) i : Matrix Bool (Bool × F) ℂ) *ᵥ x) b =
      R.apply x (b, k) :=
  congrFun (LinearMap.toMatrix'_mulVec R.apply x) (b, k)

/-- Slice a recovery isometry at each auxiliary label to obtain Kraus operators. -/
def KrausRecovery.ofRecovery (R : Recovery F K) : KrausRecovery F K where
  operator := fun k b i => R.apply.toMatrix' (b, k) i
  completeness := by
    apply (krausStack_norm_preserving_iff _).mp
    intro x
    simpa only [recovery_matrix_slice] using R.norm_preserving x

@[simp] theorem KrausRecovery.toRecovery_ofRecovery_apply (R : Recovery F K) (x : Bool × F → ℂ) :
    (ofRecovery R).toRecovery.apply x = R.apply x :=
  funext fun p => recovery_matrix_slice R p.2 x p.1

/-- Bell-test fidelity for the channel given by a normalized Kraus family. -/
def KrausRecovery.fidelity [DecidableEq L] (W : Encoding F L) (A : KrausRecovery F K) : ℝ :=
  ReadyBranch.fidelity W A.toRecovery

@[simp] theorem KrausRecovery.fidelity_ofRecovery [DecidableEq L]
    (W : Encoding F L) (R : Recovery F K) :
    (ofRecovery R).fidelity W = ReadyBranch.fidelity W R := by
  simp only [KrausRecovery.fidelity, ReadyBranch.fidelity, matching, toRecovery_ofRecovery_apply]

/-- All finite Kraus recoveries obey the same ready-slice fidelity bound. -/
theorem KrausRecovery.fidelity_le [DecidableEq L] (W : Encoding F L) (A : KrausRecovery F K) :
    A.fidelity W ≤ (1 + Real.sqrt (cnormSq (W.signal W.ready))) / 2 :=
  ReadyBranch.fidelity_le W A.toRecovery

/-- The optimal ready-branch fidelity is attained by a normalized Kraus family. -/
theorem exists_optimal_krausRecovery [DecidableEq L] (W : Encoding F L) :
    ∃ A : KrausRecovery F (Option F),
      A.fidelity W = (1 + Real.sqrt (cnormSq (W.signal W.ready))) / 2 := by
  obtain ⟨R, hR⟩ := exists_optimal_recovery W
  exact ⟨KrausRecovery.ofRecovery R, (KrausRecovery.fidelity_ofRecovery W R).trans hR⟩

#print axioms krausStack_norm_preserving_iff
#print axioms KrausRecovery.fidelity_le
#print axioms exists_optimal_krausRecovery

end

end GaloisForLFunctions.HilbertMetric.QuantumInformation.ReadyBranch

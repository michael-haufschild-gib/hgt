import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Finite response observables

Finite signed packets are tested by translated response functions, as in equation (3) of
Araújo, arXiv:2609.05560. The finite-probe norm is an operational discrepancy; it makes no
assumption that the selected probes determine the source packet.
-/
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The response of a finite weighted source at a recipient position. -/
def finiteResponseForce {ι : Type*} [Fintype ι]
    (F : ℝ → ℝ) (w z : ι → ℝ) (x : ℝ) : ℝ := ∑ i, w i * F (z i - x)

/-- Uniform distortion on an explicitly specified nonempty finite probe panel. -/
def finiteResponseDistortion {ι κ : Type*} [Fintype ι] [Fintype κ] {n : ℕ}
    (F : ℝ → ℝ) (w z : ι → ℝ) (v t : κ → ℝ) (probe : Fin (n + 1) → ℝ) : ℝ :=
  ‖fun j => finiteResponseForce F v t (probe j) - finiteResponseForce F w z (probe j)‖

theorem finiteResponseForce_add {ι : Type*} [Fintype ι]
    (F G : ℝ → ℝ) (w z : ι → ℝ) (x : ℝ) :
    finiteResponseForce (fun u => F u + G u) w z x =
      finiteResponseForce F w z x + finiteResponseForce G w z x := by
  simp [finiteResponseForce, mul_add, Finset.sum_add_distrib]

theorem finiteResponseForce_scale {ι : Type*} [Fintype ι]
    (F : ℝ → ℝ) (w z : ι → ℝ) (a x : ℝ) :
    finiteResponseForce (fun u => a * F u) w z x = a * finiteResponseForce F w z x := by
  simp only [finiteResponseForce, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Translating a source equals translating the recipient in the opposite direction. -/
theorem finiteResponseForce_translate {ι : Type*} [Fintype ι]
    (F : ℝ → ℝ) (w z : ι → ℝ) (b x : ℝ) :
    finiteResponseForce F w (fun i => z i + b) x = finiteResponseForce F w z (x - b) := by
  unfold finiteResponseForce
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  ring

/-- The operational discrepancy is symmetric, even for signed or unnormalized sources. -/
theorem finiteResponseDistortion_symm {ι κ : Type*} [Fintype ι] [Fintype κ] {n : ℕ}
    (F : ℝ → ℝ) (w z : ι → ℝ) (v t : κ → ℝ) (probe : Fin (n + 1) → ℝ) :
    finiteResponseDistortion F w z v t probe = finiteResponseDistortion F v t w z probe := by
  unfold finiteResponseDistortion
  exact norm_sub_rev _ _

/-- Finite-probe response error obeys the triangle inequality. -/
theorem finiteResponseDistortion_triangle {ι κ τ : Type*}
    [Fintype ι] [Fintype κ] [Fintype τ] {n : ℕ}
    (F : ℝ → ℝ) (w z : ι → ℝ) (v t : κ → ℝ) (p y : τ → ℝ)
    (probe : Fin (n + 1) → ℝ) :
    finiteResponseDistortion F w z p y probe ≤
      finiteResponseDistortion F w z v t probe + finiteResponseDistortion F v t p y probe := by
  unfold finiteResponseDistortion
  simpa only [Pi.sub_def, add_comm] using norm_sub_le_norm_sub_add_norm_sub
    (fun j => finiteResponseForce F p y (probe j))
    (fun j => finiteResponseForce F v t (probe j))
    (fun j => finiteResponseForce F w z (probe j))

end
end GaloisForLFunctions.HTGeometry

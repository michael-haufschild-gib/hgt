import GaloisForLFunctions.HTGeometry.FiniteKMSWightman
import Mathlib.Data.Finset.Max

/-!
# Exact decentralized maximization for positive Gibbs mixers

The monotone-mixing mechanism used by Barbosa--Dias, arXiv:2608.17210,
applies to the corpus's Gibbs probabilities. Their strict positivity makes
global maximization equivalent to coordinatewise maximization, including ties.
All parameters and local value functions are unrestricted.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric
open _root_.HTGeometry

variable {ι A : Type*} [Fintype ι] [Nonempty ι]

/-- Gibbs-weighted joint value of an independently chosen action at each coordinate. -/
def gibbsJointValue (β : ℝ) (energy : ι → ℝ) (Q : ι → A → ℝ) (action : ι → A) : ℝ :=
  ∑ i, finiteGibbsStateWeight β energy i * Q i (action i)

omit [Nonempty ι] in
/-- Changing one action changes only its strictly positive weighted local value. -/
theorem gibbsJointValue_update [DecidableEq ι] (β : ℝ) (energy : ι → ℝ) (Q : ι → A → ℝ)
    (action : ι → A) (i : ι) (a : A) :
    gibbsJointValue β energy Q (Function.update action i a) =
      gibbsJointValue β energy Q action +
        finiteGibbsStateWeight β energy i * (Q i a-Q i (action i)) := by
  classical
  unfold gibbsJointValue
  rw [← Finset.add_sum_erase Finset.univ
    (fun j => finiteGibbsStateWeight β energy j * Q j (Function.update action i a j))
    (Finset.mem_univ i), Function.update_self]
  have hs : (∑ j ∈ Finset.univ.erase i,
      finiteGibbsStateWeight β energy j * Q j (Function.update action i a j)) =
      ∑ j ∈ Finset.univ.erase i, finiteGibbsStateWeight β energy j * Q j (action j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hs, ← Finset.add_sum_erase Finset.univ
    (fun j => finiteGibbsStateWeight β energy j * Q j (action j)) (Finset.mem_univ i)]
  ring

/-- Global maximizers are exactly products of local maximizers. -/
theorem gibbsJointValue_maximizer_iff (β : ℝ) (energy : ι → ℝ)
    (Q : ι → A → ℝ) (action : ι → A) :
    (∀ other, gibbsJointValue β energy Q other ≤ gibbsJointValue β energy Q action) ↔
      ∀ i a, Q i a ≤ Q i (action i) := by
  classical
  constructor
  · intro h i a
    have hu := h (Function.update action i a)
    rw [gibbsJointValue_update] at hu
    by_contra hn
    have hp := mul_pos (finiteGibbsStateWeight_pos β energy i)
      (sub_pos.mpr (lt_of_not_ge hn))
    linarith only [hu, hp]
  · intro h other
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (h i (other i)) (finiteGibbsStateWeight_pos β energy i).le

/-- Finite local action sets always admit a jointly optimal decentralized choice. -/
theorem exists_gibbsJointValue_maximizer [Fintype A] [Nonempty A]
    (β : ℝ) (energy : ι → ℝ) (Q : ι → A → ℝ) :
    ∃ action : ι → A, (∀ i a, Q i a ≤ Q i (action i)) ∧
      ∀ other, gibbsJointValue β energy Q other ≤ gibbsJointValue β energy Q action := by
  classical
  have hlocal (i : ι) : ∃ a : A, ∀ b : A, Q i b ≤ Q i a := by
    obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ (Q i) Finset.univ_nonempty
    exact ⟨a, fun b => ha b (Finset.mem_univ b)⟩
  choose action ha using hlocal
  exact ⟨action, ha, (gibbsJointValue_maximizer_iff β energy Q action).mpr ha⟩

/-- Every Gibbs temperature gives exactly the same set of joint maximizing actions. -/
theorem gibbsJointValue_maximizers_temperature_independent
    (β γ : ℝ) (energy otherEnergy : ι → ℝ) (Q : ι → A → ℝ) (action : ι → A) :
    (∀ other, gibbsJointValue β energy Q other ≤ gibbsJointValue β energy Q action) ↔
      ∀ other, gibbsJointValue γ otherEnergy Q other ≤ gibbsJointValue γ otherEnergy Q action := by
  rw [gibbsJointValue_maximizer_iff, gibbsJointValue_maximizer_iff]

end GaloisForLFunctions.HilbertMetric

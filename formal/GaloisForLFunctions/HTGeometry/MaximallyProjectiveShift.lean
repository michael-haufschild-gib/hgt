/-
# Maximal projective independence is shift invariant

The maximal-projectivity predicate tests only *balanced* integer characters, and a balanced
character annihilates a constant.  So adding a constant to every energy changes nothing, and every
maximally projective spectrum can be recentred to have zero sum -- which is what makes the
corresponding Hamiltonian traceless.

Main results:
* `MaximallyProjectiveEnergy.add_const` — **shift invariance**.
* `recentredEnergy`, `sum_recentredEnergy` — the zero-sum recentring.
* `maximallyProjectiveEnergy_recentredEnergy` — it stays maximally projective.
* `injective_recentredEnergy_iff` — and keeps a simple spectrum simple.
-/
import GaloisForLFunctions.HTGeometry.ReplicaCollisionExtremality

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I]

/-- **Maximal projective independence is invariant under a constant energy shift.** -/
theorem MaximallyProjectiveEnergy.add_const {E : I → ℝ} (h : MaximallyProjectiveEnergy E)
    (c : ℝ) : MaximallyProjectiveEnergy fun i => E i + c := by
  intro k hbal hsum
  refine h k hbal ?_
  have hexp : (∑ i, (k i : ℝ) * (E i + c))
      = (∑ i, (k i : ℝ) * E i) + (∑ i, (k i : ℝ)) * c := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hzero : (∑ i, (k i : ℝ)) = 0 := by
    have : ((∑ i, k i : ℤ) : ℝ) = 0 := by rw [hbal]; simp
    rwa [Int.cast_sum] at this
  rw [hexp, hzero, zero_mul, add_zero] at hsum
  exact hsum

/-- The zero-sum recentring of an energy tuple. -/
def recentredEnergy (E : I → ℝ) : I → ℝ :=
  fun i => E i - (∑ j, E j) / (Fintype.card I : ℝ)

theorem sum_recentredEnergy [Nonempty I] (E : I → ℝ) : ∑ i, recentredEnergy E i = 0 := by
  have hcard : (0 : ℝ) < (Fintype.card I : ℝ) := by
    exact_mod_cast Fintype.card_pos
  show (∑ i, (E i - (∑ j, E j) / (Fintype.card I : ℝ))) = 0
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

theorem maximallyProjectiveEnergy_recentredEnergy {E : I → ℝ} (h : MaximallyProjectiveEnergy E) :
    MaximallyProjectiveEnergy (recentredEnergy E) := by
  have := h.add_const (-((∑ j, E j) / (Fintype.card I : ℝ)))
  refine (fun k hbal hsum => this k hbal ?_)
  rw [← hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (k i : ℝ) * (E i - (∑ j, E j) / (Fintype.card I : ℝ))
      = (k i : ℝ) * (E i + -((∑ j, E j) / (Fintype.card I : ℝ)))
  ring

theorem injective_recentredEnergy_iff (E : I → ℝ) :
    Function.Injective (recentredEnergy E) ↔ Function.Injective E := by
  constructor
  · intro h a b hab
    refine h ?_
    show E a - (∑ j, E j) / (Fintype.card I : ℝ) = E b - (∑ j, E j) / (Fintype.card I : ℝ)
    rw [hab]
  · intro h a b hab
    have hab' : E a - (∑ j, E j) / (Fintype.card I : ℝ)
        = E b - (∑ j, E j) / (Fintype.card I : ℝ) := hab
    exact h (by linarith [hab'])

end GaloisForLFunctions.HTGeometry

end

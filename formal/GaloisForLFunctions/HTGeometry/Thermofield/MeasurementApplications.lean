import GaloisForLFunctions.HTGeometry.Thermofield.FinitePurification
import GaloisForLFunctions.HTGeometry.TraceDynamicsBornMartingale

/-!
# Thermal branch probabilities as paired projective measurements

Energy-basis event projectors on the two copies of the thermofield double have
joint expectation equal to the Gibbs mass of the intersection. In particular,
equal events are perfectly correlated. Their one-copy expectation equals the
existing Gibbs martingale's terminal absorption probability.

This applies the entangled-state interpretation of Maldacena,
arXiv:hep-th/0106112, to the corpus branch-observation model.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry.Thermofield

open _root_.HTGeometry TraceDynamics

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- Spectral projector of a finite energy-basis event. -/
def eventProjector (s : Finset α) : Matrix α α ℂ :=
  Matrix.diagonal fun a => if a ∈ s then 1 else 0

/-- Opposite energy measurements see the same Schmidt label. -/
theorem expectation_events (β : ℝ) (E : α → ℝ) (s t : Finset α) :
    pairExpectation (amplitude β E) (eventProjector s) (eventProjector t) =
      ((∑ a ∈ s ∩ t, finiteGibbsStateWeight β E a : ℝ) : ℂ) := by
  rw [expectation_eq_kms]
  simp only [eventProjector, Matrix.diagonal_apply, mul_ite, ite_mul,
    mul_zero, zero_mul, mul_one]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true,
    finiteKMSWightmanWeight_self]
  push_cast
  simp only [← ite_and, ← Finset.mem_inter, Finset.sum_ite_mem, Finset.univ_inter]

/-- A repeated event on both copies has its ordinary Gibbs probability. -/
theorem expectation_same_event (β : ℝ) (E : α → ℝ) (s : Finset α) :
    pairExpectation (amplitude β E) (eventProjector s) (eventProjector s) =
      ((∑ a ∈ s, finiteGibbsStateWeight β E a : ℝ) : ℂ) := by
  rw [expectation_events, Finset.inter_self]

theorem eventProjector_univ : eventProjector (Finset.univ : Finset α) = 1 := by
  ext a b
  simp [eventProjector, Matrix.diagonal_apply, Matrix.one_apply]

/-- Observing an event in one copy is a Gibbs event measurement. -/
theorem expectation_event (β : ℝ) (E : α → ℝ) (s : Finset α) :
    pairExpectation (amplitude β E) (eventProjector s) 1 =
      ((∑ a ∈ s, finiteGibbsStateWeight β E a : ℝ) : ℂ) := by
  rw [← eventProjector_univ, expectation_events, Finset.inter_univ]

/-- The branch martingale's absorbed Born mass is a concrete one-copy expectation. -/
theorem expectation_event_eq_absorption (β : ℝ) (E : α → ℝ) (s : Finset α) :
    pairExpectation (amplitude β E) (eventProjector s) 1 =
      ((gibbsMeasure β E).real {a | gibbsBranchWeight β E s ⊤ a = 1} : ℂ) := by
  rw [expectation_event, gibbsBranchWeight_born_absorption]

/-- Perfect cross-copy agreement survives passage to the branch-observation model. -/
theorem expectation_same_event_eq_absorption (β : ℝ) (E : α → ℝ) (s : Finset α) :
    pairExpectation (amplitude β E) (eventProjector s) (eventProjector s) =
      ((gibbsMeasure β E).real {a | gibbsBranchWeight β E s ⊤ a = 1} : ℂ) := by
  rw [expectation_same_event, gibbsBranchWeight_born_absorption]

end

end GaloisForLFunctions.HTGeometry.Thermofield

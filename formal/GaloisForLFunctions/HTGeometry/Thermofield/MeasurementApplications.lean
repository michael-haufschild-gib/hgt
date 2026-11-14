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
  rw [pairExpectation, amplitude_adjoint]
  simp only [amplitude, eventProjector, Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  calc
    _ = ∑ a, if a ∈ s ∩ t then (finiteGibbsStateWeight β E a : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases hs : a ∈ s
      · by_cases ht : a ∈ t
        · simp only [hs, ht, Finset.mem_inter, and_self, if_true, mul_one]
          rw [← Complex.ofReal_mul,
            Real.mul_self_sqrt (finiteGibbsStateWeight_pos β E a).le]
        · simp [hs, ht]
      · simp [hs]
    _ = _ := by
      simp only [Finset.sum_ite_mem, Finset.univ_inter]
      push_cast
      rfl

/-- A repeated event on both copies has its ordinary Gibbs probability. -/
theorem expectation_same_event (β : ℝ) (E : α → ℝ) (s : Finset α) :
    pairExpectation (amplitude β E) (eventProjector s) (eventProjector s) =
      ((∑ a ∈ s, finiteGibbsStateWeight β E a : ℝ) : ℂ) := by
  rw [expectation_events, Finset.inter_self]

omit [Nonempty α] in
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

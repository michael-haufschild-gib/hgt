import GaloisForLFunctions.HTGeometry.FiniteKMSWightman
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Martingale.Basic

/-!
# Born martingales from thermal half-density amplitudes

The finite Gibbs probabilities define a probability measure. Conditional event weights
form bounded martingales under every observation filtration. Complete observation
absorbs weights at zero or one with the original thermofield squared-amplitude masses.
This is a constructed finite thermal realization of the martingale mechanism.

Source: Singh, arXiv:2609.10571, section 6.3.
-/

set_option autoImplicit false

open scoped BigOperators ENNReal
open MeasureTheory
namespace GaloisForLFunctions.HTGeometry.TraceDynamics
open _root_.HTGeometry
noncomputable section
variable {α : Type*} [Fintype α] [Nonempty α]
local instance : MeasurableSpace α := ⊤

def gibbsPMF (β : ℝ) (E : α → ℝ) : PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal (finiteGibbsStateWeight β E a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => (finiteGibbsStateWeight_pos β E a).le),
      sum_finiteGibbsStateWeight_eq_one, ENNReal.ofReal_one])

def gibbsMeasure (β : ℝ) (E : α → ℝ) : Measure α := (gibbsPMF β E).toMeasure

instance gibbsMeasure_isProbabilityMeasure (β : ℝ) (E : α → ℝ) :
    IsProbabilityMeasure (gibbsMeasure β E) :=
  inferInstanceAs (IsProbabilityMeasure (gibbsPMF β E).toMeasure)

/-- Conditional branch weight in any finite observation algebra. -/
def gibbsBranchWeight (β : ℝ) (E : α → ℝ) (s : Finset α) (m : MeasurableSpace α) : α → ℝ :=
  (gibbsMeasure β E)[(s : Set α).indicator (fun _ => (1 : ℝ)) | m]

theorem gibbsMeasure_real_finset (β : ℝ) (E : α → ℝ) (s : Finset α) :
    (gibbsMeasure β E).real s = ∑ a ∈ s, finiteGibbsStateWeight β E a := by
  rw [measureReal_def, gibbsMeasure, PMF.toMeasure_apply_finset]
  simp only [gibbsPMF, PMF.ofFintype_apply]
  rw [ENNReal.toReal_sum (fun a _ => ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro a _
  exact ENNReal.toReal_ofReal (finiteGibbsStateWeight_pos β E a).le

/-- Every branch process is an actual bounded-event martingale under arbitrary observation. -/
theorem gibbsBranchWeight_martingale (β : ℝ) (E : α → ℝ) (s : Finset α)
    (F : Filtration ℕ (⊤ : MeasurableSpace α)) :
    Martingale (fun n => gibbsBranchWeight β E s (F n)) F (gibbsMeasure β E) :=
  martingale_condExp _ F _

/-- Initial branch weight is its exact Gibbs/Born event probability. -/
theorem gibbsBranchWeight_initial (β : ℝ) (E : α → ℝ) (s : Finset α) :
    gibbsBranchWeight β E s ⊥ = fun _ => ∑ a ∈ s, finiteGibbsStateWeight β E a := by
  unfold gibbsBranchWeight
  rw [condExp_bot']
  simp only [probReal_univ, inv_one, one_smul]
  rw [integral_indicator (show MeasurableSet[⊤] (s : Set α) from trivial), setIntegral_const]
  simp only [smul_eq_mul, mul_one, gibbsMeasure_real_finset]

/-- Complete observation absorbs every branch weight at zero or one. -/
theorem gibbsBranchWeight_terminal (β : ℝ) (E : α → ℝ) (s : Finset α) :
    gibbsBranchWeight β E s ⊤ = (s : Set α).indicator (fun _ => (1 : ℝ)) := by
  apply condExp_of_stronglyMeasurable le_rfl
  · exact stronglyMeasurable_const.indicator (show MeasurableSet[⊤] (s : Set α) from trivial)
  · exact (integrable_const 1).indicator (show MeasurableSet[⊤] (s : Set α) from trivial)

/-- Expected branch weight is unchanged by any coarse observation. -/
theorem gibbsBranchWeight_expectation (β : ℝ) (E : α → ℝ) (s : Finset α)
    (m : MeasurableSpace α) :
    (∫ a, gibbsBranchWeight β E s m a ∂gibbsMeasure β E) =
      ∑ a ∈ s, finiteGibbsStateWeight β E a := by
  rw [gibbsBranchWeight, integral_condExp le_top,
    integral_indicator (show MeasurableSet[⊤] (s : Set α) from trivial), setIntegral_const]
  simp only [smul_eq_mul, mul_one, gibbsMeasure_real_finset]

/-- The probability of terminal absorption at one equals the initial branch weight. -/
theorem gibbsBranchWeight_born_absorption (β : ℝ) (E : α → ℝ) (s : Finset α) :
    (gibbsMeasure β E).real {a | gibbsBranchWeight β E s ⊤ a = 1} =
      ∑ a ∈ s, finiteGibbsStateWeight β E a := by
  rw [gibbsBranchWeight_terminal]
  have heq : {a : α | (s : Set α).indicator (fun _ => (1 : ℝ)) a = 1} = s := by
    ext a
    by_cases h : a ∈ s <;> simp [h]
  rw [heq, gibbsMeasure_real_finset]

/-- Conditional branch weights stay in the probability interval almost everywhere. -/
theorem gibbsBranchWeight_bounds (β : ℝ) (E : α → ℝ) (s : Finset α)
    (m : MeasurableSpace α) :
    ∀ᵐ a ∂gibbsMeasure β E, 0 ≤ gibbsBranchWeight β E s m a ∧
      gibbsBranchWeight β E s m a ≤ 1 := by
  have hnonneg : (0 : α → ℝ) ≤ᵐ[gibbsMeasure β E]
      (s : Set α).indicator (fun _ => (1 : ℝ)) :=
    Filter.Eventually.of_forall fun a => by by_cases h : a ∈ s <;> simp [h]
  have hle : (s : Set α).indicator (fun _ => (1 : ℝ)) ≤ᵐ[gibbsMeasure β E]
      (fun _ => (1 : ℝ)) :=
    Filter.Eventually.of_forall fun a => by by_cases h : a ∈ s <;> simp [h]
  have hlo := condExp_nonneg (m := m) hnonneg
  have hhi := condExp_mono (m := m)
    ((integrable_const 1).indicator (show MeasurableSet[⊤] (s : Set α) from trivial))
    (integrable_const 1) hle
  rw [condExp_const le_top] at hhi
  exact hlo.and hhi

/-- Thermofield half-density squares supply the Born mass of every absorbed branch. -/
theorem gibbsBranchWeight_thermofield_born (β : ℝ) (E : α → ℝ) (s : Finset α) :
    (gibbsMeasure β E).real {a | gibbsBranchWeight β E s ⊤ a = 1} =
      ∑ a ∈ s, ∑ b, finiteKMSWightmanWeight β E a b ^ 2 := by
  rw [gibbsBranchWeight_born_absorption]
  apply Finset.sum_congr rfl
  intro a _
  exact (sum_sq_finiteKMSWightmanWeight_eq_stateWeight β E a).symm

end
end GaloisForLFunctions.HTGeometry.TraceDynamics

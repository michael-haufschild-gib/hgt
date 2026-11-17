import GaloisForLFunctions.ExclusionOfTheCriticalState.Certificates.WeilProbeSignBellman
import GaloisForLFunctions.ExclusionOfTheCriticalState.Certificates.ReluDecisionBellman

/-!
# ReLU realization and perturbation control for actual Weil sign optimization

The full finite sign minimum is an exact ReLU computation on the weighted
kernel entries. Its value changes by at most the total absolute entry
change. This bounds errors before selecting an optimal sign vector and
preserves strict negativity whenever its margin exceeds that entry error.
-/

open scoped BigOperators
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeCuts
open Pick DecisionBellman
noncomputable section

private theorem choices_value_stability (n : ℕ) (g h : (Fin n → Bool) → ℝ) (ε : ℝ)
    (hb : ∀ σ, |g σ - h σ| ≤ ε) :
    |value g (choices n id) - value h (choices n id)| ≤ ε := by
  obtain ⟨σ, hσ⟩ := (choices_value_isLeast n g).1
  obtain ⟨τ, hτ⟩ := (choices_value_isLeast n h).1
  have hg := (choices_value_isLeast n g).2 ⟨τ, rfl⟩
  have hh := (choices_value_isLeast n h).2 ⟨σ, rfl⟩
  have hσb := abs_le.mp (hb σ)
  have hτb := abs_le.mp (hb τ)
  apply abs_le.mpr
  constructor <;> linarith only [hg, hh, hσ, hτ, hσb.1, hτb.2]

private theorem signPayoff_entries {n : ℕ} (p a : Fin n → ℝ) (σ : Fin n → Bool) :
    signPayoff p a σ = ∑ i, ∑ j,
      if σ i = σ j then weight p a i j else -weight p a i j := by
  unfold signPayoff sourceQuadratic
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  cases hi : σ i <;> cases hj : σ j <;>
    simp [signedCoefficients, hi, hj, weight]

/-- Total entrywise discrepancy, including diagonals and both orientations. -/
def entryError {n : ℕ} (p a q b : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, |weight p a i j - weight q b i j|

private theorem signPayoff_error {n : ℕ} (p a q b : Fin n → ℝ) (σ : Fin n → Bool) :
    |signPayoff p a σ - signPayoff q b σ| ≤ entryError p a q b := by
  let d (i j : Fin n) : ℝ :=
    (if σ i = σ j then weight p a i j else -weight p a i j) -
      (if σ i = σ j then weight q b i j else -weight q b i j)
  rw [signPayoff_entries, signPayoff_entries]
  simp only [← Finset.sum_sub_distrib]
  change |∑ i, ∑ j, d i j| ≤ entryError p a q b
  calc
    |∑ i, ∑ j, d i j| ≤ ∑ i, |∑ j, d i j| := by
      simpa only [Real.norm_eq_abs] using norm_sum_le Finset.univ (fun i => ∑ j, d i j)
    _ ≤ ∑ i, ∑ j, |d i j| := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Real.norm_eq_abs] using norm_sum_le Finset.univ (d i)
    _ = entryError p a q b := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : σ i = σ j
      · simp only [d, if_pos h]
      · simp only [d, if_neg h]
        rw [show -weight p a i j - -weight q b i j =
          -(weight p a i j - weight q b i j) by ring, abs_neg]

/-- Global optimization is stable under the total error of the actual weighted Weil entries. -/
theorem signValue_entry_stability {n : ℕ} (p a q b : Fin n → ℝ) :
    |signValue p a - signValue q b| ≤ entryError p a q b :=
  choices_value_stability n (signPayoff p a) (signPayoff q b) (entryError p a q b)
    (signPayoff_error p a q b)

/-- The exact Weil sign minimum has a finite ReLU realization with a precise gate count. -/
theorem signValue_relu_realization {n : ℕ} (p a : Fin n → ℝ) :
    reluValue (signPayoff p a) (choices n id) = signValue p a ∧
      reluGates (choices n (id : (Fin n → Bool) → (Fin n → Bool))) + 1 = 2 ^ n :=
  ⟨reluValue_eq_value _ _, choices_reluGates n id⟩

/-- A negative optimum survives every perturbation smaller than its explicit energy margin. -/
theorem signValue_negative_under_entry_error {n : ℕ} (p a q b : Fin n → ℝ) :
    signValue p a + entryError p a q b < 0 → signValue q b < 0 := by
  intro h
  have he := (abs_le.mp (signValue_entry_stability p a q b)).1
  linarith only [he, h]

#print axioms signValue_entry_stability
#print axioms signValue_relu_realization
#print axioms signValue_negative_under_entry_error
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeCuts

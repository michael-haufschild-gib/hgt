import GaloisForLFunctions.ExclusionOfTheCriticalState.Certificates.BinaryChoiceBellman
import GaloisForLFunctions.ExclusionOfTheCriticalState.Certificates.WeilProbeCutBudget

/-!
# Bellman certificates for genuine finite Weil sign tests

Binary decisions select coefficient signs while retaining every mixed
probe term. Exact Bellman minimization is equivalent to maximizing the
positive cut weight. Its residual certificate detects precisely those
cuts that violate the Weil positive-semidefiniteness budget.
-/

namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeCuts
open Pick DecisionBellman
noncomputable section

/-- The terminal objective is the full finite Weil form. -/
def signPayoff {n : ℕ} (p a : Fin n → ℝ) (σ : Fin n → Bool) : ℝ :=
  sourceQuadratic n p (signedCoefficients a σ)

/-- Exact minimum among all coefficient vectors with the prescribed magnitudes. -/
def signValue {n : ℕ} (p a : Fin n → ℝ) : ℝ :=
  value (signPayoff p a) (choices n id)

/-- A single configuration simultaneously minimizes Weil energy and maximizes cut weight. -/
theorem exists_optimal_signs {n : ℕ} (p a : Fin n → ℝ) :
    ∃ σ : Fin n → Bool,
      signValue p a = signPayoff p a σ ∧
      (∀ τ, signPayoff p a σ ≤ signPayoff p a τ) ∧
      (∀ τ, cutWeight p a τ ≤ cutWeight p a σ) := by
  obtain ⟨σ, hσ⟩ := (choices_value_isLeast n (signPayoff p a)).1
  have hmin (τ : Fin n → Bool) : signPayoff p a σ ≤ signPayoff p a τ := by
    rw [hσ]
    exact (choices_value_isLeast n (signPayoff p a)).2 ⟨τ, rfl⟩
  refine ⟨σ, hσ.symm, hmin, ?_⟩
  intro τ
  have h := hmin τ
  simp only [signPayoff, signed_energy_eq_aligned_sub_cut] at h
  linarith only [h]

/-- Exactly `n + 1` sweeps recover the minimum, from every initial candidate. -/
theorem sign_sweeps_exact {n : ℕ} (p a : Fin n → ℝ)
    (W : DecisionBellman.Tree (Fin n → Bool) → ℝ) :
    (step (signPayoff p a))^[n + 1] W (choices n id) = signValue p a :=
  choices_iterate_exact n (signPayoff p a) W

/-- Local residuals bound the true optimum over all finite sign choices. -/
theorem sign_value_certificate {n : ℕ} (p a : Fin n → ℝ)
    (W : DecisionBellman.Tree (Fin n → Bool) → ℝ) :
    |W (choices n id) - signValue p a| ≤ certificate (signPayoff p a) W (choices n id) :=
  abs_error_le_certificate (signPayoff p a) W (choices n id)

/-- A strict Bellman certificate exists exactly when a cut exceeds the sharp energy budget. -/
theorem sign_certificate_iff_excessive_cut {n : ℕ} (p a : Fin n → ℝ) :
    (∃ W : DecisionBellman.Tree (Fin n → Bool) → ℝ,
      W (choices n id) + certificate (signPayoff p a) W (choices n id) < 0) ↔
      ∃ σ : Fin n → Bool, alignedEnergy p a / 4 < cutWeight p a σ := by
  rw [choices_negative_certificate_iff]
  exact exists_congr fun σ => negative_signed_energy_iff p a σ

/-- The certified finite search exhausts all real negative Weil witnesses. -/
theorem negative_probe_form_iff_sign_certificate (n : ℕ) (p : Fin n → ℝ) :
    (∃ c : Fin n → ℝ, sourceQuadratic n p c < 0) ↔
      ∃ (a : Fin n → ℝ) (W : DecisionBellman.Tree (Fin n → Bool) → ℝ),
        W (choices n id) + certificate (signPayoff p a) W (choices n id) < 0 := by
  rw [negative_probe_form_iff_excessive_cut]
  exact exists_congr fun a => (sign_certificate_iff_excessive_cut p a).symm

#print axioms exists_optimal_signs
#print axioms sign_sweeps_exact
#print axioms sign_value_certificate
#print axioms sign_certificate_iff_excessive_cut
#print axioms negative_probe_form_iff_sign_certificate
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeCuts

/-
# Finite Dirichlet-character family zero count

This is the finite-family aggregation layer before a conductor-uniform
zero-density estimate.  At every concrete modulus `n + 1`, all certified
nonprincipal characters use the common completed-L anchor `2`.  The proof
chooses the individual Jensen constants internally and combines them over the
finite character family.  It assumes no RH-, GRH-, or zero-density input.
-/
import GaloisForLFunctions.RHTower.DirichletLZeroCount

open Complex Metric
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Total multiplicity of zeros of all certified nonprincipal completed Dirichlet L-functions
modulo `n + 1` in the common disc centered at `2`. -/
def completedLFunctionFamilyZeroCount (n : ℕ) (r : ℝ) : ℝ :=
  ∑ χ : NonprincipalDirichletCharacter n,
    (↑(∑ᶠ u, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.1)
      (closedBall (2 : ℂ) r)) u) : ℝ)

/-- Every fixed finite nonprincipal Dirichlet-character family has a closed Jensen zero-count
bound in its common anchor discs.  The constant is constructed from the finite family itself;
this is not yet a conductor-uniform zero-density exponent. -/
theorem completedLFunction_family_zeroCount_growth_at_two
    (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      completedLFunctionFamilyZeroCount n r ≤ C * (1 + r) * Real.log (2 + r) := by
  choose C hCpos hCbound using completedLFunction_zeroCount_growth_at_two (n := n)
  have hCsum : 0 ≤ ∑ χ : NonprincipalDirichletCharacter n, C χ :=
    Finset.sum_nonneg (fun χ _ ↦ (hCpos χ).le)
  refine ⟨1 + ∑ χ : NonprincipalDirichletCharacter n, C χ, by linarith, ?_⟩
  intro r hr
  have hPnonneg : 0 ≤ (1 + r) * Real.log (2 + r) := by
    apply mul_nonneg (by linarith)
    exact Real.log_nonneg (by linarith)
  rw [completedLFunctionFamilyZeroCount]
  calc
    _ ≤ ∑ χ : NonprincipalDirichletCharacter n,
        C χ * (1 + r) * Real.log (2 + r) := by
      exact Finset.sum_le_sum (fun χ _ ↦ hCbound χ r hr)
    _ = (∑ χ : NonprincipalDirichletCharacter n, C χ) *
        ((1 + r) * Real.log (2 + r)) := by
      simp_rw [mul_assoc]
      rw [Finset.sum_mul]
    _ ≤ (1 + ∑ χ : NonprincipalDirichletCharacter n, C χ) *
        ((1 + r) * Real.log (2 + r)) := by
      nlinarith [mul_le_mul_of_nonneg_right (by linarith :
        (∑ χ : NonprincipalDirichletCharacter n, C χ) ≤ 1 + ∑ χ, C χ) hPnonneg]
    _ = _ := by ring

end RHTower

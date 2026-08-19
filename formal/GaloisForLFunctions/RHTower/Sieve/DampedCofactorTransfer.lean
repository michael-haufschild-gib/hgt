import GaloisForLFunctions.RHTower.Sieve.DampedCofactorIntegral

/-!
# Transferring a uniform saving to the damped cofactor

Averaging over `t ∈ [0,1]` cannot increase a sup bound, so any saving for the `t^{ω_P}`-weighted
Möbius cofactor polynomial that holds uniformly in `t` is inherited by the damped cofactor
polynomial `∑_m μ(m)/(ω_P(m)+1) · e(w log m)`.

This isolates the one analytic input the exact-Ramaré route still needs, in a form with no Ramaré
bookkeeping left in it.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- **A uniform saving transfers to the damped cofactor.** -/
theorem norm_logPoly_ramareCofactorCoeff_le_of_uniform (P C : Finset ℕ) (w : ℝ) {s : ℝ}
    (hunif : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖logPoly (dampedOmegaMoebius P t) C w‖ ≤ s) :
    ‖logPoly (ramareCofactorCoeff P) C w‖ ≤ s := by
  rw [logPoly_ramareCofactorCoeff_eq_integral]
  have hbd : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖logPoly (dampedOmegaMoebius P t) C w‖ ≤ s := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact hunif t ⟨le_of_lt ht.1, ht.2⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  have habs : |(1 : ℝ) - 0| = 1 := by norm_num
  rw [habs, mul_one] at h
  exact h

end

end RHTower.Sieve

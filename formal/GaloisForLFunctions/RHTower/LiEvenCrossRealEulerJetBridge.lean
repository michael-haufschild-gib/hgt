import GaloisForLFunctions.RHTower.LiEvenCrossEulerCurrentBridge
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Real derivatives of the actual first LI logarithmic-mass current

The real function `t ↦ v exp(t) C₀(v exp(t))` is the restriction of the
literal complex source continuation. Its real iterated derivatives equal the
real parts of the complex jets. At every positive mass, its even derivatives
therefore take both strict signs in every tail.
-/

namespace RHTower

private theorem realEuler_iteratedDeriv_restrict {f : ℂ → ℂ}
    (hf : ∀ x : ℝ, AnalyticAt ℂ f (x : ℂ)) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun t : ℝ => (f (t : ℂ)).re) x =
      (iteratedDeriv n f (x : ℂ)).re := by
  have ha : ∀ k : ℕ, ∀ t : ℝ, AnalyticAt ℂ (iteratedDeriv k f) (t : ℂ) := by
    intro k
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hf
    | succ k hk =>
      intro t
      rw [iteratedDeriv_succ]
      exact (hk t).deriv
  induction n generalizing x with
  | zero => rfl
  | succ n hn =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have hfun : iteratedDeriv n (fun t : ℝ => (f (t : ℂ)).re) =
        fun t : ℝ => (iteratedDeriv n f (t : ℂ)).re := by
      funext t
      exact hn t
    rw [hfun]
    exact ((ha n x).differentiableAt.hasDerivAt.real_of_complex).deriv

noncomputable section

/-- Literal real first current in logarithmic mass, centered at `v`. -/
def liEvenCrossRealLogMassFirstCurrent (v : ℝ) (t : ℝ) : ℝ :=
  v * Real.exp t * liEvenCrossSquareMassAdjacentCurrent (v * Real.exp t) 0

theorem liEvenCrossRealLogMassFirstCurrent_eq_re_complex
    {v : ℝ} (hv : 0 < v) (t : ℝ) :
    liEvenCrossRealLogMassFirstCurrent v t =
      (liEvenCrossLogMassFirstCurrent v (t : ℂ)).re := by
  have h := congrArg Complex.re (liEvenCrossLogMassFirstCurrent_real hv t)
  simpa only [Complex.ofReal_re, liEvenCrossRealLogMassFirstCurrent] using h.symm

private theorem realEuler_analyticAt_firstCurrent_real
    {v : ℝ} (hv : 0 < v) (t : ℝ) :
    AnalyticAt ℂ (liEvenCrossLogMassFirstCurrent v) (t : ℂ) := by
  have hz := analyticAt_liEvenCrossCassiniLogMassCurrent_of_source_ne_zero
    (xiSquaredSeamCassiniSource_one_sub_posMass_ne_zero
      (mul_pos hv (Real.exp_pos t)))
  have he : (v : ℂ) * Complex.exp (t : ℂ) = ((v * Real.exp t : ℝ) : ℂ) := by
    simp [Complex.ofReal_exp]
  rw [← he] at hz
  exact hz.comp (f := fun w : ℂ => (v : ℂ) * Complex.exp w) (x := (t : ℂ))
    (by fun_prop)

/-- Real differentiation of the actual current agrees with complex source jets. -/
theorem liEvenCrossRealLogMassFirstCurrent_iteratedDeriv_eq_complex
    {v : ℝ} (hv : 0 < v) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (liEvenCrossRealLogMassFirstCurrent v) t =
      (iteratedDeriv n (liEvenCrossLogMassFirstCurrent v) (t : ℂ)).re := by
  have hfun : liEvenCrossRealLogMassFirstCurrent v =
      fun x : ℝ => (liEvenCrossLogMassFirstCurrent v (x : ℂ)).re := by
    funext x
    exact liEvenCrossRealLogMassFirstCurrent_eq_re_complex hv x
  rw [hfun]
  exact realEuler_iteratedDeriv_restrict (realEuler_analyticAt_firstCurrent_real hv) n t

/-- The real even derivative has the exact unnormalized shifted Euler jet. -/
theorem liEvenCrossRealLogMassFirstCurrent_even_deriv_eq_eulerJet
    {v : ℝ} (hv : 0 < v) (k : ℕ) :
    iteratedDeriv (2 * k) (liEvenCrossRealLogMassFirstCurrent v) 0 =
      liEvenCrossFirstCurrentEvenEulerJet v k := by
  simpa only [Complex.ofReal_zero, liEvenCrossFirstCurrentEvenEulerJet] using
    liEvenCrossRealLogMassFirstCurrent_iteratedDeriv_eq_complex hv (2 * k) 0

/-- At every positive mass, every tail contains real even derivatives of both signs. -/
theorem liEvenCrossRealLogMassFirstCurrent_even_deriv_cofinal_both_signs
    (v : LiEvenCrossPositiveMass) :
    (∀ N : ℕ, ∃ k, N ≤ k ∧
      iteratedDeriv (2 * k) (liEvenCrossRealLogMassFirstCurrent v.val) 0 < 0) ∧
    (∀ N : ℕ, ∃ k, N ≤ k ∧
      0 < iteratedDeriv (2 * k) (liEvenCrossRealLogMassFirstCurrent v.val) 0) := by
  simpa only [liEvenCrossRealLogMassFirstCurrent_even_deriv_eq_eulerJet v.property] using
    liEvenCrossFirstCurrentEvenEulerJet_cofinal_both_signs v

end

end RHTower

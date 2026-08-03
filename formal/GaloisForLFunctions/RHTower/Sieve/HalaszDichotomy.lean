import GaloisForLFunctions.RHTower.Sieve.FrequencySeparation
import GaloisForLFunctions.RHTower.Sieve.EulerIntegerIndex

/-!
# The Halász dichotomy

Two facts now combine.  A frequency at distance more than `δ` gives a damped Dirichlet sum,

`‖∑_{n squarefree, P-smooth} f(n) n^{-it}/n‖ ≤ exp(∑_{p ∈ P} 1/p + ∑_{p ∈ P} 1/p² - δ²)`,

and, by the quantitative separation, at most one frequency can be within `δ`.  So for every
frequency except at most one the sum is damped: the exceptional frequency of Halász's theorem is
unique, and away from it the bound is uniform.

Nothing here identifies the exceptional frequency or bounds `δ` from below; that is the analytic
content the elementary theory does not supply.
-/

namespace RHTower.Sieve

open Finset

/-- **Uniqueness of a close frequency.** -/
theorem eq_of_both_close {f : ℕ → ℂ} {P : Finset ℕ} (hf : ∀ p ∈ P, ‖f p‖ ≤ 1)
    (hP : ∀ p ∈ P, 0 < p) {t u δ : ℝ}
    (ht : Real.sqrt (mulDistSqPair f (charFn t) P) ≤ δ)
    (hu : Real.sqrt (mulDistSqPair f (charFn u) P) ≤ δ)
    (hsmall : ∀ p ∈ P, |(t - u) * Real.log (p : ℝ)| ≤ Real.pi)
    (hsep : t ≠ u → 2 * Real.pi ^ 2 * δ ^ 2
      < (t - u) ^ 2 * ∑ p ∈ P, Real.log (p : ℝ) ^ 2 / (p : ℝ)) : t = u := by
  by_contra hne
  have h1 := sq_mul_sum_sq_log_le_of_close hf hP ht hu hsmall
  linarith [hsep hne]

/-- **A far frequency gives a damped sum.** -/
theorem norm_sum_smooth_le_exp_of_far {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b) (h1 : f 1 = 1) (t : ℝ)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {δ : ℝ} (hδ : 0 ≤ δ)
    (hfar : δ ≤ Real.sqrt (mulDistSqPair f (charFn t) P)) :
    ‖∑ n ∈ P.powerset.image (fun T => ∏ p ∈ T, p), ((1 / (n : ℝ) : ℝ) : ℂ)
        * (f n * Complex.exp (((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I))‖
      ≤ Real.exp ((∑ p ∈ P, 1 / (p : ℝ)) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) - δ ^ 2) := by
  refine le_trans (norm_sum_smooth_le_exp hf hmul h1 t hP) (Real.exp_le_exp.mpr ?_)
  have hnn : 0 ≤ mulDistSqPair f (charFn t) P :=
    mulDistSqPair_nonneg_disc (fun p _ => hf p) (fun p _ => (norm_charFn t p).le)
      (fun p hp => (hP p hp).pos)
  have hsq : Real.sqrt (mulDistSqPair f (charFn t) P) ^ 2 = mulDistSqPair f (charFn t) P :=
    Real.sq_sqrt hnn
  have hδ2 : δ ^ 2 ≤ mulDistSqPair f (charFn t) P := by
    rw [← hsq]
    exact pow_le_pow_left₀ hδ hfar 2
  rw [mulDistSq_eq_pair]
  linarith

end RHTower.Sieve

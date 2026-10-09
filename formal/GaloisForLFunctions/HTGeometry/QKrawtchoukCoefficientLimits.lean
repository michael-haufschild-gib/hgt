import GaloisForLFunctions.HTGeometry.QKrawtchoukEdgeMoments
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Finite q-Krawtchouk recurrences converge to the constructed edge moments

We specialize arXiv:2609.24149, Propositions 3.1 and 8.1, to the exact
balanced scaling `M = 2K`, `N = K`, with constant rescaled shape. For the
inverse-q Hermite branch `ρ = exp (2u)`; for the companion branch `c = exp u`
and `ρ = c⁻¹`. Both sides have base `exp (-exp t)` in `(0,1)`.

The finite matrix uses rows `0,...,2K`. The formulas are extended algebraically
beyond those rows solely to state fixed-degree limits. Every fixed row and
polynomial degree eventually belongs to the finite matrix.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace HTGeometry

def qKrawtchoukEdgeBase (t : ℝ) : ℝ := Real.exp (-Real.exp t)

private theorem edgeBase_pos (t : ℝ) : 0 < qKrawtchoukEdgeBase t := Real.exp_pos _

private theorem edgeBase_lt_one (t : ℝ) : qKrawtchoukEdgeBase t < 1 :=
  Real.exp_lt_one_iff.mpr (by have := Real.exp_pos t; linarith)

private theorem edgeBase_pow_zero (t : ℝ) :
    Tendsto (fun K : ℕ => qKrawtchoukEdgeBase t ^ K) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (edgeBase_pos t).le (edgeBase_lt_one t)

/-- The finite right-end truncation factor multiplying the lower coefficient. -/
def qKrawtchoukEdgeCutoff (t : ℝ) (K n : ℕ) : ℝ :=
  1 - Real.exp (Real.exp t * (n - 1 : ℝ)) * (qKrawtchoukEdgeBase t ^ K) ^ 2

/-- Identification with the paper's literal `1-q^(M-n+1)` factor. -/
theorem qKrawtchoukEdgeCutoff_eq (t : ℝ) (K n : ℕ) :
    qKrawtchoukEdgeCutoff t K n =
      1 - Real.exp (-Real.exp t * (2 * (K : ℝ) - n + 1)) := by
  unfold qKrawtchoukEdgeCutoff qKrawtchoukEdgeBase
  rw [← Real.exp_nat_mul, pow_two, ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

def qKrawtchoukHermiteFiniteDiagonal (t u : ℝ) (K n : ℕ) : ℝ :=
  (Real.exp (-u) - Real.exp u) *
    (1 - Real.exp (Real.exp t * n) * qKrawtchoukEdgeBase t ^ K)

def qKrawtchoukHermiteFiniteLower (t : ℝ) (K n : ℕ) : ℝ :=
  inverseQHermiteLower t n * qKrawtchoukEdgeCutoff t K n

def qKrawtchoukCompanionFiniteDiagonal (t u : ℝ) (K n : ℕ) : ℝ :=
  alSalamCarlitzDiagonal t u n + (Real.exp u - 1) * qKrawtchoukEdgeBase t ^ K

def qKrawtchoukCompanionFiniteLower (t u : ℝ) (K n : ℕ) : ℝ :=
  alSalamCarlitzLower t u n * qKrawtchoukEdgeCutoff t K n

private theorem edgeCutoff_one (t : ℝ) (n : ℕ) :
    Tendsto (fun K => qKrawtchoukEdgeCutoff t K n) atTop (𝓝 1) := by
  simpa [qKrawtchoukEdgeCutoff] using
    tendsto_const_nhds.sub
      (((edgeBase_pow_zero t).pow 2).const_mul (Real.exp (Real.exp t * (n - 1 : ℝ))))

/-- The finite inverse-q Hermite diagonal tends to the actual moment diagonal. -/
theorem qKrawtchoukHermiteFiniteDiagonal_tendsto (t u : ℝ) (n : ℕ) :
    Tendsto (fun K => qKrawtchoukHermiteFiniteDiagonal t u K n) atTop
      (𝓝 (monicOrthoAlpha (inverseQHermiteMoment t u) n)) := by
  rw [inverseQHermiteMoment_alpha]
  simpa [qKrawtchoukHermiteFiniteDiagonal] using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
      ((edgeBase_pow_zero t).const_mul
      (Real.exp (Real.exp t * n)))).const_mul (Real.exp (-u) - Real.exp u)

/-- Convergence of every finite inverse-q Hermite lower monic coefficient. -/
theorem qKrawtchoukHermiteFiniteLower_tendsto (t : ℝ) (n : ℕ) :
    Tendsto (fun K => qKrawtchoukHermiteFiniteLower t K n) atTop
      (𝓝 (inverseQHermiteLower t n)) := by
  simpa [qKrawtchoukHermiteFiniteLower] using
    (edgeCutoff_one t n).const_mul (inverseQHermiteLower t n)

/-- Convergence of every finite companion diagonal. -/
theorem qKrawtchoukCompanionFiniteDiagonal_tendsto (t u : ℝ) (n : ℕ) :
    Tendsto (fun K => qKrawtchoukCompanionFiniteDiagonal t u K n) atTop
      (𝓝 (monicOrthoAlpha (alSalamCarlitzMoment t u) n)) := by
  rw [alSalamCarlitzMoment_alpha]
  simpa [qKrawtchoukCompanionFiniteDiagonal] using
    ((edgeBase_pow_zero t).const_mul (Real.exp u - 1)).const_add
      (alSalamCarlitzDiagonal t u n)

/-- Convergence of every finite companion lower monic coefficient. -/
theorem qKrawtchoukCompanionFiniteLower_tendsto (t u : ℝ) (n : ℕ) :
    Tendsto (fun K => qKrawtchoukCompanionFiniteLower t u K n) atTop
      (𝓝 (alSalamCarlitzLower t u n)) := by
  simpa [qKrawtchoukCompanionFiniteLower] using
    (edgeCutoff_one t n).const_mul (alSalamCarlitzLower t u n)

/-- The actual positive off-diagonal coefficients converge in both branches. -/
theorem qKrawtchoukFiniteOffDiagonal_tendsto (t u : ℝ) (n : ℕ) :
    Tendsto (fun K => Real.sqrt (qKrawtchoukHermiteFiniteLower t K (n + 1))) atTop
      (𝓝 (Real.sqrt (monicOrthoBeta (inverseQHermiteMoment t u) (n + 1)))) ∧
    Tendsto (fun K => Real.sqrt (qKrawtchoukCompanionFiniteLower t u K (n + 1))) atTop
      (𝓝 (Real.sqrt (monicOrthoBeta (alSalamCarlitzMoment t u) (n + 1)))) := by
  rw [inverseQHermiteMoment_beta, alSalamCarlitzMoment_beta]
  constructor
  · simpa only [inverseQHermiteLower, Nat.cast_add, Nat.cast_one] using
      (qKrawtchoukHermiteFiniteLower_tendsto t (n + 1)).sqrt
  · exact (qKrawtchoukCompanionFiniteLower_tendsto t u (n + 1)).sqrt

private theorem favard_eval_tendsto (α β : ℕ → ℕ → ℝ) (a b : ℕ → ℝ)
    (hα : ∀ n, Tendsto (fun K => α K n) atTop (𝓝 (a n)))
    (hβ : ∀ n, Tendsto (fun K => β K n) atTop (𝓝 (b n))) (x : ℝ) (n : ℕ) :
    Tendsto (fun K => (favardPoly (α K) (β K) n).eval x) atTop
      (𝓝 ((favardPoly a b n).eval x)) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      simp only [favardPoly_zero, Polynomial.eval_one]
      exact tendsto_const_nhds
  | one =>
      simpa only [favardPoly_one, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        using tendsto_const_nhds.sub (hα 0)
  | more n hn hn1 =>
      simpa only [favardPoly_succ_succ, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_C] using
        ((tendsto_const_nhds.sub (hα (n + 1))).mul hn1).sub ((hβ (n + 1)).mul hn)

/-- Fixed-degree finite polynomials converge to the orthogonal polynomials of
the indeterminate edge moment sequence constructed in the corpus. -/
theorem qKrawtchoukHermiteFinitePoly_tendsto (t u x : ℝ) (n : ℕ) :
    Tendsto (fun K => (favardPoly (qKrawtchoukHermiteFiniteDiagonal t u K)
      (qKrawtchoukHermiteFiniteLower t K) n).eval x) atTop
      (𝓝 ((monicOrtho (inverseQHermiteMoment t u) n).eval x)) := by
  rw [inverseQHermiteMoment_monicOrtho]
  exact favard_eval_tendsto _ _ _ _
    (fun j => by simpa only [inverseQHermiteMoment_alpha] using
      qKrawtchoukHermiteFiniteDiagonal_tendsto t u j)
    (qKrawtchoukHermiteFiniteLower_tendsto t) x n

/-- The companion finite polynomials converge to the corpus's Al-Salam--Carlitz
orthogonal family at every fixed degree and evaluation point. -/
theorem qKrawtchoukCompanionFinitePoly_tendsto (t u x : ℝ) (n : ℕ) :
    Tendsto (fun K => (favardPoly (qKrawtchoukCompanionFiniteDiagonal t u K)
      (qKrawtchoukCompanionFiniteLower t u K) n).eval x) atTop
      (𝓝 ((monicOrtho (alSalamCarlitzMoment t u) n).eval x)) := by
  rw [alSalamCarlitzMoment_monicOrtho]
  exact favard_eval_tendsto _ _ _ _
    (fun j => by simpa only [alSalamCarlitzMoment_alpha] using
      qKrawtchoukCompanionFiniteDiagonal_tendsto t u j)
    (qKrawtchoukCompanionFiniteLower_tendsto t u) x n

private theorem favard_coeff_tendsto (α β : ℕ → ℕ → ℝ) (a b : ℕ → ℝ)
    (hα : ∀ n, Tendsto (fun K => α K n) atTop (𝓝 (a n)))
    (hβ : ∀ n, Tendsto (fun K => β K n) atTop (𝓝 (b n))) (n j : ℕ) :
    Tendsto (fun K => (favardPoly (α K) (β K) n).coeff j) atTop
      (𝓝 ((favardPoly a b n).coeff j)) := by
  induction n using Nat.twoStepInduction generalizing j with
  | zero =>
      simp only [favardPoly_zero]
      exact tendsto_const_nhds
  | one =>
      cases j with
      | zero => simpa [favardPoly_one] using (hα 0).neg
      | succ j => simp [favardPoly_one]
  | more n hn hn1 =>
      cases j with
      | zero =>
          simpa only [favardPoly_succ_succ, sub_mul, Polynomial.coeff_sub,
            Polynomial.coeff_X_mul_zero, Polynomial.coeff_C_mul, zero_sub] using
            ((hα (n + 1)).mul (hn1 0)).neg.sub ((hβ (n + 1)).mul (hn 0))
      | succ j =>
          simpa only [favardPoly_succ_succ, sub_mul, Polynomial.coeff_sub,
            Polynomial.coeff_X_mul, Polynomial.coeff_C_mul] using
            ((hn1 j).sub ((hα (n + 1)).mul (hn1 (j + 1)))).sub
              ((hβ (n + 1)).mul (hn (j + 1)))

private theorem favard_moment_tendsto (α β : ℕ → ℕ → ℝ) (a b : ℕ → ℝ)
    (hα : ∀ n, Tendsto (fun K => α K n) atTop (𝓝 (a n)))
    (hβ : ∀ n, Tendsto (fun K => β K n) atTop (𝓝 (b n))) (n : ℕ) :
    Tendsto (fun K => favardMoment (α K) (β K) n) atTop (𝓝 (favardMoment a b n)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        simp only [favardMoment_zero]
        exact tendsto_const_nhds
      have hfun : (fun K => favardMoment (α K) (β K) n) =
          fun K => -∑ i : Fin n,
            (favardPoly (α K) (β K) n).coeff i.1 * favardMoment (α K) (β K) i.1 := by
        funext K
        rw [favardMoment_eq, if_neg hn]
      rw [hfun, favardMoment_eq a b n, if_neg hn]
      exact (tendsto_finsetSum Finset.univ fun i _ =>
        (favard_coeff_tendsto α β a b hα hβ n i.1).mul (ih i.1 i.2)).neg

/-- Every fixed finite recurrence moment converges to the actual inverse-q
Hermite moment. Coefficient convergence alone does not select a measure. -/
theorem qKrawtchoukHermiteFiniteMoment_tendsto (t u : ℝ) (n : ℕ) :
    Tendsto (fun K => favardMoment (qKrawtchoukHermiteFiniteDiagonal t u K)
      (qKrawtchoukHermiteFiniteLower t K) n) atTop (𝓝 (inverseQHermiteMoment t u n)) :=
  favard_moment_tendsto _ _ _ _
    (fun j => by simpa only [inverseQHermiteMoment_alpha] using
      qKrawtchoukHermiteFiniteDiagonal_tendsto t u j)
    (qKrawtchoukHermiteFiniteLower_tendsto t) n

/-- Every fixed finite companion recurrence moment converges to the uniquely
representable Al-Salam--Carlitz moment sequence. -/
theorem qKrawtchoukCompanionFiniteMoment_tendsto (t u : ℝ) (n : ℕ) :
    Tendsto (fun K => favardMoment (qKrawtchoukCompanionFiniteDiagonal t u K)
      (qKrawtchoukCompanionFiniteLower t u K) n) atTop (𝓝 (alSalamCarlitzMoment t u n)) :=
  favard_moment_tendsto _ _ _ _
    (fun j => by simpa only [alSalamCarlitzMoment_alpha] using
      qKrawtchoukCompanionFiniteDiagonal_tendsto t u j)
    (qKrawtchoukCompanionFiniteLower_tendsto t u) n

end HTGeometry

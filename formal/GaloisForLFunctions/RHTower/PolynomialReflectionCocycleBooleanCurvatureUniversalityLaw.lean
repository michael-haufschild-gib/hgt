import GaloisForLFunctions.HTGeometry.ProuhetAlternating
import GaloisForLFunctions.RHTower.CocycleExponentRigidity

/-!
# Boolean-curvature universality for polynomial reflection cocycles

Reflection symmetry and vertical logarithmic growth force every polynomial cocycle exponent to be
affine.  Prouhet annihilation then removes every translated Boolean interaction of depth at least
two.  Thus the same hypotheses force both continuous logarithmic curvature and every higher
Boolean logarithmic curvature to vanish.
-/

namespace RHTower

open Complex Polynomial

noncomputable section

/-- Every translated Boolean logarithmic curvature of an admissible polynomial reflection
cocycle vanishes at interaction depth at least two. -/
theorem polynomialExponentReflectionCocycle_booleanLogCurvatureZero
    {P : Polynomial ℂ} {c : ℂ}
    (hc : ∀ s : ℂ, P.eval s + P.eval (1 - s) = c)
    (hgrowth : ∀ σ : ℝ, ∃ K : ℝ, ∀ t : ℝ,
      (P.eval ((σ : ℂ) + (t : ℂ) * Complex.I)).re ≤
        K * Real.log (2 + |t|))
    (n : ℕ) (hn : 2 ≤ n) (b : ℂ) (w : ℕ → ℂ) :
    ∑ S ∈ (Finset.range n).powerset,
        (-1 : ℂ) ^ S.card * P.eval ((∑ i ∈ S, w i) + b) = 0 := by
  have hPdeg : P.natDegree ≤ 1 :=
    cocycle_exponent_rigidity hc hgrowth
  let Q : Polynomial ℂ := P.comp (Polynomial.X + Polynomial.C b)
  have hQdeg : Q.natDegree < n := by
    simp only [Q, Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
    omega
  simpa only [Q, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C] using
    (GaloisForLFunctions.prouhet_alternating_annihilation w Q hQdeg)

/-- **Polynomial-reflection-cocycle complete curvature-flatness universality law.**
Reflection symmetry and vertical logarithmic growth simultaneously force ordinary differential
curvature to vanish and every translated Boolean logarithmic curvature of depth at least two to
vanish.  Exponentiating the latter gives unit multiplicative holonomy. -/
theorem polynomialExponentReflectionCocycle_completeCurvatureFlatness
    {P : Polynomial ℂ} {c : ℂ}
    (hc : ∀ s : ℂ, P.eval s + P.eval (1 - s) = c)
    (hgrowth : ∀ σ : ℝ, ∃ K : ℝ, ∀ t : ℝ,
      (P.eval ((σ : ℂ) + (t : ℂ) * Complex.I)).re ≤
        K * Real.log (2 + |t|)) :
    deriv (logDeriv fun s => Complex.exp (P.eval s)) = (0 : ℂ → ℂ) ∧
      ∀ n : ℕ, 2 ≤ n → ∀ (b : ℂ) (w : ℕ → ℂ),
        (∑ S ∈ (Finset.range n).powerset,
            (-1 : ℂ) ^ S.card * P.eval ((∑ i ∈ S, w i) + b)) = 0 ∧
          Complex.exp
            (∑ S ∈ (Finset.range n).powerset,
              (-1 : ℂ) ^ S.card * P.eval ((∑ i ∈ S, w i) + b)) = 1 := by
  refine ⟨cocycle_exponent_curvature_zero hc hgrowth, ?_⟩
  intro n hn b w
  have hzero :=
    polynomialExponentReflectionCocycle_booleanLogCurvatureZero
      hc hgrowth n hn b w
  exact ⟨hzero, by rw [hzero, Complex.exp_zero]⟩

end

end RHTower

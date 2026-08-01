import GaloisForLFunctions.HTGeometry.MvPolynomialPhaseRank
import GaloisForLFunctions.HTGeometry.MvPolynomialDropLast
import GaloisForLFunctions.HTGeometry.ConstantSolutionPhaseRank

/-!
# Finite phase rank for any polynomial differential relation

The nondegeneracy hypothesis is now removed by descent.  If the relation is degenerate in its top jet
at every point of the line, its derivative in that jet is again a relation, of strictly smaller degree
there; when that derivative vanishes identically the relation no longer involves the top jet, so it is
a relation of lower order; and an algebraic equation in the function alone forces the function to be
constant, whose frequency rank is zero.

So a strip almost periodic holomorphic function satisfying *any* nonzero polynomial relation in its
jets has finite rational Bohr frequency rank.
-/

open Filter Topology Metric Set MvPolynomial

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {σ R r ρ : ℝ} {M : ℕ}

/-- A polynomial in the jets of a holomorphic function is holomorphic. -/
theorem differentiableOn_mvEval_jets {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R)) (p : MvPolynomial (Fin M) ℂ) :
    DifferentiableOn ℂ
      (fun z : ℂ => MvPolynomial.eval (fun k : Fin M => iteratedDeriv (k : ℕ) Φ z) p)
      (verticalStrip σ R) := by
  have hjets : DifferentiableOn ℂ
      (fun z : ℂ => (fun k : Fin M => iteratedDeriv (k : ℕ) Φ z)) (verticalStrip σ R) :=
    differentiableOn_pi.mpr fun k => differentiableOn_iteratedDeriv_verticalStrip hΦ (k : ℕ)
  have hp : Differentiable ℂ (fun y : Fin M → ℂ => MvPolynomial.eval y p) := fun y =>
    (hasFDerivAt_mvEval p y).differentiableAt
  exact hp.comp_differentiableOn hjets

/-- A polynomial jet relation valid on the central line is valid on the strip. -/
theorem mvEval_eqOn_zero_of_line (hR : 0 < R) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R)) (p : MvPolynomial (Fin M) ℂ)
    (hline : ∀ t : ℝ, MvPolynomial.eval
      (fun k : Fin M => iteratedDeriv (k : ℕ) Φ ((σ : ℂ) + (t : ℂ) * Complex.I)) p = 0)
    {z : ℂ} (hz : z ∈ verticalStrip σ R) :
    MvPolynomial.eval (fun k : Fin M => iteratedDeriv (k : ℕ) Φ z) p = 0 := by
  have h := eqOn_of_eqOn_line hR (differentiableOn_mvEval_jets hΦ p)
    (differentiableOn_const (0 : ℂ)) (fun t => by simpa using hline t) hz
  simpa using h

/-- Evaluation of a one-variable multivariate polynomial is evaluation of the corresponding
univariate polynomial. -/
theorem eval_fin_one (p : MvPolynomial (Fin 1) ℂ) (x : ℂ) :
    MvPolynomial.eval (fun _ => x) p
      = Polynomial.eval x (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- **Finite phase rank from any nonzero polynomial differential relation.**  Descending on the
degree in the top jet and then on the order, a strip almost periodic holomorphic function satisfying
a nonzero polynomial relation in its jets has finite rational Bohr frequency rank: either the
relation is nondegenerate somewhere in its top jet, or its derivative in that jet is a relation of
smaller degree, or the relation has lower order — and an algebraic equation in the function alone
forces it to be constant. -/
theorem rank_finite_of_polynomial_relation (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R)
    {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R))
    (hap : IsStripAlmostPeriodic Φ σ R)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)] :
    ∀ (n : ℕ) (p : MvPolynomial (Fin (n + 1)) ℂ), p ≠ 0 →
      (∀ z ∈ verticalStrip σ R,
        MvPolynomial.eval (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) Φ z) p = 0) →
      ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  have hRpos : 0 < R := by linarith
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    match n with
    | 0 =>
        intro p hp hrel
        -- the relation is algebraic in the function itself, so the function is constant
        refine ⟨0, ?_⟩
        set q : Polynomial ℂ := MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) p with hq
        have hqne : q ≠ 0 := by
          intro hzero
          refine hp ((MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).injective ?_)
          rw [map_zero]
          rw [hq] at hzero
          exact hzero
        have hrelq : ∀ z ∈ verticalStrip σ R, q.eval (Φ z) = 0 := by
          intro z hz
          have h := hrel z hz
          have hfun : (fun k : Fin 1 => iteratedDeriv (k : ℕ) Φ z) = fun _ : Fin 1 => Φ z := by
            funext k
            have hk : (k : ℕ) = 0 := by omega
            rw [hk, iteratedDeriv_zero]
          rw [hfun, eval_fin_one] at h
          exact h
        have hconst : ∀ x : ℝ, f x = Φ ((σ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) := by
          intro x
          rw [hf x]
          exact const_of_polynomial_relation hΦ.continuousOn q hqne hrelq
            (mem_verticalStrip_line hRpos σ x) (mem_verticalStrip_line hRpos σ 0)
        rw [rank_eq_zero_of_const hconst]
        exact le_rfl
    | (m + 1) =>
        have hn : 0 < m + 1 := Nat.succ_pos m
        suffices H : ∀ d : ℕ, ∀ p : MvPolynomial (Fin (m + 1 + 1)) ℂ,
            MvPolynomial.degreeOf (Fin.last (m + 1)) p ≤ d → p ≠ 0 →
            (∀ z ∈ verticalStrip σ R,
              MvPolynomial.eval (fun k : Fin (m + 1 + 1) => iteratedDeriv (k : ℕ) Φ z) p = 0) →
            ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) by
          intro p hp hrel
          exact H _ p le_rfl hp hrel
        intro d
        induction d with
        | zero =>
            intro p hdeg hp hrel
            -- the relation does not involve the top jet: it is a relation of lower order
            have hdeg0 : MvPolynomial.degreeOf (Fin.last (m + 1)) p = 0 := Nat.le_zero.mp hdeg
            have hq := dropLastPoly_ne_zero hdeg0 hp
            refine ihn m (Nat.lt_succ_self m) (dropLastPoly p) hq ?_
            intro z hz
            have h := eval_dropLastPoly hdeg0 (fun k : Fin (m + 1 + 1) =>
              iteratedDeriv (k : ℕ) Φ z)
            rw [← hrel z hz, ← h]
            rfl
        | succ d ihd =>
            intro p hdeg hp hrel
            by_cases hnd : ∃ t₀ : ℝ, MvPolynomial.eval
                (fun k : Fin (m + 1 + 1) =>
                  iteratedDeriv (k : ℕ) Φ ((σ : ℂ) + (t₀ : ℂ) * Complex.I))
                ((pderiv (Fin.last (m + 1))) p) ≠ 0
            · exact rank_finite_of_mvPolynomial_relation hr hρ hrρ hΦ hap hf hfu hftb hn p hrel hnd
            · push Not at hnd
              have hrel' : ∀ z ∈ verticalStrip σ R, MvPolynomial.eval
                  (fun k : Fin (m + 1 + 1) => iteratedDeriv (k : ℕ) Φ z)
                  ((pderiv (Fin.last (m + 1))) p) = 0 := fun z hz =>
                mvEval_eqOn_zero_of_line hRpos hΦ _ hnd hz
              by_cases hp' : (pderiv (Fin.last (m + 1))) p = 0
              · -- the relation does not involve the top jet
                have hdeg0 : MvPolynomial.degreeOf (Fin.last (m + 1)) p = 0 :=
                  degreeOf_eq_zero_of_pderiv_eq_zero hp'
                have hq := dropLastPoly_ne_zero hdeg0 hp
                refine ihn m (Nat.lt_succ_self m) (dropLastPoly p) hq ?_
                intro z hz
                have h := eval_dropLastPoly hdeg0 (fun k : Fin (m + 1 + 1) =>
                  iteratedDeriv (k : ℕ) Φ z)
                rw [← hrel z hz, ← h]
                rfl
              · refine ihd ((pderiv (Fin.last (m + 1))) p) ?_ hp' hrel'
                have hlt := degreeOf_pderiv_lt hp'
                omega

end GaloisForLFunctions

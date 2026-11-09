import GaloisForLFunctions.ArithmeticPositiveDuality.HarmonicZeroPacketsForcePositiveAnnihilatorMass

/-!
# Exact positive polynomials from simultaneous phase combinations

A finite positive combination of nonconstant monomial phases with value minus
one yields a normalized positive Dirichlet annihilator. Exponential rescaling
sets the real abscissa while preserving both phase cancellation and total mass.
-/

noncomputable section
set_option autoImplicit false
open scoped NNReal

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

private theorem dirichletEval_monomial (s : ℂ) (d : Fin 2 →₀ ℕ) (c : ℝ≥0) :
    dirichletEval s (MvPolynomial.monomial d c) =
      ((c : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * s) := by
  classical
  rw [dirichletEval_eq_frequency_sum, MvPolynomial.support_monomial]
  split_ifs with hc
  · simp [hc]
  · simp only [Finset.sum_singleton, MvPolynomial.coeff_monomial, ite_true]

private def massScaledMonomial (β : ℝ) (d : Fin 2 →₀ ℕ) (a : ℝ≥0) :
    MvPolynomial (Fin 2) ℝ≥0 :=
  MvPolynomial.monomial d
    ⟨(a : ℝ) * Real.exp (monomialLog d * β), mul_nonneg a.coe_nonneg (Real.exp_pos _).le⟩

private theorem massScaledMonomial_eval (β : ℝ) (d : Fin 2 →₀ ℕ) (a : ℝ≥0) (s : ℂ) :
    dirichletEval s (massScaledMonomial β d a) =
      ((a : ℝ) : ℂ) * Complex.exp ((monomialLog d : ℂ) * ((β : ℂ) - s)) := by
  rw [massScaledMonomial, dirichletEval_monomial]
  change (((a : ℝ) * Real.exp (monomialLog d * β) : ℝ) : ℂ) *
    Complex.exp (-(monomialLog d : ℂ) * s) = _
  simp only [Complex.ofReal_mul, Complex.ofReal_exp]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem massScaledMonomial_eval_real (β : ℝ) (d : Fin 2 →₀ ℕ) (a : ℝ≥0) :
    dirichletEval (β : ℂ) (massScaledMonomial β d a) = ((a : ℝ) : ℂ) := by
  rw [massScaledMonomial_eval]
  simp only [sub_self, mul_zero, Complex.exp_zero, mul_one]

private theorem massScaledMonomial_eval_ordinate (β γ : ℝ) (d : Fin 2 →₀ ℕ) (a : ℝ≥0) :
    dirichletEval (harmonicPacketPoint β γ 1) (massScaledMonomial β d a) =
      ((a : ℝ) : ℂ) * monomialPhase γ d := by
  rw [massScaledMonomial_eval]
  unfold harmonicPacketPoint monomialPhase
  congr 2
  push_cast
  ring

/-- A finite positive phase combination gives exact simultaneous annihilation;
its coefficient sum is exactly the nonconstant mass at the chosen abscissa. -/
theorem exists_annihilator_of_phase_combination {ι κ : Type*} [Fintype κ]
    (β : ℝ) (γ : ι → ℝ) (d : κ → Fin 2 →₀ ℕ) (a : κ → ℝ≥0)
    (hd : ∀ k, d k ≠ 0)
    (ha : ∀ i, ∑ k, ((a k : ℝ) : ℂ) * monomialPhase (γ i) (d k) = -1) :
    ∃ P : MvPolynomial (Fin 2) ℝ≥0, MvPolynomial.constantCoeff P = 1 ∧
      (∀ i, dirichletEval (harmonicPacketPoint β (γ i) 1) P = 0) ∧
      dirichletTailMass P β = ∑ k, (a k : ℝ) := by
  classical
  let P : MvPolynomial (Fin 2) ℝ≥0 := 1 + ∑ k, massScaledMonomial β (d k) (a k)
  have hc : MvPolynomial.constantCoeff P = 1 := by
    simp only [P, map_add, map_one, map_sum, massScaledMonomial,
      MvPolynomial.constantCoeff_monomial, hd, ite_false, Finset.sum_const_zero, add_zero]
  refine ⟨P, hc, ?_, ?_⟩
  · intro i
    simp only [P, map_add, map_one, map_sum, massScaledMonomial_eval_ordinate, ha, add_neg_cancel]
  · have he : dirichletEval (β : ℂ) P = ((1 + ∑ k, (a k : ℝ) : ℝ) : ℂ) := by
      simp only [P, map_add, map_one, map_sum, massScaledMonomial_eval_real,
        Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_sum]
    rw [dirichletEval_ofReal_eq_one_add_tail hc] at he
    have hr := Complex.ofReal_inj.mp he
    linarith only [hr]

#print axioms exists_annihilator_of_phase_combination

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

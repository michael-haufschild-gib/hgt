import GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilatorAccuracyForcesLeftGrowth

/-!
# The unit-mass boundary of positive Dirichlet annihilators

At unit nonconstant mass, every cancelling phase equals minus one. The real
part of the derivative is then a positive logarithmic moment, at least `log 2`.
Such a zero is simple. Positive trinomials with double zeros approach unit mass,
so multiplicity gives a strict inequality without a uniform positive gap.
-/

noncomputable section
set_option autoImplicit false
open Complex Finset
open scoped NNReal

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

/-- Every nonconstant two-prime monomial has logarithmic frequency at least `log 2`. -/
theorem log_two_le_monomialLog (d : Fin 2 →₀ ℕ) (hd : d ≠ 0) :
    Real.log 2 ≤ monomialLog d := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h23 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  have hn : d 0 ≠ 0 ∨ d 1 ≠ 0 := by
    by_contra! h
    apply hd
    ext i
    fin_cases i
    · exact h.1
    · exact h.2
  change Real.log 2 ≤ (d 0 : ℝ) * Real.log 2 + (d 1 : ℝ) * Real.log 3
  rcases hn with hn | hn
  · have hp : (1 : ℝ) ≤ (d 0 : ℝ) := by
      exact_mod_cast (show 1 ≤ d 0 from Nat.pos_of_ne_zero hn)
    have hm : Real.log 2 ≤ (d 0 : ℝ) * Real.log 2 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp h2.le
    exact hm.trans (le_add_of_nonneg_right (by positivity))
  · have hp : (1 : ℝ) ≤ (d 1 : ℝ) := by
      exact_mod_cast (show 1 ≤ d 1 from Nat.pos_of_ne_zero hn)
    have hm : Real.log 3 ≤ (d 1 : ℝ) * Real.log 3 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp h3.le
    exact (h23.trans hm).trans (le_add_of_nonneg_left (by positivity))

/-- Differentiating the nonconstant Dirichlet monomials multiplies them by minus their logs. -/
theorem hasDerivAt_dirichletEval_tail {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) (ρ : ℂ) :
    HasDerivAt (fun s => dirichletEval s P)
      (∑ d ∈ P.support.erase 0, ((-monomialLog d * ((P.coeff d : ℝ≥0) : ℝ) : ℝ) : ℂ) *
        Complex.exp (-(monomialLog d : ℂ) * ρ)) ρ := by
  have hfun : (fun s => dirichletEval s P) = fun s => 1 +
      ∑ d ∈ P.support.erase 0, (((P.coeff d : ℝ≥0) : ℝ) : ℂ) *
        Complex.exp (-(monomialLog d : ℂ) * s) := by
    funext s
    exact dirichletEval_eq_one_add_tail hP s
  rw [hfun]
  apply HasDerivAt.const_add
  apply HasDerivAt.fun_sum
  intro d _
  have h := (Complex.hasDerivAt_exp (-(monomialLog d : ℂ) * ρ)).comp ρ
    ((hasDerivAt_id ρ).const_mul (-(monomialLog d : ℂ)))
  have heq : (((P.coeff d : ℝ≥0) : ℝ) : ℂ) *
      (Complex.exp (-(monomialLog d : ℂ) * ρ) * (-(monomialLog d : ℂ))) =
      ((-monomialLog d * ((P.coeff d : ℝ≥0) : ℝ) : ℝ) : ℂ) *
        Complex.exp (-(monomialLog d : ℂ) * ρ) := by
    push_cast
    ring
  rw [← heq]
  simpa only [Function.comp_def, mul_one] using
    h.const_mul (((P.coeff d : ℝ≥0) : ℝ) : ℂ)

/-- At unit mass, the real derivative is the positive logarithmic moment. -/
theorem deriv_re_at_unit_tail_mass {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {ρ : ℂ} (hz : dirichletEval ρ P = 0)
    (hm : dirichletTailMass P ρ.re = 1) :
    (deriv (fun s => dirichletEval s P) ρ).re =
      ∑ d ∈ P.support.erase 0, monomialLog d *
        (((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * ρ.re)) := by
  have hphase := (dirichletTailMass_eq_one_iff_phases hP hz).mp hm
  rw [(hasDerivAt_dirichletEval_tail hP ρ).deriv]
  change Complex.reAddGroupHom (∑ d ∈ P.support.erase 0,
    ((-monomialLog d * ((P.coeff d : ℝ≥0) : ℝ) : ℝ) : ℂ) *
      Complex.exp (-(monomialLog d : ℂ) * ρ)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  change (((-monomialLog d * ((P.coeff d : ℝ≥0) : ℝ) : ℝ) : ℂ) *
    Complex.exp (-(monomialLog d : ℂ) * ρ)).re = _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.exp_re, Complex.neg_re, Complex.neg_im,
    Complex.mul_im, add_zero, neg_mul, Real.cos_neg]
  rw [hphase d hd]
  ring

/-- The unit-mass boundary has a uniform positive real derivative. -/
theorem log_two_le_deriv_re_at_unit_tail_mass {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {ρ : ℂ} (hz : dirichletEval ρ P = 0)
    (hm : dirichletTailMass P ρ.re = 1) :
    Real.log 2 ≤ (deriv (fun s => dirichletEval s P) ρ).re := by
  rw [deriv_re_at_unit_tail_mass hP hz hm]
  calc
    Real.log 2 = Real.log 2 * dirichletTailMass P ρ.re := by rw [hm, mul_one]
    _ = ∑ d ∈ P.support.erase 0, Real.log 2 *
        (((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * ρ.re)) := by
      rw [dirichletTailMass, Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun d hd =>
      mul_le_mul_of_nonneg_right (log_two_le_monomialLog d (Finset.mem_erase.mp hd).1)
        (mul_nonneg (P.coeff d).coe_nonneg (Real.exp_pos _).le)

/-- A zero on the unit-mass boundary is simple. -/
theorem analyticOrderAt_eq_one_of_unit_tail_mass {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {ρ : ℂ} (hz : dirichletEval ρ P = 0)
    (hm : dirichletTailMass P ρ.re = 1) :
    analyticOrderAt (fun s => dirichletEval s P) ρ = 1 := by
  apply ((differentiable_dirichletEval P).analyticAt ρ).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz
  intro hd
  have hp := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le
    (log_two_le_deriv_re_at_unit_tail_mass hP hz hm)
  rw [hd, Complex.zero_re] at hp
  exact (lt_irrefl 0) hp

/-- A multiple zero requires strictly greater than unit tail mass. -/
theorem one_lt_tail_mass_of_zero_deriv {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {ρ : ℂ} (hz : dirichletEval ρ P = 0)
    (hd : deriv (fun s => dirichletEval s P) ρ = 0) :
    1 < dirichletTailMass P ρ.re := by
  by_contra! hm
  have heq := le_antisymm hm (one_le_dirichletTailMass_of_zero hP hz)
  have hp := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le
    (log_two_le_deriv_re_at_unit_tail_mass hP hz heq)
  rw [hd, Complex.zero_re] at hp
  exact (lt_irrefl 0) hp

#print axioms log_two_le_deriv_re_at_unit_tail_mass
#print axioms analyticOrderAt_eq_one_of_unit_tail_mass
#print axioms one_lt_tail_mass_of_zero_deriv

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

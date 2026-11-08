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

/-- The scaled prime-two monomial takes the value minus one at the marked zero. -/
def scaledTwoMonomial (β : ℝ) : MvPolynomial (Fin 2) ℝ≥0 :=
  MvPolynomial.C (sharpBinomialCoefficient β) * MvPolynomial.X 0

/-- A double zero incurs the sharp mass cost imposed by its finite frequency range. -/
theorem double_zero_forces_frequency_span_cost {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {ρ : ℂ} (hz : dirichletEval ρ P = 0)
    (hd : deriv (fun s => dirichletEval s P) ρ = 0) (B : ℝ)
    (hB : ∀ d ∈ P.support.erase 0, monomialLog d ≤ B) :
    Real.log 2 < B ∧
      (B + Real.log 2) / (B - Real.log 2) ≤ dirichletTailMass P ρ.re := by
  let c : ℝ := (B + Real.log 2) / 2
  let r : ℝ := (B - Real.log 2) / 2
  have htail : (∑ d ∈ P.support.erase 0, (((P.coeff d : ℝ≥0) : ℝ) : ℂ) *
      Complex.exp (-(monomialLog d : ℂ) * ρ)) = -1 := by
    have he := dirichletEval_eq_one_add_tail hP ρ
    rw [hz] at he
    linear_combination -he
  have hslope : (∑ d ∈ P.support.erase 0,
      ((-monomialLog d * ((P.coeff d : ℝ≥0) : ℝ) : ℝ) : ℂ) *
        Complex.exp (-(monomialLog d : ℂ) * ρ)) = 0 := by
    rw [← (hasDerivAt_dirichletEval_tail hP ρ).deriv, hd]
  have hcenter : (∑ d ∈ P.support.erase 0,
      (((c - monomialLog d) * ((P.coeff d : ℝ≥0) : ℝ) : ℝ) : ℂ) *
        Complex.exp (-(monomialLog d : ℂ) * ρ)) = -(c : ℂ) := by
    calc
      _ = (c : ℂ) * (∑ d ∈ P.support.erase 0, (((P.coeff d : ℝ≥0) : ℝ) : ℂ) *
          Complex.exp (-(monomialLog d : ℂ) * ρ)) +
          ∑ d ∈ P.support.erase 0,
            ((-monomialLog d * ((P.coeff d : ℝ≥0) : ℝ) : ℝ) : ℂ) *
              Complex.exp (-(monomialLog d : ℂ) * ρ) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro d _
        push_cast
        ring
      _ = _ := by rw [htail, hslope]; ring
  have hterm (d : Fin 2 →₀ ℕ) (hd : d ∈ P.support.erase 0) :
      ‖(((c - monomialLog d) * ((P.coeff d : ℝ≥0) : ℝ) : ℝ) : ℂ) *
        Complex.exp (-(monomialLog d : ℂ) * ρ)‖ ≤
      r * (((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * ρ.re)) := by
    have hlow := log_two_le_monomialLog d (Finset.mem_erase.mp hd).1
    have hupp := hB d hd
    have hdist : |c - monomialLog d| ≤ r := by
      apply abs_le.mpr
      constructor <;> dsimp only [c, r] <;> linarith only [hlow, hupp]
    calc
      _ = |c - monomialLog d| *
          (((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * ρ.re)) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (P.coeff d).coe_nonneg, Complex.norm_exp]
        simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
          Complex.neg_im, Complex.ofReal_im, neg_zero, zero_mul, sub_zero, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_right hdist
        (mul_nonneg (P.coeff d).coe_nonneg (Real.exp_pos _).le)
  have hcost : c ≤ r * dirichletTailMass P ρ.re := by
    calc
      c ≤ ‖(c : ℂ)‖ := Complex.re_le_norm (c : ℂ)
      _ = ‖∑ d ∈ P.support.erase 0,
          (((c - monomialLog d) * ((P.coeff d : ℝ≥0) : ℝ) : ℝ) : ℂ) *
            Complex.exp (-(monomialLog d : ℂ) * ρ)‖ := by rw [hcenter, norm_neg]
      _ ≤ ∑ d ∈ P.support.erase 0,
          ‖(((c - monomialLog d) * ((P.coeff d : ℝ≥0) : ℝ) : ℝ) : ℂ) *
            Complex.exp (-(monomialLog d : ℂ) * ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ P.support.erase 0, r *
          (((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * ρ.re)) :=
        Finset.sum_le_sum hterm
      _ = _ := by rw [dirichletTailMass, Finset.mul_sum]
  have hcost' : B + Real.log 2 ≤ (B - Real.log 2) * dirichletTailMass P ρ.re := by
    dsimp only [c, r] at hcost
    linarith only [hcost]
  have hS : (P.support.erase 0).Nonempty := by
    have hm := one_le_dirichletTailMass_of_zero hP hz
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty] at hn
    simp only [dirichletTailMass, hn, Finset.sum_empty] at hm
    norm_num at hm
  obtain ⟨d, hdmem⟩ := hS
  have hBlo := (log_two_le_monomialLog d (Finset.mem_erase.mp hdmem).1).trans (hB d hdmem)
  have hgap : Real.log 2 < B := by
    by_contra! hle
    have heq := le_antisymm hle hBlo
    rw [heq, sub_self, zero_mul] at hcost'
    linarith only [hcost', Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  refine ⟨hgap, (div_le_iff₀ (sub_pos.mpr hgap)).mpr ?_⟩
  simpa only [mul_comm] using hcost'

theorem dirichletEval_scaledTwoMonomial (β : ℝ) (s : ℂ) :
    dirichletEval s (scaledTwoMonomial β) =
      Complex.exp ((Real.log 2 : ℂ) * ((β : ℂ) - s)) := by
  have h := dirichletEval_sharpBinomial β s
  change dirichletEval s (1 + scaledTwoMonomial β) = _ at h
  rw [map_add, map_one] at h
  exact add_left_cancel h

theorem scaledTwoMonomial_at_root (β : ℝ) :
    dirichletEval (sharpBinomialRoot β) (scaledTwoMonomial β) = -1 := by
  have h := sharpBinomial_vanishes β
  change dirichletEval (sharpBinomialRoot β) (1 + scaledTwoMonomial β) = 0 at h
  rw [map_add, map_one] at h
  linear_combination h

theorem scaledTwoMonomial_at_real (β : ℝ) :
    dirichletEval (β : ℂ) (scaledTwoMonomial β) = 1 := by
  rw [dirichletEval_scaledTwoMonomial, sub_self, mul_zero, Complex.exp_zero]

theorem scaledTwoMonomial_hasDerivAt_root (β : ℝ) :
    HasDerivAt (fun s => dirichletEval s (scaledTwoMonomial β)) (Real.log 2 : ℂ)
      (sharpBinomialRoot β) := by
  have hvalue : Complex.exp ((Real.log 2 : ℂ) * ((β : ℂ) - sharpBinomialRoot β)) = -1 := by
    rw [← dirichletEval_scaledTwoMonomial, scaledTwoMonomial_at_root]
  have hfun : (fun s => dirichletEval s (scaledTwoMonomial β)) =
      fun s => Complex.exp ((Real.log 2 : ℂ) * ((β : ℂ) - s)) := by
    funext s
    exact dirichletEval_scaledTwoMonomial β s
  rw [hfun]
  have h := (Complex.hasDerivAt_exp
    ((Real.log 2 : ℂ) * ((β : ℂ) - sharpBinomialRoot β))).comp (sharpBinomialRoot β)
      (((hasDerivAt_const (sharpBinomialRoot β) (β : ℂ)).sub
        (hasDerivAt_id (sharpBinomialRoot β))).const_mul (Real.log 2 : ℂ))
  simpa only [Function.comp_def, Pi.sub_def, id_eq, hvalue, zero_sub, mul_neg_one,
    neg_one_mul, neg_neg] using h

/-- The extremal binomial attains the derivative bound at its marked zero. -/
theorem sharpBinomial_hasDerivAt_root (β : ℝ) :
    HasDerivAt (fun s => dirichletEval s (sharpBinomial β)) (Real.log 2 : ℂ)
      (sharpBinomialRoot β) := by
  have hfun : (fun s => dirichletEval s (sharpBinomial β)) =
      fun s => 1 + dirichletEval s (scaledTwoMonomial β) := by
    funext s
    change dirichletEval s (1 + scaledTwoMonomial β) = _
    rw [map_add, map_one]
  rw [hfun]
  exact (scaledTwoMonomial_hasDerivAt_root β).const_add 1

/-- Unit mass and the derivative bound are attained simultaneously on every real line. -/
theorem exists_sharp_unit_mass_simple_annihilator (β : ℝ) :
    ∃ P : MvPolynomial (Fin 2) ℝ≥0, ∃ ρ : ℂ,
      MvPolynomial.constantCoeff P = 1 ∧ ρ.re = β ∧ dirichletEval ρ P = 0 ∧
      dirichletTailMass P β = 1 ∧ deriv (fun s => dirichletEval s P) ρ = (Real.log 2 : ℂ) ∧
      analyticOrderAt (fun s => dirichletEval s P) ρ = 1 := by
  have hm : dirichletTailMass (sharpBinomial β) β = 1 := by
    rw [dirichletTailMass_sharpBinomial, sub_self, mul_zero, Real.exp_zero]
  refine ⟨sharpBinomial β, sharpBinomialRoot β, sharpBinomial_constantCoeff β,
    sharpBinomialRoot_re β, sharpBinomial_vanishes β, hm,
    (sharpBinomial_hasDerivAt_root β).deriv, ?_⟩
  apply analyticOrderAt_eq_one_of_unit_tail_mass (sharpBinomial_constantCoeff β)
    (sharpBinomial_vanishes β)
  simpa only [sharpBinomialRoot_re] using hm

/-- The linear coefficient of the positive double-zero trinomial. -/
def doubleZeroLinearCoefficient (m : ℕ) : ℝ≥0 :=
  ⟨(2 * (m : ℝ) + 2) / (2 * (m : ℝ) + 1), by positivity⟩

/-- The high-degree coefficient of the positive double-zero trinomial. -/
def doubleZeroTailCoefficient (m : ℕ) : ℝ≥0 :=
  ⟨1 / (2 * (m : ℝ) + 1), by positivity⟩

/-- A positive trinomial with a double zero and tail mass tending to one. -/
def doubleZeroAnnihilator (β : ℝ) (m : ℕ) : MvPolynomial (Fin 2) ℝ≥0 :=
  1 + MvPolynomial.C (doubleZeroLinearCoefficient m) * scaledTwoMonomial β +
    MvPolynomial.C (doubleZeroTailCoefficient m) * scaledTwoMonomial β ^ (2 * m + 2)

theorem doubleZeroAnnihilator_constantCoeff (β : ℝ) (m : ℕ) :
    MvPolynomial.constantCoeff (doubleZeroAnnihilator β m) = 1 := by
  simp [doubleZeroAnnihilator, scaledTwoMonomial, pow_add]

theorem dirichletEval_doubleZeroAnnihilator (β : ℝ) (m : ℕ) (s : ℂ) :
    dirichletEval s (doubleZeroAnnihilator β m) =
      1 + (((2 * (m : ℝ) + 2) / (2 * (m : ℝ) + 1) : ℝ) : ℂ) *
        dirichletEval s (scaledTwoMonomial β) +
      ((1 / (2 * (m : ℝ) + 1) : ℝ) : ℂ) *
        dirichletEval s (scaledTwoMonomial β) ^ (2 * m + 2) := by
  simp only [doubleZeroAnnihilator, map_add, map_one, map_mul, map_pow,
    dirichletEval, MvPolynomial.eval₂Hom_C]
  rfl

theorem doubleZeroAnnihilator_vanishes (β : ℝ) (m : ℕ) :
    dirichletEval (sharpBinomialRoot β) (doubleZeroAnnihilator β m) = 0 := by
  have hd : 2 * (m : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show 2 * (m : ℝ) + 1 ≠ 0 by positivity)
  have hp : (-1 : ℂ) ^ (2 * m + 2) = 1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [dirichletEval_doubleZeroAnnihilator, scaledTwoMonomial_at_root, hp]
  push_cast
  field_simp [hd]
  ring

theorem doubleZeroAnnihilator_deriv_eq_zero (β : ℝ) (m : ℕ) :
    deriv (fun s => dirichletEval s (doubleZeroAnnihilator β m)) (sharpBinomialRoot β) = 0 := by
  have hV := scaledTwoMonomial_hasDerivAt_root β
  have h := ((hV.const_mul
    (((2 * (m : ℝ) + 2) / (2 * (m : ℝ) + 1) : ℝ) : ℂ)).const_add 1).add
      ((hV.pow (2 * m + 2)).const_mul ((1 / (2 * (m : ℝ) + 1) : ℝ) : ℂ))
  have hp : (-1 : ℂ) ^ (2 * m + 2 - 1) = -1 := by
    rw [show 2 * m + 2 - 1 = 2 * m + 1 by omega, pow_succ, pow_mul]
    norm_num
  have hd : 2 * (m : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show 2 * (m : ℝ) + 1 ≠ 0 by positivity)
  have hc : (((2 * (m : ℝ) + 2) / (2 * (m : ℝ) + 1) : ℝ) : ℂ) * (Real.log 2 : ℂ) +
      ((1 / (2 * (m : ℝ) + 1) : ℝ) : ℂ) *
        (((2 * m + 2 : ℕ) : ℂ) * (-1 : ℂ) * (Real.log 2 : ℂ)) = 0 := by
    push_cast
    field_simp [hd]
    ring
  rw [scaledTwoMonomial_at_root, hp, hc] at h
  have hfun : (fun s => dirichletEval s (doubleZeroAnnihilator β m)) =
      fun s => 1 + (((2 * (m : ℝ) + 2) / (2 * (m : ℝ) + 1) : ℝ) : ℂ) *
        dirichletEval s (scaledTwoMonomial β) +
        ((1 / (2 * (m : ℝ) + 1) : ℝ) : ℂ) *
          dirichletEval s (scaledTwoMonomial β) ^ (2 * m + 2) := by
    funext s
    exact dirichletEval_doubleZeroAnnihilator β m s
  rw [hfun]
  exact h.deriv

theorem doubleZeroAnnihilator_tail_mass (β : ℝ) (m : ℕ) :
    dirichletTailMass (doubleZeroAnnihilator β m) β = 1 + 2 / (2 * (m : ℝ) + 1) := by
  rw [← norm_dirichletEval_real_error (doubleZeroAnnihilator_constantCoeff β m)]
  have hd : 2 * (m : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show 2 * (m : ℝ) + 1 ≠ 0 by positivity)
  have he : dirichletEval (β : ℂ) (doubleZeroAnnihilator β m) - 1 =
      ((1 + 2 / (2 * (m : ℝ) + 1) : ℝ) : ℂ) := by
    rw [dirichletEval_doubleZeroAnnihilator, scaledTwoMonomial_at_real, one_pow]
    push_cast
    field_simp [hd]
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- Double zeros of positive Dirichlet polynomials have no uniform mass gap above one. -/
theorem exists_double_zero_annihilator_with_mass_near_one (β : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin 2) ℝ≥0, ∃ ρ : ℂ,
      MvPolynomial.constantCoeff P = 1 ∧ ρ.re = β ∧ dirichletEval ρ P = 0 ∧
      deriv (fun s => dirichletEval s P) ρ = 0 ∧
      1 < dirichletTailMass P β ∧ dirichletTailMass P β < 1 + ε := by
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε)
  have hmε : 1 < (m : ℝ) * ε := (div_lt_iff₀ hε).mp hm
  have hden : 0 < 2 * (m : ℝ) + 1 := by positivity
  have hsmall : 2 / (2 * (m : ℝ) + 1) < ε := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith only [hmε, hε]
  refine ⟨doubleZeroAnnihilator β m, sharpBinomialRoot β,
    doubleZeroAnnihilator_constantCoeff β m, sharpBinomialRoot_re β,
    doubleZeroAnnihilator_vanishes β m, doubleZeroAnnihilator_deriv_eq_zero β m, ?_, ?_⟩
  · rw [doubleZeroAnnihilator_tail_mass]
    linarith only [div_pos (by norm_num : (0 : ℝ) < 2) hden]
  · rw [doubleZeroAnnihilator_tail_mass]
    linarith only [hsmall]

#print axioms log_two_le_deriv_re_at_unit_tail_mass
#print axioms analyticOrderAt_eq_one_of_unit_tail_mass
#print axioms one_lt_tail_mass_of_zero_deriv
#print axioms double_zero_forces_frequency_span_cost
#print axioms exists_sharp_unit_mass_simple_annihilator
#print axioms exists_double_zero_annihilator_with_mass_near_one

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

import GaloisForLFunctions.ArithmeticPositiveDuality.SparseHarmonicAnnihilatorMass

/-!
# Exact accuracy frontier for sparse harmonic annihilation

Two conjugate fifth-root phases attain the golden-ratio mass bound. Scaling their positive
coefficients realizes every accuracy between zero and one, at every real abscissa.
-/

noncomputable section
set_option autoImplicit false

open Complex Finset
open scoped NNReal ComplexConjugate

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

private def sparseHarmonicCoefficient (ε : ℝ) : ℝ≥0 :=
  ⟨max ((1 - ε) / Real.goldenRatio) 0, le_max_right _ _⟩

/-- A positive three-term polynomial attaining the sparse-harmonic accuracy bound. -/
def sparseHarmonicAnnihilator (β ε : ℝ) : MvPolynomial (Fin 2) ℝ≥0 :=
  1 + MvPolynomial.C (sparseHarmonicCoefficient ε) *
    (scaledTwoMonomial β ^ 2 + scaledTwoMonomial β ^ 3)

theorem sparseHarmonicAnnihilator_constantCoeff (β ε : ℝ) :
    MvPolynomial.constantCoeff (sparseHarmonicAnnihilator β ε) = 1 := by
  simp [sparseHarmonicAnnihilator, scaledTwoMonomial]

private theorem sparseHarmonicAnnihilator_eval (β ε : ℝ) (hε : ε ≤ 1) (s : ℂ) :
    dirichletEval s (sparseHarmonicAnnihilator β ε) =
      1 + (((1 - ε) / Real.goldenRatio : ℝ) : ℂ) *
        (dirichletEval s (scaledTwoMonomial β) ^ 2 +
          dirichletEval s (scaledTwoMonomial β) ^ 3) := by
  have hn : 0 ≤ (1 - ε) / Real.goldenRatio :=
    div_nonneg (sub_nonneg.mpr hε) Real.goldenRatio_pos.le
  have hc : dirichletEval s (MvPolynomial.C (sparseHarmonicCoefficient ε)) =
      (((1 - ε) / Real.goldenRatio : ℝ) : ℂ) := by
    simp only [dirichletEval, MvPolynomial.eval₂Hom_C]
    change ((max ((1 - ε) / Real.goldenRatio) 0 : ℝ) : ℂ) = _
    rw [max_eq_left hn]
  simp only [sparseHarmonicAnnihilator, map_add, map_one, map_mul, map_pow]
  rw [hc]

theorem sparseHarmonicAnnihilator_tail_mass (β ε : ℝ) (hε : ε ≤ 1) :
    dirichletTailMass (sparseHarmonicAnnihilator β ε) β =
      sparseHarmonicMassConstant * (1 - ε) := by
  have he := dirichletEval_ofReal_eq_one_add_tail
    (sparseHarmonicAnnihilator_constantCoeff β ε) β
  rw [sparseHarmonicAnnihilator_eval β ε hε, scaledTwoMonomial_at_real] at he
  have hr := congrArg Complex.re he
  simp only [one_pow, Complex.add_re, Complex.one_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hr
  have hm : (1 - ε) / Real.goldenRatio * (1 + 1) =
      sparseHarmonicMassConstant * (1 - ε) := by
    unfold sparseHarmonicMassConstant
    ring
  linarith only [hr, hm]

private def fifthUnit : ℂ := Complex.exp (-(2 * (Real.pi : ℂ)) * I / 5)

private theorem fifthUnit_norm : ‖fifthUnit‖ = 1 := by
  norm_num [fifthUnit, Complex.norm_exp]

private theorem fifthUnit_pow_five : fifthUnit ^ 5 = 1 := by
  unfold fifthUnit
  rw [← Complex.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have he : (5 : ℂ) * (-(2 * (Real.pi : ℂ)) * I / 5) =
      -(Real.pi * I) + -(Real.pi * I) := by ring
  rw [he, Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

private theorem fifthUnit_pair : fifthUnit ^ 2 + fifthUnit ^ 3 = -(Real.goldenRatio : ℂ) := by
  have hreal : (fifthUnit ^ 2).re = -Real.goldenRatio / 2 := by
    unfold fifthUnit
    rw [← Complex.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    have he : (2 : ℂ) * (-(2 * (Real.pi : ℂ)) * I / 5) =
        ((-(4 * Real.pi / 5) : ℝ) : ℂ) * I := by push_cast; ring
    rw [he, Complex.exp_re]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, sub_self, Complex.mul_im, mul_one, add_zero,
      Real.exp_zero, one_mul, Real.cos_neg]
    rw [show 4 * Real.pi / 5 = Real.pi - Real.pi / 5 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_five]
    unfold Real.goldenRatio
    ring
  have hunit : conj (fifthUnit ^ 2) * fifthUnit ^ 2 = 1 := by
    rw [Complex.conj_mul', norm_pow, fifthUnit_norm, one_pow]
    norm_num
  have hpow : fifthUnit ^ 3 * fifthUnit ^ 2 = 1 := by
    rw [← pow_add]
    exact fifthUnit_pow_five
  have hn : fifthUnit ^ 2 ≠ 0 :=
    pow_ne_zero _ (Complex.exp_ne_zero _)
  have hc : fifthUnit ^ 3 = conj (fifthUnit ^ 2) :=
    mul_right_cancel₀ hn (hpow.trans hunit.symm)
  rw [hc]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.conj_re, hreal, Complex.neg_re, Complex.ofReal_re]
    ring
  · simp only [Complex.add_im, Complex.conj_im, add_neg_cancel, Complex.neg_im,
      Complex.ofReal_im, neg_zero]

private theorem fifthUnit_sparse_pair (k : ℕ) (hk : k = 1 ∨ k = 4) :
    (fifthUnit ^ k) ^ 2 + (fifthUnit ^ k) ^ 3 = -(Real.goldenRatio : ℂ) := by
  rcases hk with rfl | rfl
  · simpa only [pow_one] using fifthUnit_pair
  · rw [← pow_mul, ← pow_mul,
      show 4 * 2 = 5 + 3 by rfl, show 4 * 3 = 5 + 5 + 2 by rfl,
      pow_add, pow_add, pow_add, fifthUnit_pow_five]
    simpa only [one_mul, one_mul, add_comm] using fifthUnit_pair

private theorem scaledTwoMonomial_at_fifth (β : ℝ) (k : ℕ) :
    dirichletEval (harmonicPacketPoint β (harmonicPacketStep 4) k)
      (scaledTwoMonomial β) = fifthUnit ^ k := by
  rw [dirichletEval_scaledTwoMonomial]
  have hl : (Real.log 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'
  have he : (Real.log 2 : ℂ) *
      ((β : ℂ) - harmonicPacketPoint β (harmonicPacketStep 4) k) =
      (k : ℂ) * (-(2 * (Real.pi : ℂ)) * I / 5) := by
    simp only [harmonicPacketPoint, harmonicPacketStep, Complex.ofReal_div,
      Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one,
      Nat.cast_ofNat, Complex.ofReal_ofNat]
    norm_num only
    field_simp [hl]
    ring
  rw [he, Complex.exp_nat_mul]
  rfl

/-- Both sparse harmonic evaluations equal the prescribed real accuracy. -/
theorem sparseHarmonicAnnihilator_at_harmonic (β ε : ℝ) (hε : ε ≤ 1)
    (k : ℕ) (hk : k = 1 ∨ k = 4) :
    dirichletEval (harmonicPacketPoint β (harmonicPacketStep 4) k)
      (sparseHarmonicAnnihilator β ε) = (ε : ℂ) := by
  rw [sparseHarmonicAnnihilator_eval β ε hε, scaledTwoMonomial_at_fifth,
    fifthUnit_sparse_pair k hk]
  have hp : (Real.goldenRatio : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.goldenRatio_ne_zero
  rw [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one]
  field_simp [hp]
  ring

/-- At every abscissa and every accuracy in `[0,1]`, the mass bound is attained by a positive
polynomial supported on powers of two. -/
theorem exists_sharp_sparse_harmonic_accuracy (β ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ∃ (P : MvPolynomial (Fin 2) ℝ≥0) (γ : ℝ),
      MvPolynomial.constantCoeff P = 1 ∧ 0 < γ ∧
      ‖dirichletEval (harmonicPacketPoint β γ 1) P‖ = ε ∧
      ‖dirichletEval (harmonicPacketPoint β γ 4) P‖ = ε ∧
      dirichletTailMass P β = sparseHarmonicMassConstant * (1 - ε) := by
  refine ⟨sparseHarmonicAnnihilator β ε, harmonicPacketStep 4,
    sparseHarmonicAnnihilator_constantCoeff β ε, harmonicPacketStep_pos 4, ?_, ?_,
    sparseHarmonicAnnihilator_tail_mass β ε hε1⟩
  · rw [sparseHarmonicAnnihilator_at_harmonic β ε hε1 1 (Or.inl rfl),
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε0]
  · rw [sparseHarmonicAnnihilator_at_harmonic β ε hε1 4 (Or.inr rfl),
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε0]

/-- The exact feasible mass threshold for simultaneous sparse harmonic accuracy. -/
theorem sparse_harmonic_accuracy_frontier (β ε H : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∃ (P : MvPolynomial (Fin 2) ℝ≥0) (γ : ℝ),
      MvPolynomial.constantCoeff P = 1 ∧ 0 < γ ∧
      ‖dirichletEval (harmonicPacketPoint β γ 1) P‖ ≤ ε ∧
      ‖dirichletEval (harmonicPacketPoint β γ 4) P‖ ≤ ε ∧
      dirichletTailMass P β ≤ H) ↔ sparseHarmonicMassConstant * (1 - ε) ≤ H := by
  constructor
  · rintro ⟨P, γ, hP, _, h1, h4, hH⟩
    exact (sparseHarmonic_accuracy_mass_bound hP β γ ε h1 h4).trans hH
  · intro hH
    obtain ⟨P, γ, hP, hγ, h1, h4, hmass⟩ := exists_sharp_sparse_harmonic_accuracy β ε hε0 hε1
    exact ⟨P, γ, hP, hγ, h1.le, h4.le, hmass.le.trans hH⟩

#print axioms sparseHarmonicAnnihilator_at_harmonic
#print axioms exists_sharp_sparse_harmonic_accuracy
#print axioms sparse_harmonic_accuracy_frontier

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

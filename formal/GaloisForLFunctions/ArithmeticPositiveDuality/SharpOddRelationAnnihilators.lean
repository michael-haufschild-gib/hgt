import GaloisForLFunctions.ArithmeticPositiveDuality.SharpOddOrdinateRelationMass

/-!
# Positive extremizers for every odd relation length

The two central powers of a primitive odd root have sum `-2 cos (π/q)`.
Their positive Dirichlet polynomial realizes the sharp mass threshold at every
real abscissa and every prescribed accuracy between zero and one.
-/

noncomputable section
set_option autoImplicit false

open Complex Finset
open scoped NNReal ComplexConjugate

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

private theorem odd_cycle_cos_pos (r : ℕ) (hr : 1 ≤ r) :
    0 < Real.cos (Real.pi / (2 * r + 1 : ℕ)) := by
  have hq : (0 : ℝ) < (2 * r + 1 : ℕ) := by positivity
  have h3 : (3 : ℝ) ≤ (2 * r + 1 : ℕ) := by exact_mod_cast (by omega : 3 ≤ 2 * r + 1)
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have hp := div_pos Real.pi_pos hq
    linarith only [hp, Real.pi_pos]
  · apply (div_lt_iff₀ hq).mpr
    nlinarith only [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr h3), Real.pi_pos]

private def oddRelationCoefficient (r : ℕ) (ε : ℝ) : ℝ≥0 :=
  ⟨max ((1 - ε) / (2 * Real.cos (Real.pi / (2 * r + 1 : ℕ)))) 0, le_max_right _ _⟩

/-- The positive polynomial on the two central powers of an odd root. -/
def oddRelationAnnihilator (β ε : ℝ) (r : ℕ) : MvPolynomial (Fin 2) ℝ≥0 :=
  1 + MvPolynomial.C (oddRelationCoefficient r ε) *
    (scaledTwoMonomial β ^ r + scaledTwoMonomial β ^ (r + 1))

theorem oddRelationAnnihilator_constantCoeff (β ε : ℝ) (r : ℕ) (hr : 1 ≤ r) :
    MvPolynomial.constantCoeff (oddRelationAnnihilator β ε r) = 1 := by
  have hz : MvPolynomial.constantCoeff (scaledTwoMonomial β) = 0 := by
    simp [scaledTwoMonomial]
  simp only [oddRelationAnnihilator, map_add, map_one, map_mul, map_pow, hz,
    zero_pow (by omega : r ≠ 0), zero_pow (Nat.succ_ne_zero r), add_zero, mul_zero]

private theorem oddRelationAnnihilator_eval (β ε : ℝ) (r : ℕ) (hr : 1 ≤ r)
    (hε : ε ≤ 1) (s : ℂ) :
    dirichletEval s (oddRelationAnnihilator β ε r) =
      1 + (((1 - ε) / (2 * Real.cos (Real.pi / (2 * r + 1 : ℕ))) : ℝ) : ℂ) *
        (dirichletEval s (scaledTwoMonomial β) ^ r +
          dirichletEval s (scaledTwoMonomial β) ^ (r + 1)) := by
  have hn : 0 ≤ (1 - ε) / (2 * Real.cos (Real.pi / (2 * r + 1 : ℕ))) :=
    div_nonneg (sub_nonneg.mpr hε) (mul_pos (by norm_num) (odd_cycle_cos_pos r hr)).le
  have hc : dirichletEval s (MvPolynomial.C (oddRelationCoefficient r ε)) =
      (((1 - ε) / (2 * Real.cos (Real.pi / (2 * r + 1 : ℕ))) : ℝ) : ℂ) := by
    simp only [dirichletEval, MvPolynomial.eval₂Hom_C]
    change ((max ((1 - ε) / (2 * Real.cos (Real.pi / (2 * r + 1 : ℕ)))) 0 : ℝ) : ℂ) = _
    rw [max_eq_left hn]
  simp only [oddRelationAnnihilator, map_add, map_one, map_mul, map_pow]
  rw [hc]

theorem oddRelationAnnihilator_tail_mass (β ε : ℝ) (r : ℕ) (hr : 1 ≤ r)
    (hε : ε ≤ 1) :
    dirichletTailMass (oddRelationAnnihilator β ε r) β =
      (1 - ε) / Real.cos (Real.pi / (2 * r + 1 : ℕ)) := by
  have he := dirichletEval_ofReal_eq_one_add_tail
    (oddRelationAnnihilator_constantCoeff β ε r hr) β
  rw [oddRelationAnnihilator_eval β ε r hr hε, scaledTwoMonomial_at_real] at he
  have h := congrArg Complex.re he
  simp only [one_pow, Complex.add_re, Complex.one_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  have hc := (odd_cycle_cos_pos r hr).ne'
  have heq : (1 - ε) / (2 * Real.cos (Real.pi / (2 * r + 1 : ℕ))) * (1 + 1) =
      (1 - ε) / Real.cos (Real.pi / (2 * r + 1 : ℕ)) := by field_simp; ring
  linarith only [h, heq]

private def oddUnit (r : ℕ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ)) * I / (2 * r + 1 : ℕ))

private theorem oddUnit_norm (r : ℕ) : ‖oddUnit r‖ = 1 := by
  simp [oddUnit, Complex.norm_exp, Complex.div_re, Complex.mul_re, Complex.mul_im]

private theorem oddUnit_pow_order (r : ℕ) : oddUnit r ^ (2 * r + 1) = 1 := by
  unfold oddUnit
  rw [← Complex.exp_nat_mul]
  have hq : ((2 * r + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2 * r + 1 ≠ 0)
  have he : ((2 * r + 1 : ℕ) : ℂ) *
      (-(2 * (Real.pi : ℂ)) * I / (2 * r + 1 : ℕ)) =
        -(Real.pi * I) + -(Real.pi * I) := by field_simp [hq]; ring
  rw [he, Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

private theorem oddUnit_pair (r : ℕ) :
    oddUnit r ^ r + oddUnit r ^ (r + 1) =
      ((-2 * Real.cos (Real.pi / (2 * r + 1 : ℕ)) : ℝ) : ℂ) := by
  have hreal : (oddUnit r ^ r).re = -Real.cos (Real.pi / (2 * r + 1 : ℕ)) := by
    unfold oddUnit
    rw [← Complex.exp_nat_mul]
    have hangle : (r : ℝ) * (-(2 * Real.pi) / (2 * r + 1 : ℕ)) =
        -(Real.pi - Real.pi / (2 * r + 1 : ℕ)) := by
      have hq : ((2 * r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp [hq]
      push_cast
      ring
    have he : (r : ℂ) * (-(2 * (Real.pi : ℂ)) * I / (2 * r + 1 : ℕ)) =
        (((-(Real.pi - Real.pi / (2 * r + 1 : ℕ)) : ℝ) : ℂ) * I) := by
      calc
        _ = (((r : ℝ) * (-(2 * Real.pi) / (2 * r + 1 : ℕ)) : ℝ) : ℂ) * I := by
          push_cast
          ring
        _ = _ := by rw [hangle]
    rw [he, Complex.exp_ofReal_mul_I_re, Real.cos_neg, Real.cos_pi_sub]
  have hunit : conj (oddUnit r ^ r) * oddUnit r ^ r = 1 := by
    rw [Complex.conj_mul', norm_pow, oddUnit_norm, one_pow]
    norm_num
  have hpow : oddUnit r ^ (r + 1) * oddUnit r ^ r = 1 := by
    rw [← pow_add, show r + 1 + r = 2 * r + 1 by omega, oddUnit_pow_order]
  have hn : oddUnit r ^ r ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  have hc : oddUnit r ^ (r + 1) = conj (oddUnit r ^ r) :=
    mul_right_cancel₀ hn (hpow.trans hunit.symm)
  rw [hc]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.conj_re, hreal, Complex.ofReal_re]
    ring
  · simp only [Complex.add_im, Complex.conj_im, add_neg_cancel, Complex.ofReal_im]

private theorem oddUnit_pair_last (r : ℕ) :
    (oddUnit r ^ (2 * r)) ^ r + (oddUnit r ^ (2 * r)) ^ (r + 1) =
      ((-2 * Real.cos (Real.pi / (2 * r + 1 : ℕ)) : ℝ) : ℂ) := by
  have hu : conj (oddUnit r) * oddUnit r = 1 := by
    rw [Complex.conj_mul', oddUnit_norm]
    norm_num
  have hp : oddUnit r ^ (2 * r) * oddUnit r = 1 := by
    rw [← pow_succ, oddUnit_pow_order]
  have hc : oddUnit r ^ (2 * r) = conj (oddUnit r) :=
    mul_right_cancel₀ (Complex.exp_ne_zero _) (hp.trans hu.symm)
  rw [hc, ← map_pow, ← map_pow, ← map_add, oddUnit_pair]
  rw [Complex.conj_ofReal]

private theorem scaledTwoMonomial_at_odd (β : ℝ) (r k : ℕ) :
    dirichletEval (harmonicPacketPoint β (harmonicPacketStep (2 * r)) k)
      (scaledTwoMonomial β) = oddUnit r ^ k := by
  rw [dirichletEval_scaledTwoMonomial]
  have htR : Real.log 2 * harmonicPacketStep (2 * r) =
      2 * Real.pi / (2 * r + 1 : ℕ) := by
    have hl := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    simp only [harmonicPacketStep, Nat.cast_add, Nat.cast_one]
    field_simp [hl]
  have ht := congrArg Complex.ofReal htR
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_ofNat] at ht
  have he : (Real.log 2 : ℂ) *
      ((β : ℂ) - harmonicPacketPoint β (harmonicPacketStep (2 * r)) k) =
        (k : ℂ) * (-(2 * (Real.pi : ℂ)) * I / (2 * r + 1 : ℕ)) := by
    calc
      _ = -(k : ℂ) * ((Real.log 2 : ℂ) * (harmonicPacketStep (2 * r) : ℂ)) * I := by
        unfold harmonicPacketPoint
        ring
      _ = _ := by rw [ht]; ring
  rw [he, Complex.exp_nat_mul]
  rfl

/-- The first and last nontrivial harmonics attain the prescribed accuracy. -/
theorem oddRelationAnnihilator_at_harmonic (β ε : ℝ) (r : ℕ) (hr : 1 ≤ r)
    (hε : ε ≤ 1) (k : ℕ) (hk : k = 1 ∨ k = 2 * r) :
    dirichletEval (harmonicPacketPoint β (harmonicPacketStep (2 * r)) k)
      (oddRelationAnnihilator β ε r) = (ε : ℂ) := by
  rw [oddRelationAnnihilator_eval β ε r hr hε, scaledTwoMonomial_at_odd]
  have hpair : (oddUnit r ^ k) ^ r + (oddUnit r ^ k) ^ (r + 1) =
      ((-2 * Real.cos (Real.pi / (2 * r + 1 : ℕ)) : ℝ) : ℂ) := by
    rcases hk with rfl | rfl
    · simpa only [pow_one] using oddUnit_pair r
    · exact oddUnit_pair_last r
  rw [hpair]
  have hc : (Real.cos (Real.pi / (2 * r + 1 : ℕ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (odd_cycle_cos_pos r hr).ne'
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_neg]
  field_simp [hc]; ring

private theorem eval_conjugate (P : MvPolynomial (Fin 2) ℝ≥0) (s : ℂ) :
    dirichletEval (conj s) P = conj (dirichletEval s P) := by
  simp only [dirichletEval_eq_frequency_sum, map_sum, map_mul, ← Complex.exp_conj,
    map_neg, Complex.conj_ofReal]

/-- Every odd relation length admits positive extremizers at every abscissa and accuracy. -/
theorem exists_sharp_odd_relation_accuracy {q : ℕ} [NeZero q] (hq : Odd q) (h3 : 3 ≤ q)
    (β ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ∃ (P : MvPolynomial (Fin 2) ℝ≥0) (γ : ZMod q → ℝ),
      MvPolynomial.constantCoeff P = 1 ∧ (∑ j, γ j = 0) ∧
      (∀ j, ‖dirichletEval (harmonicPacketPoint β (γ j) 1) P‖ = ε) ∧
      dirichletTailMass P β = (1 - ε) / Real.cos (Real.pi / q) := by
  obtain ⟨r, rfl⟩ := hq
  have hr : 1 ≤ r := by omega
  let t := harmonicPacketStep (2 * r)
  let γ : ZMod (2 * r + 1) → ℝ := fun j => if j = 0 then -((2 * r : ℕ) : ℝ) * t else t
  refine ⟨oddRelationAnnihilator β ε r, γ,
    oddRelationAnnihilator_constantCoeff β ε r hr, ?_, ?_,
    oddRelationAnnihilator_tail_mass β ε r hr hε1⟩
  · calc
      (∑ j, γ j) = ∑ j : ZMod (2 * r + 1),
          (t + if j = 0 then -(((2 * r + 1 : ℕ) : ℝ) * t) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = 0
        · simp only [γ, hj, ite_true, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
          ring
        · simp only [γ, hj, ite_false, add_zero]
      _ = 0 := by simp [Finset.sum_add_distrib]
  · intro j
    by_cases hj : j = 0
    · have hp : harmonicPacketPoint β (γ j) 1 =
          conj (harmonicPacketPoint β t (2 * r)) := by
        apply Complex.ext <;> simp [harmonicPacketPoint, γ, hj]
      rw [hp, eval_conjugate,
        oddRelationAnnihilator_at_harmonic β ε r hr hε1 (2 * r) (Or.inr rfl),
        Complex.conj_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε0]
    · change ‖dirichletEval (harmonicPacketPoint β (if j = 0 then _ else _) 1) _‖ = ε
      rw [if_neg hj,
        oddRelationAnnihilator_at_harmonic β ε r hr hε1 1 (Or.inl rfl),
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε0]

/-- The exact feasible mass threshold over all zero-sum lists of a fixed odd length. -/
theorem odd_relation_accuracy_frontier {q : ℕ} [NeZero q] (hq : Odd q) (h3 : 3 ≤ q)
    (β ε H : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∃ (P : MvPolynomial (Fin 2) ℝ≥0) (γ : ZMod q → ℝ),
      MvPolynomial.constantCoeff P = 1 ∧ (∑ j, γ j = 0) ∧
      (∀ j, ‖dirichletEval (harmonicPacketPoint β (γ j) 1) P‖ ≤ ε) ∧
      dirichletTailMass P β ≤ H) ↔ (1 - ε) / Real.cos (Real.pi / q) ≤ H := by
  have hc : 0 < Real.cos (Real.pi / q) := by
    obtain ⟨r, rfl⟩ := hq
    exact odd_cycle_cos_pos r (by omega)
  constructor
  · rintro ⟨P, γ, hP, hs, he, hH⟩
    have hm := odd_ordinate_relation_sharp_mass_bound hP hq h3 β ε γ hs he
    have hd : (1 - ε) / Real.cos (Real.pi / q) ≤ dirichletTailMass P β := by
      apply (div_le_iff₀ hc).mpr
      nlinarith only [hm]
    exact hd.trans hH
  · obtain ⟨P, γ, hP, hs, he, hmass⟩ := exists_sharp_odd_relation_accuracy hq h3 β ε hε0 hε1
    intro hH
    exact ⟨P, γ, hP, hs, fun j => (he j).le, hmass.le.trans hH⟩

#print axioms oddRelationAnnihilator_at_harmonic
#print axioms exists_sharp_odd_relation_accuracy
#print axioms odd_relation_accuracy_frontier

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

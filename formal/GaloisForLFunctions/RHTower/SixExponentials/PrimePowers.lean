import GaloisForLFunctions.RHTower.SixExponentials.Main

/-!
# Six exponentials at prime powers

For a nonreal `ρ` and three distinct primes `p, q, r`, the numbers `p^ρ, q^ρ, r^ρ` are not all
algebraic: apply the six exponentials theorem to `x = (1, ρ)` and `y = (log p, log q, log r)`.
The rational independence of `1, ρ` is the nonreality of `ρ`; that of the three logarithms is
the multiplicative independence of distinct primes.
-/

open Complex

namespace GaloisForLFunctions.RHTower.SixExponentials

/-- `exp(ρ · log p) = p^ρ` for a positive integer base. -/
theorem exp_mul_log_eq_cpow {p : ℕ} (hp : 0 < p) (ρ : ℂ) :
    Complex.exp (ρ * (Real.log p : ℂ)) = (p : ℂ) ^ ρ := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [Complex.cpow_def_of_ne_zero hp0, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (Nat.cast_nonneg p), mul_comm]

/-- `exp(log p) = p`. -/
theorem exp_log_nat {p : ℕ} (hp : 0 < p) : Complex.exp ((Real.log p : ℂ)) = (p : ℂ) := by
  rw [← Complex.ofReal_exp, Real.exp_log (by exact_mod_cast hp)]
  push_cast
  rfl

/-- Integer relations among the logarithms of three distinct primes are trivial. -/
theorem prime_logs_independent {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (m₀ m₁ m₂ : ℤ)
    (h : (m₀ : ℂ) * (Real.log p : ℂ) + (m₁ : ℂ) * (Real.log q : ℂ)
      + (m₂ : ℂ) * (Real.log r : ℂ) = 0) : m₀ = 0 ∧ m₁ = 0 ∧ m₂ = 0 := by
  have hreal : (m₀ : ℝ) * Real.log p + (m₁ : ℝ) * Real.log q + (m₂ : ℝ) * Real.log r = 0 := by
    have := congrArg Complex.re h
    simpa only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.zero_re] using this
  let P : Fin 3 → ℕ := ![p, q, r]
  have hPinj : Function.Injective P := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [P]
  have hPprime : ∀ i, (P i).Prime := by
    intro i
    fin_cases i <;> simp [P, hp, hq, hr]
  let c : Fin 3 → ℝ := ![(m₀ : ℝ), (m₁ : ℝ), (m₂ : ℝ)]
  have hcalg : ∀ i, IsAlgebraic ℤ (c i) := by
    intro i
    fin_cases i <;> simp [c] <;> exact isAlgebraic_int _
  have hprod : ∏ i, (P i : ℝ) ^ (c i) = 1 := by
    have hpos : ∀ i, (0 : ℝ) < (P i : ℝ) := fun i => by exact_mod_cast (hPprime i).pos
    have hexp : ∀ i, (P i : ℝ) ^ (c i) = Real.exp (c i * Real.log (P i)) := by
      intro i
      rw [Real.rpow_def_of_pos (hpos i), mul_comm]
    simp only [hexp]
    rw [← Real.exp_sum]
    rw [Fin.sum_univ_three]
    simp only [P, c, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    rw [hreal]
    exact Real.exp_zero
  have hzero := RHTower.baker_prime_mult_indep P hPinj hPprime c hcalg hprod
  refine ⟨?_, ?_, ?_⟩
  · have := hzero 0; simpa [c] using this
  · have := hzero 1; simpa [c] using this
  · have := hzero 2; simpa [c] using this

/-- **At most two of three distinct primes can have `p^ρ` algebraic for a nonreal `ρ`.** -/
theorem not_all_three_prime_cpow_isAlgebraic {ρ : ℂ} (hρ : ρ.im ≠ 0) {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ¬ (IsAlgebraic ℚ ((p : ℂ) ^ ρ) ∧ IsAlgebraic ℚ ((q : ℂ) ^ ρ) ∧ IsAlgebraic ℚ ((r : ℂ) ^ ρ)) := by
  rintro ⟨hap, haq, har⟩
  have hx : ∀ a b : ℤ, (a : ℂ) * 1 + (b : ℂ) * ρ = 0 → a = 0 ∧ b = 0 := by
    intro a b h
    have him := congrArg Complex.im h
    simp at him
    have hb : b = 0 := by
      rcases him with hb0 | him0
      · exact_mod_cast hb0
      · exact absurd him0 hρ
    subst hb
    simp at h
    exact ⟨by exact_mod_cast h, rfl⟩
  have hy := fun m₀ m₁ m₂ h => prime_logs_independent hp hq hr hpq hpr hqr m₀ m₁ m₂ h
  apply six_exponentials hx hy
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, one_mul, Fin.mk_one, Fin.isValue,
    Fin.reduceFinMk]
  · rw [exp_log_nat hp.pos]; exact isAlgebraic_nat p
  · rw [exp_log_nat hq.pos]; exact isAlgebraic_nat q
  · rw [exp_log_nat hr.pos]; exact isAlgebraic_nat r
  · rw [exp_mul_log_eq_cpow hp.pos]; exact hap
  · rw [exp_mul_log_eq_cpow hq.pos]; exact haq
  · rw [exp_mul_log_eq_cpow hr.pos]; exact har

end GaloisForLFunctions.RHTower.SixExponentials

import GaloisForLFunctions.HTGeometry.StateIndependenceFromSeparation

/-!
# The exponential tower separates growth

A growth separation asks, for every nonzero two-variable polynomial and every level, for a point at
which the polynomial in the coordinate and the inner state is bounded below while the outer state
outgrows any fixed multiple of the joint scale.  The exponential tower supplies one on the positive
real axis: there the polynomial in `(x, eˣ)` is dominated by a single monomial, so it is bounded
below by a constant, while `exp exp` grows like `eˣ` in logarithmic scale — beyond every multiple of
the joint scale, which is only linear in `x`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-! ## Ratios of monomials on the real axis -/

/-- A monomial that is smaller in the exponential-first order is negligible against the dominant
one. -/
theorem tendsto_monomialRatio_zero {p d b J : ℕ} (h : b < J ∨ (b = J ∧ p < d)) :
    Tendsto (fun x : ℝ => (x ^ p * Real.exp (b * x)) / (x ^ d * Real.exp (J * x)))
      atTop (𝓝 0) := by
  rcases h with hb | ⟨hbJ, hpd⟩
  · refine squeeze_zero' ?_ ?_ (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero p)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
      positivity
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
      have hden : (0 : ℝ) < x ^ d * Real.exp (J * x) := by positivity
      rw [div_le_iff₀ hden]
      have hpow : x ^ p ≤ x ^ (p + d) := pow_le_pow_right₀ hx (Nat.le_add_right p d)
      have hbJ' : (b : ℝ) * x ≤ ((J : ℝ) - 1) * x := by
        have : (b : ℝ) ≤ (J : ℝ) - 1 := by
          have : (b : ℝ) + 1 ≤ (J : ℝ) := by exact_mod_cast hb
          linarith
        nlinarith
      have hexp : Real.exp ((b : ℝ) * x) ≤ Real.exp (((J : ℝ) - 1) * x) :=
        Real.exp_le_exp.mpr hbJ'
      have hrhs : x ^ p * Real.exp (-x) * (x ^ d * Real.exp ((J : ℝ) * x))
          = x ^ (p + d) * Real.exp (((J : ℝ) - 1) * x) := by
        rw [pow_add, show ((J : ℝ) - 1) * x = (J : ℝ) * x + (-x) by ring, Real.exp_add]
        ring
      rw [hrhs]
      exact mul_le_mul hpow hexp (Real.exp_pos _).le (by positivity)
  · subst hbJ
    refine squeeze_zero' ?_ ?_ (tendsto_inv_atTop_zero (𝕜 := ℝ))
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
      positivity
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
      have hE : (0 : ℝ) < Real.exp ((b : ℝ) * x) := Real.exp_pos _
      have hsimp : (x ^ p * Real.exp ((b : ℝ) * x)) / (x ^ d * Real.exp ((b : ℝ) * x))
          = x ^ p / x ^ d := by
        rw [mul_comm (x ^ p), mul_comm (x ^ d), mul_div_mul_left _ _ (ne_of_gt hE)]
      rw [hsimp, div_le_iff₀ (by positivity : (0 : ℝ) < x ^ d)]
      have hstep : x ^ p * x ≤ x ^ d := by
        have : x ^ (p + 1) ≤ x ^ d := pow_le_pow_right₀ hx hpd
        rwa [pow_succ] at this
      rw [inv_mul_eq_div, le_div_iff₀ hx0]
      exact hstep

/-! ## The dominant monomial -/

/-- Every nonzero two-variable polynomial has a monomial strictly dominant for the order that reads
the exponential exponent first. -/
theorem exists_dominant_monomial {A : MvPolynomial (Fin 2) ℂ} (hA : A ≠ 0) :
    ∃ m₀ ∈ A.support, ∀ m ∈ A.support, m ≠ m₀ → (m 1 < m₀ 1 ∨ (m 1 = m₀ 1 ∧ m 0 < m₀ 0)) := by
  classical
  have hne : A.support.Nonempty := MvPolynomial.support_nonempty.mpr hA
  obtain ⟨mJ, hmJ, hJ⟩ := A.support.exists_mem_eq_sup hne (fun m => m 1)
  set J : ℕ := A.support.sup (fun m => m 1) with hJdef
  set T : Finset (Fin 2 →₀ ℕ) := A.support.filter (fun m => m 1 = J) with hT
  have hTne : T.Nonempty := ⟨mJ, by rw [hT, Finset.mem_filter]; exact ⟨hmJ, hJ.symm⟩⟩
  obtain ⟨m₀, hm₀T, hd⟩ := T.exists_mem_eq_sup hTne (fun m => m 0)
  have hm₀ : m₀ ∈ A.support ∧ m₀ 1 = J := by
    rw [hT, Finset.mem_filter] at hm₀T
    exact hm₀T
  refine ⟨m₀, hm₀.1, ?_⟩
  intro m hm hne'
  have hmJle : m 1 ≤ J := by
    rw [hJdef]
    exact Finset.le_sup (f := fun m : Fin 2 →₀ ℕ => m 1) hm
  rcases lt_or_eq_of_le hmJle with hlt | heq
  · exact Or.inl (by rw [hm₀.2]; exact hlt)
  · have hmT : m ∈ T := by rw [hT, Finset.mem_filter]; exact ⟨hm, heq⟩
    have hm0le : m 0 ≤ m₀ 0 := by
      rw [← hd]
      exact Finset.le_sup (f := fun m : Fin 2 →₀ ℕ => m 0) hmT
    rcases lt_or_eq_of_le hm0le with hlt0 | heq0
    · exact Or.inr ⟨by rw [hm₀.2]; exact heq, hlt0⟩
    · exfalso
      refine hne' (Finsupp.ext fun a => ?_)
      fin_cases a
      · show m 0 = m₀ 0
        exact heq0
      · show m 1 = m₀ 1
        rw [heq, hm₀.2]


/-! ## The polynomial in `(x, eˣ)` is bounded below -/

/-- **A nonzero two-variable polynomial in the coordinate and the exponential is eventually bounded
away from zero on the positive real axis.**  Its dominant monomial outgrows every other one. -/
theorem exists_eventually_norm_eval_exp_ge {A : MvPolynomial (Fin 2) ℂ} (hA : A ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ x : ℝ in atTop,
      ε ≤ ‖MvPolynomial.eval ![(x : ℂ), Complex.exp (x : ℂ)] A‖ := by
  classical
  obtain ⟨m₀, hm₀, hdom⟩ := exists_dominant_monomial hA
  set a : ℂ := MvPolynomial.coeff m₀ A with ha
  have hane : a ≠ 0 := by
    rw [ha]
    exact MvPolynomial.mem_support_iff.mp hm₀
  set g : ℝ → ℝ := fun x => x ^ (m₀ 0) * Real.exp ((m₀ 1 : ℝ) * x) with hg
  have hgpos : ∀ x : ℝ, 0 < x → 0 < g x := by
    intro x hx
    rw [hg]
    positivity
  have hexpand : ∀ x : ℝ, 0 < x →
      MvPolynomial.eval ![(x : ℂ), Complex.exp (x : ℂ)] A
        = (((g x : ℝ) : ℂ)) *
            ∑ m ∈ A.support, MvPolynomial.coeff m A *
              (((x ^ (m 0) * Real.exp ((m 1 : ℝ) * x)) / g x : ℝ) : ℂ) := by
    intro x hx
    rw [MvPolynomial.eval_eq', Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hpow : (Complex.exp (x : ℂ)) ^ (m 1) = ((Real.exp ((m 1 : ℝ) * x) : ℝ) : ℂ) := by
      rw [Real.exp_nat_mul, Complex.ofReal_pow, Complex.ofReal_exp]
    have hx0 : (g x) ≠ 0 := ne_of_gt (hgpos x hx)
    have hxC : ((g x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0
    rw [hpow]
    push_cast
    field_simp
  have hterm : ∀ m ∈ A.support,
      Tendsto (fun x : ℝ => MvPolynomial.coeff m A *
        (((x ^ (m 0) * Real.exp ((m 1 : ℝ) * x)) / g x : ℝ) : ℂ))
        atTop (𝓝 (if m = m₀ then a else 0)) := by
    intro m hm
    by_cases hmm : m = m₀
    · subst hmm
      have hone : ∀ᶠ x : ℝ in atTop,
          ((x ^ (m 0) * Real.exp ((m 1 : ℝ) * x)) / g x : ℝ) = 1 := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        rw [hg]
        exact div_self (ne_of_gt (hgpos x hx))
      rw [if_pos (rfl : m = m)]
      refine Tendsto.congr' ?_ (tendsto_const_nhds (x := a))
      filter_upwards [hone] with x hx
      rw [hx]
      simp [ha]
    · simp only [if_neg hmm]
      have hratio := tendsto_monomialRatio_zero (p := m 0) (d := m₀ 0) (b := m 1) (J := m₀ 1)
        (hdom m hm hmm)
      have hcast : Tendsto (fun x : ℝ =>
          (((x ^ (m 0) * Real.exp ((m 1 : ℝ) * x)) / g x : ℝ) : ℂ)) atTop (𝓝 0) := by
        have := (Complex.continuous_ofReal.tendsto 0).comp hratio
        simpa [Function.comp_def, hg] using this
      simpa using hcast.const_mul (MvPolynomial.coeff m A)
  have hsum : Tendsto (fun x : ℝ => ∑ m ∈ A.support, MvPolynomial.coeff m A *
      (((x ^ (m 0) * Real.exp ((m 1 : ℝ) * x)) / g x : ℝ) : ℂ)) atTop (𝓝 a) := by
    have := tendsto_finsetSum A.support hterm
    have hval : ∑ m ∈ A.support, (if m = m₀ then a else 0) = a := by
      rw [Finset.sum_ite_eq' A.support m₀ (fun _ => a)]
      simp [hm₀]
    rwa [hval] at this
  refine ⟨‖a‖ / 2, by positivity, ?_⟩
  have hnorm : Tendsto (fun x : ℝ => ‖∑ m ∈ A.support, MvPolynomial.coeff m A *
      (((x ^ (m 0) * Real.exp ((m 1 : ℝ) * x)) / g x : ℝ) : ℂ)‖) atTop (𝓝 ‖a‖) := hsum.norm
  have hhalf : ∀ᶠ x : ℝ in atTop, ‖a‖ / 2 ≤ ‖∑ m ∈ A.support, MvPolynomial.coeff m A *
      (((x ^ (m 0) * Real.exp ((m 1 : ℝ) * x)) / g x : ℝ) : ℂ)‖ := by
    have hlt : ‖a‖ / 2 < ‖a‖ := by
      have : 0 < ‖a‖ := norm_pos_iff.mpr hane
      linarith
    exact hnorm.eventually (eventually_ge_nhds hlt)
  filter_upwards [hhalf, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
  have hgge : (1 : ℝ) ≤ g x := by
    rw [hg]
    have h1 : (1 : ℝ) ≤ x ^ (m₀ 0) := one_le_pow₀ hx1
    have h2 : (1 : ℝ) ≤ Real.exp ((m₀ 1 : ℝ) * x) := by
      rw [Real.one_le_exp_iff]
      positivity
    nlinarith
  rw [hexpand x hx0, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hgpos x hx0)]
  nlinarith [hx, hgge, norm_nonneg (∑ m ∈ A.support, MvPolynomial.coeff m A *
      (((x ^ (m 0) * Real.exp ((m 1 : ℝ) * x)) / g x : ℝ) : ℂ))]


/-! ## The separation -/

theorem posLog_apply (y : ℝ) : Real.posLog y = max 0 (Real.log y) := by
  rw [Real.posLog_def]
  rfl

theorem posLog_le_self_exponentialTowerGrowthSeparation {x : ℝ} (hx : 1 ≤ x) : Real.posLog x ≤ x := by
  rw [posLog_apply]
  refine max_le (by linarith) (Real.log_le_self (by linarith))

theorem posLog_exp {x : ℝ} (hx : 0 ≤ x) : Real.posLog (Real.exp x) = x := by
  rw [posLog_apply, Real.log_exp]
  exact max_eq_right hx

theorem norm_exp_ofReal (x : ℝ) : ‖Complex.exp ((x : ℝ) : ℂ)‖ = Real.exp x := by
  rw [Complex.norm_exp, Complex.ofReal_re]

/-- **The exponential tower separates growth.**  Along the positive real axis the polynomial in the
coordinate and `exp` is bounded below by a constant, the joint scale grows linearly, and the outer
state's logarithmic size is `eˣ`. -/
theorem growthSeparation_exp_expExp :
    GrowthSeparation Complex.exp (fun z => Complex.exp (Complex.exp z)) := by
  intro A hA c hc
  obtain ⟨ε, hε, hev⟩ := exists_eventually_norm_eval_exp_ge hA
  set K : ℝ := Real.posLog ε⁻¹ with hK
  have hK0 : 0 ≤ K := by
    rw [hK, posLog_apply]
    exact le_max_left _ _
  set B : ℝ := c * (1 + K) + 2 * c with hB
  have hB0 : 0 ≤ B := by
    rw [hB]
    positivity
  have hgrow : ∀ᶠ x : ℝ in atTop, B + 1 < Real.exp x / x ^ 1 :=
    (Real.tendsto_exp_div_pow_atTop 1).eventually_gt_atTop (B + 1)
  obtain ⟨x, ⟨hxbound, hxgrow⟩, hx1⟩ :=
    ((hev.and hgrow).and (eventually_ge_atTop (1 : ℝ))).exists
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
  refine ⟨(x : ℂ), ε, hε, hxbound, ?_⟩
  have hz : ‖((x : ℝ) : ℂ)‖ = x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
  have hF1 : ‖Complex.exp ((x : ℝ) : ℂ)‖ = Real.exp x := norm_exp_ofReal x
  have hF2 : ‖Complex.exp (Complex.exp ((x : ℝ) : ℂ))‖ = Real.exp (Real.exp x) := by
    rw [Complex.norm_exp, ← Complex.ofReal_exp, Complex.ofReal_re]
  rw [hz, hF1, hF2, posLog_exp (le_of_lt (Real.exp_pos x)),
    posLog_exp hx0.le]
  have hlogx : Real.posLog x ≤ x := posLog_le_self_exponentialTowerGrowthSeparation hx1
  have hlin : c * (1 + Real.posLog x + x + K) ≤ B * x := by
    have h2 : c * (1 + Real.posLog x + x + K) ≤ c * (1 + x + x + K) := by
      have := mul_le_mul_of_nonneg_left hlogx hc
      linarith
    have h3 : c * (1 + x + x + K) ≤ B * x := by
      rw [hB]
      have hcK : (0 : ℝ) ≤ c * (1 + K) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hx1 hcK
      rw [mul_one] at hmul
      nlinarith [hmul, hc, hx1]
    linarith
  have hexp : B * x < Real.exp x := by
    rw [pow_one] at hxgrow
    have h := (lt_div_iff₀ hx0).mp hxgrow
    nlinarith [h, hx0]
  linarith


/-- **State independence for the exponential tower.**  The coordinate, the exponential and the
double exponential satisfy no nonzero polynomial relation. -/
theorem not_three_var_relation_exp_expExp (P : MvPolynomial (Fin 3) ℂ) (hP : P ≠ 0) :
    ¬ (∀ z : ℂ,
        MvPolynomial.eval ![z, Complex.exp z, Complex.exp (Complex.exp z)] P = 0) :=
  not_three_var_relation_of_growthSeparation transcendentalEntire_exp
    growthSeparation_exp_expExp P hP

end GaloisForLFunctions.HTGeometry

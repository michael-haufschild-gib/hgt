import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseLocalPolynomialSeries

/-!
# Canonical coprime endpoints do not detect local polynomial variance

The same literal coefficient sequence has canonical coprime ratios for every
modulus and positive period variance whenever its normalized local polynomial
is nonconstant. This is a model classification, not a full-positive source.
-/

open Complex Polynomial Finset Filter Topology
noncomputable section
namespace RHTower.WeilSingularArithmetic

theorem continuous_localModelFactor {p : ℕ} (hp : p ≠ 0) (P : Polynomial ℝ) :
    Continuous (localModelFactor p P) := by
  unfold localModelFactor
  apply continuous_finsetSum
  intro j _
  haveI : NeZero (((p ^ j : ℕ) : ℂ)) := ⟨by exact_mod_cast pow_ne_zero j hp⟩
  exact continuous_const.mul ((continuous_const_cpow _).comp continuous_id.neg)

theorem localModelFactor_one (p : ℕ) (P : Polynomial ℝ) :
    localModelFactor p P 1 = ((P.eval (p : ℝ)⁻¹ : ℝ) : ℂ) := by
  rw [localModelFactor, Polynomial.eval_eq_sum_range]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_inv, Complex.ofReal_natCast, Complex.cpow_neg_one, Nat.cast_pow, inv_pow]

theorem tendsto_localModelFactor_one {p : ℕ} (hp : p ≠ 0) (P : Polynomial ℝ) :
    Tendsto (fun s : ℝ => localModelFactor p P (s : ℂ)) (𝓝[>] 1)
      (𝓝 ((P.eval (p : ℝ)⁻¹ : ℝ) : ℂ)) := by
  rw [← localModelFactor_one]
  exact (continuous_localModelFactor hp P).continuousAt.tendsto.comp
    (tendsto_ofReal_nhdsWithin_ne_one.mono_right nhdsWithin_le_nhds)

private theorem localModel_canonical_density (Q : ℕ) [NeZero Q] :
    (∏ q ∈ Q.primeFactors, (1 - (q : ℂ)⁻¹)) = (Q.totient : ℂ) / Q := by
  have h := congrArg (fun x : ℚ => (x : ℂ)) (Nat.totient_eq_mul_prod_factors Q)
  push_cast at h
  exact (eq_div_iff (by exact_mod_cast (NeZero.ne Q) : (Q : ℂ) ≠ 0)).mpr
    (by simpa only [mul_comm] using h.symm)

/-- Every coprime deletion has the canonical ratio, for this actual model sequence. -/
theorem localModel_coprime_ratio_limit {p : ℕ} (hp : p ≠ 0)
    (P : Polynomial ℝ) (h0 : P.eval 0 = 1) (h1 : P.eval (p : ℝ)⁻¹ = 1)
    (Q : ℕ) [NeZero Q] :
    Tendsto (fun s : ℝ =>
      LSeries (coprimePart Q (localModelForwardCoeff p P)) (s : ℂ) /
        LSeries (localModelForwardCoeff p P) (s : ℂ))
      (𝓝[>] 1) (𝓝 ((Q.totient : ℂ) / Q)) := by
  have hF : Tendsto (fun s : ℝ => localModelFactor p P (s : ℂ))
      (𝓝[>] 1) (𝓝 1) := by simpa only [h1, Complex.ofReal_one] using tendsto_localModelFactor_one hp P
  have hc0 : (P.coeff 0 : ℂ) = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, h0, Complex.ofReal_one]
  have hG : Tendsto (fun s : ℝ =>
      if p.Coprime Q then localModelFactor p P (s : ℂ) else (P.coeff 0 : ℂ))
      (𝓝[>] 1) (𝓝 1) := by
    by_cases h : p.Coprime Q
    · simpa only [if_pos h] using hF
    · simp only [if_neg h, hc0]
      exact tendsto_const_nhds
  have hz := riemannZeta_residue_one.comp tendsto_ofReal_nhdsWithin_ne_one
  have hq := (DirichletCharacter.LFunctionTrivChar_residue_one (N := Q)).comp
    tendsto_ofReal_nhdsWithin_ne_one
  have ht := (hG.mul hq).div (hF.mul hz) (by simp : (1 : ℂ) * 1 ≠ 0)
  simp only [one_mul, div_one, Function.comp_def, localModel_canonical_density] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : 1 < s := hs
  have hn : (s : ℂ) - 1 ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr hs1.ne')
  rw [LSeries_coprimePart_localModelForwardCoeff hp Q P hs1,
    LSeries_localModelForwardCoeff hp P hs1]
  simp only [Pi.div_apply]
  convert mul_div_mul_left
    ((if p.Coprime Q then localModelFactor p P (s : ℂ) else (P.coeff 0 : ℂ)) *
      DirichletCharacter.LFunctionTrivChar Q (s : ℂ))
    (localModelFactor p P (s : ℂ) * riemannZeta (s : ℂ)) hn using 1
  ring

/-- The literal complex coefficient variance equals the finite-period real formula. -/
theorem localModel_period_variance {p : ℕ} (hp : p ≠ 0) (P : Polynomial ℝ)
    (h1 : P.eval (p : ℝ)⁻¹ = 1) :
    (∑ n ∈ Ioc 0 (p ^ P.natDegree), ‖localModelForwardCoeff p P n - 1‖ ^ 2) /
      (p : ℝ) ^ P.natDegree = localPolynomialPeriodVariance p P := by
  unfold localPolynomialPeriodVariance localPolynomialPeriodAverage
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Ioc.mp hn).1
  rw [localModelForwardCoeff_eq_periodic hp P hn0, h1,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- An unconditional family of model sequences invisible to every coprime endpoint,
yet detected by their positive literal period variance. -/
theorem exists_localModel_coprime_invisible_variance (p : ℕ) (hp : 1 < p) :
    ∃ P : Polynomial ℝ, P.eval 0 = 1 ∧ P.eval (p : ℝ)⁻¹ = 1 ∧ P ≠ 1 ∧
      0 < (∑ n ∈ Ioc 0 (p ^ P.natDegree), ‖localModelForwardCoeff p P n - 1‖ ^ 2) /
        (p : ℝ) ^ P.natDegree ∧
      ∀ Q : ℕ, Q ≠ 0 → Tendsto (fun s : ℝ =>
        LSeries (coprimePart Q (localModelForwardCoeff p P)) (s : ℂ) /
          LSeries (localModelForwardCoeff p P) (s : ℂ))
        (𝓝[>] 1) (𝓝 ((Q.totient : ℂ) / Q)) := by
  let r : ℝ := (p : ℝ)⁻¹
  have hr : 0 < r := inv_pos.mpr (by exact_mod_cast lt_trans Nat.zero_lt_one hp)
  let P : Polynomial ℝ := 1 + X * (X - C r)
  have h0 : P.eval 0 = 1 := by simp [P]
  have h1 : P.eval (p : ℝ)⁻¹ = 1 := by simp [P, r]
  have hP : P ≠ 1 := by
    intro he
    have h := congrArg (fun A : Polynomial ℝ => A.eval (r + 1)) he
    simp only [P, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C] at h
    nlinarith
  have hp0 : p ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one hp)
  refine ⟨P, h0, h1, hP, ?_, fun Q hQ => ?_⟩
  · rw [localModel_period_variance hp0 P h1]
    exact localPolynomial_period_variance_pos p hp P h0 hP
  · haveI : NeZero Q := ⟨hQ⟩
    exact localModel_coprime_ratio_limit hp0 P h0 h1 Q

end RHTower.WeilSingularArithmetic

import GaloisForLFunctions.HTGeometry.StrelitzHeatJetGrowth

/-!
# Isolation of the highest independent-variable face

The retained-`z` polynomial has degree at most the largest degree of the original polynomial
coefficients.  After division by its highest power of `|z|`, every lower coefficient is multiplied
by at least `exp(-x)`.  The heat-specific logarithmic bounds on `(u,v)` make those finite
coefficient evaluations polynomial in `x`, hence negligible.  Therefore the fixed nonzero highest
`z`-face itself tends to zero along the Wiman sequence.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter

/-- Coefficient faces above the largest independent-variable degree vanish. -/
theorem strelitzBaseCoefficient_eq_zero_of_polynomialMvCoeffDegree_lt
    (Q : MvPolynomial (Fin 2) (Polynomial ℂ)) {k : ℕ}
    (hk : polynomialMvCoeffDegree Q < k) :
    strelitzBaseCoefficient Q k = 0 := by
  classical
  ext e
  rw [coeff_strelitzBaseCoefficient]
  simp only [MvPolynomial.coeff_zero]
  by_cases he : e ∈ Q.support
  · rw [if_pos he, Polynomial.coeff_eq_zero_of_natDegree_lt]
    exact lt_of_le_of_lt (polynomialMvCoeffDegree_le Q he) hk
  · rw [if_neg he]

/-- Jet specialization cannot increase the independent-variable degree. -/
theorem natDegree_strelitzBaseSpecialization_le
    (Q : MvPolynomial (Fin 2) (Polynomial ℂ)) (x : Fin 2 → ℂ) :
    (strelitzBaseSpecialization Q x).natDegree ≤ polynomialMvCoeffDegree Q := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_strelitzBaseSpecialization,
    strelitzBaseCoefficient_eq_zero_of_polynomialMvCoeffDegree_lt Q hk]
  simp

/-- A polynomial's highest permitted coefficient, times the corresponding radial power, is
bounded by the value plus all lower coefficient monomials. -/
theorem norm_coeff_mul_norm_pow_le_eval_add_sum
    (p : Polynomial ℂ) (z : ℂ) (D : ℕ) (hdeg : p.natDegree ≤ D) :
    ‖p.coeff D‖ * ‖z‖ ^ D ≤
      ‖p.eval z‖ + ∑ k ∈ Finset.range D, ‖p.coeff k‖ * ‖z‖ ^ k := by
  have hp := Polynomial.as_sum_range' p (D + 1) (Nat.lt_succ_iff.mpr hdeg)
  have heval := congrArg (Polynomial.eval z) hp
  rw [Polynomial.eval_finsetSum, Finset.sum_range_succ] at heval
  simp only [Polynomial.eval_monomial] at heval
  have hterm : p.coeff D * z ^ D =
      p.eval z - ∑ k ∈ Finset.range D, p.coeff k * z ^ k := by
    rw [heval]
    ring
  calc
    ‖p.coeff D‖ * ‖z‖ ^ D = ‖p.coeff D * z ^ D‖ := by rw [norm_mul, norm_pow]
    _ = ‖p.eval z - ∑ k ∈ Finset.range D, p.coeff k * z ^ k‖ := by rw [hterm]
    _ ≤ ‖p.eval z‖ + ‖∑ k ∈ Finset.range D, p.coeff k * z ^ k‖ := norm_sub_le _ _
    _ ≤ ‖p.eval z‖ + ∑ k ∈ Finset.range D, ‖p.coeff k‖ * ‖z‖ ^ k := by
      gcongr
      refine (norm_sum_le _ _).trans ?_
      exact Finset.sum_le_sum fun k _ => by rw [norm_mul, norm_pow]

/-- Beyond the unit circle, the highest permitted coefficient is bounded by the polynomial value
plus the lower coefficient mass divided by the radius. -/
theorem norm_coeff_succ_le_eval_add_sum_div
    (p : Polynomial ℂ) (z : ℂ) (d : ℕ) (hdeg : p.natDegree ≤ d + 1)
    (hz : 1 ≤ ‖z‖) :
    ‖p.coeff (d + 1)‖ ≤
      ‖p.eval z‖ + (∑ k ∈ Finset.range (d + 1), ‖p.coeff k‖) / ‖z‖ := by
  set r : ℝ := ‖z‖ with hr
  set A : ℝ := ∑ k ∈ Finset.range (d + 1), ‖p.coeff k‖ with hA
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hz
  have hrpow : 1 ≤ r ^ (d + 1) := one_le_pow₀ hz
  have hlead := norm_coeff_mul_norm_pow_le_eval_add_sum p z (d + 1) hdeg
  rw [← hr] at hlead
  have hsum : ∑ k ∈ Finset.range (d + 1), ‖p.coeff k‖ * r ^ k ≤ A * r ^ d := by
    rw [hA, Finset.sum_mul]
    refine Finset.sum_le_sum ?_
    intro k hk
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hz (Nat.le_of_lt_succ (Finset.mem_range.mp hk))) (norm_nonneg _)
  have hmain : ‖p.coeff (d + 1)‖ * r ^ (d + 1) ≤
      (‖p.eval z‖ + A / r) * r ^ (d + 1) := by
    calc
      ‖p.coeff (d + 1)‖ * r ^ (d + 1)
          ≤ ‖p.eval z‖ + ∑ k ∈ Finset.range (d + 1), ‖p.coeff k‖ * r ^ k := hlead
      _ ≤ ‖p.eval z‖ * r ^ (d + 1) + A * r ^ d := by
        gcongr
        exact le_mul_of_one_le_right (norm_nonneg _) hrpow
      _ = (‖p.eval z‖ + A / r) * r ^ (d + 1) := by
        rw [pow_succ]
        field_simp
  nlinarith [pow_pos hrpos (d + 1)]

/-- A fixed bivariate polynomial evaluated at heat-scale logarithmic jets is killed by one factor
of `exp(-x)`. -/
theorem tendsto_norm_eval_mul_exp_neg_of_strelitzJetBounds
    (S : MvPolynomial (Fin 2) ℂ) {x : ℕ → ℝ} {u v : ℕ → ℂ}
    (hxTop : Tendsto x atTop atTop)
    (hjets : ∀ᶠ n : ℕ in atTop, ‖u n‖ ≤ 2 * x n ∧ ‖v n‖ ≤ (x n) ^ 2) :
    Tendsto (fun n => ‖MvPolynomial.eval ![u n, v n] S‖ * Real.exp (-(x n)))
      atTop (nhds 0) := by
  set C : ℝ := mvCoeffNormSum S
  set d : ℕ := S.totalDegree
  have hmodel : Tendsto (fun y : ℝ =>
      (C * 3 ^ (2 * d)) * (y ^ (4 * d) * Real.exp (-y))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := C * 3 ^ (2 * d))).mul
        (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (4 * d))
  have hcomp := hmodel.comp hxTop
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => mul_nonneg (norm_nonneg _)
    (Real.exp_pos _).le) ?_ hcomp
  filter_upwards [hjets, hxTop.eventually_ge_atTop 1] with n hn hxn
  have hx0 : 0 ≤ x n := le_trans zero_le_one hxn
  have hu3 : 1 + ‖u n‖ ≤ 3 * (x n) ^ 2 := by
    have hx_sq : x n ≤ (x n) ^ 2 := by nlinarith [sq_nonneg (x n - 1)]
    linarith [hn.1]
  have hv3 : 1 + ‖v n‖ ≤ 3 * (x n) ^ 2 := by
    have hone : (1 : ℝ) ≤ (x n) ^ 2 := by nlinarith [sq_nonneg (x n - 1)]
    linarith [hn.2]
  have hbound := norm_eval_le_mvCoeffNormSum S (u n) (v n)
  change ‖MvPolynomial.eval ![u n, v n] S‖ ≤
    C * (1 + ‖u n‖) ^ d * (1 + ‖v n‖) ^ d at hbound
  have hpoly : C * (1 + ‖u n‖) ^ d * (1 + ‖v n‖) ^ d ≤
      C * (3 * (x n) ^ 2) ^ d * (3 * (x n) ^ 2) ^ d := by
    have hC : 0 ≤ C := mvCoeffNormSum_nonneg S
    have huPow := pow_le_pow_left₀ (by positivity) hu3 d
    have hvPow := pow_le_pow_left₀ (by positivity) hv3 d
    exact mul_le_mul (mul_le_mul_of_nonneg_left huPow hC) hvPow
      (pow_nonneg (by positivity) d)
      (mul_nonneg hC (pow_nonneg (by positivity) d))
  calc
    ‖MvPolynomial.eval ![u n, v n] S‖ * Real.exp (-(x n))
        ≤ (C * (1 + ‖u n‖) ^ d * (1 + ‖v n‖) ^ d) * Real.exp (-(x n)) := by
          exact mul_le_mul_of_nonneg_right hbound (Real.exp_pos _).le
    _ ≤ (C * (3 * (x n) ^ 2) ^ d * (3 * (x n) ^ 2) ^ d) *
          Real.exp (-(x n)) := by
          exact mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ = (C * 3 ^ (2 * d)) * ((x n) ^ (4 * d) * Real.exp (-(x n))) := by
          rw [mul_pow]
          have hthree : (3 : ℝ) ^ (2 * d) = 3 ^ d * 3 ^ d := by
            rw [← pow_add]
            congr 1
            omega
          have hxpow : ((x n) ^ 2) ^ d * ((x n) ^ 2) ^ d =
              (x n) ^ (4 * d) := by
            rw [← pow_mul, ← pow_add]
            congr 1
            omega
          rw [hthree, ← hxpow]
          ring

/-- The nonzero highest `z`-coefficient face tends to zero along any sequence where the two jet
variables have the heat-scale logarithmic bounds and the full retained-`z` polynomial tends to
zero. -/
theorem tendsto_strelitzBaseLeadingFace_zero
    (Q : MvPolynomial (Fin 2) (Polynomial ℂ))
    {x : ℕ → ℝ} {z u v : ℕ → ℂ}
    (hxTop : Tendsto x atTop atTop)
    (hz : ∀ n, ‖z n‖ = Real.exp (x n))
    (hjets : ∀ᶠ n : ℕ in atTop, ‖u n‖ ≤ 2 * x n ∧ ‖v n‖ ≤ (x n) ^ 2)
    (hsmall : Tendsto (fun n =>
      ‖(strelitzBaseSpecialization Q ![u n, v n]).eval (z n)‖) atTop (nhds 0)) :
    Tendsto (fun n =>
      ‖MvPolynomial.eval ![u n, v n]
        (strelitzBaseCoefficient Q (polynomialMvCoeffDegree Q))‖) atTop (nhds 0) := by
  cases hD : polynomialMvCoeffDegree Q with
  | zero =>
      refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ hsmall
      filter_upwards with n
      have hlead := norm_coeff_mul_norm_pow_le_eval_add_sum
        (strelitzBaseSpecialization Q ![u n, v n]) (z n) 0
        (by
          have hle := natDegree_strelitzBaseSpecialization_le Q ![u n, v n]
          rw [hD] at hle
          exact hle)
      rw [pow_zero, mul_one, Finset.range_zero, Finset.sum_empty, add_zero,
        coeff_strelitzBaseSpecialization] at hlead
      exact hlead
  | succ d =>
      have hEval : Tendsto (fun n =>
          ‖(strelitzBaseSpecialization Q ![u n, v n]).eval (z n)‖) atTop (nhds 0) :=
        hsmall
      have hterms : ∀ k ∈ Finset.range (d + 1), Tendsto (fun n =>
          ‖MvPolynomial.eval ![u n, v n] (strelitzBaseCoefficient Q k)‖ *
            Real.exp (-(x n))) atTop (nhds 0) := by
        intro k hk
        exact tendsto_norm_eval_mul_exp_neg_of_strelitzJetBounds
          (strelitzBaseCoefficient Q k) hxTop hjets
      have hsum : Tendsto (fun n => ∑ k ∈ Finset.range (d + 1),
          ‖MvPolynomial.eval ![u n, v n] (strelitzBaseCoefficient Q k)‖ *
            Real.exp (-(x n))) atTop (nhds 0) := by
        simpa using tendsto_finsetSum (Finset.range (d + 1)) hterms
      have hupper : ∀ᶠ n : ℕ in atTop,
          ‖MvPolynomial.eval ![u n, v n]
              (strelitzBaseCoefficient Q (d + 1))‖ ≤
            ‖(strelitzBaseSpecialization Q ![u n, v n]).eval (z n)‖ +
              ∑ k ∈ Finset.range (d + 1),
                ‖MvPolynomial.eval ![u n, v n] (strelitzBaseCoefficient Q k)‖ *
                  Real.exp (-(x n)) := by
        filter_upwards [hxTop.eventually_ge_atTop 0] with n hxn
        have hdeg : (strelitzBaseSpecialization Q ![u n, v n]).natDegree ≤ d + 1 := by
          have hle := natDegree_strelitzBaseSpecialization_le Q ![u n, v n]
          rw [hD] at hle
          exact hle
        have h := norm_coeff_succ_le_eval_add_sum_div
          (strelitzBaseSpecialization Q ![u n, v n]) (z n) d hdeg
          (by rw [hz n]; exact Real.one_le_exp hxn)
        rw [coeff_strelitzBaseSpecialization, hz n, div_eq_mul_inv, ← Real.exp_neg,
          Finset.sum_mul] at h
        simpa only [coeff_strelitzBaseSpecialization] using h
      refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) hupper ?_
      simpa using hEval.add hsum

open GaloisForLFunctions

variable {a : ℕ → ℂ}

/-- **Highest-face analytic isolation retaining the full maximum-circle property.**
Any assumed order-two ADE for an infinite entire-heat
anchor produces a fixed nonzero complex polynomial in `(u,v)` whose values tend to zero along an
escaping Wiman sequence.  No independent-variable coefficient remains. -/
theorem exists_nonzero_strelitzBaseLeadingFace_tendsto_zero_of_order_two_entireHeat_isMaximumOnCircle
    (ha : EntireCoeffs a)
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ 2) * (n : ℂ) ^ 2 * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)))
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    (hDA : DifferentiallyAlgebraicOfOrder (coeffFun a) 2) :
    ∃ S : MvPolynomial (Fin 2) ℂ, S ≠ 0 ∧
      ∃ (x : ℕ → ℝ) (z : ℕ → ℂ),
        (∀ n : ℕ, (n : ℝ) ≤ x n) ∧
        (∀ n : ℕ, ‖z n‖ = Real.exp (x n)) ∧
        (∀ n : ℕ, maxTerm a (Real.exp (x n)) ≤ ‖coeffFun a (z n)‖) ∧
        (∀ n : ℕ, coeffFun a (z n) ≠ 0) ∧
        (∀ n : ℕ, ‖eulerLogDeriv (coeffFun a) (z n) -
            (centralIndex a (Real.exp (x n)) : ℂ)‖
          ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ)) ∧
        (∀ n : ℕ, ‖eulerLogDerivSecond (coeffFun a) (z n)‖
          ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ) ^ 2) ∧
        Tendsto x atTop atTop ∧
        Tendsto (fun n => (centralIndex a (Real.exp (x n)) : ℝ) / x n)
          atTop (nhds 0) ∧
        (∀ᶠ n : ℕ in atTop,
          (centralIndex a (Real.exp (x n)) : ℝ) ≤ x n ∧
          ‖eulerLogDeriv (coeffFun a) (z n)‖ ≤ 2 * x n ∧
          ‖eulerLogDerivSecond (coeffFun a) (z n)‖ ≤ (x n) ^ 2) ∧
        (Tendsto (fun n =>
          ‖MvPolynomial.eval
            ![eulerLogDeriv (coeffFun a) (z n),
              eulerLogDerivSecond (coeffFun a) (z n)] S‖) atTop (nhds 0)) ∧
        ∀ n : ℕ, ∀ w : ℂ, ‖w‖ = ‖z n‖ →
          ‖coeffFun a w‖ ≤ ‖coeffFun a (z n)‖ := by
  obtain ⟨P, hP, hface, x, z, hx, hz, hfloor, hfz, hu, hv,
    hxTop, hνx, hjets, hsmall, hmaxCircle⟩ :=
    exists_nonzero_strelitzBaseCoefficient_with_logarithmicJetBounds_of_order_two_entireHeat_isMaximumOnCircle
      ha hheat htrans hDA
  let u : ℕ → ℂ := fun n => eulerLogDeriv (coeffFun a) (z n)
  let v : ℕ → ℂ := fun n => eulerLogDerivSecond (coeffFun a) (z n)
  have hjets' : ∀ᶠ n : ℕ in atTop, ‖u n‖ ≤ 2 * x n ∧ ‖v n‖ ≤ (x n) ^ 2 := by
    exact hjets.mono fun n hn => ⟨hn.2.1, hn.2.2⟩
  have hfull : Tendsto (fun n =>
      ‖(strelitzBaseSpecialization P ![u n, v n]).eval (z n)‖) atTop (nhds 0) := by
    simpa [u, v] using hsmall 0
  have hfaceZero := tendsto_strelitzBaseLeadingFace_zero P hxTop hz hjets' hfull
  exact ⟨strelitzBaseCoefficient P (polynomialMvCoeffDegree P), hface,
    x, z, hx, hz, hfloor, hfz, hu, hv, hxTop, hνx, hjets,
    by simpa [u, v] using hfaceZero, hmaxCircle⟩

/-- **Highest-face analytic isolation.** Any assumed order-two ADE for an infinite entire-heat
anchor produces a fixed nonzero complex polynomial in `(u,v)` whose values tend to zero along an
escaping Wiman sequence.  No independent-variable coefficient remains. -/
theorem exists_nonzero_strelitzBaseLeadingFace_tendsto_zero_of_order_two_entireHeat
    (ha : EntireCoeffs a)
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ 2) * (n : ℂ) ^ 2 * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)))
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    (hDA : DifferentiallyAlgebraicOfOrder (coeffFun a) 2) :
    ∃ S : MvPolynomial (Fin 2) ℂ, S ≠ 0 ∧
      ∃ (x : ℕ → ℝ) (z : ℕ → ℂ),
        (∀ n : ℕ, (n : ℝ) ≤ x n) ∧
        (∀ n : ℕ, ‖z n‖ = Real.exp (x n)) ∧
        (∀ n : ℕ, maxTerm a (Real.exp (x n)) ≤ ‖coeffFun a (z n)‖) ∧
        (∀ n : ℕ, coeffFun a (z n) ≠ 0) ∧
        (∀ n : ℕ, ‖eulerLogDeriv (coeffFun a) (z n) -
            (centralIndex a (Real.exp (x n)) : ℂ)‖
          ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ)) ∧
        (∀ n : ℕ, ‖eulerLogDerivSecond (coeffFun a) (z n)‖
          ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ) ^ 2) ∧
        Tendsto x atTop atTop ∧
        Tendsto (fun n => (centralIndex a (Real.exp (x n)) : ℝ) / x n)
          atTop (nhds 0) ∧
        (∀ᶠ n : ℕ in atTop,
          (centralIndex a (Real.exp (x n)) : ℝ) ≤ x n ∧
          ‖eulerLogDeriv (coeffFun a) (z n)‖ ≤ 2 * x n ∧
          ‖eulerLogDerivSecond (coeffFun a) (z n)‖ ≤ (x n) ^ 2) ∧
        Tendsto (fun n =>
          ‖MvPolynomial.eval
            ![eulerLogDeriv (coeffFun a) (z n),
              eulerLogDerivSecond (coeffFun a) (z n)] S‖) atTop (nhds 0) := by
  obtain ⟨S, hS, x, z, hx, hz, hfloor, hfz, hu, hv,
    hxTop, hνx, hjets, hsmall, _⟩ :=
    exists_nonzero_strelitzBaseLeadingFace_tendsto_zero_of_order_two_entireHeat_isMaximumOnCircle
      ha hheat htrans hDA
  exact ⟨S, hS, x, z, hx, hz, hfloor, hfz, hu, hv,
    hxTop, hνx, hjets, hsmall⟩

end

end GaloisForLFunctions.HTGeometry

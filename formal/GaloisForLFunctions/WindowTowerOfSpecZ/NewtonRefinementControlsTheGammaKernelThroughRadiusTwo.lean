import GaloisForLFunctions.WindowTowerOfSpecZ.TheGammaKernelHasAFourteenthOrderPolynomialLowerBound

/-!
# Newton refinement of the Gamma lower kernel

For a denominator `U` and a polynomial upper bound `T`, the reciprocal
update `q(2−Tq)` has exact error `U(1/U−q)²+(T−U)q²`. Three updates of
the degree-fourteen lower polynomials retain a lower kernel and reduce
its error to `3/10¹⁷` throughout diameter two.
-/

noncomputable section
open Real
open _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.WeilLevyPoleGauss
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open ArithmeticCriticalityTheory BiScaleUncertainty

/-- Taylor upper polynomial for the normalized hyperbolic sine. -/
def gammaSinhDenominatorUpper (z : ℝ) : ℝ :=
  1 + z ^ 2 / 6 + z ^ 4 / 120 + z ^ 6 / 5040 + z ^ 8 / 362880 +
    z ^ 10 / 39916800 + z ^ 12 / 6227020800 + z ^ 14 / 1307674368000 +
    z ^ 16 / 355687428096000 + z ^ 18 / 100000000000000000

/-- Taylor upper polynomial for the hyperbolic cosine. -/
def gammaCoshDenominatorUpper (z : ℝ) : ℝ :=
  1 + z ^ 2 / 2 + z ^ 4 / 24 + z ^ 6 / 720 + z ^ 8 / 40320 +
    z ^ 10 / 3628800 + z ^ 12 / 479001600 + z ^ 14 / 87178291200 +
    z ^ 16 / 20922789888000 + z ^ 18 / 6402373705728000 +
    z ^ 19 / 100000000000000000

/-- A reciprocal update using an upper bound for the denominator. -/
def gammaReciprocalNewton (T q : ℝ) : ℝ := q * (2 - T * q)

private def newtonThree (T q : ℝ) : ℝ :=
  gammaReciprocalNewton T (gammaReciprocalNewton T (gammaReciprocalNewton T q))

/-- Three polynomial reciprocal updates for the normalized hyperbolic sine. -/
def gammaSinhPolynomialNewton3 (z : ℝ) : ℝ :=
  newtonThree (gammaSinhDenominatorUpper z) (gammaSinhPolynomial14 z)

/-- Three polynomial reciprocal updates for the hyperbolic cosine. -/
def gammaCoshPolynomialNewton3 (z : ℝ) : ℝ :=
  newtonThree (gammaCoshDenominatorUpper z) (gammaCoshPolynomial14 z)

private theorem hyperbolic_denominator_upper {z : ℝ} (h0 : 0 < z) (h1 : z ≤ 1) :
    (1 ≤ Real.sinh z / z ∧ Real.sinh z / z ≤ 2 ∧
      0 ≤ gammaSinhDenominatorUpper z - Real.sinh z / z ∧
      gammaSinhDenominatorUpper z - Real.sinh z / z ≤ 2 * z ^ 18 / 100000000000000000) ∧
    (1 ≤ Real.cosh z ∧ Real.cosh z ≤ 2 ∧
      0 ≤ gammaCoshDenominatorUpper z - Real.cosh z ∧
      gammaCoshDenominatorUpper z - Real.cosh z ≤ 2 * z ^ 18 / 100000000000000000) := by
  have hz : |z| ≤ 1 := by rwa [abs_of_pos h0]
  have hp := Real.exp_bound hz (n := 19) (by norm_num)
  have hm := Real.exp_bound (x := -z) (by simpa only [abs_neg] using hz)
    (n := 19) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg, abs_of_pos h0] at hp hm
  obtain ⟨hpl, hpu⟩ := abs_le.mp hp
  obtain ⟨hml, hmu⟩ := abs_le.mp hm
  have hn (n : ℕ) : 0 ≤ z ^ n := pow_nonneg h0.le n
  have hb (n : ℕ) : z ^ n ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ h0.le h1 n
  have h19 : z ^ 19 ≤ z ^ 18 := pow_le_pow_of_le_one h0.le h1 (by norm_num)
  have hs : Real.sinh z ≤ gammaSinhDenominatorUpper z * z ∧
      gammaSinhDenominatorUpper z * z - Real.sinh z ≤
        2 * z ^ 19 / 100000000000000000 := by
    rw [Real.sinh_eq]
    dsimp only [gammaSinhDenominatorUpper]
    constructor <;> nlinarith only [hpl, hpu, hml, hmu, hn 19]
  have hc : Real.cosh z ≤ gammaCoshDenominatorUpper z ∧
      gammaCoshDenominatorUpper z - Real.cosh z ≤
        2 * z ^ 19 / 100000000000000000 := by
    rw [Real.cosh_eq]
    dsimp only [gammaCoshDenominatorUpper]
    constructor <;> nlinarith only [hpl, hpu, hml, hmu, hn 19]
  have hTs : gammaSinhDenominatorUpper z ≤ 2 := by
    dsimp only [gammaSinhDenominatorUpper]
    linarith only [hb 2, hb 4, hb 6, hb 8, hb 10, hb 12, hb 14, hb 16, hb 18]
  have hTc : gammaCoshDenominatorUpper z ≤ 2 := by
    dsimp only [gammaCoshDenominatorUpper]
    linarith only [hb 2, hb 4, hb 6, hb 8, hb 10, hb 12, hb 14, hb 16, hb 18, hb 19]
  obtain ⟨hsl, _, hcl, _⟩ := sinh_cosh_taylor_bounds h0.le h1
  have hsu : Real.sinh z / z ≤ gammaSinhDenominatorUpper z := (div_le_iff₀ h0).mpr hs.1
  have hse : gammaSinhDenominatorUpper z - Real.sinh z / z ≤
      2 * z ^ 18 / 100000000000000000 := by
    apply (mul_le_mul_right h0).mp
    have he : (gammaSinhDenominatorUpper z - Real.sinh z / z) * z =
        gammaSinhDenominatorUpper z * z - Real.sinh z := by field_simp [h0.ne']
    rw [he]
    nlinarith only [hs.2]
  refine ⟨⟨?_, hsu.trans hTs, sub_nonneg.mpr hsu, hse⟩,
    ⟨?_, hc.1.trans hTc, sub_nonneg.mpr hc.1, ?_⟩⟩
  · apply (le_div_iff₀ h0).mpr
    nlinarith only [hsl, hn 3]
  · nlinarith only [hcl, hn 2]
  · linarith only [hc.2, h19]

private theorem reciprocal_newton_error {U T q e δ : ℝ}
    (hU1 : 1 ≤ U) (hU2 : U ≤ 2) (hT0 : 0 ≤ T - U) (hTδ : T - U ≤ δ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (he0 : 0 ≤ 1 / U - q) (he : 1 / U - q ≤ e) :
    0 ≤ 1 / U - gammaReciprocalNewton T q ∧
      1 / U - gammaReciprocalNewton T q ≤ 2 * e ^ 2 + δ := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU1
  have hid : 1 / U - gammaReciprocalNewton T q =
      U * (1 / U - q) ^ 2 + (T - U) * q ^ 2 := by
    dsimp only [gammaReciprocalNewton]
    field_simp [hU0.ne']
    ring
  rw [hid]
  refine ⟨add_nonneg (mul_nonneg hU0.le (sq_nonneg _)) (mul_nonneg hT0 (sq_nonneg _)), ?_⟩
  have hep := pow_le_pow_left₀ he0 he 2
  have hqp : q ^ 2 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hq0 hq1 2
  have hδ : 0 ≤ δ := hT0.trans hTδ
  exact add_le_add (mul_le_mul hU2 hep (sq_nonneg _) (by norm_num))
    (by simpa only [mul_one] using mul_le_mul hTδ hqp (sq_nonneg _) hδ)

private theorem newton_three_error {z U T q : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1)
    (hU1 : 1 ≤ U) (hU2 : U ≤ 2) (hT0 : 0 ≤ T - U)
    (hT : T - U ≤ 2 * z ^ 18 / 100000000000000000)
    (he0 : 0 ≤ 1 / U - q) (he : 1 / U - q ≤ z ^ 16 / 500) :
    0 ≤ 1 / U - newtonThree T q ∧
      1 / U - newtonThree T q ≤ 3 * z ^ 18 / 100000000000000000 := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU1
  have hi0 : (1 / 2 : ℝ) ≤ 1 / U := (le_div_iff₀ hU0).mpr (by linarith only [hU2])
  have hi1 : 1 / U ≤ (1 : ℝ) := (div_le_iff₀ hU0).mpr (by linarith only [hU1])
  have hn : 0 ≤ z ^ 18 := pow_nonneg h0 18
  have hb (n : ℕ) : z ^ n ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ h0 h1 n
  have h32 : z ^ 32 ≤ z ^ 18 := pow_le_pow_of_le_one h0 h1 (by norm_num)
  have h36 : z ^ 36 ≤ z ^ 18 := pow_le_pow_of_le_one h0 h1 (by norm_num)
  have hq : 0 ≤ q ∧ q ≤ 1 := by constructor <;> linarith only [hi0, hi1, he0, he, hb 16]
  let q1 := gammaReciprocalNewton T q
  let q2 := gammaReciprocalNewton T q1
  have he1 : 0 ≤ 1 / U - q1 ∧ 1 / U - q1 ≤ (9 / 1000000) * z ^ 18 := by
    obtain ⟨hlo, hhi⟩ := reciprocal_newton_error hU1 hU2 hT0 hT hq.1 hq.2 he0 he
    refine ⟨hlo, hhi.trans ?_⟩
    nlinarith only [h32, hn]
  have hq1 : 0 ≤ q1 ∧ q1 ≤ 1 := by
    constructor <;> linarith only [hi0, hi1, he1.1, he1.2, hb 18]
  have he2 : 0 ≤ 1 / U - q2 ∧ 1 / U - q2 ≤ (1 / 5000000000) * z ^ 18 := by
    obtain ⟨hlo, hhi⟩ := reciprocal_newton_error hU1 hU2 hT0 hT hq1.1 hq1.2 he1.1 he1.2
    refine ⟨hlo, hhi.trans ?_⟩
    nlinarith only [h36, hn]
  have hq2 : 0 ≤ q2 ∧ q2 ≤ 1 := by
    constructor <;> linarith only [hi0, hi1, he2.1, he2.2, hb 18]
  obtain ⟨hlo, hhi⟩ := reciprocal_newton_error hU1 hU2 hT0 hT hq2.1 hq2.2 he2.1 he2.2
  refine ⟨hlo, hhi.trans ?_⟩
  nlinarith only [h36, hn]

/-- Three updates keep both reciprocal errors below `3 z¹⁸/10¹⁷` on the unit interval. -/
theorem gamma_reciprocal_newton3_errors {z : ℝ} (h0 : 0 < z) (h1 : z ≤ 1) :
    (0 ≤ z / Real.sinh z - gammaSinhPolynomialNewton3 z ∧
      z / Real.sinh z - gammaSinhPolynomialNewton3 z ≤ 3 * z ^ 18 / 100000000000000000) ∧
    (0 ≤ 1 / Real.cosh z - gammaCoshPolynomialNewton3 z ∧
      1 / Real.cosh z - gammaCoshPolynomialNewton3 z ≤ 3 * z ^ 18 / 100000000000000000) := by
  obtain ⟨hs, hc⟩ := hyperbolic_denominator_upper h0 h1
  obtain ⟨hsl, hcl⟩ := gamma_reciprocal_polynomials14_lower h0 h1
  obtain ⟨hse, hce⟩ := gamma_reciprocal_polynomials14_errors h0 h1
  have hs0 : 0 ≤ 1 / (Real.sinh z / z) - gammaSinhPolynomial14 z := by
    simpa only [one_div_div] using sub_nonneg.mpr hsl
  have hse' : 1 / (Real.sinh z / z) - gammaSinhPolynomial14 z ≤ z ^ 16 / 500 := by
    rw [one_div_div]
    have hn := pow_nonneg h0.le 16
    linarith only [hse, hn]
  exact ⟨by simpa only [one_div_div, gammaSinhPolynomialNewton3] using
    newton_three_error h0.le h1 hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 hs0 hse',
    newton_three_error h0.le h1 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 (sub_nonneg.mpr hcl) hce⟩

/-- The polynomial Gamma lower kernel has uniform error `3/10¹⁷` through diameter two. -/
theorem archLevySinhWeight_newton3_error {t : ℝ} (h0 : 0 < t) (h2 : t ≤ 2) :
    0 ≤ archLevySinhWeight t -
        (gammaSinhPolynomialNewton3 (t / 2) / t + gammaCoshPolynomialNewton3 (t / 2) / 2) ∧
      archLevySinhWeight t -
        (gammaSinhPolynomialNewton3 (t / 2) / t + gammaCoshPolynomialNewton3 (t / 2) / 2) ≤
          3 / 100000000000000000 := by
  have hz0 : 0 < t / 2 := by linarith only [h0]
  have hz1 : t / 2 ≤ 1 := by linarith only [h2]
  obtain ⟨hs, hc⟩ := gamma_reciprocal_newton3_errors hz0 hz1
  have hs' := div_le_div_of_nonneg_right hs.2 h0.le
  have hc' := div_le_div_of_nonneg_right hc.2 (by norm_num : (0 : ℝ) ≤ 2)
  have hsn := div_nonneg hs.1 h0.le
  have hcn := div_nonneg hc.1 (by norm_num : (0 : ℝ) ≤ 2)
  have hden : Real.sinh (t / 2) ≠ 0 := (Real.sinh_pos_iff.mpr hz0).ne'
  have hcden : Real.cosh (t / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have he : archLevySinhWeight t -
      (gammaSinhPolynomialNewton3 (t / 2) / t + gammaCoshPolynomialNewton3 (t / 2) / 2) =
        ((t / 2) / Real.sinh (t / 2) - gammaSinhPolynomialNewton3 (t / 2)) / t +
          (1 / Real.cosh (t / 2) - gammaCoshPolynomialNewton3 (t / 2)) / 2 := by
    rw [archLevySinhWeight, exp_half_div_sinh_eq h0,
      archLevyDensity_eq_inv_sinh_add_inv_cosh h0]
    field_simp [h0.ne', hden, hcden]
    ring
  have hscale : (3 * (t / 2) ^ 18 / 100000000000000000) / t =
      3 * (t / 2) ^ 17 / 200000000000000000 := by
    field_simp [h0.ne']
    ring
  rw [hscale] at hs'
  have h17 : (t / 2) ^ 17 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hz0.le hz1 17
  have h18 : (t / 2) ^ 18 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hz0.le hz1 18
  rw [he]
  constructor <;> linarith only [hs', hc', hsn, hcn, h17, h18]

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.gamma_reciprocal_newton3_errors
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.archLevySinhWeight_newton3_error

import GaloisForLFunctions.RHTower.XiMassPolynomialEulerContourSourceIdentity
import GaloisForLFunctions.RHTower.XiMassArchimedeanUniformBound

/-!
# Uniform complex-time bound for the polynomial-filtered mass archimedean edge

The even polynomial weight `P(z²)²` is entire and depends only on the contour variable, so the exact
shift of the archimedean bottom integral to the centred real line survives it: the only crossed zero
is still the simple archimedean factor at `s = 1`, and its residue picks up the weight at that
point.  On the centred line the weight and the mass test both have `|·|` independent of the vertical
time, so the whole filtered archimedean contribution is uniformly bounded on every positive vertical
line.  All RH-strength growth stays in the prime channel.
-/

open Complex Filter intervalIntegral MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-! ## The even weight on a horizontal slab -/

/-- The even polynomial weight is bounded by a shifted power of the real part. -/
theorem norm_xiMassPolySquare_weight_le (P : Polynomial ℝ) {c r : ℝ} (hc : 0 ≤ c) {z : ℂ}
    (hz : ‖z‖ ≤ |r| + c) :
    ‖evalRealPolynomial P (z ^ 2) ^ 2‖
      ≤ xiMassPolyWeightConstant P c * (1 + |r| ^ (xiMassPolySquare P).natDegree) := by
  have hrw : evalRealPolynomial P (z ^ 2) ^ 2
      = evalRealPolynomial (xiMassPolySquare P) z :=
    (evalRealPolynomial_xiMassPolySquare P _).symm
  have habs0 : (0 : ℝ) ≤ |r| + c := by positivity
  have hstep := norm_evalRealPolynomial_le (xiMassPolySquare P) hz
  have hpoly := evalRealPolynomialNormBound_le_coeffSum_mul_pow (xiMassPolySquare P) habs0
    (le_refl (xiMassPolySquare P).natDegree)
  have hshift : (1 + (|r| + c)) ^ (xiMassPolySquare P).natDegree ≤
      (1 + c) ^ (xiMassPolySquare P).natDegree *
        (2 ^ (xiMassPolySquare P).natDegree *
          (1 + |r| ^ (xiMassPolySquare P).natDegree)) := by
    have hle : (1 + (|r| + c)) ≤ (1 + c) * (1 + |r|) := by nlinarith [abs_nonneg r, hc]
    calc (1 + (|r| + c)) ^ (xiMassPolySquare P).natDegree
        ≤ ((1 + c) * (1 + |r|)) ^ (xiMassPolySquare P).natDegree :=
          pow_le_pow_left₀ (by positivity) hle _
      _ = (1 + c) ^ (xiMassPolySquare P).natDegree *
            (1 + |r|) ^ (xiMassPolySquare P).natDegree := by rw [mul_pow]
      _ ≤ (1 + c) ^ (xiMassPolySquare P).natDegree *
            (2 ^ (xiMassPolySquare P).natDegree *
              (1 + |r| ^ (xiMassPolySquare P).natDegree)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have h2n : (0 : ℝ) < 2 ^ (xiMassPolySquare P).natDegree := by positivity
          have hxn : (0 : ℝ) ≤ |r| ^ (xiMassPolySquare P).natDegree := by positivity
          rcases le_or_gt (|r|) 1 with h | h
          · have hstep2 : (1 + |r|) ^ (xiMassPolySquare P).natDegree
                ≤ 2 ^ (xiMassPolySquare P).natDegree :=
              pow_le_pow_left₀ (by positivity) (by linarith) _
            nlinarith
          · have hstep2 : (1 + |r|) ^ (xiMassPolySquare P).natDegree
                ≤ (2 * |r|) ^ (xiMassPolySquare P).natDegree :=
              pow_le_pow_left₀ (by positivity) (by linarith) _
            rw [mul_pow] at hstep2
            nlinarith
  rw [hrw]
  calc ‖evalRealPolynomial (xiMassPolySquare P) z‖
      ≤ evalRealPolynomialNormBound (xiMassPolySquare P) (|r| + c) := hstep
    _ ≤ evalRealPolynomialCoeffSum (xiMassPolySquare P) *
          (1 + (|r| + c)) ^ (xiMassPolySquare P).natDegree := hpoly
    _ ≤ evalRealPolynomialCoeffSum (xiMassPolySquare P) *
          ((1 + c) ^ (xiMassPolySquare P).natDegree *
            (2 ^ (xiMassPolySquare P).natDegree *
              (1 + |r| ^ (xiMassPolySquare P).natDegree))) :=
        mul_le_mul_of_nonneg_left hshift (evalRealPolynomialCoeffSum_nonneg _)
    _ = xiMassPolyWeightConstant P c * (1 + |r| ^ (xiMassPolySquare P).natDegree) := by
        unfold xiMassPolyWeightConstant
        ring

theorem norm_verticalPoint_le {R y c : ℝ} (hy : |y| ≤ c) :
    ‖((R : ℂ) + y * I)‖ ≤ |R| + c := by
  have hbound := norm_add_le ((R : ℂ)) ((y : ℂ) * I)
  have h1 : ‖((R : ℂ))‖ = |R| := by simp
  have h2 : ‖((y : ℂ) * I)‖ = |y| := by simp
  rw [h1, h2] at hbound
  linarith

/-! ## The polynomial-filtered vertical side -/

/-- Polynomial-filtered archimedean integrand on a vertical side. -/
def xiMassPolyArchVerticalIntegrand (P : Polynomial ℝ) (a : ℝ) (τ : ℂ) (R y : ℝ) : ℂ :=
  xiMassPolyAnalyticTest P a τ ((R : ℂ) + y * I) *
    logDeriv archFactor (xiMassArchVerticalEulerPoint R y)

theorem xiMassPolyArchVerticalIntegrand_eq (P : Polynomial ℝ) (a : ℝ) (τ : ℂ) (R y : ℝ) :
    xiMassPolyArchVerticalIntegrand P a τ R y
      = evalRealPolynomial P (((R : ℂ) + y * I) ^ 2) ^ 2 *
        xiMassArchVerticalIntegrand a τ R y := by
  rw [xiMassPolyArchVerticalIntegrand, xiMassPolyAnalyticTest, xiMassArchVerticalIntegrand]
  ring

/-- Explicit side majorant for the filtered archimedean edge. -/
def xiMassPolyArchVerticalMajorant (P : Polynomial ℝ) (c : ℝ) (τ : ℂ) (R : ℝ) : ℝ :=
  xiMassPolyWeightConstant P c * (1 + |R| ^ (xiMassPolySquare P).natDegree) *
    xiMassArchVerticalMajorant c τ R

theorem norm_integral_xiMassPolyArchVerticalIntegrand_le (P : Polynomial ℝ)
    {a c R : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re)
    (hR : max 2 (1 / 2 + c) ≤ |R|) :
    ‖∫ y in -c..0, xiMassPolyArchVerticalIntegrand P a τ R y‖ ≤
      xiMassPolyArchVerticalMajorant P c τ R := by
  have hc0 : 0 < c := lt_trans (by norm_num) hhalf
  set G : ℝ := xiMassPolyWeightConstant P c * (1 + |R| ^ (xiMassPolySquare P).natDegree) with hG
  have hG0 : 0 ≤ G := by
    rw [hG]
    have := xiMassPolyWeightConstant_nonneg P hc0.le
    positivity
  have hpoint : ∀ y ∈ uIoc (-c) 0,
      ‖xiMassPolyArchVerticalIntegrand P a τ R y‖ ≤
        G * (Real.exp (-τ.re * |R| + |τ.im| * c) *
          (xiMassArchVerticalGrowthConstant + |R| / 2)) := by
    intro y hy
    have hyIoc : y ∈ Ioc (-c) 0 := by
      simpa [uIoc_of_le (by linarith : -c ≤ 0)] using hy
    have hyabs : |y| ≤ c := by
      rw [abs_le]
      exact ⟨hyIoc.1.le, le_trans hyIoc.2 hc0.le⟩
    have hw := norm_xiMassPolySquare_weight_le P (r := R) hc0.le
      (norm_verticalPoint_le hyabs)
    have hbase := norm_xiMassArchVerticalIntegrand_le hhalf hca hτ
      ⟨hyIoc.1.le, hyIoc.2⟩ hR
    rw [xiMassPolyArchVerticalIntegrand_eq, norm_mul]
    exact mul_le_mul hw hbase (norm_nonneg _) hG0
  calc ‖∫ y in -c..0, xiMassPolyArchVerticalIntegrand P a τ R y‖
      ≤ (G * (Real.exp (-τ.re * |R| + |τ.im| * c) *
          (xiMassArchVerticalGrowthConstant + |R| / 2))) * |0 - (-c)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = xiMassPolyArchVerticalMajorant P c τ R := by
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 0 - -c)]
        rw [xiMassPolyArchVerticalMajorant, xiMassArchVerticalMajorant, hG]
        ring

theorem tendsto_xiMassPolyArchVerticalMajorant_atTop (P : Polynomial ℝ)
    {c : ℝ} (_hhalf : 1 / 2 < c) {τ : ℂ} (hτ : 0 < τ.re) :
    Tendsto (xiMassPolyArchVerticalMajorant P c τ) atTop (𝓝 0) := by
  set D : ℕ := (xiMassPolySquare P).natDegree with hD
  set C : ℝ := xiMassArchVerticalGrowthConstant with hC
  set G : ℝ := xiMassPolyWeightConstant P c with hGdef
  set K : ℝ := G * (c * Real.exp (|τ.im| * c)) with hK
  have hpow (n : ℕ) :
      Tendsto (fun R : ℝ => R ^ n * Real.exp (-τ.re * R)) atTop (𝓝 0) := by
    have hraw := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) τ.re hτ
    apply hraw.congr'
    filter_upwards with R
    exact congrArg (fun u : ℝ => u * Real.exp (-τ.re * R))
      (Real.rpow_natCast R n)
  have hsum : Tendsto (fun R : ℝ =>
      K * (C * (R ^ 0 * Real.exp (-τ.re * R)))
        + K * ((1 / 2 : ℝ) * (R ^ 1 * Real.exp (-τ.re * R)))
        + K * (C * (R ^ D * Real.exp (-τ.re * R)))
        + K * ((1 / 2 : ℝ) * (R ^ (D + 1) * Real.exp (-τ.re * R)))) atTop (𝓝 0) := by
    have h0 := ((hpow 0).const_mul C).const_mul K
    have h1 := ((hpow 1).const_mul (1 / 2 : ℝ)).const_mul K
    have hD0 := ((hpow D).const_mul C).const_mul K
    have hD1 := ((hpow (D + 1)).const_mul (1 / 2 : ℝ)).const_mul K
    have := ((h0.add h1).add hD0).add hD1
    simpa using this
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR0
  rw [xiMassPolyArchVerticalMajorant, xiMassArchVerticalMajorant,
    show |R| = R from abs_of_nonneg hR0, Real.exp_add, hK, hGdef, hC, hD]
  ring

/-- The filtered right archimedean side vanishes as the rectangle exhausts horizontally. -/
theorem tendsto_integral_xiMassPolyArchVerticalIntegrand_right_atTop (P : Polynomial ℝ)
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re) :
    Tendsto (fun R : ℝ => ∫ y in -c..0,
      xiMassPolyArchVerticalIntegrand P a τ R y) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_xiMassPolyArchVerticalMajorant_atTop P hhalf hτ)
  filter_upwards [eventually_ge_atTop (max 2 (1 / 2 + c))] with R hR
  have hR0 : 0 ≤ R := by
    have : 2 ≤ R := (le_max_left 2 (1 / 2 + c)).trans hR
    linarith
  exact norm_integral_xiMassPolyArchVerticalIntegrand_le P hhalf hca hτ
    (show max 2 (1 / 2 + c) ≤ |R| by simpa [abs_of_nonneg hR0] using hR)

/-- The filtered left archimedean side vanishes as the rectangle exhausts horizontally. -/
theorem tendsto_integral_xiMassPolyArchVerticalIntegrand_left_atTop (P : Polynomial ℝ)
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re) :
    Tendsto (fun R : ℝ => ∫ y in -c..0,
      xiMassPolyArchVerticalIntegrand P a τ (-R) y) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_xiMassPolyArchVerticalMajorant_atTop P hhalf hτ)
  filter_upwards [eventually_ge_atTop (max 2 (1 / 2 + c))] with R hR
  have hR0 : 0 ≤ R := by
    have : 2 ≤ R := (le_max_left 2 (1 / 2 + c)).trans hR
    linarith
  have hbound := norm_integral_xiMassPolyArchVerticalIntegrand_le P hhalf hca hτ
    (R := -R) (show max 2 (1 / 2 + c) ≤ |-R| by
      rw [abs_neg, abs_of_nonneg hR0]
      exact hR)
  simpa [xiMassPolyArchVerticalMajorant, xiMassArchVerticalMajorant,
    abs_of_nonneg hR0] using hbound

end

end RHTower

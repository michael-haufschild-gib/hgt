/-
# Uniform quadratic remainder for Bourgain's normalized Taylor curve

The normalized curve
`(t,t²,φ₃,q(t),φ₄,q(t))` has uniformly bounded third derivative on
`0 < q ≤ 1/2`, `0 ≤ t ≤ 1`.  Consequently every subinterval of length `Δ`
has vector quadratic remainder at most `12 Δ³`.
-/
import GaloisForLFunctions.RHTower.BourgainGenericGaussianDecoupling
import GaloisForLFunctions.RHTower.BourgainQuadraticTaylorControl

namespace RHTower

noncomputable section

open Set

/-- Scalar Taylor remainder written using ordinary first and second
derivatives at the base point. -/
theorem abs_sub_quadraticJet_le
    {f : ℝ → ℝ} {a Δ C s : ℝ}
    (hΔ : 0 < Δ) (hs0 : 0 ≤ s) (hsΔ : s ≤ Δ)
    (hC0 : 0 ≤ C)
    (hf : ∀ y ∈ Icc a (a + Δ), ContDiffAt ℝ 3 f y)
    (hthird :
      ∀ y ∈ Icc a (a + Δ), |iteratedDeriv 3 f y| ≤ C) :
    |f (a + s) -
        (f a + iteratedDeriv 1 f a * s +
          iteratedDeriv 2 f a * s ^ (2 : ℕ) / 2)| ≤
      C * Δ ^ (3 : ℕ) / 2 := by
  have hab : a ≤ a + Δ := by linarith
  have hablt : a < a + Δ := by linarith
  have hx : a + s ∈ Icc a (a + Δ) := by
    constructor <;> linarith
  have hbase : a ∈ Icc a (a + Δ) := ⟨le_rfl, hab⟩
  have hcont : ContDiffOn ℝ 3 f (Icc a (a + Δ)) :=
    fun y hy => (hf y hy).contDiffWithinAt
  have hwithin :
      ∀ y ∈ Icc a (a + Δ),
        ‖iteratedDerivWithin 3 f (Icc a (a + Δ)) y‖ ≤ C := by
    intro y hy
    rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc hablt) (hf y hy) hy]
    simpa [Real.norm_eq_abs] using hthird y hy
  have hrem :=
    bourgain_quadraticTaylorWithin_remainder_of_sub_le
      hab hcont hx hC0 hwithin
      (show (a + s) - a ≤ Δ by linarith)
  rw [taylorWithinEval_two_eq] at hrem
  rw [iteratedDerivWithin_eq_iteratedDeriv (n := 1)
      (uniqueDiffOn_Icc hablt) ((hf a hbase).of_le (by norm_num)) hbase,
    iteratedDerivWithin_eq_iteratedDeriv (n := 2)
      (uniqueDiffOn_Icc hablt) ((hf a hbase).of_le (by norm_num)) hbase]
      at hrem
  norm_num [Real.norm_eq_abs] at hrem ⊢
  convert hrem using 1 <;> ring

theorem contDiffAt_bourgainNormalizedQuarticRemainder
    {q t : ℝ} {n : ℕ} (hbase : 0 < 1 + q * t) :
    ContDiffAt ℝ n (bourgainNormalizedQuarticRemainder q) t := by
  unfold bourgainNormalizedQuarticRemainder
  exact
    (contDiffAt_const.mul
      (contDiffAt_bourgainNormalizedCubicRemainder hbase)).sub
      (contDiffAt_const.mul
        ((contDiffAt_bourgainAffineRpow hbase).sub
          (by
            unfold bourgainHalfTaylorPolynomial
            fun_prop)))

/-- Uniform third-derivative bound for the normalized cubic phase. -/
theorem abs_iteratedDeriv_bourgainNormalizedCubicRemainder_three_le_six
    {q t : ℝ} (hq0 : 0 < q)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    |iteratedDeriv 3 (bourgainNormalizedCubicRemainder q) t| ≤ 6 := by
  have hqt0 : 0 ≤ q * t := mul_nonneg hq0.le ht.1
  have hbase : 0 < 1 + q * t := by linarith
  have hbase1 : 1 ≤ 1 + q * t := by linarith
  rw [iteratedDeriv_bourgainNormalizedCubicRemainder_three
    hq0.ne' hbase]
  have hrpow0 :
      0 ≤ (1 + q * t) ^ (-(3 / 2 : ℝ)) :=
    (Real.rpow_pos_of_pos hbase _).le
  have hrpow1 :
      (1 + q * t) ^ (-(3 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hbase1 (by norm_num)
  rw [abs_of_nonneg (mul_nonneg (by norm_num) hrpow0)]
  nlinarith

/-- Uniform third-derivative bound for the normalized quartic phase. -/
theorem abs_iteratedDeriv_bourgainNormalizedQuarticRemainder_three_le
    {q t : ℝ} (hq0 : 0 < q)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    |iteratedDeriv 3 (bourgainNormalizedQuarticRemainder q) t| ≤ 24 := by
  have hqt0 : 0 ≤ q * t := mul_nonneg hq0.le ht.1
  have hbase : 0 < 1 + q * t := by linarith
  have hbase1 : 1 ≤ 1 + q * t := by linarith
  rw [iteratedDeriv_bourgainNormalizedQuarticRemainder_three
    hq0.ne' hbase]
  have hrpow0 :
      0 ≤ (1 + q * t) ^ (-(5 / 2 : ℝ)) :=
    (Real.rpow_pos_of_pos hbase _).le
  have hrpow1 :
      (1 + q * t) ^ (-(5 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hbase1 (by norm_num)
  have hmul :
      t * (1 + q * t) ^ (-(5 / 2 : ℝ)) ≤ 1 := by
    calc
      t * (1 + q * t) ^ (-(5 / 2 : ℝ))
          ≤ 1 * (1 + q * t) ^ (-(5 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right ht.2 hrpow0
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hrpow1 (by norm_num)
      _ = 1 := by norm_num
  rw [abs_of_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) ht.1) hrpow0)]
  nlinarith

/-- Scalar cubic-phase quadratic remainder on any subinterval of `[0,1]`. -/
theorem abs_bourgainNormalizedCubicRemainder_sub_quadratic_le
    {q a Δ s : ℝ} (hq0 : 0 < q)
    (ha0 : 0 ≤ a) (haΔ : a + Δ ≤ 1)
    (hΔ : 0 < Δ) (hs0 : 0 ≤ s) (hsΔ : s ≤ Δ) :
    |bourgainNormalizedCubicRemainder q (a + s) -
        (bourgainNormalizedCubicRemainder q a +
          iteratedDeriv 1 (bourgainNormalizedCubicRemainder q) a * s +
          iteratedDeriv 2 (bourgainNormalizedCubicRemainder q) a *
            s ^ (2 : ℕ) / 2)| ≤
      12 * Δ ^ (3 : ℕ) := by
  have hpoint (y : ℝ) (hy : y ∈ Icc a (a + Δ)) :
      y ∈ Icc (0 : ℝ) 1 := ⟨ha0.trans hy.1, hy.2.trans haΔ⟩
  have hbase (y : ℝ) (hy : y ∈ Icc a (a + Δ)) :
      0 < 1 + q * y := by
    have := mul_nonneg hq0.le (hpoint y hy).1
    linarith
  have hrem :=
    abs_sub_quadraticJet_le hΔ hs0 hsΔ
      (show (0 : ℝ) ≤ 24 by norm_num)
      (fun y hy =>
        contDiffAt_bourgainNormalizedCubicRemainder (hbase y hy))
      (fun y hy =>
        (abs_iteratedDeriv_bourgainNormalizedCubicRemainder_three_le_six
          hq0 (hpoint y hy)).trans (by norm_num))
  nlinarith [sq_nonneg Δ, mul_nonneg (sq_nonneg Δ) hΔ.le]

/-- Scalar quartic-phase quadratic remainder on any subinterval of `[0,1]`. -/
theorem abs_bourgainNormalizedQuarticRemainder_sub_quadratic_le
    {q a Δ s : ℝ} (hq0 : 0 < q)
    (ha0 : 0 ≤ a) (haΔ : a + Δ ≤ 1)
    (hΔ : 0 < Δ) (hs0 : 0 ≤ s) (hsΔ : s ≤ Δ) :
    |bourgainNormalizedQuarticRemainder q (a + s) -
        (bourgainNormalizedQuarticRemainder q a +
          iteratedDeriv 1 (bourgainNormalizedQuarticRemainder q) a * s +
          iteratedDeriv 2 (bourgainNormalizedQuarticRemainder q) a *
            s ^ (2 : ℕ) / 2)| ≤
      12 * Δ ^ (3 : ℕ) := by
  have hpoint (y : ℝ) (hy : y ∈ Icc a (a + Δ)) :
      y ∈ Icc (0 : ℝ) 1 := ⟨ha0.trans hy.1, hy.2.trans haΔ⟩
  have hbase (y : ℝ) (hy : y ∈ Icc a (a + Δ)) :
      0 < 1 + q * y := by
    have := mul_nonneg hq0.le (hpoint y hy).1
    linarith
  have hrem :=
    abs_sub_quadraticJet_le hΔ hs0 hsΔ
      (show (0 : ℝ) ≤ 24 by norm_num)
      (fun y hy =>
        contDiffAt_bourgainNormalizedQuarticRemainder (hbase y hy))
      (fun y hy =>
        abs_iteratedDeriv_bourgainNormalizedQuarticRemainder_three_le
          hq0 (hpoint y hy))
  nlinarith [sq_nonneg Δ, mul_nonneg (sq_nonneg Δ) hΔ.le]

/-- Uniform vector quadratic remainder for Bourgain's normalized Taylor
curve. -/
theorem norm_bourgainNormalizedTaylorCurve_sub_quadratic_le
    {q a Δ s : ℝ} (hq0 : 0 < q)
    (ha0 : 0 ≤ a) (haΔ : a + Δ ≤ 1)
    (hΔ : 0 < Δ) (hs0 : 0 ≤ s) (hsΔ : s ≤ Δ) :
    ‖bourgainGenericFourCurve
          (bourgainNormalizedCubicRemainder q)
          (bourgainNormalizedQuarticRemainder q) (a + s) -
        bourgainGenericFourCurveQuadraticModel
          (bourgainNormalizedCubicRemainder q)
          (bourgainNormalizedQuarticRemainder q) a s‖ ≤
      12 * Δ ^ (3 : ℕ) := by
  have hbound0 : 0 ≤ 12 * Δ ^ (3 : ℕ) := by positivity
  rw [pi_norm_le_iff_of_nonneg hbound0]
  intro j
  fin_cases j
  · simp [bourgainGenericFourCurve,
      bourgainGenericFourCurveQuadraticModel]
    positivity
  · simp [bourgainGenericFourCurve,
      bourgainGenericFourCurveQuadraticModel]
    ring_nf
    simpa only [abs_zero, mul_comm] using hbound0
  · simpa [bourgainGenericFourCurve,
      bourgainGenericFourCurveQuadraticModel, Real.norm_eq_abs] using
      abs_bourgainNormalizedCubicRemainder_sub_quadratic_le
        hq0 ha0 haΔ hΔ hs0 hsΔ
  · simpa [bourgainGenericFourCurve,
      bourgainGenericFourCurveQuadraticModel, Real.norm_eq_abs] using
      abs_bourgainNormalizedQuarticRemainder_sub_quadratic_le
        hq0 ha0 haΔ hΔ hs0 hsΔ

end

end RHTower

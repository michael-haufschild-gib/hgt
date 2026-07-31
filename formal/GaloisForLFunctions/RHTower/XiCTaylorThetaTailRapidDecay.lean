import GaloisForLFunctions.RHTower.XiCTaylorThetaTailOrientedDefect
import Mathlib.Analysis.SumIntegralExpDecay

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Constant for a natural exponential rate of the raw theta tail. -/
def thetaCuspTailNatExpConstant (p : ℕ) : ℝ :=
  Real.exp (((p + 1 : ℕ) : ℝ) ^ 2 / (2 * Real.pi)) *
    ∑' n : ℕ, Real.exp (-(Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2)

theorem thetaCuspTailNatExpConstant_nonneg (p : ℕ) :
    0 ≤ thetaCuspTailNatExpConstant p := by
  unfold thetaCuspTailNatExpConstant
  exact mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun _ => (Real.exp_pos _).le)

theorem exp_nat_mul_abs_thetaCuspTailAtom_le
    (p : ℕ) {x : ℝ} (hx : 0 ≤ x) {q : ℕ} (hq : 0 < q) :
    Real.exp ((p : ℝ) * x) *
        |thetaCuspPolynomialAtom (1 : ℝ[X]) q x| ≤
      Real.exp (((p + 1 : ℕ) : ℝ) ^ 2 / (2 * Real.pi)) *
        Real.exp (-(Real.pi / 2) * (q : ℝ) ^ 2) := by
  let y : ℝ := (q : ℝ) * Real.exp x
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hexp1 : 1 ≤ Real.exp x := by simpa using Real.exp_le_exp.mpr hx
  have hy1 : 1 ≤ y := by
    dsimp [y]
    nlinarith [Real.exp_pos x]
  have hy0 : 0 ≤ y := zero_le_one.trans hy1
  have hqy : (q : ℝ) ≤ y := by
    dsimp [y]
    nlinarith
  have hexy : Real.exp x ≤ y := by
    dsimp [y]
    nlinarith [Real.exp_pos x]
  have hhalf : Real.exp (x / 2) ≤ Real.exp x :=
    Real.exp_le_exp.mpr (by linarith)
  have hfront : Real.exp ((p : ℝ) * x) * Real.exp (x / 2) ≤ y ^ (p + 1) := by
    calc
      Real.exp ((p : ℝ) * x) * Real.exp (x / 2) =
          Real.exp x ^ p * Real.exp (x / 2) := by
        rw [← Real.exp_nat_mul]
      _ ≤ Real.exp x ^ p * Real.exp x := by gcongr
      _ = Real.exp x ^ (p + 1) := by rw [pow_succ]
      _ ≤ y ^ (p + 1) := pow_le_pow_left₀ (Real.exp_pos x).le hexy _
  let B : ℝ := Real.exp (((p + 1 : ℕ) : ℝ) ^ 2 / (2 * Real.pi))
  have hgauss : y ^ (p + 1) * Real.exp (-(Real.pi / 2) * y ^ 2) ≤ B := by
    simpa [B] using pow_mul_exp_neg_half_pi_sq_le (p + 1) hy0
  have htail : Real.exp (-(Real.pi / 2) * y ^ 2) ≤
      Real.exp (-(Real.pi / 2) * (q : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hsq : (q : ℝ) ^ 2 ≤ y ^ 2 := by nlinarith
    nlinarith [Real.pi_pos]
  have hsplit : Real.exp (-Real.pi * y ^ 2) =
      Real.exp (-(Real.pi / 2) * y ^ 2) *
        Real.exp (-(Real.pi / 2) * y ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [thetaCuspPolynomialAtom]
  simp only [eval_one, mul_one, abs_mul, abs_of_pos (Real.exp_pos _)]
  change Real.exp ((p : ℝ) * x) *
      (Real.exp (x / 2) * Real.exp (-Real.pi * y ^ 2)) ≤ _
  calc
    Real.exp ((p : ℝ) * x) *
        (Real.exp (x / 2) * Real.exp (-Real.pi * y ^ 2)) =
        (Real.exp ((p : ℝ) * x) * Real.exp (x / 2)) *
          Real.exp (-Real.pi * y ^ 2) := by ring
    _ ≤ y ^ (p + 1) * Real.exp (-Real.pi * y ^ 2) := by
      exact mul_le_mul_of_nonneg_right hfront (Real.exp_pos _).le
    _ = (y ^ (p + 1) * Real.exp (-(Real.pi / 2) * y ^ 2)) *
          Real.exp (-(Real.pi / 2) * y ^ 2) := by rw [hsplit]; ring
    _ ≤ B * Real.exp (-(Real.pi / 2) * y ^ 2) := by
      exact mul_le_mul_of_nonneg_right hgauss (Real.exp_pos _).le
    _ ≤ B * Real.exp (-(Real.pi / 2) * (q : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left htail (Real.exp_pos _).le
    _ = Real.exp (((p + 1 : ℕ) : ℝ) ^ 2 / (2 * Real.pi)) *
          Real.exp (-(Real.pi / 2) * (q : ℝ) ^ 2) := by rfl

/-- The raw theta tail decays faster than every natural exponential rate. -/
theorem abs_thetaCuspTailDerivative_zero_le_nat_exp_neg
    (p : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |thetaCuspTailDerivative 0 x| ≤
      thetaCuspTailNatExpConstant p * Real.exp (-(p : ℝ) * x) := by
  let a : ℕ → ℝ := fun n => thetaCuspPolynomialAtom (1 : ℝ[X]) (n + 1) x
  let g : ℕ → ℝ := fun n => Real.exp (-(Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2)
  let B : ℝ := Real.exp (((p + 1 : ℕ) : ℝ) ^ 2 / (2 * Real.pi))
  have ha : Summable a := by
    simpa [a, thetaCuspTailDerivative, thetaCuspTailDerivativePolynomial] using
      summable_thetaCuspTailDerivative 0 x
  have hg : Summable g := by
    exact (summable_nat_add_iff 1).mpr summable_thetaCuspHalfGaussian
  have hag : Summable (fun n => Real.exp ((p : ℝ) * x) * |a n|) :=
    ha.norm.mul_left _
  have hBg : Summable (fun n => B * g n) := hg.mul_left _
  have hterm (n : ℕ) :
      Real.exp ((p : ℝ) * x) * |a n| ≤ B * g n := by
    exact exp_nat_mul_abs_thetaCuspTailAtom_le p hx (Nat.succ_pos n)
  have hsum : Real.exp ((p : ℝ) * x) * |∑' n, a n| ≤ B * ∑' n, g n := by
    calc
      Real.exp ((p : ℝ) * x) * |∑' n, a n| ≤
          Real.exp ((p : ℝ) * x) * ∑' n, |a n| := by
        gcongr
        exact norm_tsum_le_tsum_norm ha.norm
      _ = ∑' n, Real.exp ((p : ℝ) * x) * |a n| := by rw [tsum_mul_left]
      _ ≤ ∑' n, B * g n := hag.tsum_le_tsum hterm hBg
      _ = B * ∑' n, g n := by rw [tsum_mul_left]
  rw [thetaCuspTailDerivative]
  change |∑' n, a n| ≤ _
  calc
    |∑' n, a n| = Real.exp (-(p : ℝ) * x) *
        (Real.exp ((p : ℝ) * x) * |∑' n, a n|) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (-(p : ℝ) * x) * (B * ∑' n, g n) := by gcongr
    _ = thetaCuspTailNatExpConstant p * Real.exp (-(p : ℝ) * x) := by
      simp [thetaCuspTailNatExpConstant, B, g]
      ring

theorem integral_pow_mul_exp_nat_neg (k p : ℕ) (hp : 0 < p) :
    (∫ x : ℝ in Ioi 0, x ^ k * Real.exp (-(p : ℝ) * x)) =
      k.factorial / (p : ℝ) ^ (k + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (k : ℝ) + 1) (r := (p : ℝ)) (by positivity) (by exact_mod_cast hp)
  simp only [add_sub_cancel_right, Real.rpow_natCast] at h
  rw [show (∫ x : ℝ in Ioi 0, x ^ k * Real.exp (-(p : ℝ) * x)) =
      (∫ x : ℝ in Ioi 0, x ^ k * Real.exp (-((p : ℝ) * x))) by
        congr 1
        funext x
        ring]
  rw [h, Real.Gamma_nat_eq_factorial]
  rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hpR : (p : ℝ) ≠ 0 := by positivity
  simp only [one_div, inv_pow, pow_succ]
  field_simp

/-- The normalized theta-tail moments decay geometrically at every prescribed natural rate. -/
theorem abs_thetaCuspTailEvenCoefficient_le_nat_rate
    (n p : ℕ) (hp : 0 < p) :
    |thetaCuspTailEvenCoefficient n| ≤
      2 * thetaCuspTailNatExpConstant p / (p : ℝ) ^ (2 * n + 1) := by
  let C : ℝ := thetaCuspTailNatExpConstant p
  let k : ℕ := 2 * n
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hbase : IntegrableOn
      (fun x : ℝ => x ^ k * Real.exp (-(p : ℝ) * x)) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [integral_pow_mul_exp_nat_neg k p hp]
    positivity
  have hg : IntegrableOn
      (fun x : ℝ => C * (x ^ k * Real.exp (-(p : ℝ) * x))) (Ioi 0) :=
    hbase.const_mul C
  have hint : ‖∫ x : ℝ in Ioi 0, x ^ k * thetaCuspTailDerivative 0 x‖ ≤
      ∫ x : ℝ in Ioi 0, C * (x ^ k * Real.exp (-(p : ℝ) * x)) := by
    apply MeasureTheory.norm_integral_le_of_norm_le hg
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := hx.le
    have htail := abs_thetaCuspTailDerivative_zero_le_nat_exp_neg p hx0
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hx0]
    calc
      x ^ k * |thetaCuspTailDerivative 0 x| ≤
          x ^ k * (C * Real.exp (-(p : ℝ) * x)) := by
        exact mul_le_mul_of_nonneg_left htail (pow_nonneg hx0 _)
      _ = C * (x ^ k * Real.exp (-(p : ℝ) * x)) := by ring
  have hint' : |∫ x : ℝ in Ioi 0, x ^ k * thetaCuspTailDerivative 0 x| ≤
      C * (k.factorial / (p : ℝ) ^ (k + 1)) := by
    rw [Real.norm_eq_abs] at hint
    simpa only [integral_const_mul, integral_pow_mul_exp_nat_neg k p hp] using hint
  rw [thetaCuspTailEvenCoefficient, thetaCuspTailRawEvenMoment]
  rw [abs_div, abs_mul]
  dsimp [k] at hint' ⊢
  have hfac : (0 : ℝ) < (2 * n).factorial := by positivity
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hfac]
  rw [div_le_iff₀ hfac]
  calc
    2 * |∫ x : ℝ in Ioi 0, x ^ (2 * n) * thetaCuspTailDerivative 0 x| ≤
        2 * (C * ((2 * n).factorial / (p : ℝ) ^ (2 * n + 1))) := by
      gcongr
    _ = (2 * C / (p : ℝ) ^ (2 * n + 1)) * (2 * n).factorial := by ring

theorem norm_xiCTaylorThetaTailTopDefectPolynomial_eval
    (d : ℕ) (z : ℂ) :
    ‖(xiCTaylorThetaTailTopDefectPolynomial d).eval z‖ =
      (1 / 4 : ℝ) * |thetaCuspTailEvenCoefficient (d + 1)| *
        ‖z‖ ^ (2 * (d + 1)) := by
  simp only [xiCTaylorThetaTailTopDefectPolynomial, eval_mul, eval_C, eval_pow, eval_X,
    norm_mul, norm_pow, Complex.norm_real]
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  ring

theorem norm_xiCTaylorThetaTailTopDefectPolynomial_derivative_eval
    (d : ℕ) (z : ℂ) :
    ‖(xiCTaylorThetaTailTopDefectPolynomial d).derivative.eval z‖ =
      (2 * (d + 1) : ℕ) * ((1 / 4 : ℝ) *
        |thetaCuspTailEvenCoefficient (d + 1)|) *
          ‖z‖ ^ (2 * (d + 1) - 1) := by
  simp only [xiCTaylorThetaTailTopDefectPolynomial, derivative_mul, derivative_C,
    zero_mul, derivative_X_pow, eval_mul, eval_C,
    eval_pow, eval_X, zero_add, norm_mul, norm_pow, Complex.norm_real]
  simp only [Real.norm_eq_abs, abs_neg, abs_one, one_pow, one_mul]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  rw [Complex.norm_natCast]
  push_cast
  ring

theorem tendsto_norm_xiCTaylorThetaTailTopDefectPolynomial_eval_of_norm_lt_nat
    (z : ℂ) {p : ℕ} (hp : 0 < p) (hzp : ‖z‖ < (p : ℝ)) :
    Tendsto (fun d : ℕ =>
      ‖(xiCTaylorThetaTailTopDefectPolynomial d).eval z‖) atTop (nhds 0) := by
  let r : ℝ := ‖z‖ / (p : ℝ)
  let A : ℝ := thetaCuspTailNatExpConstant p / (2 * (p : ℝ))
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hr0 : 0 ≤ r := div_nonneg (norm_nonneg _) hpR.le
  have hr1 : r < 1 := (div_lt_one hpR).mpr hzp
  have hrpow : Tendsto (fun d : ℕ => r ^ (2 * (d + 1))) atTop (nhds 0) := by
    have hbase := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    have hsq : Tendsto (fun d : ℕ => (r ^ 2) ^ (d + 1)) atTop (nhds 0) := by
      have hr20 : 0 ≤ r ^ 2 := sq_nonneg r
      have hr21 : r ^ 2 < 1 := by nlinarith
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one hr20 hr21).comp
        (tendsto_add_atTop_nat 1)
    convert hsq using 1
    ext d
    rw [← pow_mul]
  have hmajor : Tendsto (fun d : ℕ => A * r ^ (2 * (d + 1))) atTop (nhds 0) := by
    simpa using hrpow.const_mul A
  apply squeeze_zero' (Eventually.of_forall fun d => norm_nonneg _) ?_ hmajor
  apply Eventually.of_forall
  intro d
  rw [norm_xiCTaylorThetaTailTopDefectPolynomial_eval]
  have hc := abs_thetaCuspTailEvenCoefficient_le_nat_rate (d + 1) p hp
  calc
    (1 / 4 : ℝ) * |thetaCuspTailEvenCoefficient (d + 1)| *
        ‖z‖ ^ (2 * (d + 1)) ≤
      (1 / 4 : ℝ) *
          (2 * thetaCuspTailNatExpConstant p /
            (p : ℝ) ^ (2 * (d + 1) + 1)) *
        ‖z‖ ^ (2 * (d + 1)) := by
      gcongr
    _ = A * r ^ (2 * (d + 1)) := by
      dsimp [A, r]
      rw [div_pow, pow_succ]
      field_simp [ne_of_gt hpR]
      ring

theorem tendsto_norm_xiCTaylorThetaTailTopDefectPolynomial_derivative_eval_of_norm_lt_nat
    (z : ℂ) {p : ℕ} (hp : 0 < p) (hzp : ‖z‖ < (p : ℝ)) :
    Tendsto (fun d : ℕ =>
      ‖(xiCTaylorThetaTailTopDefectPolynomial d).derivative.eval z‖)
        atTop (nhds 0) := by
  let r : ℝ := ‖z‖ / (p : ℝ)
  let s : ℝ := r ^ 2
  let A : ℝ := thetaCuspTailNatExpConstant p / (2 * (p : ℝ) ^ 2)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hr0 : 0 ≤ r := div_nonneg (norm_nonneg _) hpR.le
  have hr1 : r < 1 := (div_lt_one hpR).mpr hzp
  have hs0 : 0 ≤ s := sq_nonneg r
  have hs1 : s < 1 := by dsimp [s]; nlinarith
  have hsNorm : ‖s‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hs0] using hs1
  have hdNorm : Summable (fun d : ℕ => ‖((d : ℝ) * s ^ d : ℝ)‖) := by
    simpa only [pow_one] using
      (summable_norm_pow_mul_geometric_of_norm_lt_one 1 hsNorm)
  have hd : Tendsto (fun d : ℕ => (d : ℝ) * s ^ d) atTop (nhds 0) := by
    have h := hdNorm.tendsto_atTop_zero
    simpa [Real.norm_eq_abs, abs_of_nonneg hs0, abs_of_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hs0 _))] using h
  have hsPow : Tendsto (fun d : ℕ => s ^ d) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hs0 hs1
  have hmajor : Tendsto
      (fun d : ℕ => A * (((2 : ℝ) * r) * (((d : ℝ) + 1) * s ^ d)))
      atTop (nhds 0) := by
    have hadd : Tendsto (fun d : ℕ => ((d : ℝ) + 1) * s ^ d) atTop (nhds 0) := by
      convert hd.add hsPow using 1
      · ext d
        ring
      · ring
    simpa only [mul_zero] using (hadd.const_mul ((2 : ℝ) * r)).const_mul A
  apply squeeze_zero' (Eventually.of_forall fun d => norm_nonneg _) ?_ hmajor
  apply Eventually.of_forall
  intro d
  rw [norm_xiCTaylorThetaTailTopDefectPolynomial_derivative_eval]
  have hc := abs_thetaCuspTailEvenCoefficient_le_nat_rate (d + 1) p hp
  have hmpos : (0 : ℝ) ≤ (2 * (d + 1) : ℕ) := Nat.cast_nonneg _
  calc
    ((2 * (d + 1) : ℕ) : ℝ) *
          ((1 / 4 : ℝ) * |thetaCuspTailEvenCoefficient (d + 1)|) *
        ‖z‖ ^ (2 * (d + 1) - 1) ≤
      ((2 * (d + 1) : ℕ) : ℝ) *
          ((1 / 4 : ℝ) *
            (2 * thetaCuspTailNatExpConstant p /
              (p : ℝ) ^ (2 * (d + 1) + 1))) *
        ‖z‖ ^ (2 * (d + 1) - 1) := by
      gcongr
    _ = A * (((2 : ℝ) * r) * (((d : ℝ) + 1) * s ^ d)) := by
      dsimp [A, r, s]
      have hexp : 2 * (d + 1) - 1 = 2 * d + 1 := by omega
      have hden : 2 * (d + 1) + 1 = 2 * d + 3 := by omega
      rw [hexp, hden, show 2 * d + 3 = 2 * d + 3 by rfl,
        pow_add, pow_succ, ← pow_mul, div_pow]
      field_simp [ne_of_gt hpR, pow_ne_zero, pow_succ]
      push_cast
      ring

/-- The top defect and its derivative vanish uniformly on every fixed closed ball. -/
theorem eventually_norm_xiCTaylorThetaTailTopDefect_lt_on_closedBall
    {R epsilon : ℝ} (hR : 0 ≤ R) (hepsilon : 0 < epsilon) :
    ∀ᶠ d : ℕ in atTop, ∀ z ∈ Metric.closedBall (0 : ℂ) R,
      ‖(xiCTaylorThetaTailTopDefectPolynomial d).eval z‖ < epsilon ∧
      ‖(xiCTaylorThetaTailTopDefectPolynomial d).derivative.eval z‖ < epsilon := by
  let p : ℕ := ⌈R⌉₊ + 1
  have hp : 0 < p := by dsimp [p]; omega
  have hRp : R < (p : ℝ) := by
    dsimp [p]
    push_cast
    exact (Nat.le_ceil R).trans_lt (lt_add_one _)
  have hnormR : ‖(R : ℂ)‖ = R := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR]
  have hval :=
    tendsto_norm_xiCTaylorThetaTailTopDefectPolynomial_eval_of_norm_lt_nat
      (R : ℂ) hp (by simpa only [hnormR] using hRp)
  have hderiv :=
    tendsto_norm_xiCTaylorThetaTailTopDefectPolynomial_derivative_eval_of_norm_lt_nat
      (R : ℂ) hp (by simpa only [hnormR] using hRp)
  have hvalEv : ∀ᶠ d : ℕ in atTop,
      ‖(xiCTaylorThetaTailTopDefectPolynomial d).eval (R : ℂ)‖ < epsilon :=
    hval.eventually (eventually_lt_nhds hepsilon)
  have hderivEv : ∀ᶠ d : ℕ in atTop,
      ‖(xiCTaylorThetaTailTopDefectPolynomial d).derivative.eval (R : ℂ)‖ < epsilon :=
    hderiv.eventually (eventually_lt_nhds hepsilon)
  filter_upwards [hvalEv, hderivEv] with d hdValue hdDeriv
  intro z hz
  have hzNorm : ‖z‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  constructor
  · apply lt_of_le_of_lt ?_ hdValue
    rw [norm_xiCTaylorThetaTailTopDefectPolynomial_eval,
      norm_xiCTaylorThetaTailTopDefectPolynomial_eval, hnormR]
    gcongr
  · apply lt_of_le_of_lt ?_ hdDeriv
    rw [norm_xiCTaylorThetaTailTopDefectPolynomial_derivative_eval,
      norm_xiCTaylorThetaTailTopDefectPolynomial_derivative_eval, hnormR]
    gcongr


end
end RHTower

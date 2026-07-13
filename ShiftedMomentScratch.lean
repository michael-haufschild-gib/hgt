import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationBounds

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

#check add_pow
#check MeasureTheory.integral_finsetSum
#check MeasureTheory.integrable_finsetSum
#check Finset.sum_range_reflect
#check Nat.choose_mul_factorial_mul_factorial
#check MeasureTheory.integral_mono_measure

theorem test_integral_shifted_pow
    (N p : ℕ) (hp : 0 < p) (a : ℝ) :
    (∫ x : ℝ in Ioi 0, (x + a) ^ N * Real.exp (-(p : ℝ) * x)) =
      ∑ m ∈ Finset.range (N + 1),
        (N.choose m : ℝ) * a ^ (N - m) *
          (m.factorial / (p : ℝ) ^ (m + 1)) := by
  have hInt (m : ℕ) : IntegrableOn
      (fun x : ℝ => ((N.choose m : ℝ) * a ^ (N - m)) *
        (x ^ m * Real.exp (-(p : ℝ) * x))) (Ioi 0) := by
    have hb : IntegrableOn
        (fun x : ℝ => x ^ m * Real.exp (-(p : ℝ) * x)) (Ioi 0) := by
      apply Integrable.of_integral_ne_zero
      rw [integral_pow_mul_exp_nat_neg m p hp]
      positivity
    exact hb.const_mul _
  rw [show (fun x : ℝ => (x + a) ^ N * Real.exp (-(p : ℝ) * x)) =
      fun x : ℝ => ∑ m ∈ Finset.range (N + 1),
        ((N.choose m : ℝ) * a ^ (N - m)) *
          (x ^ m * Real.exp (-(p : ℝ) * x)) by
    funext x
    rw [add_pow]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _hm
    ring]
  rw [MeasureTheory.integral_finsetSum _ (fun m _hm => hInt m)]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [MeasureTheory.integral_const_mul, integral_pow_mul_exp_nat_neg m p hp]

theorem test_shifted_moment_sum_eq
    (N p : ℕ) (hp : 0 < p) (a : ℝ) :
    (∑ m ∈ Finset.range (N + 1),
        (N.choose m : ℝ) * a ^ (N - m) *
          (m.factorial / (p : ℝ) ^ (m + 1))) =
      (N.factorial / (p : ℝ) ^ (N + 1)) *
        ∑ j ∈ Finset.range (N + 1),
          (((p : ℝ) * a) ^ j / j.factorial) := by
  rw [← Finset.sum_range_reflect
    (fun j : ℕ => (((p : ℝ) * a) ^ j / j.factorial)) (N + 1)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmle : m ≤ N := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hm)
  rw [show N + 1 - 1 - m = N - m by omega]
  have hfacNat := Nat.choose_mul_factorial_mul_factorial hmle
  have hfac : (N.choose m : ℝ) * m.factorial * (N - m).factorial =
      N.factorial := by exact_mod_cast hfacNat
  have hpR : (p : ℝ) ≠ 0 := by positivity
  have hmf : ((m.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hsubf : (((N - m).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hpR, hmf, hsubf]
  rw [mul_pow]
  rw [show N + 1 = (m + 1) + (N - m) by omega, pow_add]
  rw [← hfac]
  ring

theorem test_shifted_moment_sum_le
    (N p : ℕ) (hp : 0 < p) {a : ℝ} (ha : 0 ≤ a) :
    (∑ m ∈ Finset.range (N + 1),
        (N.choose m : ℝ) * a ^ (N - m) *
          (m.factorial / (p : ℝ) ^ (m + 1))) ≤
      (N.factorial / (p : ℝ) ^ (N + 1)) * Real.exp ((p : ℝ) * a) := by
  rw [test_shifted_moment_sum_eq N p hp a]
  gcongr
  exact Real.sum_le_exp_of_nonneg (mul_nonneg (Nat.cast_nonneg _) ha) _

theorem test_integrable_shifted_pow
    (N p : ℕ) (hp : 0 < p) (a : ℝ) :
    IntegrableOn (fun x : ℝ =>
      (x + a) ^ N * Real.exp (-(p : ℝ) * x)) (Ioi 0) := by
  have hInt (m : ℕ) : IntegrableOn
      (fun x : ℝ => ((N.choose m : ℝ) * a ^ (N - m)) *
        (x ^ m * Real.exp (-(p : ℝ) * x))) (Ioi 0) := by
    have hb : IntegrableOn
        (fun x : ℝ => x ^ m * Real.exp (-(p : ℝ) * x)) (Ioi 0) := by
      apply Integrable.of_integral_ne_zero
      rw [integral_pow_mul_exp_nat_neg m p hp]
      positivity
    exact hb.const_mul _
  rw [show (fun x : ℝ => (x + a) ^ N * Real.exp (-(p : ℝ) * x)) =
      fun x : ℝ => ∑ m ∈ Finset.range (N + 1),
        ((N.choose m : ℝ) * a ^ (N - m)) *
          (x ^ m * Real.exp (-(p : ℝ) * x)) by
    funext x
    rw [add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _hm
    ring]
  exact MeasureTheory.integrable_finsetSum _ (fun m _hm => hInt m)

theorem test_general_moment
    (ell m p : ℕ) (hp : 0 < p) :
    (∫ x : ℝ in Ioi 0,
      |x ^ m * thetaCuspTailDerivative ell x|) ≤
        thetaCuspTailDerivativeNatExpConstant ell p *
          (m.factorial / (p : ℝ) ^ (m + 1)) := by
  let C : ℝ := thetaCuspTailDerivativeNatExpConstant ell p
  have hf : IntegrableOn
      (fun x : ℝ => |x ^ m * thetaCuspTailDerivative ell x|) (Ioi 0) := by
    simpa only [Real.norm_eq_abs] using
      (integrableOn_pow_mul_thetaCuspTailDerivative m ell).norm
  have hbase : IntegrableOn
      (fun x : ℝ => x ^ m * Real.exp (-(p : ℝ) * x)) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [integral_pow_mul_exp_nat_neg m p hp]
    positivity
  have hg : IntegrableOn
      (fun x : ℝ => C * (x ^ m * Real.exp (-(p : ℝ) * x))) (Ioi 0) :=
    hbase.const_mul C
  calc
    (∫ x : ℝ in Ioi 0, |x ^ m * thetaCuspTailDerivative ell x|) ≤
        ∫ x : ℝ in Ioi 0,
          C * (x ^ m * Real.exp (-(p : ℝ) * x)) := by
      apply MeasureTheory.integral_mono_ae hf hg
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 ≤ x := hx.le
      have htail := abs_thetaCuspTailDerivative_le_nat_exp_neg ell p hx0
      rw [abs_mul, abs_pow, abs_of_nonneg hx0]
      calc
        x ^ m * |thetaCuspTailDerivative ell x| ≤
            x ^ m * (C * Real.exp (-(p : ℝ) * x)) :=
          mul_le_mul_of_nonneg_left htail (pow_nonneg hx0 _)
        _ = C * (x ^ m * Real.exp (-(p : ℝ) * x)) := by ring
    _ = thetaCuspTailDerivativeNatExpConstant ell p *
          (m.factorial / (p : ℝ) ^ (m + 1)) := by
      rw [integral_const_mul, integral_pow_mul_exp_nat_neg m p hp]

theorem test_shifted_factorial_envelope
    (ell N p r : ℕ) (hp : 0 < p) {a : ℝ} (ha : 0 ≤ a) :
    (∫ x : ℝ in Ioi 0,
      |thetaCuspTailDerivative ell x| *
        ((((r : ℝ) * (x + a)) ^ N / N.factorial) *
          Real.exp ((r : ℝ) * (x + a)))) ≤
      thetaCuspTailDerivativeNatExpConstant ell (p + r) *
        ((r : ℝ) ^ N / (p : ℝ) ^ (N + 1)) *
          Real.exp (((p + r : ℕ) : ℝ) * a) := by
  let C : ℝ := thetaCuspTailDerivativeNatExpConstant ell (p + r)
  have hpr : 0 < p + r := by omega
  have hfac : (0 : ℝ) < N.factorial := by positivity
  have hC : 0 ≤ C := by
    have hbound := abs_thetaCuspTailDerivative_le_nat_exp_neg ell (p + r)
      (x := 0) (by norm_num : (0 : ℝ) ≤ 0)
    have hbound' : |thetaCuspTailDerivative ell 0| ≤ C := by
      simpa only [C, mul_zero, neg_zero, Real.exp_zero, mul_one] using hbound
    exact (abs_nonneg _).trans hbound'
  have hmajorInt : IntegrableOn (fun x : ℝ =>
      (C * ((r : ℝ) ^ N / N.factorial) * Real.exp ((r : ℝ) * a)) *
        ((x + a) ^ N * Real.exp (-(p : ℝ) * x))) (Ioi 0) :=
    (test_integrable_shifted_pow N p hp a).const_mul _
  have hminorMeas : AEStronglyMeasurable
      (fun x : ℝ => |thetaCuspTailDerivative ell x| *
        ((((r : ℝ) * (x + a)) ^ N / N.factorial) *
          Real.exp ((r : ℝ) * (x + a))))
      (volume.restrict (Ioi 0)) := by
    exact (((differentiable_thetaCuspTailDerivative ell).continuous.abs).mul
      (((continuous_const.mul (continuous_id.add continuous_const)).pow N).div_const _ |>.mul
        (Real.continuous_exp.comp
          (continuous_const.mul (continuous_id.add continuous_const))))).aestronglyMeasurable.restrict
  have hpoint (x : ℝ) (hx0 : 0 ≤ x) :
      |thetaCuspTailDerivative ell x| *
          ((((r : ℝ) * (x + a)) ^ N / N.factorial) *
            Real.exp ((r : ℝ) * (x + a))) ≤
        (C * ((r : ℝ) ^ N / N.factorial) * Real.exp ((r : ℝ) * a)) *
          ((x + a) ^ N * Real.exp (-(p : ℝ) * x)) := by
    have htail := abs_thetaCuspTailDerivative_le_nat_exp_neg ell (p + r) hx0
    have hexpcombine :
        Real.exp (-((p + r : ℕ) : ℝ) * x) *
            Real.exp ((r : ℝ) * (x + a)) =
          Real.exp ((r : ℝ) * a) * Real.exp (-(p : ℝ) * x) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      push_cast
      ring
    calc
      |thetaCuspTailDerivative ell x| *
          ((((r : ℝ) * (x + a)) ^ N / N.factorial) *
            Real.exp ((r : ℝ) * (x + a))) ≤
        (C * Real.exp (-((p + r : ℕ) : ℝ) * x)) *
          ((((r : ℝ) * (x + a)) ^ N / N.factorial) *
            Real.exp ((r : ℝ) * (x + a))) := by gcongr
      _ = (C * ((r : ℝ) ^ N / N.factorial) * Real.exp ((r : ℝ) * a)) *
          ((x + a) ^ N * Real.exp (-(p : ℝ) * x)) := by
        rw [mul_pow]
        calc
          _ = C * ((r : ℝ) ^ N / N.factorial) * (x + a) ^ N *
              (Real.exp (-((p + r : ℕ) : ℝ) * x) *
                Real.exp ((r : ℝ) * (x + a))) := by ring
          _ = _ := by rw [hexpcombine]; ring
  have hminorInt : IntegrableOn
      (fun x : ℝ => |thetaCuspTailDerivative ell x| *
        ((((r : ℝ) * (x + a)) ^ N / N.factorial) *
          Real.exp ((r : ℝ) * (x + a)))) (Ioi 0) := by
    apply hmajorInt.mono' hminorMeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := hx.le
    have hxa : 0 ≤ x + a := add_nonneg hx0 ha
    have hminor0 : 0 ≤ |thetaCuspTailDerivative ell x| *
        ((((r : ℝ) * (x + a)) ^ N / N.factorial) *
          Real.exp ((r : ℝ) * (x + a))) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hminor0]
    exact hpoint x hx0
  calc
    (∫ x : ℝ in Ioi 0,
      |thetaCuspTailDerivative ell x| *
        ((((r : ℝ) * (x + a)) ^ N / N.factorial) *
          Real.exp ((r : ℝ) * (x + a)))) ≤
      ∫ x : ℝ in Ioi 0,
        (C * ((r : ℝ) ^ N / N.factorial) * Real.exp ((r : ℝ) * a)) *
          ((x + a) ^ N * Real.exp (-(p : ℝ) * x)) := by
      apply MeasureTheory.integral_mono_ae hminorInt hmajorInt
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hpoint x hx.le
    _ = (C * ((r : ℝ) ^ N / N.factorial) * Real.exp ((r : ℝ) * a)) *
        (∫ x : ℝ in Ioi 0, (x + a) ^ N * Real.exp (-(p : ℝ) * x)) := by
      rw [integral_const_mul]
    _ ≤ (C * ((r : ℝ) ^ N / N.factorial) * Real.exp ((r : ℝ) * a)) *
        ((N.factorial / (p : ℝ) ^ (N + 1)) * Real.exp ((p : ℝ) * a)) := by
      have hI : (∫ x : ℝ in Ioi 0,
          (x + a) ^ N * Real.exp (-(p : ℝ) * x)) ≤
          (N.factorial / (p : ℝ) ^ (N + 1)) * Real.exp ((p : ℝ) * a) := by
        rw [test_integral_shifted_pow N p hp a]
        exact test_shifted_moment_sum_le N p hp ha
      have hcoef : 0 ≤ C * ((r : ℝ) ^ N / N.factorial) *
          Real.exp ((r : ℝ) * a) := by positivity
      exact mul_le_mul_of_nonneg_left hI hcoef
    _ = thetaCuspTailDerivativeNatExpConstant ell (p + r) *
        ((r : ℝ) ^ N / (p : ℝ) ^ (N + 1)) *
          Real.exp (((p + r : ℕ) : ℝ) * a) := by
      dsimp [C]
      have hexpa : Real.exp ((r : ℝ) * a) * Real.exp ((p : ℝ) * a) =
          Real.exp (((p + r : ℕ) : ℝ) * a) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      have hpR : (p : ℝ) ≠ 0 := by positivity
      calc
        _ = thetaCuspTailDerivativeNatExpConstant ell (p + r) *
            ((r : ℝ) ^ N / (p : ℝ) ^ (N + 1)) *
              (Real.exp ((r : ℝ) * a) * Real.exp ((p : ℝ) * a)) := by
          field_simp
        _ = _ := by rw [hexpa]

theorem test_pointwise_edge_envelope
    (d R : ℕ) (x a : ℝ) (z : ℂ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hz : ‖z‖ ≤ R) :
    ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖ ≤
      3 * (((R : ℝ) * (x + a)) ^ (2 * d + 1) / (2 * d + 1).factorial *
        Real.exp ((R : ℝ) * (x + a))) := by
  let N : ℕ := 2 * d + 1
  let rx : ℝ := ‖(x : ℂ) * I * z‖
  let ra : ℝ := ‖(a : ℂ) * I * z‖
  let rs : ℝ := ‖((x + a : ℝ) : ℂ) * I * z‖
  let B : ℝ := (R : ℝ) * (x + a)
  have hxa : 0 ≤ x + a := add_nonneg hx ha
  have hR : 0 ≤ (R : ℝ) := Nat.cast_nonneg _
  have hB : 0 ≤ B := mul_nonneg hR hxa
  have hrx : rx = x * ‖z‖ := by simp [rx, abs_of_nonneg hx]
  have hra : ra = a * ‖z‖ := by simp [ra, abs_of_nonneg ha]
  have hrs : rs = (x + a) * ‖z‖ := by
    simp only [rs, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I,
      mul_one, abs_of_nonneg hxa]
  have hrsle : rs ≤ B := by
    rw [hrs]
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_left hz hxa]
  have hrxle : rx ≤ B := by
    rw [hrx]
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_left hz hx]
  have hrale : ra ≤ B := by
    rw [hra]
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_left hz ha]
  have hsumle : rx + ra ≤ B := by
    rw [hrx, hra]
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_left hz hxa]
  have htermX :
      (rx ^ N / N.factorial) * Real.exp rx * Real.exp ra ≤
        (B ^ N / N.factorial) * Real.exp B := by
    rw [show (rx ^ N / N.factorial) * Real.exp rx * Real.exp ra =
      (rx ^ N / N.factorial) * Real.exp (rx + ra) by rw [Real.exp_add]; ring]
    gcongr
  have htermA :
      Real.exp rx * ((ra ^ N / N.factorial) * Real.exp ra) ≤
        (B ^ N / N.factorial) * Real.exp B := by
    rw [show Real.exp rx * ((ra ^ N / N.factorial) * Real.exp ra) =
      (ra ^ N / N.factorial) * Real.exp (rx + ra) by rw [Real.exp_add]; ring]
    gcongr
  have htermS :
      (rs ^ N / N.factorial) * Real.exp rs ≤
        (B ^ N / N.factorial) * Real.exp B := by
    gcongr
  have h := norm_eval_finitePositivePhaseTranslationTopEdge_le d x a z
  change ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖ ≤
      (rx ^ N / N.factorial) * Real.exp rx * Real.exp ra +
        Real.exp rx * ((ra ^ N / N.factorial) * Real.exp ra) +
        (rs ^ N / N.factorial) * Real.exp rs at h
  change ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖ ≤
      3 * (B ^ N / N.factorial * Real.exp B)
  nlinarith

theorem test_succ_factorial_envelope_eq (N : ℕ) (B : ℝ) :
    B * (B ^ N / N.factorial) =
      (N + 1) * (B ^ (N + 1) / (N + 1).factorial) := by
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  rw [pow_succ]
  ring

theorem test_continuous_phase_eval (d : ℕ) (z : ℂ) : Continuous (fun x : ℝ =>
    (finitePositivePhasePolynomial d x).eval z) := by
  have h : Continuous (fun x : ℝ =>
      ∑ m ∈ Finset.range (2 * d + 1),
        (((x : ℂ) * I * z) ^ m) / m.factorial) := by fun_prop
  convert h using 1
  funext x
  exact eval_finitePositivePhasePolynomial_eq_sum d z x

theorem test_continuous_edge_eval (d : ℕ) (a : ℝ) (z : ℂ) : Continuous (fun x : ℝ =>
    (finitePositivePhaseTranslationTopEdge d x a).eval z) := by
  have hphase := test_continuous_phase_eval d z
  have h : Continuous (fun x : ℝ =>
      (finitePositivePhasePolynomial d x).eval z *
          (finitePositivePhasePolynomial d a).eval z -
        (finitePositivePhasePolynomial d (x + a)).eval z) :=
    (hphase.mul continuous_const).sub
      (hphase.comp (continuous_id.add continuous_const))
  convert h using 1
  funext x
  exact eval_finitePositivePhaseTranslationTopEdge d x a z

theorem test_continuous_phase_derivative_eval (d : ℕ) (z : ℂ) : Continuous (fun x : ℝ =>
    (finitePositivePhasePolynomial d x).derivative.eval z) := by
  have h : Continuous (fun x : ℝ =>
      ((x : ℂ) * I) * ∑ m ∈ Finset.range (2 * d),
        (((x : ℂ) * I * z) ^ m) / m.factorial) := by fun_prop
  convert h using 1
  funext x
  exact eval_derivative_finitePositivePhasePolynomial_eq_sum d z x

theorem test_continuous_edge_derivative_eval (d : ℕ) (a : ℝ) (z : ℂ) :
    Continuous (fun x : ℝ =>
      (finitePositivePhaseTranslationTopEdge d x a).derivative.eval z) := by
  have hphase := test_continuous_phase_eval d z
  have hderiv := test_continuous_phase_derivative_eval d z
  have h : Continuous (fun x : ℝ =>
      (finitePositivePhasePolynomial d x).derivative.eval z *
          (finitePositivePhasePolynomial d a).eval z +
        (finitePositivePhasePolynomial d x).eval z *
          (finitePositivePhasePolynomial d a).derivative.eval z -
        (finitePositivePhasePolynomial d (x + a)).derivative.eval z) :=
    ((hderiv.mul continuous_const).add (hphase.mul continuous_const)).sub
      (hderiv.comp (continuous_id.add continuous_const))
  convert h using 1
  funext x
  exact eval_derivative_finitePositivePhaseTranslationTopEdge d x a z

theorem test_pointwise_edge_derivative_envelope
    (d R : ℕ) (x a : ℝ) (z : ℂ)
    (hRone : 1 ≤ R) (hx : 0 ≤ x) (ha : 0 ≤ a) (hz : ‖z‖ ≤ R) :
    ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖ ≤
      3 * (2 * d + 1 : ℕ) *
          ((((R : ℝ) * (x + a)) ^ (2 * d + 1) / (2 * d + 1).factorial) *
            Real.exp ((R : ℝ) * (x + a))) +
        2 * (2 * d + 2 : ℕ) *
          ((((R : ℝ) * (x + a)) ^ (2 * d + 2) / (2 * d + 2).factorial) *
            Real.exp ((R : ℝ) * (x + a))) := by
  let M : ℕ := 2 * d
  let N : ℕ := M + 1
  let rx : ℝ := ‖(x : ℂ) * I * z‖
  let ra : ℝ := ‖(a : ℂ) * I * z‖
  let rs : ℝ := ‖((x + a : ℝ) : ℂ) * I * z‖
  let cx : ℝ := ‖(x : ℂ) * I‖
  let ca : ℝ := ‖(a : ℂ) * I‖
  let cs : ℝ := ‖((x + a : ℝ) : ℂ) * I‖
  let B : ℝ := (R : ℝ) * (x + a)
  let EN : ℝ := (B ^ N / N.factorial) * Real.exp B
  let EN1 : ℝ := (B ^ (N + 1) / (N + 1).factorial) * Real.exp B
  have hxa : 0 ≤ x + a := add_nonneg hx ha
  have hR : (1 : ℝ) ≤ R := by exact_mod_cast hRone
  have hB : 0 ≤ B := mul_nonneg (by positivity) hxa
  have hrx : rx = x * ‖z‖ := by simp [rx, abs_of_nonneg hx]
  have hra : ra = a * ‖z‖ := by simp [ra, abs_of_nonneg ha]
  have hrs : rs = (x + a) * ‖z‖ := by
    simp only [rs, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I,
      mul_one, abs_of_nonneg hxa]
  have hcx : cx = x := by simp [cx, abs_of_nonneg hx]
  have hca : ca = a := by simp [ca, abs_of_nonneg ha]
  have hcs : cs = x + a := by
    simp only [cs, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I,
      mul_one, abs_of_nonneg hxa]
  have hrsle : rs ≤ B := by
    rw [hrs]
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_left hz hxa]
  have hrxle : rx ≤ B := by
    rw [hrx]
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_left hz hx]
  have hrale : ra ≤ B := by
    rw [hra]
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_left hz ha]
  have hsumle : rx + ra ≤ B := by
    rw [hrx, hra]
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_left hz hxa]
  have hcxle : cx ≤ B := by
    rw [hcx]
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_right hR hxa]
  have hcale : ca ≤ B := by
    rw [hca]
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_right hR hxa]
  have hcsle : cs ≤ B := by
    rw [hcs]
    dsimp [B]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hR hxa
  have hMN : N = 2 * d + 1 := by dsimp [N, M]
  have hderX :
      (cx * ((rx ^ M / M.factorial) * Real.exp rx)) * Real.exp ra ≤
        N * EN := by
    rw [show (cx * ((rx ^ M / M.factorial) * Real.exp rx)) * Real.exp ra =
      cx * (rx ^ M / M.factorial) * Real.exp (rx + ra) by rw [Real.exp_add]; ring]
    calc
      _ ≤ B * (B ^ M / M.factorial) * Real.exp B := by gcongr
      _ = N * EN := by
        dsimp [EN, N]
        rw [Nat.factorial_succ]
        push_cast
        field_simp
        ring
  have hderA :
      Real.exp rx * (ca * ((ra ^ M / M.factorial) * Real.exp ra)) ≤
        N * EN := by
    rw [show Real.exp rx * (ca * ((ra ^ M / M.factorial) * Real.exp ra)) =
      ca * (ra ^ M / M.factorial) * Real.exp (rx + ra) by rw [Real.exp_add]; ring]
    calc
      _ ≤ B * (B ^ M / M.factorial) * Real.exp B := by gcongr
      _ = N * EN := by
        dsimp [EN, N]
        rw [Nat.factorial_succ]
        push_cast
        field_simp
        ring
  have hderS :
      cs * ((rs ^ M / M.factorial) * Real.exp rs) ≤ N * EN := by
    have htailS : (rs ^ M / M.factorial) * Real.exp rs ≤
        (B ^ M / M.factorial) * Real.exp B := by gcongr
    calc
      _ ≤ B * ((B ^ M / M.factorial) * Real.exp B) :=
        mul_le_mul hcsle htailS (by positivity) hB
      _ = B * (B ^ M / M.factorial) * Real.exp B := by ring
      _ = N * EN := by
        dsimp [EN, N]
        rw [Nat.factorial_succ]
        push_cast
        field_simp
        ring
  have hvalA :
      cx * Real.exp rx * ((ra ^ N / N.factorial) * Real.exp ra) ≤
        (N + 1) * EN1 := by
    rw [show cx * Real.exp rx * ((ra ^ N / N.factorial) * Real.exp ra) =
      cx * (ra ^ N / N.factorial) * Real.exp (rx + ra) by rw [Real.exp_add]; ring]
    calc
      _ ≤ B * (B ^ N / N.factorial) * Real.exp B := by gcongr
      _ = (N + 1) * EN1 := by
        dsimp only [EN1]
        rw [← mul_assoc, test_succ_factorial_envelope_eq]
  have hvalX :
      ((rx ^ N / N.factorial) * Real.exp rx) *
          (ca * Real.exp ra) ≤ (N + 1) * EN1 := by
    rw [show ((rx ^ N / N.factorial) * Real.exp rx) *
        (ca * Real.exp ra) =
      ca * (rx ^ N / N.factorial) * Real.exp (rx + ra) by rw [Real.exp_add]; ring]
    calc
      _ ≤ B * (B ^ N / N.factorial) * Real.exp B := by gcongr
      _ = (N + 1) * EN1 := by
        dsimp only [EN1]
        rw [← mul_assoc, test_succ_factorial_envelope_eq]
  have h := norm_eval_derivative_finitePositivePhaseTranslationTopEdge_le d x a z
  change ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖ ≤
      (cx * ((rx ^ M / M.factorial) * Real.exp rx)) * Real.exp ra +
        cx * Real.exp rx * ((ra ^ N / N.factorial) * Real.exp ra) +
        ((rx ^ N / N.factorial) * Real.exp rx) * (ca * Real.exp ra) +
        Real.exp rx * (ca * ((ra ^ M / M.factorial) * Real.exp ra)) +
        cs * ((rs ^ M / M.factorial) * Real.exp rs) at h
  have hcomb : ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖ ≤
      3 * N * EN + 2 * (N + 1) * EN1 := by nlinarith
  calc
    _ ≤ 3 * N * EN + 2 * (N + 1) * EN1 := hcomb
    _ = _ := by
      dsimp only [EN, EN1, B]
      rw [hMN]
      push_cast
      ring

theorem test_integrable_shifted_factorial_source_envelope
    (ell N p r : ℕ) (hp : 0 < p) {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun x : ℝ =>
      |thetaCuspTailDerivative ell x| *
        ((((r : ℝ) * (x + a)) ^ N / N.factorial) *
          Real.exp ((r : ℝ) * (x + a)))) (Ioi 0) := by
  let C : ℝ := thetaCuspTailDerivativeNatExpConstant ell (p + r)
  have hC : 0 ≤ C := by
    have hbound := abs_thetaCuspTailDerivative_le_nat_exp_neg ell (p + r)
      (x := 0) (by norm_num : (0 : ℝ) ≤ 0)
    have hbound' : |thetaCuspTailDerivative ell 0| ≤ C := by
      simpa only [C, mul_zero, neg_zero, Real.exp_zero, mul_one] using hbound
    exact (abs_nonneg _).trans hbound'
  have hmajorInt : IntegrableOn (fun x : ℝ =>
      (C * ((r : ℝ) ^ N / N.factorial) * Real.exp ((r : ℝ) * a)) *
        ((x + a) ^ N * Real.exp (-(p : ℝ) * x))) (Ioi 0) :=
    (test_integrable_shifted_pow N p hp a).const_mul _
  have hminorMeas : AEStronglyMeasurable
      (fun x : ℝ => |thetaCuspTailDerivative ell x| *
        ((((r : ℝ) * (x + a)) ^ N / N.factorial) *
          Real.exp ((r : ℝ) * (x + a))))
      (volume.restrict (Ioi 0)) := by
    exact (((differentiable_thetaCuspTailDerivative ell).continuous.abs).mul
      (((continuous_const.mul (continuous_id.add continuous_const)).pow N).div_const _ |>.mul
        (Real.continuous_exp.comp
          (continuous_const.mul (continuous_id.add continuous_const))))).aestronglyMeasurable.restrict
  apply hmajorInt.mono' hminorMeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := hx.le
  have hxa : 0 ≤ x + a := add_nonneg hx0 ha
  have htail := abs_thetaCuspTailDerivative_le_nat_exp_neg ell (p + r) hx0
  have hexpcombine :
      Real.exp (-((p + r : ℕ) : ℝ) * x) *
          Real.exp ((r : ℝ) * (x + a)) =
        Real.exp ((r : ℝ) * a) * Real.exp (-(p : ℝ) * x) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hpoint :
      |thetaCuspTailDerivative ell x| *
          ((((r : ℝ) * (x + a)) ^ N / N.factorial) *
            Real.exp ((r : ℝ) * (x + a))) ≤
        (C * ((r : ℝ) ^ N / N.factorial) * Real.exp ((r : ℝ) * a)) *
          ((x + a) ^ N * Real.exp (-(p : ℝ) * x)) := by
    calc
      |thetaCuspTailDerivative ell x| *
          ((((r : ℝ) * (x + a)) ^ N / N.factorial) *
            Real.exp ((r : ℝ) * (x + a))) ≤
        (C * Real.exp (-((p + r : ℕ) : ℝ) * x)) *
          ((((r : ℝ) * (x + a)) ^ N / N.factorial) *
            Real.exp ((r : ℝ) * (x + a))) := by gcongr
      _ = (C * ((r : ℝ) ^ N / N.factorial) * Real.exp ((r : ℝ) * a)) *
          ((x + a) ^ N * Real.exp (-(p : ℝ) * x)) := by
        rw [mul_pow]
        calc
          _ = C * ((r : ℝ) ^ N / N.factorial) * (x + a) ^ N *
              (Real.exp (-((p + r : ℕ) : ℝ) * x) *
                Real.exp ((r : ℝ) * (x + a))) := by ring
          _ = _ := by rw [hexpcombine]; ring
  have hminor0 : 0 ≤ |thetaCuspTailDerivative ell x| *
      ((((r : ℝ) * (x + a)) ^ N / N.factorial) *
        Real.exp ((r : ℝ) * (x + a))) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hminor0]
  exact hpoint

theorem test_integral_density_mul_edge_norm_le
    (d R p : ℕ) (hp : 0 < p) {a : ℝ} (ha : 0 ≤ a)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    (∫ x : ℝ in Ioi 0,
      |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖) ≤
      12 * thetaCuspTailDerivativeNatExpConstant 2 (p + R) *
        ((R : ℝ) ^ (2 * d + 1) / (p : ℝ) ^ (2 * d + 2)) *
          Real.exp (((p + R : ℕ) : ℝ) * a) := by
  let N : ℕ := 2 * d + 1
  let E : ℝ → ℝ := fun x =>
    (((R : ℝ) * (x + a)) ^ N / N.factorial) *
      Real.exp ((R : ℝ) * (x + a))
  have hEnvInt : IntegrableOn (fun x : ℝ =>
      |thetaCuspTailDerivative 2 x| * E x) (Ioi 0) := by
    simpa only [E, N] using
      test_integrable_shifted_factorial_source_envelope 2 N p R hp ha
  have hmajorInt : IntegrableOn (fun x : ℝ =>
      12 * (|thetaCuspTailDerivative 2 x| * E x)) (Ioi 0) :=
    hEnvInt.const_mul 12
  have hedgeCont := test_continuous_edge_eval d a z
  have hminorMeas : AEStronglyMeasurable (fun x : ℝ =>
      |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖)
      (volume.restrict (Ioi 0)) := by
    exact ((((differentiable_thetaCuspTailDerivative 2).continuous.const_mul 4).abs).mul
      hedgeCont.norm).aestronglyMeasurable.restrict
  have hminorInt : IntegrableOn (fun x : ℝ =>
      |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖) (Ioi 0) := by
    apply hmajorInt.mono' hminorMeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := hx.le
    have hedge := test_pointwise_edge_envelope d R x a z hx0 ha hz
    have hrho : |thetaCuspTailSecondDensity x| =
        4 * |thetaCuspTailDerivative 2 x| := by
      simp [thetaCuspTailSecondDensity, abs_mul]
    have hnon : 0 ≤ |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖ := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnon, hrho]
    change 4 * |thetaCuspTailDerivative 2 x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖ ≤
      12 * (|thetaCuspTailDerivative 2 x| * E x)
    change ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖ ≤ 3 * E x at hedge
    nlinarith [abs_nonneg (thetaCuspTailDerivative 2 x)]
  calc
    (∫ x : ℝ in Ioi 0,
      |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖) ≤
      ∫ x : ℝ in Ioi 0,
        12 * (|thetaCuspTailDerivative 2 x| * E x) := by
      apply MeasureTheory.integral_mono_ae hminorInt hmajorInt
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 ≤ x := hx.le
      have hedge := test_pointwise_edge_envelope d R x a z hx0 ha hz
      have hrho : |thetaCuspTailSecondDensity x| =
          4 * |thetaCuspTailDerivative 2 x| := by
        simp [thetaCuspTailSecondDensity, abs_mul]
      rw [hrho]
      change 4 * |thetaCuspTailDerivative 2 x| *
          ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖ ≤
        12 * (|thetaCuspTailDerivative 2 x| * E x)
      change ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖ ≤ 3 * E x at hedge
      nlinarith [abs_nonneg (thetaCuspTailDerivative 2 x)]
    _ = 12 * (∫ x : ℝ in Ioi 0,
        |thetaCuspTailDerivative 2 x| * E x) := by rw [integral_const_mul]
    _ ≤ 12 * (thetaCuspTailDerivativeNatExpConstant 2 (p + R) *
        ((R : ℝ) ^ N / (p : ℝ) ^ (N + 1)) *
          Real.exp (((p + R : ℕ) : ℝ) * a)) := by
      gcongr
      simpa only [E] using test_shifted_factorial_envelope 2 N p R hp ha
    _ = _ := by dsimp [N]; ring

theorem test_integral_density_mul_edge_derivative_norm_le
    (d R p : ℕ) (hRone : 1 ≤ R) (hp : 0 < p) {a : ℝ} (ha : 0 ≤ a)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    (∫ x : ℝ in Ioi 0,
      |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖) ≤
      12 * (2 * d + 1 : ℕ) *
          (thetaCuspTailDerivativeNatExpConstant 2 (p + R) *
            ((R : ℝ) ^ (2 * d + 1) / (p : ℝ) ^ (2 * d + 2)) *
              Real.exp (((p + R : ℕ) : ℝ) * a)) +
        8 * (2 * d + 2 : ℕ) *
          (thetaCuspTailDerivativeNatExpConstant 2 (p + R) *
            ((R : ℝ) ^ (2 * d + 2) / (p : ℝ) ^ (2 * d + 3)) *
              Real.exp (((p + R : ℕ) : ℝ) * a)) := by
  let N : ℕ := 2 * d + 1
  let N1 : ℕ := 2 * d + 2
  let E : ℕ → ℝ → ℝ := fun m x =>
    (((R : ℝ) * (x + a)) ^ m / m.factorial) *
      Real.exp ((R : ℝ) * (x + a))
  let A : ℝ := 12 * N
  let B : ℝ := 8 * N1
  let fN : ℝ → ℝ := fun x => |thetaCuspTailDerivative 2 x| * E N x
  let fN1 : ℝ → ℝ := fun x => |thetaCuspTailDerivative 2 x| * E N1 x
  let major : ℝ → ℝ := fun x => A * fN x + B * fN1 x
  have hNInt : IntegrableOn fN (Ioi 0) := by
    simpa only [fN, E] using
      test_integrable_shifted_factorial_source_envelope 2 N p R hp ha
  have hN1Int : IntegrableOn fN1 (Ioi 0) := by
    simpa only [fN1, E] using
      test_integrable_shifted_factorial_source_envelope 2 N1 p R hp ha
  have hmajorInt : IntegrableOn major (Ioi 0) :=
    (hNInt.const_mul A).add (hN1Int.const_mul B)
  have hedgeCont := test_continuous_edge_derivative_eval d a z
  have hminorMeas : AEStronglyMeasurable (fun x : ℝ =>
      |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖)
      (volume.restrict (Ioi 0)) := by
    exact ((((differentiable_thetaCuspTailDerivative 2).continuous.const_mul 4).abs).mul
      hedgeCont.norm).aestronglyMeasurable.restrict
  have hpoint (x : ℝ) (hx0 : 0 ≤ x) :
      |thetaCuspTailSecondDensity x| *
          ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖ ≤
        major x := by
    have hedge := test_pointwise_edge_derivative_envelope d R x a z hRone hx0 ha hz
    have hrho : |thetaCuspTailSecondDensity x| =
        4 * |thetaCuspTailDerivative 2 x| := by
      simp [thetaCuspTailSecondDensity, abs_mul]
    rw [hrho]
    change 4 * |thetaCuspTailDerivative 2 x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖ ≤
      A * fN x + B * fN1 x
    have hedge' : ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖ ≤
        3 * N * E N x + 2 * N1 * E N1 x := by
      simpa only [N, N1, E] using hedge
    dsimp only [major, A, B, fN, fN1]
    nlinarith [hedge', abs_nonneg (thetaCuspTailDerivative 2 x)]
  have hminorInt : IntegrableOn (fun x : ℝ =>
      |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖) (Ioi 0) := by
    apply hmajorInt.mono' hminorMeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hnon : 0 ≤ |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖ := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnon]
    exact hpoint x hx.le
  have hNBound : (∫ x : ℝ in Ioi 0, fN x) ≤
      thetaCuspTailDerivativeNatExpConstant 2 (p + R) *
        ((R : ℝ) ^ N / (p : ℝ) ^ (N + 1)) *
          Real.exp (((p + R : ℕ) : ℝ) * a) := by
    simpa only [fN, E] using test_shifted_factorial_envelope 2 N p R hp ha
  have hN1Bound : (∫ x : ℝ in Ioi 0, fN1 x) ≤
      thetaCuspTailDerivativeNatExpConstant 2 (p + R) *
        ((R : ℝ) ^ N1 / (p : ℝ) ^ (N1 + 1)) *
          Real.exp (((p + R : ℕ) : ℝ) * a) := by
    simpa only [fN1, E] using test_shifted_factorial_envelope 2 N1 p R hp ha
  calc
    (∫ x : ℝ in Ioi 0,
      |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖) ≤
      ∫ x : ℝ in Ioi 0, major x := by
      apply MeasureTheory.integral_mono_ae hminorInt hmajorInt
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hpoint x hx.le
    _ = A * (∫ x : ℝ in Ioi 0, fN x) +
        B * (∫ x : ℝ in Ioi 0, fN1 x) := by
      dsimp only [major]
      rw [integral_add (hNInt.const_mul A) (hN1Int.const_mul B),
        integral_const_mul, integral_const_mul]
    _ ≤ A * (thetaCuspTailDerivativeNatExpConstant 2 (p + R) *
          ((R : ℝ) ^ N / (p : ℝ) ^ (N + 1)) *
            Real.exp (((p + R : ℕ) : ℝ) * a)) +
        B * (thetaCuspTailDerivativeNatExpConstant 2 (p + R) *
          ((R : ℝ) ^ N1 / (p : ℝ) ^ (N1 + 1)) *
            Real.exp (((p + R : ℕ) : ℝ) * a)) := by
      gcongr
    _ = _ := by
      dsimp only [A, B]

end

end RHTower

import GaloisForLFunctions.RHTower.SuzukiExplicitScrewZeroSeries
import GaloisForLFunctions.RHTower.Sieve.ChebyshevLlPNT
import GaloisForLFunctions.RHTower.ChebyshevPsiScaling
import Mathlib.NumberTheory.AbelSummation

open Filter Topology Set MeasureTheory Asymptotics ArithmeticFunction intervalIntegral
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- Abel weight selecting Suzuki's prime hinge at logarithmic time `t`. -/
def suzukiPrimeAbelWeight (t x : ℝ) : ℝ :=
  (t - Real.log x) / Real.sqrt x

/-- Positive kernel obtained by differentiating Suzuki's Abel weight. -/
def suzukiPrimeAbelKernel (t x : ℝ) : ℝ :=
  (1 + (t - Real.log x) / 2) / (x * Real.sqrt x)

theorem hasDerivAt_suzukiPrimeAbelWeight {t x : ℝ} (hx : 0 < x) :
    HasDerivAt (suzukiPrimeAbelWeight t) (-suzukiPrimeAbelKernel t x) x := by
  have hsqrt : HasDerivAt Real.sqrt ((2 * Real.sqrt x)⁻¹) x :=
    by simpa [one_div] using Real.hasDerivAt_sqrt (ne_of_gt hx)
  have hnum : HasDerivAt (fun y : ℝ => t - Real.log y) (-x⁻¹) x := by
    convert! (hasDerivAt_const x t).sub (Real.hasDerivAt_log (ne_of_gt hx)) using 1
    ring
  have h := hnum.div hsqrt (ne_of_gt (Real.sqrt_pos.2 hx))
  have hcoef :
      (-x⁻¹ * Real.sqrt x - (t - Real.log x) * (2 * Real.sqrt x)⁻¹) /
          Real.sqrt x ^ 2 = -suzukiPrimeAbelKernel t x := by
    unfold suzukiPrimeAbelKernel
    have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
    have hs2 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.le
    field_simp
    rw [hs2]
    ring
  change HasDerivAt (fun y : ℝ => (t - Real.log y) / Real.sqrt y)
    (-suzukiPrimeAbelKernel t x) x
  rw [← hcoef]
  exact h

theorem deriv_suzukiPrimeAbelWeight {t x : ℝ} (hx : 0 < x) :
    deriv (suzukiPrimeAbelWeight t) x = -suzukiPrimeAbelKernel t x :=
  (hasDerivAt_suzukiPrimeAbelWeight hx).deriv

theorem continuousOn_suzukiPrimeAbelKernel {t a b : ℝ} (ha : 0 < a) :
    ContinuousOn (suzukiPrimeAbelKernel t) (Icc a b) := by
  intro x hx
  unfold suzukiPrimeAbelKernel
  have hx0 : 0 < x := ha.trans_le hx.1
  exact (continuousAt_const.add
      ((continuousAt_const.sub (Real.continuousAt_log hx0.ne')).div_const 2)).div
    (continuousAt_id.mul Real.continuous_sqrt.continuousAt)
      (mul_ne_zero hx0.ne' (Real.sqrt_pos.2 hx0).ne') |>.continuousWithinAt

theorem integrableOn_deriv_suzukiPrimeAbelWeight {t b : ℝ} :
    IntegrableOn (deriv (suzukiPrimeAbelWeight t)) (Icc 2 b) := by
  have hcont : ContinuousOn (fun x => -suzukiPrimeAbelKernel t x) (Icc 2 b) :=
    (continuousOn_suzukiPrimeAbelKernel (t := t) (b := b) (by norm_num)).neg
  refine hcont.integrableOn_Icc.congr_fun (fun x hx => ?_) measurableSet_Icc
  exact (deriv_suzukiPrimeAbelWeight (t := t) (by linarith [hx.1])).symm

theorem suzukiPrimeAbelWeight_exp_self (t : ℝ) :
    suzukiPrimeAbelWeight t (Real.exp t) = 0 := by
  simp [suzukiPrimeAbelWeight]

theorem suzukiPrimeAbelWeight_nat_mul_vonMangoldt (t : ℝ) (n : ℕ) :
    suzukiPrimeAbelWeight t n * (vonMangoldt n : ℝ) =
      screwPrimeWeight n * (t - Real.log n) := by
  rw [suzukiPrimeAbelWeight, screwPrimeWeight]
  ring

/-- Exact finite Abel identity behind Suzuki 2022, Proposition 2.1. -/
theorem screwPrimeSum_eq_integral_chebyshevPsi_kernel {t : ℝ} (ht : Real.log 2 ≤ t) :
    screwPrimeSum t =
      ∫ x : ℝ in Ioc 2 (Real.exp t),
        suzukiPrimeAbelKernel t x * Chebyshev.psi x := by
  have h2exp : (2 : ℝ) ≤ Real.exp t := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr ht
  have habel := sum_mul_eq_sub_integral_mul₁ (𝕜 := ℝ)
    (fun n : ℕ => (vonMangoldt n : ℝ)) (by simp) (by simp)
    (b := Real.exp t) (f := suzukiPrimeAbelWeight t)
    (fun x hx => (hasDerivAt_suzukiPrimeAbelWeight (by linarith [hx.1])).differentiableAt)
    integrableOn_deriv_suzukiPrimeAbelWeight
  rw [suzukiPrimeAbelWeight_exp_self, zero_mul, zero_sub,
    show (∑ k ∈ Finset.Icc 0 ⌊Real.exp t⌋₊,
        suzukiPrimeAbelWeight t k * (vonMangoldt k : ℝ)) = screwPrimeSum t by
      rw [screwPrimeSum]
      calc
        _ = ∑ n ∈ Finset.Icc 0 ⌊Real.exp t⌋₊,
            screwPrimeWeight n * (t - Real.log n) := by
          exact Finset.sum_congr rfl fun n _ =>
            suzukiPrimeAbelWeight_nat_mul_vonMangoldt t n
        _ = ∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊,
            screwPrimeWeight n * (t - Real.log n) := by
          symm
          apply Finset.sum_subset (by
            intro n hn
            exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_Icc.mp hn).2⟩)
          intro n hn hnot
          have hnlt : n < 2 := by
            by_contra h
            exact hnot (Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hn).2⟩)
          interval_cases n <;> simp [screwPrimeWeight]
      ] at habel
  rw [habel, ← MeasureTheory.integral_neg]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [deriv_suzukiPrimeAbelWeight (by linarith [hx.1]), Chebyshev.psi_eq_sum_Icc]
  ring

/-- Primitive of the main term in Suzuki's Abel integral. -/
def suzukiPrimeMainPrimitive (t x : ℝ) : ℝ :=
  Real.sqrt x * (4 + t - Real.log x)

theorem hasDerivAt_suzukiPrimeMainPrimitive {t x : ℝ} (hx : 0 < x) :
    HasDerivAt (suzukiPrimeMainPrimitive t)
      (suzukiPrimeAbelKernel t x * x) x := by
  have hsqrt := Real.hasDerivAt_sqrt (ne_of_gt hx)
  have hlin : HasDerivAt (fun y : ℝ => 4 + t - Real.log y) (-x⁻¹) x := by
    convert! (hasDerivAt_const x (4 + t)).sub (Real.hasDerivAt_log (ne_of_gt hx)) using 1
    ring
  have h := hsqrt.mul hlin
  have hcoef :
      1 / (2 * Real.sqrt x) * (4 + t - Real.log x) +
          Real.sqrt x * -x⁻¹ = suzukiPrimeAbelKernel t x * x := by
    unfold suzukiPrimeAbelKernel
    have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
    have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
    field_simp
    rw [hs2]
    ring
  change HasDerivAt (fun y : ℝ => Real.sqrt y * (4 + t - Real.log y)) _ x
  rw [← hcoef]
  exact h

theorem intervalIntegral_suzukiPrimeAbelKernel_mul_id {t a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ x : ℝ in a..b, suzukiPrimeAbelKernel t x * x) =
      suzukiPrimeMainPrimitive t b - suzukiPrimeMainPrimitive t a := by
  have hint : IntervalIntegrable (fun x : ℝ => suzukiPrimeAbelKernel t x * x)
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact ((continuousOn_suzukiPrimeAbelKernel (t := t) (a := a) (b := b) ha).mul
      continuousOn_id).congr (fun x _ => rfl)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hasDerivAt_suzukiPrimeMainPrimitive (by
      rw [uIcc_of_le hab] at hx
      exact ha.trans_le hx.1)) hint]

theorem integral_suzukiPrimeAbelKernel_mul_id_general {t b : ℝ} (hb : 2 ≤ b) :
    (∫ x : ℝ in Ioc 2 b, suzukiPrimeAbelKernel t x * x) =
      suzukiPrimeMainPrimitive t b - suzukiPrimeMainPrimitive t 2 := by
  rw [← integral_of_le hb]
  exact intervalIntegral_suzukiPrimeAbelKernel_mul_id (by norm_num) hb

theorem integral_suzukiPrimeAbelKernel_mul_id {t : ℝ} (ht : Real.log 2 ≤ t) :
    (∫ x : ℝ in Ioc 2 (Real.exp t), suzukiPrimeAbelKernel t x * x) =
      4 * Real.exp (t / 2) - Real.sqrt 2 * (4 + t - Real.log 2) := by
  have h2exp : (2 : ℝ) ≤ Real.exp t := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr ht
  rw [integral_suzukiPrimeAbelKernel_mul_id_general h2exp]
  unfold suzukiPrimeMainPrimitive
  rw [Real.log_exp]
  have hsqrt_exp : Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
    have hsq1 : Real.sqrt (Real.exp t) ^ 2 = Real.exp t :=
      Real.sq_sqrt (Real.exp_nonneg t)
    have hsq2 : Real.exp (t / 2) ^ 2 = Real.exp t := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    nlinarith [Real.sqrt_nonneg (Real.exp t), Real.exp_pos (t / 2)]
  rw [hsqrt_exp]
  ring

/-- Chebyshev error in the exact sharp-cutoff normalization used by Suzuki. -/
def suzukiChebyshevError (x : ℝ) : ℝ := Chebyshev.psi x - x

/-- Littlewood's PNT implies the (weaker) de la Vallée Poussin scale used by Suzuki. -/
theorem exists_abs_suzukiChebyshevError_le_sqrtLog :
    ∃ c B : ℝ, 0 < c ∧ 0 ≤ B ∧ ∀ᶠ x : ℝ in atTop,
      |suzukiChebyshevError x| ≤
        B * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨a, B, ha, hB, hrate⟩ :=
    Sieve.exists_abs_sum_vonMangoldt_sub_self_ll_rate
  refine ⟨Real.sqrt a / 48, B, by positivity, hB, ?_⟩
  filter_upwards [hrate, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)] with x hrate hx hlog
  have hlog0 : 0 ≤ Real.log x := (Real.log_pos hx).le
  have hloglog : 1 ≤ Real.log (Real.log x) := by
    rw [Real.le_log_iff_exp_le (Real.log_pos hx)]
    exact hlog
  have hprod : a * Real.log x ≤
      a * Real.log x * Real.log (Real.log x) := by
    nlinarith [mul_nonneg ha.le hlog0]
  have hsqrt : Real.sqrt a * Real.sqrt (Real.log x) ≤
      Real.sqrt (Sieve.chebQuadLl a x) := by
    rw [Sieve.chebQuadLl,
      Real.sqrt_mul ha.le]
    exact mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by nlinarith [hlog0])) (Real.sqrt_nonneg a)
  have hexp :
      Real.exp (-(Real.sqrt (Sieve.chebQuadLl a x) / 48)) ≤
        Real.exp (-(Real.sqrt a / 48) * Real.sqrt (Real.log x)) := by
    rw [Real.exp_le_exp]
    nlinarith
  rw [suzukiChebyshevError, Chebyshev.psi_eq_sum_range]
  exact hrate.trans (mul_le_mul_of_nonneg_left hexp
    (mul_nonneg hB (by linarith : 0 ≤ x)))

/-- Global elementary linear bound for the sharp Chebyshev error. -/
theorem exists_abs_suzukiChebyshevError_le_linear :
    ∃ D : ℝ, 0 < D ∧ ∀ x : ℝ, 1 ≤ x → |suzukiChebyshevError x| ≤ D * x := by
  obtain ⟨C, hC, hpsi⟩ := exists_chebyshevPsiReal_le_linear
  refine ⟨C + 1, by linarith, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have hpsi0 : 0 ≤ Chebyshev.psi x := Chebyshev.psi_nonneg x
  have hident : chebyshevPsiReal x = Chebyshev.psi x := by
    rw [chebyshevPsiReal_eq_sum_range, Chebyshev.psi_eq_sum_range]
  have hupper : Chebyshev.psi x ≤ C * x := by
    rw [← hident]
    exact hpsi x hx
  rw [suzukiChebyshevError]
  calc
    |Chebyshev.psi x - x| ≤ |Chebyshev.psi x| + |x| := abs_sub _ _
    _ = Chebyshev.psi x + x := by rw [abs_of_nonneg hpsi0, abs_of_nonneg hx0]
    _ ≤ C * x + x := by gcongr
    _ = (C + 1) * x := by ring

theorem intervalIntegrable_suzukiChebyshevError {a b : ℝ} :
    IntervalIntegrable suzukiChebyshevError volume a b := by
  have hpsi : IntervalIntegrable Chebyshev.psi volume a b :=
    Chebyshev.psi_mono.intervalIntegrable
  have hid : IntervalIntegrable id volume a b := continuous_id.intervalIntegrable a b
  change IntervalIntegrable (fun x => Chebyshev.psi x - x) volume a b
  exact (hpsi.sub hid).congr (fun x _ => by rfl)

theorem intervalIntegrable_suzukiPrimeErrorIntegrand {t a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable
      (fun x => suzukiPrimeAbelKernel t x * suzukiChebyshevError x) volume a b := by
  apply IntervalIntegrable.continuousOn_mul intervalIntegrable_suzukiChebyshevError
  simpa only [uIcc] using
    continuousOn_suzukiPrimeAbelKernel (t := t) (a := min a b) (b := max a b)
      (lt_min ha hb)

/-- Exact PNT-remainder decomposition of Suzuki's prime hinge. -/
theorem screwPrimeSum_eq_main_add_error {t : ℝ} (ht : Real.log 2 ≤ t) :
    screwPrimeSum t =
      4 * Real.exp (t / 2) - Real.sqrt 2 * (4 + t - Real.log 2) +
        ∫ x : ℝ in Ioc 2 (Real.exp t),
          suzukiPrimeAbelKernel t x * suzukiChebyshevError x := by
  rw [screwPrimeSum_eq_integral_chebyshevPsi_kernel ht]
  have h2exp : (2 : ℝ) ≤ Real.exp t := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr ht
  have hmain : IntegrableOn (fun x : ℝ => suzukiPrimeAbelKernel t x * x)
      (Ioc 2 (Real.exp t)) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le h2exp]
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le h2exp]
    exact ((continuousOn_suzukiPrimeAbelKernel (t := t) (a := 2) (b := Real.exp t)
      (by norm_num)).mul continuousOn_id).congr (fun x _ => rfl)
  have herr : IntegrableOn
      (fun x => suzukiPrimeAbelKernel t x * suzukiChebyshevError x)
      (Ioc 2 (Real.exp t)) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le h2exp]
    exact intervalIntegrable_suzukiPrimeErrorIntegrand (by norm_num) (Real.exp_pos t)
  have hsplit :
      (fun x => suzukiPrimeAbelKernel t x * Chebyshev.psi x) =
        (fun x => suzukiPrimeAbelKernel t x * x +
          suzukiPrimeAbelKernel t x * suzukiChebyshevError x) := by
    funext x
    unfold suzukiChebyshevError
    ring
  rw [hsplit, MeasureTheory.integral_add hmain herr,
    integral_suzukiPrimeAbelKernel_mul_id ht]

theorem sqrt_exp_eq_exp_half (u : ℝ) :
    Real.sqrt (Real.exp u) = Real.exp (u / 2) := by
  have hsq1 : Real.sqrt (Real.exp u) ^ 2 = Real.exp u :=
    Real.sq_sqrt (Real.exp_nonneg u)
  have hsq2 : Real.exp (u / 2) ^ 2 = Real.exp u := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  nlinarith [Real.sqrt_nonneg (Real.exp u), Real.exp_pos (u / 2)]

theorem suzukiPrimeAbelKernel_nonneg {t x : ℝ}
    (hx : 0 < x) (hlog : Real.log x ≤ t) :
    0 ≤ suzukiPrimeAbelKernel t x := by
  unfold suzukiPrimeAbelKernel
  exact div_nonneg (by linarith) (mul_nonneg hx.le (Real.sqrt_nonneg x))

theorem intervalIntegrable_suzukiPrimeMainIntegrand {t a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x => suzukiPrimeAbelKernel t x * x) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc]
  have hK := continuousOn_suzukiPrimeAbelKernel
    (t := t) (a := min a b) (b := max a b) (lt_min ha hb)
  intro x hx
  exact (hK x hx).mul continuousWithinAt_id

set_option maxHeartbeats 800000 in
/-- Quantitative Abel transfer from a square-root-log PNT error to Suzuki's weighted prime hinge.
This is the analytic core of Suzuki 2022, Proposition 2.1. -/
theorem abs_suzukiPrimeErrorIntegral_le
    {c B D x₀ t : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hlinear : ∀ x : ℝ, 1 ≤ x → |suzukiChebyshevError x| ≤ D * x)
    (hrate : ∀ x : ℝ, x₀ ≤ x → |suzukiChebyshevError x| ≤
      B * x * Real.exp (-c * Real.sqrt (Real.log x)))
    (ht0 : 0 ≤ t) (ht2 : Real.log 2 ≤ t / 2)
    (hthreshold : x₀ ≤ Real.exp (t / 2)) (habsorb : 16 * c ^ 2 ≤ t) :
    |∫ x : ℝ in Ioc 2 (Real.exp t),
        suzukiPrimeAbelKernel t x * suzukiChebyshevError x| ≤
      (8 * D + 4 * B) * Real.exp (t / 2 - (c / 2) * Real.sqrt t) := by
  let Y : ℝ := Real.exp (t / 2)
  let X : ℝ := Real.exp t
  let f : ℝ → ℝ := fun x => suzukiPrimeAbelKernel t x * suzukiChebyshevError x
  let m : ℝ → ℝ := fun x => suzukiPrimeAbelKernel t x * x
  have h2Y : (2 : ℝ) ≤ Y := by
    dsimp only [Y]
    have h := Real.exp_le_exp.mpr ht2
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h
  have hYX : Y ≤ X := by
    dsimp only [Y, X]
    exact Real.exp_le_exp.mpr (by linarith)
  have h2X : (2 : ℝ) ≤ X := h2Y.trans hYX
  have hY0 : 0 < Y := by dsimp only [Y]; positivity
  have hX0 : 0 < X := by dsimp only [X]; positivity
  have hfhead : IntervalIntegrable f volume 2 Y := by
    exact intervalIntegrable_suzukiPrimeErrorIntegrand (by norm_num) hY0
  have hftail : IntervalIntegrable f volume Y X := by
    exact intervalIntegrable_suzukiPrimeErrorIntegrand hY0 hX0
  have hmhead : IntervalIntegrable m volume 2 Y := by
    exact intervalIntegrable_suzukiPrimeMainIntegrand (by norm_num) hY0
  have hmtail : IntervalIntegrable m volume Y X := by
    exact intervalIntegrable_suzukiPrimeMainIntegrand hY0 hX0
  have hsplit :
      (∫ x : ℝ in Ioc 2 X, f x) = (∫ x : ℝ in 2..Y, f x) + ∫ x : ℝ in Y..X, f x := by
    rw [← integral_of_le h2X]
    exact (intervalIntegral.integral_add_adjacent_intervals hfhead hftail).symm
  have hlog_le {x : ℝ} (hx : x ∈ Icc 2 X) : Real.log x ≤ t := by
    have hx0 : 0 < x := by linarith [hx.1]
    apply (Real.log_le_iff_le_exp hx0).mpr
    simpa only [X] using hx.2
  have hkernel {x : ℝ} (hx : x ∈ Icc 2 X) :
      0 ≤ suzukiPrimeAbelKernel t x :=
    suzukiPrimeAbelKernel_nonneg (by linarith [hx.1]) (hlog_le hx)
  have hheadPoint : ∀ x ∈ Icc 2 Y, |f x| ≤ D * m x := by
    intro x hx
    have hxX : x ∈ Icc 2 X := ⟨hx.1, hx.2.trans hYX⟩
    have hk := hkernel hxX
    have he := hlinear x (by linarith [hx.1])
    dsimp only [f, m]
    rw [abs_mul, abs_of_nonneg hk]
    calc
      suzukiPrimeAbelKernel t x * |suzukiChebyshevError x| ≤
          suzukiPrimeAbelKernel t x * (D * x) := mul_le_mul_of_nonneg_left he hk
      _ = D * (suzukiPrimeAbelKernel t x * x) := by ring
  have hheadAbs :
      |∫ x : ℝ in 2..Y, f x| ≤ D * ∫ x : ℝ in 2..Y, m x := by
    calc
      |∫ x : ℝ in 2..Y, f x| ≤ ∫ x : ℝ in 2..Y, |f x| :=
        intervalIntegral.abs_integral_le_integral_abs h2Y
      _ ≤ ∫ x : ℝ in 2..Y, D * m x := by
        apply intervalIntegral.integral_mono_on h2Y hfhead.abs
          (hmhead.const_mul D)
        exact hheadPoint
      _ = D * ∫ x : ℝ in 2..Y, m x :=
        intervalIntegral.integral_const_mul D m
  have hmainHead :
      (∫ x : ℝ in 2..Y, m x) ≤ Real.exp (t / 4) * (4 + t / 2) := by
    rw [show (∫ x : ℝ in 2..Y, m x) =
        suzukiPrimeMainPrimitive t Y - suzukiPrimeMainPrimitive t 2 by
      exact intervalIntegral_suzukiPrimeAbelKernel_mul_id (by norm_num) h2Y]
    dsimp only [m, Y, suzukiPrimeMainPrimitive]
    rw [sqrt_exp_eq_exp_half, Real.log_exp]
    have hlower : 0 ≤ Real.sqrt 2 * (4 + t - Real.log 2) := by
      apply mul_nonneg (Real.sqrt_nonneg 2)
      linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    have heq : Real.exp (t / 2 / 2) = Real.exp (t / 4) := by
      congr 1
      ring
    rw [heq]
    linarith
  have hpoly : 4 + t / 2 ≤ 8 * Real.exp (t / 8) := by
    have h := Real.add_one_le_exp (t / 8)
    nlinarith
  have hsqrtAbsorb : (c / 2) * Real.sqrt t ≤ t / 8 := by
    have h4c : 4 * c ≤ Real.sqrt t := by
      rw [Real.le_sqrt (by positivity) ht0]
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right h4c (Real.sqrt_nonneg t)
    rw [← pow_two, Real.sq_sqrt ht0] at hmul
    nlinarith
  have hheadFinal :
      |∫ x : ℝ in 2..Y, f x| ≤
        8 * D * Real.exp (t / 2 - (c / 2) * Real.sqrt t) := by
    calc
      |∫ x : ℝ in 2..Y, f x| ≤ D * (Real.exp (t / 4) * (4 + t / 2)) :=
        hheadAbs.trans (mul_le_mul_of_nonneg_left hmainHead hD)
      _ ≤ D * (Real.exp (t / 4) * (8 * Real.exp (t / 8))) := by
        gcongr
      _ = 8 * D * Real.exp (3 * t / 8) := by
        rw [show D * (Real.exp (t / 4) * (8 * Real.exp (t / 8))) =
          8 * D * (Real.exp (t / 4) * Real.exp (t / 8)) by ring,
          ← Real.exp_add]
        congr 2
        ring
      _ ≤ 8 * D * Real.exp (t / 2 - (c / 2) * Real.sqrt t) := by
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by linarith)) (by positivity)
  have hsqrtHalf : Real.sqrt t / 2 ≤ Real.sqrt (t / 2) := by
    have hsq1 : (Real.sqrt t / 2) ^ 2 = t / 4 := by
      rw [div_pow, Real.sq_sqrt ht0]
      norm_num
    have hsq2 : Real.sqrt (t / 2) ^ 2 = t / 2 :=
      Real.sq_sqrt (by linarith)
    nlinarith [Real.sqrt_nonneg t, Real.sqrt_nonneg (t / 2)]
  have htailPoint : ∀ x ∈ Icc Y X,
      |f x| ≤ B * Real.exp (-(c / 2) * Real.sqrt t) * m x := by
    intro x hx
    have hxX : x ∈ Icc 2 X := ⟨h2Y.trans hx.1, hx.2⟩
    have hk := hkernel hxX
    have hxy0 : 0 < x := hY0.trans_le hx.1
    have hlogLower : t / 2 ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le hxy0]
      simpa only [Y] using hx.1
    have hsqrtLower : Real.sqrt t / 2 ≤ Real.sqrt (Real.log x) :=
      hsqrtHalf.trans (Real.sqrt_le_sqrt hlogLower)
    have he := hrate x (hthreshold.trans hx.1)
    have hexp : Real.exp (-c * Real.sqrt (Real.log x)) ≤
        Real.exp (-(c / 2) * Real.sqrt t) := by
      rw [Real.exp_le_exp]
      nlinarith
    dsimp only [f, m]
    rw [abs_mul, abs_of_nonneg hk]
    calc
      suzukiPrimeAbelKernel t x * |suzukiChebyshevError x| ≤
          suzukiPrimeAbelKernel t x *
            (B * x * Real.exp (-c * Real.sqrt (Real.log x))) :=
        mul_le_mul_of_nonneg_left he hk
      _ ≤ suzukiPrimeAbelKernel t x *
            (B * x * Real.exp (-(c / 2) * Real.sqrt t)) := by
        gcongr
      _ = B * Real.exp (-(c / 2) * Real.sqrt t) *
            (suzukiPrimeAbelKernel t x * x) := by ring
  have htailAbs :
      |∫ x : ℝ in Y..X, f x| ≤
        B * Real.exp (-(c / 2) * Real.sqrt t) * ∫ x : ℝ in Y..X, m x := by
    calc
      |∫ x : ℝ in Y..X, f x| ≤ ∫ x : ℝ in Y..X, |f x| :=
        intervalIntegral.abs_integral_le_integral_abs hYX
      _ ≤ ∫ x : ℝ in Y..X,
          (B * Real.exp (-(c / 2) * Real.sqrt t)) * m x := by
        apply intervalIntegral.integral_mono_on hYX hftail.abs
          (hmtail.const_mul (B * Real.exp (-(c / 2) * Real.sqrt t)))
        exact htailPoint
      _ = B * Real.exp (-(c / 2) * Real.sqrt t) * ∫ x : ℝ in Y..X, m x :=
        intervalIntegral.integral_const_mul
          (B * Real.exp (-(c / 2) * Real.sqrt t)) m
  have hmainTail : (∫ x : ℝ in Y..X, m x) ≤ 4 * Real.exp (t / 2) := by
    rw [show (∫ x : ℝ in Y..X, m x) =
        suzukiPrimeMainPrimitive t X - suzukiPrimeMainPrimitive t Y by
      exact intervalIntegral_suzukiPrimeAbelKernel_mul_id hY0 hYX]
    dsimp only [m, X, Y, suzukiPrimeMainPrimitive]
    rw [sqrt_exp_eq_exp_half, sqrt_exp_eq_exp_half, Real.log_exp, Real.log_exp]
    have hpos : 0 ≤ Real.exp (t / 2 / 2) * (4 + t - t / 2) :=
      mul_nonneg (Real.exp_nonneg _) (by linarith)
    have heq : Real.exp (t / 2) * (4 + t - t) = 4 * Real.exp (t / 2) := by ring
    rw [heq]
    linarith
  have htailFinal :
      |∫ x : ℝ in Y..X, f x| ≤
        4 * B * Real.exp (t / 2 - (c / 2) * Real.sqrt t) := by
    calc
      |∫ x : ℝ in Y..X, f x| ≤
          B * Real.exp (-(c / 2) * Real.sqrt t) * (4 * Real.exp (t / 2)) :=
        htailAbs.trans (mul_le_mul_of_nonneg_left hmainTail
          (mul_nonneg hB (Real.exp_nonneg _)))
      _ = 4 * B * Real.exp (t / 2 - (c / 2) * Real.sqrt t) := by
        rw [show B * Real.exp (-(c / 2) * Real.sqrt t) * (4 * Real.exp (t / 2)) =
          4 * B * (Real.exp (-(c / 2) * Real.sqrt t) * Real.exp (t / 2)) by ring,
          ← Real.exp_add]
        congr 2
        ring
  rw [show Real.exp t = X by rfl, hsplit]
  calc
    |(∫ x : ℝ in 2..Y, f x) + ∫ x : ℝ in Y..X, f x| ≤
        |∫ x : ℝ in 2..Y, f x| + |∫ x : ℝ in Y..X, f x| := abs_add_le _ _
    _ ≤
        8 * D * Real.exp (t / 2 - (c / 2) * Real.sqrt t) +
          4 * B * Real.exp (t / 2 - (c / 2) * Real.sqrt t) :=
      add_le_add hheadFinal htailFinal
    _ = (8 * D + 4 * B) * Real.exp (t / 2 - (c / 2) * Real.sqrt t) := by ring

/-- **Suzuki 2022, Proposition 2.1.**  Exact weighted von Mangoldt asymptotic at the
de la Vallée Poussin square-root scale. -/
theorem exists_screwPrimeSum_sub_four_exp_half_le :
    ∃ c M : ℝ, 0 < c ∧ 0 < M ∧ ∀ᶠ t : ℝ in atTop,
      |screwPrimeSum t - 4 * Real.exp (t / 2)| ≤
        M * Real.exp (t / 2 - c * Real.sqrt t) := by
  obtain ⟨c, B, hc, hB, hrateEv⟩ := exists_abs_suzukiChebyshevError_le_sqrtLog
  obtain ⟨D, hD, hlinear⟩ := exists_abs_suzukiChebyshevError_le_linear
  obtain ⟨x₀, hx₀all⟩ :=
    (hrateEv.and (eventually_ge_atTop (1 : ℝ))).exists_forall_of_atTop
  have hx₀ : 1 ≤ x₀ := (hx₀all x₀ le_rfl).2
  have hx₀pos : 0 < x₀ := lt_of_lt_of_le zero_lt_one hx₀
  let K : ℝ := Real.sqrt 2 * (5 + |Real.log 2|)
  have hK : 0 < K := by dsimp only [K]; positivity
  let M : ℝ := (8 * D + 4 * B) + 8 * K
  have hM : 0 < M := by
    dsimp only [M]
    nlinarith [hD, hB, hK]
  refine ⟨c / 2, M, by positivity, hM, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    eventually_ge_atTop (2 * Real.log 2),
    eventually_ge_atTop (2 * Real.log x₀),
    eventually_ge_atTop (16 * c ^ 2)] with t ht0 ht2raw htx₀ habsorb
  have ht2 : Real.log 2 ≤ t / 2 := by linarith
  have hthreshold : x₀ ≤ Real.exp (t / 2) := by
    rw [← Real.exp_log hx₀pos]
    exact Real.exp_le_exp.mpr (by linarith)
  have herr := abs_suzukiPrimeErrorIntegral_le hc hB hD.le hlinear
    (fun x hx => (hx₀all x hx).1) ht0 ht2 hthreshold habsorb
  have hdecomp := screwPrimeSum_eq_main_add_error (by linarith : Real.log 2 ≤ t)
  have hcorr :
      |Real.sqrt 2 * (4 + t - Real.log 2)| ≤ K * (t + 1) := by
    have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have ht1 : 0 ≤ t + 1 := by linarith
    calc
      |Real.sqrt 2 * (4 + t - Real.log 2)| =
          Real.sqrt 2 * |4 + t - Real.log 2| := by
        rw [abs_mul, abs_of_nonneg hs2]
      _ ≤ Real.sqrt 2 * (4 + t + |Real.log 2|) := by
        gcongr
        calc
          |4 + t - Real.log 2| ≤ |4 + t| + |Real.log 2| := abs_sub _ _
          _ = 4 + t + |Real.log 2| := by rw [abs_of_nonneg (by linarith)]
      _ ≤ K * (t + 1) := by
        dsimp only [K]
        have hbase : 0 ≤ 5 + |Real.log 2| := by positivity
        have hinside : 4 + t + |Real.log 2| ≤
            (5 + |Real.log 2|) * (t + 1) := by
          nlinarith [abs_nonneg (Real.log 2)]
        calc
          Real.sqrt 2 * (4 + t + |Real.log 2|) ≤
              Real.sqrt 2 * ((5 + |Real.log 2|) * (t + 1)) :=
            mul_le_mul_of_nonneg_left hinside hs2
          _ = Real.sqrt 2 * (5 + |Real.log 2|) * (t + 1) := by ring
  have hpoly : t + 1 ≤ 8 * Real.exp (t / 8) := by
    have h := Real.add_one_le_exp (t / 8)
    nlinarith
  have hsqrtAbsorb : (c / 2) * Real.sqrt t ≤ t / 8 := by
    have h4c : 4 * c ≤ Real.sqrt t := by
      rw [Real.le_sqrt (by positivity) ht0]
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right h4c (Real.sqrt_nonneg t)
    rw [← pow_two, Real.sq_sqrt ht0] at hmul
    nlinarith
  have hcorrFinal :
      |Real.sqrt 2 * (4 + t - Real.log 2)| ≤
        8 * K * Real.exp (t / 2 - (c / 2) * Real.sqrt t) := by
    calc
      |Real.sqrt 2 * (4 + t - Real.log 2)| ≤ K * (t + 1) := hcorr
      _ ≤ K * (8 * Real.exp (t / 8)) := mul_le_mul_of_nonneg_left hpoly hK.le
      _ = 8 * K * Real.exp (t / 8) := by ring
      _ ≤ 8 * K * Real.exp (t / 2 - (c / 2) * Real.sqrt t) := by
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by linarith)) (by positivity)
  rw [hdecomp]
  have hrewrite :
      (4 * Real.exp (t / 2) - Real.sqrt 2 * (4 + t - Real.log 2) +
          ∫ x : ℝ in Ioc 2 (Real.exp t),
            suzukiPrimeAbelKernel t x * suzukiChebyshevError x) -
          4 * Real.exp (t / 2) =
        (∫ x : ℝ in Ioc 2 (Real.exp t),
            suzukiPrimeAbelKernel t x * suzukiChebyshevError x) -
          Real.sqrt 2 * (4 + t - Real.log 2) := by ring
  rw [hrewrite]
  calc
    |(∫ x : ℝ in Ioc 2 (Real.exp t),
        suzukiPrimeAbelKernel t x * suzukiChebyshevError x) -
          Real.sqrt 2 * (4 + t - Real.log 2)| ≤
      |∫ x : ℝ in Ioc 2 (Real.exp t),
        suzukiPrimeAbelKernel t x * suzukiChebyshevError x| +
          |Real.sqrt 2 * (4 + t - Real.log 2)| := abs_sub _ _
    _ ≤ (8 * D + 4 * B) * Real.exp (t / 2 - (c / 2) * Real.sqrt t) +
        8 * K * Real.exp (t / 2 - (c / 2) * Real.sqrt t) :=
      add_le_add herr hcorrFinal
    _ = M * Real.exp (t / 2 - (c / 2) * Real.sqrt t) := by
      dsimp only [M]
      ring

theorem screwLerchConst_nonneg : 0 ≤ screwLerchConst := by
  unfold screwLerchConst screwLerchTail
  exact tsum_nonneg fun n => div_nonneg (Real.exp_nonneg _) (sq_nonneg _)

theorem abs_screwLerchTail_le_const {t : ℝ} (ht : 0 < t) :
    |screwLerchTail t| ≤ screwLerchConst := by
  have hsumt := summable_screwLerchTerm ht
  have hbase := summable_one_div_lerchExp_sq
  have hnonneg : 0 ≤ screwLerchTail t := by
    unfold screwLerchTail
    exact tsum_nonneg fun n => div_nonneg (Real.exp_nonneg _) (sq_nonneg _)
  rw [abs_of_nonneg hnonneg, screwLerchTail, screwLerchConst, screwLerchTail]
  have hbase' : Summable (fun n : ℕ =>
      Real.exp (-(lerchExp n * 0)) / lerchExp n ^ 2) := by
    simpa using hbase
  apply Summable.tsum_le_tsum (fun n => ?_) hsumt hbase'
  have hexp : Real.exp (-(lerchExp n * t)) ≤ Real.exp (-(lerchExp n * 0)) := by
    rw [Real.exp_le_exp]
    have := lerchExp_pos n
    nlinarith
  exact div_le_div_of_nonneg_right hexp (sq_nonneg _)

set_option maxHeartbeats 800000 in
/-- **Suzuki 2022, Theorem 1.1(iii).**  The literal prime--Lerch screw function satisfies
`Psi(t) ≪ exp(t/2 - c sqrt(t))` unconditionally. -/
theorem exists_abs_suzukiPsi_le_exp_half_sub_sqrt :
    ∃ c M : ℝ, 0 < c ∧ 0 < M ∧ ∀ᶠ t : ℝ in atTop,
      |suzukiPsi t| ≤ M * Real.exp (t / 2 - c * Real.sqrt t) := by
  obtain ⟨c, P, hc, hP, hprime⟩ := exists_screwPrimeSum_sub_four_exp_half_le
  let K : ℝ := 12 + |screwLinearCoeff| + 2 * screwLerchConst
  have hK : 0 < K := by
    dsimp only [K]
    nlinarith [abs_nonneg screwLinearCoeff, screwLerchConst_nonneg]
  let M : ℝ := P + 8 * K
  have hM : 0 < M := by dsimp only [M]; nlinarith
  refine ⟨c, M, hc, hM, ?_⟩
  filter_upwards [hprime, eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (64 * c ^ 2)] with t hprime ht1 habsorb
  have ht0 : 0 ≤ t := by linarith
  have htail := abs_screwLerchTail_le_const (by linarith : 0 < t)
  let R : ℝ := 4 * Real.exp (-(t / 2)) - 8 +
    screwLinearCoeff / 2 * t + (screwLerchConst - screwLerchTail t)
  have hRbound : |R| ≤ K * (t + 1) := by
    have hexp : Real.exp (-(t / 2)) ≤ 1 := by
      rw [← Real.exp_zero, Real.exp_le_exp]
      linarith
    have ha : |4 * Real.exp (-(t / 2))| ≤ 4 := by
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      nlinarith [Real.exp_nonneg (-(t / 2))]
    have hb : |(-8 : ℝ)| = 8 := by norm_num
    have hc₁ : |screwLinearCoeff / 2 * t| ≤ |screwLinearCoeff| * t := by
      rw [abs_mul, abs_div, abs_of_nonneg ht0]
      have hhalf : |(2 : ℝ)| = 2 := by norm_num
      rw [hhalf]
      have ht0' : 0 ≤ |screwLinearCoeff| * t := mul_nonneg (abs_nonneg _) ht0
      nlinarith
    have hd : |screwLerchConst - screwLerchTail t| ≤ 2 * screwLerchConst := by
      calc
        |screwLerchConst - screwLerchTail t| ≤
            |screwLerchConst| + |screwLerchTail t| := abs_sub _ _
        _ ≤ screwLerchConst + screwLerchConst := by
          rw [abs_of_nonneg screwLerchConst_nonneg]
          linarith
        _ = 2 * screwLerchConst := by ring
    have htri : |R| ≤ |4 * Real.exp (-(t / 2))| + |(-8 : ℝ)| +
        |screwLinearCoeff / 2 * t| +
          |screwLerchConst - screwLerchTail t| := by
      dsimp only [R]
      calc
        |4 * Real.exp (-(t / 2)) - 8 + screwLinearCoeff / 2 * t +
            (screwLerchConst - screwLerchTail t)| ≤
          |4 * Real.exp (-(t / 2)) - 8 + screwLinearCoeff / 2 * t| +
            |screwLerchConst - screwLerchTail t| := abs_add_le _ _
        _ ≤ (|4 * Real.exp (-(t / 2)) - 8| +
            |screwLinearCoeff / 2 * t|) +
            |screwLerchConst - screwLerchTail t| := by gcongr; exact abs_add_le _ _
        _ ≤ ((|4 * Real.exp (-(t / 2))| + |(-8 : ℝ)|) +
            |screwLinearCoeff / 2 * t|) +
            |screwLerchConst - screwLerchTail t| := by
          gcongr
          simpa only [sub_eq_add_neg] using abs_add_le (4 * Real.exp (-(t / 2))) (-8)
        _ = _ := by ring
    calc
      |R| ≤ |4 * Real.exp (-(t / 2))| + |(-8 : ℝ)| +
          |screwLinearCoeff / 2 * t| +
            |screwLerchConst - screwLerchTail t| := htri
      _ ≤ 4 + 8 + |screwLinearCoeff| * t + 2 * screwLerchConst := by
        nlinarith [ha, hc₁, hd, show |(-8 : ℝ)| ≤ 8 by norm_num]
      _ ≤ K * (t + 1) := by
        dsimp only [K]
        nlinarith [abs_nonneg screwLinearCoeff, screwLerchConst_nonneg]
  have hsqrtAbsorb : c * Real.sqrt t ≤ t / 8 := by
    have h8c : 8 * c ≤ Real.sqrt t := by
      rw [Real.le_sqrt (by positivity) ht0]
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right h8c (Real.sqrt_nonneg t)
    rw [← pow_two, Real.sq_sqrt ht0] at hmul
    nlinarith
  have hpoly : t + 1 ≤ 8 * Real.exp (t / 8) := by
    have h := Real.add_one_le_exp (t / 8)
    nlinarith
  have hRfinal : |R| ≤ 8 * K * Real.exp (t / 2 - c * Real.sqrt t) := by
    calc
      |R| ≤ K * (t + 1) := hRbound
      _ ≤ K * (8 * Real.exp (t / 8)) := mul_le_mul_of_nonneg_left hpoly hK.le
      _ = 8 * K * Real.exp (t / 8) := by ring
      _ ≤ 8 * K * Real.exp (t / 2 - c * Real.sqrt t) := by
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by linarith)) (by positivity)
  have hPsi : suzukiPsi t = -(screwPrimeSum t - 4 * Real.exp (t / 2)) + R := by
    rw [suzukiPsi, abs_of_nonneg ht0]
    unfold screwFn
    dsimp only [R]
    ring
  rw [hPsi]
  calc
    |-(screwPrimeSum t - 4 * Real.exp (t / 2)) + R| ≤
        |screwPrimeSum t - 4 * Real.exp (t / 2)| + |R| := by
      simpa only [abs_neg] using
        abs_add_le (-(screwPrimeSum t - 4 * Real.exp (t / 2))) R
    _ ≤ P * Real.exp (t / 2 - c * Real.sqrt t) +
        8 * K * Real.exp (t / 2 - c * Real.sqrt t) :=
      add_le_add hprime hRfinal
    _ = M * Real.exp (t / 2 - c * Real.sqrt t) := by
      dsimp only [M]
      ring

/-- Landau-symbol form of Suzuki 2022, Theorem 1.1(iii). -/
theorem suzukiPsi_isBigO_exp_half_sub_sqrt :
    ∃ c : ℝ, 0 < c ∧ suzukiPsi =O[atTop]
      (fun t : ℝ => Real.exp (t / 2 - c * Real.sqrt t)) := by
  obtain ⟨c, M, hc, hM, hbound⟩ := exists_abs_suzukiPsi_le_exp_half_sub_sqrt
  refine ⟨c, hc, Asymptotics.IsBigO.of_bound M ?_⟩
  filter_upwards [hbound] with t ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact ht

end

end RHTower

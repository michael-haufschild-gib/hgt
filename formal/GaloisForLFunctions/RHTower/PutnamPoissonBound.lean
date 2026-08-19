import GaloisForLFunctions.RHTower.PutnamPeriodizationIntegrable
import GaloisForLFunctions.HTGeometry.CauchyCircleIntegral

/-!
# The Poisson bound for the periodised Putnam kernel

Pairing the periodisation against the Cauchy kernel `(1 - r e^{idy})^{-1}` uses only the Fourier
coefficients of nonnegative index: expanding the conjugate kernel in a geometric series shows that
the conjugate pairing vanishes as soon as those coefficients do, and adding the two pairings turns
the Cauchy kernel into the Poisson kernel, which is nonnegative of total mass one.  The Cauchy
transform of the periodisation is therefore bounded by the sup norm of the periodisation.
-/

open Complex MeasureTheory Set HTGeometry

noncomputable section

namespace RHTower

/-- A uniform bound for the periodisation on a period. -/
def periodizationBound (d : ℝ) : ℝ :=
  Real.exp (putnamPeriod d / 2) * ∑' k : ℤ, Real.exp (-(putnamPeriod d / 2 * |(k : ℝ)|))

theorem periodizationBound_nonneg (d : ℝ) : 0 ≤ periodizationBound d := by
  refine mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun k => (Real.exp_pos _).le)

theorem norm_putnamPeriodization_le_bound {a d : ℝ} (hd : 0 < d) {y : ℝ}
    (hy : y ∈ Ioc (0 : ℝ) (putnamPeriod d)) :
    ‖putnamPeriodization a d y‖ ≤ periodizationBound d := by
  refine le_trans (norm_putnamPeriodization_le hd y) ?_
  have hS : (0 : ℝ) ≤ ∑' k : ℤ, Real.exp (-(putnamPeriod d / 2 * |(k : ℝ)|)) :=
    tsum_nonneg fun k => (Real.exp_pos _).le
  have hxb : |y| ≤ putnamPeriod d := by
    rw [abs_of_pos hy.1]
    exact hy.2
  have hexp : Real.exp (|y| / 2) ≤ Real.exp (putnamPeriod d / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [periodizationBound]
  exact mul_le_mul_of_nonneg_right hexp hS

/-- The periodisation multiplied by a bounded continuous factor is integrable on a period. -/
theorem integrableOn_periodization_mul {a d : ℝ} (hd : 0 < d) {g : ℝ → ℂ} (hg : Continuous g)
    {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) :
    IntegrableOn (fun y => putnamPeriodization a d y * g y) (Ioc (0 : ℝ) (putnamPeriod d)) := by
  have h := (integrableOn_putnamPeriodization (a := a) hd).bdd_mul
    (hg.aestronglyMeasurable.restrict) (Filter.Eventually.of_forall hC)
  exact h.congr (Filter.Eventually.of_forall fun x => mul_comm _ _)

theorem norm_circleKernel_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (d y : ℝ) :
    ‖(circleFactor r d y)⁻¹‖ ≤ (1 - r)⁻¹ := by
  have hre : (1 : ℝ) - r ≤ (circleFactor r d y).re := by
    rw [circleFactor_re]
    nlinarith [Real.cos_le_one (d * y), Real.neg_one_le_cos (d * y)]
  have hnorm : (1 : ℝ) - r ≤ ‖circleFactor r d y‖ :=
    le_trans hre (le_trans (le_abs_self _) (Complex.abs_re_le_norm _))
  rw [norm_inv]
  gcongr

/-- The `n`-th power pairing vanishes: it is the `n`-th Fourier coefficient scaled by `r^n`. -/
theorem integral_periodization_conjPow_eq_zero {a d r : ℝ}
    (hzero : ∀ n : ℕ,
      (∫ x in Ioc (0 : ℝ) (putnamPeriod d), putnamPeriodTwist a d (n : ℤ) x) = 0) (m : ℕ) :
    (∫ y in Ioc (0 : ℝ) (putnamPeriod d),
        putnamPeriodization a d y * ((r : ℂ) * Complex.exp (-(d : ℂ) * (y : ℂ) * I)) ^ m) = 0 := by
  have hpt : ∀ y : ℝ, putnamPeriodization a d y * ((r : ℂ) * Complex.exp (-(d : ℂ) * (y : ℂ) * I)) ^ m
      = (r : ℂ) ^ m * putnamPeriodTwist a d (m : ℤ) y := by
    intro y
    rw [putnamPeriodTwist, mul_pow, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioc (fun y _ => hpt y), integral_const_mul, hzero m,
    mul_zero]

/-- The conjugate circle factor. -/
theorem conj_circleFactor (r d y : ℝ) :
    (starRingEnd ℂ) (circleFactor r d y) = 1 - (r : ℂ) * Complex.exp (-(d : ℂ) * (y : ℂ) * I) := by
  rw [circleFactor]
  simp only [map_sub, map_one, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp [Complex.conj_I]

theorem norm_conjArg (r d y : ℝ) (hr0 : 0 ≤ r) :
    ‖(r : ℂ) * Complex.exp (-(d : ℂ) * (y : ℂ) * I)‖ = r := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, Complex.norm_exp]
  have hre : (-(d : ℂ) * (y : ℂ) * I).re = 0 := by simp [Complex.mul_re]
  rw [hre, Real.exp_zero, mul_one]

theorem continuous_conjArg (r d : ℝ) :
    Continuous (fun y : ℝ => (r : ℂ) * Complex.exp (-(d : ℂ) * (y : ℂ) * I)) := by fun_prop

theorem one_sub_conjArg_ne_zero {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (d y : ℝ) :
    (1 : ℂ) - (r : ℂ) * Complex.exp (-(d : ℂ) * (y : ℂ) * I) ≠ 0 := by
  intro h
  refine circleFactor_ne_zero hr0 hr1 d y ?_
  have h2 : (starRingEnd ℂ) (circleFactor r d y) = 0 := by rw [conj_circleFactor]; exact h
  simpa using congrArg (starRingEnd ℂ) h2

theorem norm_one_sub_conjArg_ge {r : ℝ} (hr0 : 0 ≤ r) (d y : ℝ) :
    1 - r ≤ ‖(1 : ℂ) - (r : ℂ) * Complex.exp (-(d : ℂ) * (y : ℂ) * I)‖ := by
  have h := conj_circleFactor r d y
  rw [← h, RCLike.norm_conj]
  have hre : (1 : ℝ) - r ≤ (circleFactor r d y).re := by
    rw [circleFactor_re]
    nlinarith [Real.cos_le_one (d * y), Real.neg_one_le_cos (d * y)]
  exact le_trans hre (le_trans (le_abs_self _) (Complex.abs_re_le_norm _))

/-- **The conjugate Cauchy pairing vanishes.**  Only Fourier coefficients of nonnegative index
enter, because the conjugate Cauchy kernel expands in nonnegative powers. -/
theorem integral_periodization_conjCauchy_eq_zero {a d r : ℝ} (hd : 0 < d)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hzero : ∀ n : ℕ,
      (∫ x in Ioc (0 : ℝ) (putnamPeriod d), putnamPeriodTwist a d (n : ℤ) x) = 0) :
    (∫ y in Ioc (0 : ℝ) (putnamPeriod d),
        putnamPeriodization a d y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹)) = 0 := by
  classical
  set P := putnamPeriod d with hPdef
  set D := putnamPeriodization a d with hDdef
  set w : ℝ → ℂ := fun y => (r : ℂ) * Complex.exp (-(d : ℂ) * (y : ℂ) * I) with hwdef
  set M := periodizationBound d with hMdef
  have hPpos : 0 < P := putnamPeriod_pos hd
  have hrle : (0 : ℝ) < 1 - r := by linarith
  have hkey : ∀ y : ℝ, (starRingEnd ℂ) ((circleFactor r d y)⁻¹) = (1 - w y)⁻¹ := by
    intro y
    rw [map_inv₀, conj_circleFactor]
  have hcontK : Continuous (fun y : ℝ => (1 - w y)⁻¹) :=
    (continuous_const.sub (continuous_conjArg r d)).inv₀
      (fun y => one_sub_conjArg_ne_zero hr0 hr1 d y)
  have hboundK : ∀ y : ℝ, ‖(1 - w y)⁻¹‖ ≤ (1 - r)⁻¹ := by
    intro y
    rw [norm_inv]
    gcongr
    exact norm_one_sub_conjArg_ge hr0 d y
  have hintK : IntegrableOn (fun y => D y * (1 - w y)⁻¹) (Ioc (0 : ℝ) P) :=
    integrableOn_periodization_mul hd hcontK hboundK
  have hpow : ∀ n : ℕ, IntegrableOn (fun y => D y * (w y ^ n * (1 - w y)⁻¹)) (Ioc (0 : ℝ) P) := by
    intro n
    refine integrableOn_periodization_mul hd
      (((continuous_conjArg r d).pow n).mul hcontK) (C := r ^ n * (1 - r)⁻¹) (fun y => ?_)
    rw [norm_mul, norm_pow, norm_conjArg r d y hr0]
    exact mul_le_mul_of_nonneg_left (hboundK y) (by positivity)
  have hsum : ∀ n : ℕ, IntegrableOn (fun y => D y * ∑ m ∈ Finset.range n, w y ^ m)
      (Ioc (0 : ℝ) P) := by
    intro n
    refine integrableOn_periodization_mul hd
      (continuous_finsetSum _ fun m _ => (continuous_conjArg r d).pow m)
      (C := ∑ m ∈ Finset.range n, r ^ m) (fun y => ?_)
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m _ => ?_)
    rw [norm_pow, norm_conjArg r d y hr0]
  have hzeropow : ∀ n : ℕ, (∫ y in Ioc (0 : ℝ) P, D y * ∑ m ∈ Finset.range n, w y ^ m) = 0 := by
    intro n
    have hpt : ∀ y : ℝ, D y * ∑ m ∈ Finset.range n, w y ^ m
        = ∑ m ∈ Finset.range n, D y * w y ^ m := fun y => by rw [Finset.mul_sum]
    rw [setIntegral_congr_fun measurableSet_Ioc (fun y _ => hpt y)]
    rw [MeasureTheory.integral_finsetSum (s := Finset.range n)
      (f := fun (m : ℕ) (y : ℝ) => D y * w y ^ m)
      (fun m _ => integrableOn_periodization_mul hd ((continuous_conjArg r d).pow m)
        (C := r ^ m) (fun y => by rw [norm_pow, norm_conjArg r d y hr0]))]
    refine Finset.sum_eq_zero fun m _ => ?_
    exact integral_periodization_conjPow_eq_zero hzero m
  have hstep : ∀ n : ℕ, (∫ y in Ioc (0 : ℝ) P, D y * (1 - w y)⁻¹)
      = ∫ y in Ioc (0 : ℝ) P, D y * (w y ^ n * (1 - w y)⁻¹) := by
    intro n
    have hpt : ∀ y : ℝ, D y * (1 - w y)⁻¹
        = D y * ∑ m ∈ Finset.range n, w y ^ m + D y * (w y ^ n * (1 - w y)⁻¹) := by
      intro y
      have hne : (1 : ℂ) - w y ≠ 0 := one_sub_conjArg_ne_zero hr0 hr1 d y
      have hg := geom_sum_mul (w y) n
      field_simp
      linear_combination (D y) * hg
    rw [setIntegral_congr_fun measurableSet_Ioc (fun y _ => hpt y),
      integral_add (hsum n) (hpow n), hzeropow n, zero_add]
  have hbound : ∀ n : ℕ, ‖∫ y in Ioc (0 : ℝ) P, D y * (1 - w y)⁻¹‖
      ≤ M * (1 - r)⁻¹ * P * r ^ n := by
    intro n
    rw [hstep n]
    refine le_trans (norm_integral_le_of_norm_le_const (C := M * (1 - r)⁻¹ * r ^ n) ?_) ?_
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall fun y hy => ?_)
      rw [norm_mul, norm_mul, norm_pow, norm_conjArg r d y hr0]
      have h1 : ‖D y‖ ≤ M := norm_putnamPeriodization_le_bound hd hy
      have h2 : ‖(1 - w y)⁻¹‖ ≤ (1 - r)⁻¹ := hboundK y
      have hMnn : (0 : ℝ) ≤ M := periodizationBound_nonneg d
      have hrnn : (0 : ℝ) ≤ r ^ n := by positivity
      have hinn : (0 : ℝ) ≤ (1 - r)⁻¹ := by positivity
      calc ‖D y‖ * (r ^ n * ‖(1 - w y)⁻¹‖)
          ≤ M * (r ^ n * (1 - r)⁻¹) := by
            refine mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 hrnn) (by positivity) hMnn
        _ = M * (1 - r)⁻¹ * r ^ n := by ring
    · have hmeas : (volume.restrict (Ioc (0 : ℝ) P)).real univ = P := by
        simp [MeasureTheory.Measure.real, Real.volume_Ioc]
        linarith
      rw [hmeas]
      have hnn : (0 : ℝ) ≤ M * (1 - r)⁻¹ * r ^ n := by
        have := periodizationBound_nonneg d
        positivity
      nlinarith [hnn, hPpos]
  have hlim : Filter.Tendsto (fun n : ℕ => M * (1 - r)⁻¹ * P * r ^ n) Filter.atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    simpa using this.const_mul (M * (1 - r)⁻¹ * P)
  have hle : ‖∫ y in Ioc (0 : ℝ) P, D y * (1 - w y)⁻¹‖ ≤ 0 :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  have hzz : (∫ y in Ioc (0 : ℝ) P, D y * (1 - w y)⁻¹) = 0 := by
    have := norm_nonneg (∫ y in Ioc (0 : ℝ) P, D y * (1 - w y)⁻¹)
    exact norm_eq_zero.mp (le_antisymm hle this)
  rw [setIntegral_congr_fun measurableSet_Ioc (fun y _ => by rw [hkey y])]
  exact hzz

/-- The mean of the periodisation over a period is its zeroth Fourier coefficient. -/
theorem integral_periodization_eq_zero {a d : ℝ}
    (hzero : ∀ n : ℕ,
      (∫ x in Ioc (0 : ℝ) (putnamPeriod d), putnamPeriodTwist a d (n : ℤ) x) = 0) :
    (∫ y in Ioc (0 : ℝ) (putnamPeriod d), putnamPeriodization a d y) = 0 := by
  rw [← hzero 0]
  refine setIntegral_congr_fun measurableSet_Ioc (fun y _ => ?_)
  rw [putnamPeriodTwist]
  norm_num

theorem continuous_circleKernel_im {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (d : ℝ) :
    Continuous (fun y : ℝ => (((circleFactor r d y)⁻¹).im : ℂ)) :=
  Complex.continuous_ofReal.comp
    (Complex.continuous_im.comp (continuous_circleKernel hr0 hr1 d))

theorem continuous_poissonFactor {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (d : ℝ) :
    Continuous (poissonFactor r d) := by
  unfold poissonFactor
  exact (continuous_const.mul
    (Complex.continuous_re.comp (continuous_circleKernel hr0 hr1 d))).sub continuous_const

theorem abs_poissonFactor_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (d y : ℝ) :
    |poissonFactor r d y| ≤ 2 * (1 - r)⁻¹ + 1 := by
  have h := norm_circleKernel_le hr0 hr1 d y
  have hre : |((circleFactor r d y)⁻¹).re| ≤ (1 - r)⁻¹ :=
    le_trans (Complex.abs_re_le_norm _) h
  rw [poissonFactor]
  calc |2 * ((circleFactor r d y)⁻¹).re - 1|
      ≤ |2 * ((circleFactor r d y)⁻¹).re| + |(1 : ℝ)| := abs_sub _ _
    _ ≤ 2 * (1 - r)⁻¹ + 1 := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_one]
        linarith [hre]

/-- The Cauchy kernel integrates to the period. -/
theorem integral_circleKernel_period {d r : ℝ} (hd : 0 < d) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∫ y in Ioc (0 : ℝ) (putnamPeriod d), (circleFactor r d y)⁻¹)
      = ((putnamPeriod d : ℝ) : ℂ) := by
  have hP : 0 < putnamPeriod d := putnamPeriod_pos hd
  have hdP : d * putnamPeriod d = 2 * Real.pi := by
    rw [putnamPeriod]
    field_simp
  have hend : circleFactor r d (putnamPeriod d) = circleFactor r d 0 := by
    rw [circleFactor, circleFactor]
    congr 2
    rw [show (d : ℂ) * ((putnamPeriod d : ℝ) : ℂ) * I = ((2 * Real.pi : ℝ) : ℂ) * I by
      push_cast [← hdP]; ring]
    rw [show ((2 * Real.pi : ℝ) : ℂ) * I = 2 * Real.pi * I by push_cast; ring]
    rw [Complex.exp_two_pi_mul_I]
    simp
  rw [← intervalIntegral.integral_of_le hP.le, integral_circleKernel hr0 hr1 hd.ne' 0
    (putnamPeriod d), hend]
  push_cast
  ring

/-- **The Cauchy transform is the Poisson transform.** -/
theorem cauchy_eq_poisson {a d r : ℝ} (hd : 0 < d) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hzero : ∀ n : ℕ,
      (∫ x in Ioc (0 : ℝ) (putnamPeriod d), putnamPeriodTwist a d (n : ℤ) x) = 0) :
    (∫ y in Ioc (0 : ℝ) (putnamPeriod d),
        putnamPeriodization a d y * (circleFactor r d y)⁻¹)
      = ∫ y in Ioc (0 : ℝ) (putnamPeriod d),
          putnamPeriodization a d y * ((poissonFactor r d y : ℝ) : ℂ) := by
  set P := putnamPeriod d with hPdef
  set D := putnamPeriodization a d with hDdef
  have hfin : (volume (Ioc (0 : ℝ) P)) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hint1 : IntegrableOn (fun y => D y * (circleFactor r d y)⁻¹) (Ioc (0 : ℝ) P) :=
    integrableOn_periodization_mul hd (continuous_circleKernel hr0 hr1 d)
      (norm_circleKernel_le hr0 hr1 d)
  have hint2 : IntegrableOn (fun y => D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹))
      (Ioc (0 : ℝ) P) := by
    refine integrableOn_periodization_mul hd
      (Complex.continuous_conj.comp (continuous_circleKernel hr0 hr1 d))
      (C := (1 - r)⁻¹) (fun y => ?_)
    rw [RCLike.norm_conj]
    exact norm_circleKernel_le hr0 hr1 d y
  have hint3 : IntegrableOn D (Ioc (0 : ℝ) P) := integrableOn_putnamPeriodization hd
  have hpt : ∀ y : ℝ, D y * ((poissonFactor r d y : ℝ) : ℂ)
      = D y * (circleFactor r d y)⁻¹ + D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹) - D y := by
    intro y
    have hconj : (circleFactor r d y)⁻¹ + (starRingEnd ℂ) ((circleFactor r d y)⁻¹)
        = 2 * ((((circleFactor r d y)⁻¹).re : ℝ) : ℂ) := by
      rw [Complex.add_conj]
      push_cast
      ring
    rw [poissonFactor]
    push_cast
    rw [show (2 : ℂ) * ((((circleFactor r d y)⁻¹).re : ℝ) : ℂ)
        = (circleFactor r d y)⁻¹ + (starRingEnd ℂ) ((circleFactor r d y)⁻¹) from hconj.symm]
    ring
  have hsplit : (∫ y in Ioc (0 : ℝ) P,
        (D y * (circleFactor r d y)⁻¹ + D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹) - D y))
      = (∫ y in Ioc (0 : ℝ) P,
          (D y * (circleFactor r d y)⁻¹ + D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹)))
        - ∫ y in Ioc (0 : ℝ) P, D y :=
    integral_sub (hint1.add hint2) hint3
  have hadd : (∫ y in Ioc (0 : ℝ) P,
        (D y * (circleFactor r d y)⁻¹ + D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹)))
      = (∫ y in Ioc (0 : ℝ) P, D y * (circleFactor r d y)⁻¹)
        + ∫ y in Ioc (0 : ℝ) P, D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹) :=
    integral_add hint1 hint2
  rw [setIntegral_congr_fun measurableSet_Ioc (fun y _ => hpt y), hsplit, hadd,
    integral_periodization_conjCauchy_eq_zero hd hr0 hr1 hzero,
    integral_periodization_eq_zero hzero]
  ring

/-- The Poisson factor has total mass equal to the period. -/
theorem integral_poissonFactor {d r : ℝ} (hd : 0 < d) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∫ y in Ioc (0 : ℝ) (putnamPeriod d), poissonFactor r d y) = putnamPeriod d := by
  have hP : 0 < putnamPeriod d := putnamPeriod_pos hd
  have hfin : (volume (Ioc (0 : ℝ) (putnamPeriod d))) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hint1 : IntegrableOn (fun y => (circleFactor r d y)⁻¹)
      (Ioc (0 : ℝ) (putnamPeriod d)) := by
    refine Integrable.mono' (g := fun _ : ℝ => (1 - r)⁻¹) (integrableOn_const hfin)
      ((continuous_circleKernel hr0 hr1 d).aestronglyMeasurable.restrict)
      (Filter.Eventually.of_forall fun y => norm_circleKernel_le hr0 hr1 d y)
  have hint2 : IntegrableOn (fun y => (starRingEnd ℂ) ((circleFactor r d y)⁻¹))
      (Ioc (0 : ℝ) (putnamPeriod d)) := by
    refine Integrable.mono' (g := fun _ : ℝ => (1 - r)⁻¹) (integrableOn_const hfin)
      ((Complex.continuous_conj.comp
        (continuous_circleKernel hr0 hr1 d)).aestronglyMeasurable.restrict)
      (Filter.Eventually.of_forall fun y => by
        rw [RCLike.norm_conj]; exact norm_circleKernel_le hr0 hr1 d y)
  have hconstint : (∫ _y in Ioc (0 : ℝ) (putnamPeriod d), (1 : ℂ))
      = ((putnamPeriod d : ℝ) : ℂ) := by
    rw [setIntegral_const]
    simp [MeasureTheory.Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal hP.le]
  have hco : (∫ y in Ioc (0 : ℝ) (putnamPeriod d), ((poissonFactor r d y : ℝ) : ℂ))
      = (((∫ y in Ioc (0 : ℝ) (putnamPeriod d), poissonFactor r d y) : ℝ) : ℂ) := integral_ofReal
  have hpt : ∀ y : ℝ, ((poissonFactor r d y : ℝ) : ℂ)
      = (circleFactor r d y)⁻¹ + (starRingEnd ℂ) ((circleFactor r d y)⁻¹) - 1 := by
    intro y
    have hconj : (circleFactor r d y)⁻¹ + (starRingEnd ℂ) ((circleFactor r d y)⁻¹)
        = 2 * ((((circleFactor r d y)⁻¹).re : ℝ) : ℂ) := by
      rw [Complex.add_conj]
      push_cast
      ring
    rw [poissonFactor]
    push_cast
    rw [show (2 : ℂ) * ((((circleFactor r d y)⁻¹).re : ℝ) : ℂ)
        = (circleFactor r d y)⁻¹ + (starRingEnd ℂ) ((circleFactor r d y)⁻¹) from hconj.symm]
  have hsplit : (∫ y in Ioc (0 : ℝ) (putnamPeriod d),
        ((circleFactor r d y)⁻¹ + (starRingEnd ℂ) ((circleFactor r d y)⁻¹) - 1))
      = (∫ y in Ioc (0 : ℝ) (putnamPeriod d),
          ((circleFactor r d y)⁻¹ + (starRingEnd ℂ) ((circleFactor r d y)⁻¹)))
        - ∫ _y in Ioc (0 : ℝ) (putnamPeriod d), (1 : ℂ) :=
    integral_sub (hint1.add hint2) (integrableOn_const hfin)
  have hadd : (∫ y in Ioc (0 : ℝ) (putnamPeriod d),
        ((circleFactor r d y)⁻¹ + (starRingEnd ℂ) ((circleFactor r d y)⁻¹)))
      = (∫ y in Ioc (0 : ℝ) (putnamPeriod d), (circleFactor r d y)⁻¹)
        + ∫ y in Ioc (0 : ℝ) (putnamPeriod d), (starRingEnd ℂ) ((circleFactor r d y)⁻¹) :=
    integral_add hint1 hint2
  have hconjint : (∫ y in Ioc (0 : ℝ) (putnamPeriod d),
        (starRingEnd ℂ) ((circleFactor r d y)⁻¹))
      = (starRingEnd ℂ) (∫ y in Ioc (0 : ℝ) (putnamPeriod d), (circleFactor r d y)⁻¹) :=
    integral_conj
  have hcast : (((∫ y in Ioc (0 : ℝ) (putnamPeriod d), poissonFactor r d y) : ℝ) : ℂ)
      = ((putnamPeriod d : ℝ) : ℂ) := by
    rw [← hco, setIntegral_congr_fun measurableSet_Ioc (fun y _ => hpt y), hsplit, hadd,
      hconjint, integral_circleKernel_period hd hr0 hr1, Complex.conj_ofReal, hconstint]
    ring
  exact_mod_cast hcast

theorem integrableOn_poissonFactor {d r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    IntegrableOn (poissonFactor r d) (Ioc (0 : ℝ) (putnamPeriod d)) := by
  have hfin : (volume (Ioc (0 : ℝ) (putnamPeriod d))) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  refine Integrable.mono' (g := fun _ : ℝ => 2 * (1 - r)⁻¹ + 1) (integrableOn_const hfin)
    ((continuous_poissonFactor hr0 hr1 d).aestronglyMeasurable.restrict)
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  exact abs_poissonFactor_le hr0 hr1 d y

/-- **The Poisson bound.**  The Cauchy transform of the periodisation is bounded by the sup norm of
the periodisation times the period, uniformly in `r`. -/
theorem norm_cauchy_le {a d r : ℝ} (hd : 0 < d) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hzero : ∀ n : ℕ,
      (∫ x in Ioc (0 : ℝ) (putnamPeriod d), putnamPeriodTwist a d (n : ℤ) x) = 0) :
    ‖∫ y in Ioc (0 : ℝ) (putnamPeriod d),
        putnamPeriodization a d y * (circleFactor r d y)⁻¹‖
      ≤ periodizationBound d * putnamPeriod d := by
  set P := putnamPeriod d with hPdef
  set D := putnamPeriodization a d with hDdef
  set M := periodizationBound d with hMdef
  have hMnn : (0 : ℝ) ≤ M := periodizationBound_nonneg d
  have hpoint : ∀ y : ℝ, ‖D y * ((poissonFactor r d y : ℝ) : ℂ)‖
      = poissonFactor r d y * ‖D y‖ := by
    intro y
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (poissonFactor_nonneg hr0 hr1 d y)]
    ring
  have hPint : IntegrableOn (poissonFactor r d) (Ioc (0 : ℝ) P) :=
    integrableOn_poissonFactor hr0 hr1
  have hint1 : IntegrableOn (fun y => poissonFactor r d y * ‖D y‖) (Ioc (0 : ℝ) P) := by
    refine ((integrableOn_putnamPeriodization (a := a) hd).norm).bdd_mul
      (c := 2 * (1 - r)⁻¹ + 1)
      ((continuous_poissonFactor hr0 hr1 d).aestronglyMeasurable.restrict)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    exact abs_poissonFactor_le hr0 hr1 d y
  have hint2 : IntegrableOn (fun y => poissonFactor r d y * M) (Ioc (0 : ℝ) P) :=
    hPint.mul_const M
  have hmono : (∫ y in Ioc (0 : ℝ) P, poissonFactor r d y * ‖D y‖)
      ≤ ∫ y in Ioc (0 : ℝ) P, poissonFactor r d y * M := by
    refine setIntegral_mono_on hint1 hint2 measurableSet_Ioc (fun y hy => ?_)
    exact mul_le_mul_of_nonneg_left (norm_putnamPeriodization_le_bound hd hy)
      (poissonFactor_nonneg hr0 hr1 d y)
  have hval : (∫ y in Ioc (0 : ℝ) P, poissonFactor r d y * M) = P * M := by
    rw [integral_mul_const, integral_poissonFactor hd hr0 hr1]
  rw [cauchy_eq_poisson hd hr0 hr1 hzero]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  rw [setIntegral_congr_fun measurableSet_Ioc (fun y _ => hpoint y)]
  rw [hval] at hmono
  linarith [hmono]

/-- **The pairing against the imaginary part of the Cauchy kernel** is half the Cauchy transform. -/
theorem norm_integral_periodization_kernelIm_le {a d r : ℝ} (hd : 0 < d) (hr0 : 0 ≤ r)
    (hr1 : r < 1)
    (hzero : ∀ n : ℕ,
      (∫ x in Ioc (0 : ℝ) (putnamPeriod d), putnamPeriodTwist a d (n : ℤ) x) = 0) :
    ‖∫ y in Ioc (0 : ℝ) (putnamPeriod d),
        putnamPeriodization a d y * ((((circleFactor r d y)⁻¹).im : ℝ) : ℂ)‖
      ≤ periodizationBound d * putnamPeriod d / 2 := by
  set P := putnamPeriod d with hPdef
  set D := putnamPeriodization a d with hDdef
  have hint1 : IntegrableOn (fun y => D y * (circleFactor r d y)⁻¹) (Ioc (0 : ℝ) P) :=
    integrableOn_periodization_mul hd (continuous_circleKernel hr0 hr1 d)
      (norm_circleKernel_le hr0 hr1 d)
  have hint2 : IntegrableOn (fun y => D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹))
      (Ioc (0 : ℝ) P) := by
    refine integrableOn_periodization_mul hd
      (Complex.continuous_conj.comp (continuous_circleKernel hr0 hr1 d))
      (C := (1 - r)⁻¹) (fun y => ?_)
    rw [RCLike.norm_conj]
    exact norm_circleKernel_le hr0 hr1 d y
  have hsub : (∫ y in Ioc (0 : ℝ) P,
        (D y * (circleFactor r d y)⁻¹ - D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹)))
      = (∫ y in Ioc (0 : ℝ) P, D y * (circleFactor r d y)⁻¹)
        - ∫ y in Ioc (0 : ℝ) P, D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹) :=
    integral_sub hint1 hint2
  have hpt : ∀ y : ℝ,
      D y * (circleFactor r d y)⁻¹ - D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹)
        = (2 * I) * (D y * ((((circleFactor r d y)⁻¹).im : ℝ) : ℂ)) := by
    intro y
    have h := Complex.sub_conj ((circleFactor r d y)⁻¹)
    rw [show D y * (circleFactor r d y)⁻¹ - D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹)
        = D y * ((circleFactor r d y)⁻¹ - (starRingEnd ℂ) ((circleFactor r d y)⁻¹)) by ring, h]
    push_cast
    ring
  have hkey : (∫ y in Ioc (0 : ℝ) P, D y * (circleFactor r d y)⁻¹)
      = (2 * I) * ∫ y in Ioc (0 : ℝ) P, D y * ((((circleFactor r d y)⁻¹).im : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    rw [← setIntegral_congr_fun measurableSet_Ioc (fun y _ => hpt y), hsub,
      integral_periodization_conjCauchy_eq_zero hd hr0 hr1 hzero, sub_zero]
  have hnorm := norm_cauchy_le (a := a) hd hr0 hr1 hzero
  rw [hkey, norm_mul] at hnorm
  have h2 : ‖(2 : ℂ) * I‖ = 2 := by
    rw [norm_mul, Complex.norm_I, mul_one]
    norm_num
  rw [h2] at hnorm
  linarith [hnorm]

end RHTower

end

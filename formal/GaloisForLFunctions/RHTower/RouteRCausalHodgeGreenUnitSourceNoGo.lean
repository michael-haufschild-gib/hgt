import GaloisForLFunctions.RHTower.Suzuki.SuzukiAbelLogFourierKernel
import GaloisForLFunctions.RHTower.GaussHodgeMassCurrent

/-!
# Route R causal Hodge--Green unit-source obstruction

This module formalizes C22 of the Route R prepolar audit.  The causal half-density sine kernel
reads the literal Gauss--Hodge mass collar by an exact resolvent identity.  For `rho = x + iy` in
the open critical strip, the reading is

`(2*x-1)^(2 : ℕ) / ((x^(2 : ℕ)+y^(2 : ℕ)) * ((1-x)^(2 : ℕ)+y^(2 : ℕ)))`.

The identity includes the continuous zero-frequency kernel `u * exp (-u/2)`.  The same kernel
solves the first-order covariant Green system, has zero boundary value, but has covariant boundary
derivative exactly one.  Consequently any ordinary Stokes-flat rule that kills this unit boundary
charge also deletes the physical Green reader: source exactness alone cannot annihilate Route R's
Cartier energy.  A surviving producer must provide an independent arithmetic charge `-1` before
divisor specialization.

No Xi-zero location, RH, critical-line placement, physical annihilation, or same-fibre norm
identity is used.
-/

open Real Set MeasureTheory

noncomputable section

namespace RHTower

def routeRCausalSineKernel (y u : ℝ) : ℝ :=
  if y = 0 then u * Real.exp (-u / 2)
  else Real.exp (-u / 2) * Real.sin (y * u) / y

def routeRCartierHodgeCollar (t u : ℝ) : ℝ :=
  t * (Real.exp (t * u / 2) - Real.exp (-t * u / 2))

theorem routeRCartierHodgeCollar_eq_hodgeMassShape (t u : ℝ) :
    routeRCartierHodgeCollar t u = hodgeMassShape (Real.exp (u / 2)) t := by
  rw [routeRCartierHodgeCollar, hodgeMassShape,
    Real.rpow_def_of_pos (Real.exp_pos _) t,
    Real.rpow_def_of_pos (Real.exp_pos _) (-t), Real.log_exp]
  congr 2 <;> ring_nf

theorem routeRCausalSineKernel_mul_collar_eq
    {y : ℝ} (hy : y ≠ 0) (t u : ℝ) :
    routeRCausalSineKernel y u * routeRCartierHodgeCollar t u =
      (t / y) *
        (Real.exp (-((1 - t) / 2 * u)) * Real.sin (y * u) -
          Real.exp (-((1 + t) / 2 * u)) * Real.sin (y * u)) := by
  rw [routeRCausalSineKernel, if_neg hy, routeRCartierHodgeCollar]
  have hfirst : Real.exp (-u / 2) * Real.exp (t * u / 2) =
      Real.exp (-((1 - t) / 2 * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring_nf
  have hsecond : Real.exp (-u / 2) * Real.exp (-t * u / 2) =
      Real.exp (-((1 + t) / 2 * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring_nf
  calc
    Real.exp (-u / 2) * Real.sin (y * u) / y *
          (t * (Real.exp (t * u / 2) - Real.exp (-t * u / 2))) =
        (t / y) *
          ((Real.exp (-u / 2) * Real.exp (t * u / 2)) * Real.sin (y * u) -
            (Real.exp (-u / 2) * Real.exp (-t * u / 2)) * Real.sin (y * u)) := by
      field_simp
    _ = _ := by rw [hfirst, hsecond]

private theorem integrableOn_exp_neg_mul_sin
    {delta : ℝ} (hdelta : 0 < delta) (y : ℝ) :
    IntegrableOn (fun u : ℝ =>
      Real.exp (-(delta * u)) * Real.sin (y * u)) (Ioi 0) := by
  have hdom : IntegrableOn (fun u : ℝ => Real.exp (-delta * u)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hdelta
  refine Integrable.mono' hdom
    (((Real.continuous_exp.comp (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable) ?_
  filter_upwards with u
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hs := Real.abs_sin_le_one (y * u)
  have he : 0 ≤ Real.exp (-(delta * u)) := (Real.exp_pos _).le
  have hbound : Real.exp (-(delta * u)) * |Real.sin (y * u)| ≤
      Real.exp (-(delta * u)) * 1 := mul_le_mul_of_nonneg_left hs he
  convert hbound using 1
  all_goals ring_nf

theorem integrableOn_routeRCausalSineKernel_mul_collar
    {y t : ℝ} (hy : y ≠ 0) (ht : |t| < 1) :
    IntegrableOn (fun u : ℝ =>
      routeRCausalSineKernel y u * routeRCartierHodgeCollar t u) (Ioi 0) := by
  have hminus : 0 < (1 - t) / 2 := by
    have := lt_of_le_of_lt (le_abs_self t) ht
    linarith
  have hplus : 0 < (1 + t) / 2 := by
    have := lt_of_le_of_lt (neg_le_abs t) ht
    linarith
  have h1r : IntegrableOn (fun u : ℝ =>
      Real.exp (-((1 - t) / 2 * u)) * Real.sin (y * u)) (Ioi 0) := by
    exact integrableOn_exp_neg_mul_sin hminus y
  have h2r : IntegrableOn (fun u : ℝ =>
      Real.exp (-((1 + t) / 2 * u)) * Real.sin (y * u)) (Ioi 0) := by
    exact integrableOn_exp_neg_mul_sin hplus y
  refine MeasureTheory.IntegrableOn.congr_fun
    ((h1r.sub h2r).const_mul (t / y)) ?_ measurableSet_Ioi
  intro u hu
  exact (routeRCausalSineKernel_mul_collar_eq hy t u).symm

theorem integral_routeRCausalSineKernel_mul_collar
    {y t : ℝ} (hy : y ≠ 0) (ht : |t| < 1) :
    (∫ u : ℝ in Ioi 0,
      routeRCausalSineKernel y u * routeRCartierHodgeCollar t u) =
      t * (1 / (((1 - t) / 2) ^ 2 + y ^ 2) -
        1 / (((1 + t) / 2) ^ 2 + y ^ 2)) := by
  have hminus : 0 < (1 - t) / 2 := by
    have := lt_of_le_of_lt (le_abs_self t) ht
    linarith
  have hplus : 0 < (1 + t) / 2 := by
    have := lt_of_le_of_lt (neg_le_abs t) ht
    linarith
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun u _ => routeRCausalSineKernel_mul_collar_eq hy t u)]
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_sub]
  · rw [integral_Ioi_exp_neg_mul_sin hminus,
      integral_Ioi_exp_neg_mul_sin hplus]
    have hA : 0 < ((1 - t) / 2) ^ 2 + y ^ 2 := by
      exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hminus) (sq_nonneg y)
    have hB : 0 < ((1 + t) / 2) ^ 2 + y ^ 2 := by
      exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hplus) (sq_nonneg y)
    field_simp [hy, ne_of_gt hA, ne_of_gt hB]
  · exact integrableOn_exp_neg_mul_sin hminus y
  · exact integrableOn_exp_neg_mul_sin hplus y

theorem routeRCausalSineKernel_zeroFrequency_mul_collar_eq (t u : ℝ) :
    routeRCausalSineKernel 0 u * routeRCartierHodgeCollar t u =
      t * (u * Real.exp (-((1 - t) / 2 * u)) -
        u * Real.exp (-((1 + t) / 2 * u))) := by
  rw [routeRCausalSineKernel, if_pos rfl, routeRCartierHodgeCollar]
  have hfirst : Real.exp (-u / 2) * Real.exp (t * u / 2) =
      Real.exp (-((1 - t) / 2 * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring_nf
  have hsecond : Real.exp (-u / 2) * Real.exp (-t * u / 2) =
      Real.exp (-((1 + t) / 2 * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring_nf
  calc
    u * Real.exp (-u / 2) *
          (t * (Real.exp (t * u / 2) - Real.exp (-t * u / 2))) =
        t * (u * (Real.exp (-u / 2) * Real.exp (t * u / 2)) -
          u * (Real.exp (-u / 2) * Real.exp (-t * u / 2))) := by ring
    _ = _ := by rw [hfirst, hsecond]

theorem integral_routeRCausalSineKernel_zeroFrequency_mul_collar
    {t : ℝ} (ht : |t| < 1) :
    (∫ u : ℝ in Ioi 0,
      routeRCausalSineKernel 0 u * routeRCartierHodgeCollar t u) =
      t * (1 / (((1 - t) / 2) ^ 2) -
        1 / (((1 + t) / 2) ^ 2)) := by
  have hminus : 0 < (1 - t) / 2 := by
    have := lt_of_le_of_lt (le_abs_self t) ht
    linarith
  have hplus : 0 < (1 + t) / 2 := by
    have := lt_of_le_of_lt (neg_le_abs t) ht
    linarith
  have hminusIntegrable : IntegrableOn (fun u : ℝ =>
      u * Real.exp (-((1 - t) / 2 * u))) (Ioi 0) := by
    simpa only [pow_one] using integrableOn_pow_mul_exp_neg_mul_Ioi hminus 1
  have hplusIntegrable : IntegrableOn (fun u : ℝ =>
      u * Real.exp (-((1 + t) / 2 * u))) (Ioi 0) := by
    simpa only [pow_one] using integrableOn_pow_mul_exp_neg_mul_Ioi hplus 1
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun u _ => routeRCausalSineKernel_zeroFrequency_mul_collar_eq t u),
    MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub hminusIntegrable hplusIntegrable]
  have hminusIntegral :
      (∫ u : ℝ in Ioi 0, u * Real.exp (-((1 - t) / 2 * u))) =
        1 / ((1 - t) / 2) ^ 2 := by
    simpa only [pow_one, Nat.factorial_one, Nat.cast_one, one_div] using
      integral_pow_mul_exp_neg_mul_Ioi hminus 1
  have hplusIntegral :
      (∫ u : ℝ in Ioi 0, u * Real.exp (-((1 + t) / 2 * u))) =
        1 / ((1 + t) / 2) ^ 2 := by
    simpa only [pow_one, Nat.factorial_one, Nat.cast_one, one_div] using
      integral_pow_mul_exp_neg_mul_Ioi hplus 1
  rw [hminusIntegral, hplusIntegral]

/-- Exact C22 rational resolvent at a strip coordinate `x`, away from the zero frequency. -/
theorem integral_routeRCausalSineKernel_mul_collar_eq_cartierEnergy
    {x y : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hy : y ≠ 0) :
    (∫ u : ℝ in Ioi 0,
      routeRCausalSineKernel y u *
        routeRCartierHodgeCollar (2 * x - 1) u) =
      (2 * x - 1) ^ 2 /
        ((x ^ 2 + y ^ 2) * ((1 - x) ^ 2 + y ^ 2)) := by
  have ht : |2 * x - 1| < 1 := (abs_lt).2 ⟨by linarith, by linarith⟩
  rw [integral_routeRCausalSineKernel_mul_collar hy ht]
  have hA : 0 < x ^ 2 + y ^ 2 := by positivity
  have hB : 0 < (1 - x) ^ 2 + y ^ 2 := by positivity
  field_simp [ne_of_gt hA, ne_of_gt hB]
  ring

/-- Exact C22 rational resolvent at every real frequency, including `y=0`. -/
theorem integral_routeRCausalSineKernel_mul_collar_eq_cartierEnergy_all
    {x y : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (∫ u : ℝ in Ioi 0,
      routeRCausalSineKernel y u *
        routeRCartierHodgeCollar (2 * x - 1) u) =
      (2 * x - 1) ^ 2 /
        ((x ^ 2 + y ^ 2) * ((1 - x) ^ 2 + y ^ 2)) := by
  by_cases hy : y = 0
  · subst y
    have ht : |2 * x - 1| < 1 := (abs_lt).2 ⟨by linarith, by linarith⟩
    rw [integral_routeRCausalSineKernel_zeroFrequency_mul_collar ht]
    rw [show (1 - (2 * x - 1)) / 2 = 1 - x by ring,
      show (1 + (2 * x - 1)) / 2 = x by ring]
    have hxne : x ≠ 0 := hx0.ne'
    have h1xne : 1 - x ≠ 0 := sub_ne_zero.mpr hx1.ne'
    field_simp [hxne, h1xne]
    ring
  · exact integral_routeRCausalSineKernel_mul_collar_eq_cartierEnergy hx0 hx1 hy

/-- Closed formula for the covariant first derivative `(D+1/2) k_y`. -/
def routeRCausalSineKernelCovariantDerivative (y u : ℝ) : ℝ :=
  if y = 0 then Real.exp (-u / 2)
  else Real.exp (-u / 2) * Real.cos (y * u)

/-- Ordinary derivative of the causal kernel, written as covariant derivative minus half-density
drift. -/
theorem hasDerivAt_routeRCausalSineKernel (y u : ℝ) :
    HasDerivAt (routeRCausalSineKernel y)
      (routeRCausalSineKernelCovariantDerivative y u -
        (1 / 2 : ℝ) * routeRCausalSineKernel y u) u := by
  by_cases hy : y = 0
  · subst y
    simp only [routeRCausalSineKernel, routeRCausalSineKernelCovariantDerivative,
      if_pos, zero_mul, Real.sin_zero, mul_zero, zero_div]
    rw [show routeRCausalSineKernel 0 =
        (fun v : ℝ => v * Real.exp (-v / 2)) by
      funext v
      simp [routeRCausalSineKernel]]
    change HasDerivAt (fun v : ℝ => v * Real.exp (-v / 2))
      (Real.exp (-u / 2) - (1 / 2 : ℝ) * (u * Real.exp (-u / 2))) u
    have hexp : HasDerivAt (fun v : ℝ => Real.exp (-v / 2))
        (Real.exp (-u / 2) * (-(1 : ℝ) / 2)) u :=
      ((hasDerivAt_id u).neg.div_const 2).exp
    refine ((hasDerivAt_id u).mul hexp).congr_deriv ?_
    simp only [id_eq]
    ring
  · rw [show routeRCausalSineKernel y =
        (fun v : ℝ => Real.exp (-v / 2) * Real.sin (y * v) / y) by
      funext v
      simp [routeRCausalSineKernel, hy]]
    simp only [routeRCausalSineKernelCovariantDerivative, if_neg hy]
    change HasDerivAt
      (fun v : ℝ => Real.exp (-v / 2) * Real.sin (y * v) / y)
      (Real.exp (-u / 2) * Real.cos (y * u) -
        (1 / 2 : ℝ) * (Real.exp (-u / 2) * Real.sin (y * u) / y)) u
    have hexp : HasDerivAt (fun v : ℝ => Real.exp (-v / 2))
        (Real.exp (-u / 2) * (-(1 : ℝ) / 2)) u :=
      ((hasDerivAt_id u).neg.div_const 2).exp
    have hsin : HasDerivAt (fun v : ℝ => Real.sin (y * v))
        (Real.cos (y * u) * y) u := by
      simpa using ((hasDerivAt_const u y).mul (hasDerivAt_id u) |>.sin)
    refine ((hexp.mul hsin).div_const y).congr_deriv ?_
    field_simp [hy]
    ring

/-- The covariant derivative has its complementary derivative law. -/
theorem hasDerivAt_routeRCausalSineKernelCovariantDerivative (y u : ℝ) :
    HasDerivAt (routeRCausalSineKernelCovariantDerivative y)
      (-(1 / 2 : ℝ) * routeRCausalSineKernelCovariantDerivative y u -
        y ^ 2 * routeRCausalSineKernel y u) u := by
  by_cases hy : y = 0
  · subst y
    simp only [routeRCausalSineKernel, routeRCausalSineKernelCovariantDerivative,
      if_pos, zero_mul, Real.sin_zero, mul_zero, zero_div]
    rw [show routeRCausalSineKernelCovariantDerivative 0 =
        (fun v : ℝ => Real.exp (-v / 2)) by
      funext v
      simp [routeRCausalSineKernelCovariantDerivative]]
    norm_num
    refine (((hasDerivAt_id u).neg.div_const 2).exp).congr_deriv ?_
    simp only [Pi.neg_apply, id_eq]
    ring
  · simp only [routeRCausalSineKernel, routeRCausalSineKernelCovariantDerivative,
      if_neg hy]
    rw [show routeRCausalSineKernelCovariantDerivative y =
        (fun v : ℝ => Real.exp (-v / 2) * Real.cos (y * v)) by
      funext v
      simp [routeRCausalSineKernelCovariantDerivative, hy]]
    change HasDerivAt
      (fun v : ℝ => Real.exp (-v / 2) * Real.cos (y * v))
      (-(1 / 2 : ℝ) * (Real.exp (-u / 2) * Real.cos (y * u)) -
        y ^ 2 * (Real.exp (-u / 2) * Real.sin (y * u) / y)) u
    have hexp : HasDerivAt (fun v : ℝ => Real.exp (-v / 2))
        (Real.exp (-u / 2) * (-(1 : ℝ) / 2)) u :=
      ((hasDerivAt_id u).neg.div_const 2).exp
    have hcos : HasDerivAt (fun v : ℝ => Real.cos (y * v))
        (-Real.sin (y * u) * y) u := by
      simpa using ((hasDerivAt_const u y).mul (hasDerivAt_id u) |>.cos)
    refine (hexp.mul hcos).congr_deriv ?_
    field_simp [hy]
    ring

/-- The causal Green kernel has zero boundary value. -/
theorem routeRCausalSineKernel_zero (y : ℝ) :
    routeRCausalSineKernel y 0 = 0 := by
  by_cases hy : y = 0 <;>
    simp [routeRCausalSineKernel, hy]

/-- C22 unit-source anomaly: its covariant boundary derivative is exactly one for every
frequency, including the continuous zero-frequency extension. -/
theorem routeRCausalSineKernelCovariantDerivative_zero (y : ℝ) :
    routeRCausalSineKernelCovariantDerivative y 0 = 1 := by
  by_cases hy : y = 0 <;>
    simp [routeRCausalSineKernelCovariantDerivative, hy]

/-- A source-flat boundary condition is incompatible with the physical causal Green reader. -/
theorem not_routeRCausalSineKernel_sourceFlat (y : ℝ) :
    routeRCausalSineKernelCovariantDerivative y 0 ≠ 0 := by
  rw [routeRCausalSineKernelCovariantDerivative_zero]
  norm_num

end RHTower

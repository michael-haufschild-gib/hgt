import GaloisForLFunctions.RHTower.WeilLogShiftDomainBoundary
import GaloisForLFunctions.RHTower.WeilLogShiftReflection

/-!
# The critical exponential endpoint diverges

A shrinking central interval retains the exact double-exponential constant in
the autocorrelation lower bound. At integer logarithms its width leaves a
harmonic factor, which excludes summability at the critical coefficient rate.
-/

open MeasureTheory Filter Topology Set Zeta23 Real

noncomputable section

namespace RHTower

open WeilExcess

/-- An arbitrary positive central radius gives a full-kernel lower bound;
there is no cutoff-transition factor. -/
theorem riemannAutocorr_central_lower {z d : ℝ} (hz : 0 ≤ z) (hd : 0 < d) :
    (2 * d * (2 * π ^ 2) ^ 2) * exp (-(2 * π * exp (z + 2 * d))) ≤
      riemannAutocorr z := by
  have hpoint : ∀ t ∈ Ioc (z / 2 - d) (z / 2 + d),
      (2 * π ^ 2) ^ 2 * exp (-(2 * π * exp (z + 2 * d))) ≤
        riemannKernelReal t * riemannKernelReal (t - z) := by
    intro t ht
    have ht1 : |t| ≤ z / 2 + d := by
      rw [abs_le]
      constructor <;> linarith only [ht.1, ht.2, hz]
    have ht2 : |t - z| ≤ z / 2 + d := by
      rw [abs_le]
      constructor <;> linarith only [ht.1, ht.2, hz]
    have h1 := exp_le_exp.mpr (show 2 * |t| ≤ z + 2 * d by linarith only [ht1])
    have h2 := exp_le_exp.mpr (show 2 * |t - z| ≤ z + 2 * d by linarith only [ht2])
    have hs : π * (exp (2 * |t|) + exp (2 * |t - z|)) ≤ 2 * π * exp (z + 2 * d) := by
      have h := mul_le_mul_of_nonneg_left (add_le_add h1 h2) pi_pos.le
      nlinarith only [h]
    have heq (U V : ℝ) : (2 * π ^ 2 * exp U) * (2 * π ^ 2 * exp V) =
        (2 * π ^ 2) ^ 2 * exp (U + V) := by rw [exp_add]; ring
    have hprod : (2 * π ^ 2) ^ 2 * exp (-(2 * π * exp (z + 2 * d))) ≤
        (2 * π ^ 2 * exp (-(π * exp (2 * |t|)))) *
          (2 * π ^ 2 * exp (-(π * exp (2 * |t - z|)))) := by
      rw [heq]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply exp_le_exp.mpr
      linarith only [hs]
    exact hprod.trans (mul_le_mul (ExposingRayTail.phi_lower t)
      (ExposingRayTail.phi_lower (t - z)) (by positivity) (riemannKernelReal_pos _).le)
  have hi := setIntegral_mono_on (integrableOn_const (by simp))
    (integrable_riemannKernelReal_mul z).integrableOn measurableSet_Ioc hpoint
  have hconst : (∫ t in Ioc (z / 2 - d) (z / 2 + d),
      (2 * π ^ 2) ^ 2 * exp (-(2 * π * exp (z + 2 * d)))) =
      (2 * d * (2 * π ^ 2) ^ 2) * exp (-(2 * π * exp (z + 2 * d))) := by
    rw [setIntegral_const, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    simp only [smul_eq_mul]
    ring
  rw [hconst] at hi
  exact hi.trans (setIntegral_le_integral (integrable_riemannKernelReal_mul z)
    (Eventually.of_forall fun t => mul_nonneg (riemannKernelReal_pos t).le
      (riemannKernelReal_pos (t - z)).le))

private theorem exp_two_mul_le_chord {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    exp (2 * d) ≤ 1 + (exp 2 - 1) * d := by
  have h := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (2 : ℝ))
    (show 0 ≤ 1 - d by linarith only [hd1]) hd0 (show 1 - d + d = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, exp_zero, mul_one] at h
  rw [mul_comm d 2] at h
  nlinarith only [h]

/-- A shrinking interval retains the exact critical exponential constant,
at the cost of a single exponential width factor. -/
theorem exists_riemannAutocorr_critical_lower :
    ∃ D : ℝ, 0 < D ∧ ∀ z : ℝ, 0 ≤ z →
      D * exp (-z) * exp (-(2 * π * exp z)) ≤ riemannAutocorr z := by
  let A := exp (2 : ℝ) - 1
  let D := 2 * (2 * π ^ 2) ^ 2 * exp (-(2 * π * A))
  refine ⟨D, by dsimp only [D]; positivity, fun z hz => ?_⟩
  let d := exp (-z)
  have hd : 0 < d := exp_pos _
  have hd1 : d ≤ 1 := exp_le_one_iff.mpr (by linarith only [hz])
  have hchord := exp_two_mul_le_chord hd.le hd1
  have hcancel : exp z * d = 1 := by
    dsimp only [d]
    rw [← exp_add, add_neg_cancel, exp_zero]
  have hscale : exp (z + 2 * d) ≤ exp z + A := by
    rw [exp_add]
    calc exp z * exp (2 * d) ≤ exp z * (1 + A * d) :=
        mul_le_mul_of_nonneg_left hchord (exp_pos _).le
      _ = exp z + A * (exp z * d) := by ring
      _ = exp z + A := by rw [hcancel, mul_one]
  calc D * exp (-z) * exp (-(2 * π * exp z)) =
      (2 * d * (2 * π ^ 2) ^ 2) * exp (-(2 * π * (exp z + A))) := by
        rw [show -(2 * π * (exp z + A)) = -(2 * π * A) + -(2 * π * exp z) by ring, exp_add]
        dsimp only [D, d]
        ring
    _ ≤ (2 * d * (2 * π ^ 2) ^ 2) * exp (-(2 * π * exp (z + 2 * d))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply exp_le_exp.mpr
      exact neg_le_neg (mul_le_mul_of_nonneg_left hscale (by positivity))
    _ ≤ riemannAutocorr z := riemannAutocorr_central_lower hz hd

/-- At the critical rate, the paired kernel still has a positive harmonic
lower envelope on the integer tail. -/
theorem exists_paired_logKernel_critical_lower (y : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop,
      (D / n) * exp (-(logKernelCriticalRate y * n)) ≤ pairedLogKernel y n := by
  obtain ⟨D, hD, hK⟩ := exists_riemannAutocorr_critical_lower
  refine ⟨D * exp |y|, by positivity,
    eventually_atTop.mpr ⟨⌊exp |y|⌋₊ + 1, fun n hn => ?_⟩⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnR : (⌊exp |y|⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hlog : |y| < log n := (lt_log_iff_exp_lt hnpos).mpr
    ((Nat.lt_floor_add_one _).trans_le hnR)
  have hk := hK (log n - |y|) (by linarith only [hlog])
  have hwidth : exp (-(log n - |y|)) = exp |y| / n := by
    rw [show -(log n - |y|) = |y| - log n by ring, exp_sub, exp_log hnpos]
  have hrate : 2 * π * exp (log n - |y|) = logKernelCriticalRate y * n := by
    rw [sub_eq_add_neg, exp_add, exp_log hnpos, logKernelCriticalRate]
    ring
  rw [hwidth, hrate] at hk
  have hpair : riemannAutocorr (log n - |y|) ≤ pairedLogKernel y n := by
    unfold pairedLogKernel
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy, show log n - y = -(y - log n) by ring, riemannAutocorr_neg]
      linarith only [riemannAutocorr_nonneg (y + log n)]
    · rw [abs_of_neg (lt_of_not_ge hy), sub_neg_eq_add, add_comm (log n) y]
      linarith only [riemannAutocorr_nonneg (y - log n)]
  calc (D * exp |y| / n) * exp (-(logKernelCriticalRate y * n)) =
      D * (exp |y| / n) * exp (-(logKernelCriticalRate y * n)) := by ring
    _ ≤ riemannAutocorr (log n - |y|) := hk
    _ ≤ pairedLogKernel y n := hpair

/-- Potential convergence forces a critical-rate damping moment with one
harmonic factor, improving the former strictly supercritical necessity. -/
theorem summable_critical_damping_over_nat_of_kernelPotential {v : ℕ → ℝ} {y : ℝ}
    (hs : Summable fun n => v n * pairedLogKernel y n) :
    Summable fun n => (|v n| / n) * exp (-(logKernelCriticalRate y * n)) := by
  obtain ⟨D, hD, hlower⟩ := exists_paired_logKernel_critical_lower y
  refine (hs.norm.mul_left (1 / D)).of_norm_bounded_eventually_nat ?_
  filter_upwards [hlower] with n hn
  have h := mul_le_mul_of_nonneg_left hn (abs_nonneg (v n))
  simp only [Real.norm_eq_abs, abs_mul, abs_div, abs_abs,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n), abs_of_pos (exp_pos _),
    abs_of_pos (pairedLogKernel_pos y n)]
  calc (|v n| / n) * exp (-(logKernelCriticalRate y * n)) ≤
      (|v n| * pairedLogKernel y n) / D := by
        apply (le_div_iff₀ hD).mpr
        calc ((|v n| / n) * exp (-(logKernelCriticalRate y * n))) * D =
            |v n| * ((D / n) * exp (-(logKernelCriticalRate y * n))) := by ring
          _ ≤ _ := h
    _ = _ := by ring

/-- Pure exponential coefficient growth at the exact critical rate diverges. -/
theorem not_summable_critical_exponential_kernelPotential (y : ℝ) :
    ¬ Summable fun n : ℕ => exp (logKernelCriticalRate y * n) * pairedLogKernel y n := by
  intro hs
  have hd := summable_critical_damping_over_nat_of_kernelPotential hs
  have hh : Summable fun n : ℕ => (1 : ℝ) / n := by
    refine hd.congr fun n => ?_
    rw [abs_of_pos (exp_pos _)]
    calc (exp (logKernelCriticalRate y * n) / n) * exp (-(logKernelCriticalRate y * n)) =
        (exp (logKernelCriticalRate y * n) * exp (-(logKernelCriticalRate y * n))) / n := by ring
      _ = 1 / n := by rw [← exp_add, add_neg_cancel, exp_zero]
  have hfalse := (summable_one_div_nat_pow (p := 1)).mp (by simpa only [pow_one] using hh)
  norm_num at hfalse

/-- Exact pure-exponential convergence criterion, now including the critical
endpoint in the divergent side. -/
theorem summable_exponential_kernelPotential_iff (y ρ : ℝ) :
    (Summable fun n : ℕ => exp (ρ * n) * pairedLogKernel y n) ↔ ρ < logKernelCriticalRate y := by
  constructor
  · intro hs
    by_contra hρ
    rcases lt_or_eq_of_le (le_of_not_gt hρ) with h | h
    · exact not_summable_exponential_kernelPotential_of_rate_lt h hs
    · rw [← h] at hs
      exact not_summable_critical_exponential_kernelPotential y hs
  · intro hρ
    apply summable_kernelPotential_of_exponential_growth hρ (C := 1)
    intro n
    rw [abs_of_pos (exp_pos _), one_mul]

/-- Equality and every larger rate are excluded by the exact criterion. -/
theorem not_summable_exponential_kernelPotential_of_rate_le {y ρ : ℝ}
    (hρ : logKernelCriticalRate y ≤ ρ) :
    ¬ Summable fun n : ℕ => exp (ρ * n) * pairedLogKernel y n :=
  fun hs => (not_lt_of_ge hρ) ((summable_exponential_kernelPotential_iff y ρ).mp hs)

/-- The positive exponential majorant drives the actual probe to plus infinity
at and above the inverse-location rate. -/
theorem exponential_majorant_logShift_probe_atTop_of_rate_le {m : ℕ} (hm : 2 ≤ m)
    {ρ : ℝ} (hρ : 2 * π / m ≤ ρ) :
    Tendsto (fun L : ℝ => (weilFullFunctional
      (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + sqrt n * exp (ρ * n))
      (EF.weilTest (logShiftRiemannDifference L (log m))
        (logShiftRiemannDifference L (log m)))).re) atTop atTop := by
  let lam (n : ℕ) : ℝ := (ArithmeticFunction.vonMangoldt n : ℝ) + sqrt n * exp (ρ * n)
  have hdev (n : ℕ) : weilDeviation lam n = if 2 ≤ n then exp (ρ * n) else 0 := by
    by_cases hn : 2 ≤ n
    · have hsqrt : sqrt (n : ℝ) ≠ 0 :=
        (sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))).ne'
      simp only [weilDeviation, if_pos hn]
      dsimp only [lam]
      calc ((ArithmeticFunction.vonMangoldt n : ℝ) + sqrt n * exp (ρ * n) -
          ArithmeticFunction.vonMangoldt n) / sqrt n = exp (ρ * n) * (sqrt n / sqrt n) := by ring
        _ = exp (ρ * n) := by rw [div_self hsqrt, mul_one]
    · simp only [weilDeviation, if_neg hn]
  have hdef (n : ℕ) : deviationDeficit lam n = 0 := by
    rw [deviationDeficit, hdev]
    split_ifs
    · exact max_eq_right (neg_nonpos.mpr (exp_pos _).le)
    · simp only [neg_zero, max_self]
  have hbad : ¬ Summable fun n => weilDeviation lam n * pairedLogKernel (log m) n := by
    intro hs
    have hr : logKernelCriticalRate (log m) ≤ ρ := by
      rwa [logKernelCriticalRate_log_nat (show 1 ≤ m by omega)]
    apply not_summable_exponential_kernelPotential_of_rate_le hr
    refine hs.of_norm_bounded_eventually_nat ?_
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    rw [hdev, if_pos hn, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (exp_pos _).le (pairedLogKernel_pos (log m) n).le)]
  apply tendsto_logShift_probe_atTop_of_nonsummable_sample_of_local_deficit hm _ hbad
  simpa only [hdef, zero_mul] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))

end RHTower

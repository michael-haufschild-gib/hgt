import GaloisForLFunctions.RHTower.CCMPrimeDeficitForceAction

/-!
# Exact signed-work law at the critical scale

The squared square-root-normalized deficit is a nonnegative energy. Its
derivative has unit damping and the literal signed arithmetic work as input.
Absolute continuity gives the balance across every prime entry. Neither a
sign nor a uniform bound is imposed on the input. On the initial prime-free
chamber the energy strictly increases, excluding dissipation from time zero.
-/

noncomputable section
open MeasureTheory Filter Set

namespace RHTower

def ccmPrimeDeficitCriticalEnergy (t : ℝ) : ℝ :=
  Real.exp (-t) * ccmLogChebyshevDeficitPrimitive t ^ 2

def ccmPrimeDeficitSignedWorkDensity (t : ℝ) : ℝ :=
  Real.exp (-t) * ccmLogChebyshevDeficitPrimitive t *
    (Real.exp t - Chebyshev.psi (Real.exp t))

private theorem deficit_locallyIntegrable :
    LocallyIntegrable (fun t => Real.exp t - Chebyshev.psi (Real.exp t)) volume :=
  Real.continuous_exp.locallyIntegrable.sub
    ((Chebyshev.psi_mono.comp Real.exp_monotone).locallyIntegrable)

private theorem deficit_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun t => Real.exp t - Chebyshev.psi (Real.exp t)) volume a b :=
  (Real.continuous_exp.intervalIntegrable a b).sub
    (Chebyshev.psi_mono.comp Real.exp_monotone).intervalIntegrable

theorem ae_hasDerivAt_ccmLogChebyshevDeficitPrimitive :
    ∀ᵐ t : ℝ ∂volume, HasDerivAt ccmLogChebyshevDeficitPrimitive
      (Real.exp t - Chebyshev.psi (Real.exp t)) t := by
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral deficit_locallyIntegrable]
    with t ht
  exact ht 0

theorem ccmPrimeDeficitCriticalEnergy_nonneg (t : ℝ) :
    0 ≤ ccmPrimeDeficitCriticalEnergy t :=
  mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

@[simp] theorem ccmPrimeDeficitCriticalEnergy_zero : ccmPrimeDeficitCriticalEnergy 0 = 0 := by
  simp [ccmPrimeDeficitCriticalEnergy, ccmLogChebyshevDeficitPrimitive]

theorem continuous_ccmPrimeDeficitCriticalEnergy : Continuous ccmPrimeDeficitCriticalEnergy :=
  Real.continuous_exp.comp continuous_neg |>.mul (continuous_ccmLogChebyshevDeficitPrimitive.pow 2)

theorem intervalIntegrable_ccmPrimeDeficitSignedWorkDensity (a b : ℝ) :
    IntervalIntegrable ccmPrimeDeficitSignedWorkDensity volume a b :=
  (deficit_intervalIntegrable a b).continuousOn_mul
    (((Real.continuous_exp.comp continuous_neg).mul
      continuous_ccmLogChebyshevDeficitPrimitive).continuousOn)

/-- The critical energy has unit damping, but its source is signed prime work. -/
theorem ae_hasDerivAt_ccmPrimeDeficitCriticalEnergy :
    ∀ᵐ t : ℝ ∂volume, HasDerivAt ccmPrimeDeficitCriticalEnergy
      (2 * ccmPrimeDeficitSignedWorkDensity t - ccmPrimeDeficitCriticalEnergy t) t := by
  filter_upwards [ae_hasDerivAt_ccmLogChebyshevDeficitPrimitive] with t ht
  have he := ((hasDerivAt_id t).neg).exp
  convert! he.mul (ht.pow 2) using 1
  simp only [ccmPrimeDeficitCriticalEnergy, ccmPrimeDeficitSignedWorkDensity, id_eq,
    Pi.neg_apply, Pi.pow_apply]
  ring

/-- Exact balance across all prime entries on every finite time interval. -/
theorem ccmPrimeDeficitCriticalEnergy_balance (a b : ℝ) :
    ccmPrimeDeficitCriticalEnergy b - ccmPrimeDeficitCriticalEnergy a +
      (∫ t in a..b, ccmPrimeDeficitCriticalEnergy t) =
      2 * ∫ t in a..b, ccmPrimeDeficitSignedWorkDensity t := by
  have hD : AbsolutelyContinuousOnInterval ccmLogChebyshevDeficitPrimitive a b := by
    have hi := deficit_intervalIntegrable a b
    have h : AbsolutelyContinuousOnInterval
        (fun t => ∫ s in a..t, Real.exp s - Chebyshev.psi (Real.exp s)) a b :=
      hi.absolutelyContinuousOnInterval_intervalIntegral (by simp)
    have heq : ccmLogChebyshevDeficitPrimitive = fun t =>
        ccmLogChebyshevDeficitPrimitive a +
          ∫ s in a..t, Real.exp s - Chebyshev.psi (Real.exp s) := by
      funext t
      exact (intervalIntegral.integral_add_adjacent_intervals
        (deficit_intervalIntegrable 0 a)
        (deficit_intervalIntegrable a t)).symm
    rw [heq]
    have hc : ContDiff ℝ 1 (fun _ : ℝ => ccmLogChebyshevDeficitPrimitive a) := contDiff_const
    exact hc.contDiffOn.absolutelyContinuousOnInterval.fun_add h
  have he : ContDiff ℝ 1 (fun t : ℝ => Real.exp (-t)) := by fun_prop
  have hE : AbsolutelyContinuousOnInterval ccmPrimeDeficitCriticalEnergy a b := by
    change AbsolutelyContinuousOnInterval
      (fun t => Real.exp (-t) * ccmLogChebyshevDeficitPrimitive t ^ 2) a b
    simpa only [pow_two] using
      he.contDiffOn.absolutelyContinuousOnInterval.fun_mul (hD.fun_mul hD)
  have hint := hE.integral_deriv_eq_sub
  have heq : (∫ t in a..b, deriv ccmPrimeDeficitCriticalEnergy t) =
      ∫ t in a..b, 2 * ccmPrimeDeficitSignedWorkDensity t - ccmPrimeDeficitCriticalEnergy t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_hasDerivAt_ccmPrimeDeficitCriticalEnergy] with t ht _
    exact ht.deriv
  rw [heq, intervalIntegral.integral_sub
    ((intervalIntegrable_ccmPrimeDeficitSignedWorkDensity a b).const_mul 2)
    (continuous_ccmPrimeDeficitCriticalEnergy.intervalIntegrable a b),
    intervalIntegral.integral_const_mul] at hint
  linarith only [hint]

/-- Despite an uncontrolled pointwise sign, total signed work from the
initial state is nonnegative: it pays for both terminal energy and damping. -/
theorem ccmPrimeDeficitSignedWork_nonneg {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ ∫ t in (0 : ℝ)..T, ccmPrimeDeficitSignedWorkDensity t := by
  have h := ccmPrimeDeficitCriticalEnergy_balance 0 T
  rw [ccmPrimeDeficitCriticalEnergy_zero, sub_zero] at h
  have hi : 0 ≤ ∫ t in (0 : ℝ)..T, ccmPrimeDeficitCriticalEnergy t :=
    intervalIntegral.integral_nonneg hT (fun t _ => ccmPrimeDeficitCriticalEnergy_nonneg t)
  linarith [ccmPrimeDeficitCriticalEnergy_nonneg T]

theorem ccmLogChebyshevDeficitPrimitive_before_first_prime {t : ℝ}
    (ht : 0 ≤ t) (hfirst : t < Real.log 2) :
    ccmLogChebyshevDeficitPrimitive t = Real.exp t - 1 := by
  have heq : ccmLogChebyshevDeficitPrimitive t = ∫ s in (0 : ℝ)..t, Real.exp s := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hst : s ≤ t := (uIcc_of_le ht ▸ hs).2
    have he : Real.exp s < 2 := (Real.lt_log_iff_exp_lt (by norm_num)).mp (hst.trans_lt hfirst)
    change Real.exp s - Chebyshev.psi (Real.exp s) = Real.exp s
    rw [Chebyshev.psi_eq_zero_of_lt_two he, sub_zero]
  rw [heq, integral_exp, Real.exp_zero]

/-- A direct test rejects monotone dissipation from the initial state. This
does not decide whether a bounded signed-work estimate holds later. -/
theorem ccmPrimeDeficitCriticalEnergy_pos_before_first_prime {t : ℝ}
    (ht : 0 < t) (hfirst : t < Real.log 2) :
    0 < ccmPrimeDeficitCriticalEnergy t := by
  rw [ccmPrimeDeficitCriticalEnergy,
    ccmLogChebyshevDeficitPrimitive_before_first_prime ht.le hfirst]
  exact mul_pos (Real.exp_pos _) (sq_pos_of_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)))

/-- The proposed global monotone-energy control is false for the actual
arithmetic source, already before its first prime entry. -/
theorem not_antitoneOn_ccmPrimeDeficitCriticalEnergy :
    ¬AntitoneOn ccmPrimeDeficitCriticalEnergy (Ici 0) := by
  intro h
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpos := ccmPrimeDeficitCriticalEnergy_pos_before_first_prime
    (half_pos hlog) (half_lt_self hlog)
  have hle := h (show (0 : ℝ) ∈ Ici 0 by simp)
    (show Real.log 2 / 2 ∈ Ici 0 from (half_pos hlog).le) (half_pos hlog).le
  rw [ccmPrimeDeficitCriticalEnergy_zero] at hle
  exact (not_le_of_gt hpos) hle

end RHTower

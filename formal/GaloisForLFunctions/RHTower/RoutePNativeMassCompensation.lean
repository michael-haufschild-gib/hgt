import GaloisForLFunctions.RHTower.RoutePNativeLatePrimeMixedAdmission
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The terminal energy retained by native mass compensation

The actual logarithmic profile has zero total mass. Its causal mass
primitive can therefore restore the mass of a truncation. This operation
does not remove the native square: its exact finite-window energy contains
the original energy and a nonnegative terminal square for damping at most
one. At zero damping the compensated profile still has infinite energy.

No positive-damping energy admission is assumed or produced here.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace RHTower

def routePNativeMassPrefix (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, criticalAbelLogProfile t

def routePNativeMassCompensatedProfile (ε t : ℝ) : ℝ :=
  Real.exp (t / 2) *
    (criticalAbelLogProfile t + (1 - ε) * routePNativeMassPrefix t)

private theorem mass_deriv (t : ℝ) :
    HasDerivAt routePNativeMassPrefix (criticalAbelLogProfile t) t :=
  intervalIntegral.integral_hasDerivAt_right
    (continuous_criticalAbelLogProfile.intervalIntegrable _ _)
    continuous_criticalAbelLogProfile.aestronglyMeasurable.stronglyMeasurableAtFilter
    continuous_criticalAbelLogProfile.continuousAt

private theorem mass_continuous : Continuous routePNativeMassPrefix :=
  (show Differentiable ℝ routePNativeMassPrefix from
    fun t => (mass_deriv t).differentiableAt).continuous

private theorem mass_zero : routePNativeMassPrefix 0 = 0 := by
  simp [routePNativeMassPrefix]

private theorem compensated_continuous (ε : ℝ) :
    Continuous (routePNativeMassCompensatedProfile ε) :=
  (Real.continuous_exp.comp (continuous_id.div_const 2)).mul
    (continuous_criticalAbelLogProfile.add (continuous_const.mul mass_continuous))

/-- The correction uses the literal remaining signed native mass. -/
theorem routePNativeMassPrefix_eq_neg_tail (T : ℝ) :
    routePNativeMassPrefix T = -(∫ t in Ioi T, criticalAbelLogProfile t) := by
  have h := intervalIntegral.integral_interval_add_Ioi
    (integrable_criticalAbelLogProfile.integrableOn (s := Ioi 0))
    (integrable_criticalAbelLogProfile.integrableOn (s := Ioi T))
  rw [criticalAbelLogProfile_mass_zero] at h
  exact eq_neg_of_add_eq_zero_left h

private theorem weighted_square (ε t v : ℝ) :
    Real.exp (-ε * t) * (Real.exp (t / 2) * v) ^ 2 =
      Real.exp ((1 - ε) * t) * v ^ 2 := by
  rw [mul_pow, sq (Real.exp (t / 2)), ← Real.exp_add]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

private theorem boundary_deriv (lam t : ℝ) :
    HasDerivAt (fun u => lam * Real.exp (lam * u) * routePNativeMassPrefix u ^ 2)
      (Real.exp (lam * t) *
        ((criticalAbelLogProfile t + lam * routePNativeMassPrefix t) ^ 2 -
          criticalAbelLogProfile t ^ 2)) t := by
  have h := (((hasDerivAt_id t).const_mul lam).exp.const_mul lam).mul
    ((mass_deriv t).pow 2)
  change HasDerivAt ((fun u => lam * Real.exp (lam * u)) * routePNativeMassPrefix ^ 2) _ t
  apply h.congr_deriv
  simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

/-- Exact native finite-window energy identity, retaining the full terminal
mass square. It holds before any whole-ray admission is known. -/
theorem routePNativeMassCompensatedProfile_energy (ε T : ℝ) :
    (∫ t in (0 : ℝ)..T, Real.exp (-ε * t) *
      routePNativeMassCompensatedProfile ε t ^ 2) =
    (∫ t in (0 : ℝ)..T, Real.exp (-ε * t) * routePNativeCriticalProfile t ^ 2) +
      (1 - ε) * Real.exp ((1 - ε) * T) * routePNativeMassPrefix T ^ 2 := by
  let lam := 1 - ε
  have hc : Continuous (fun t => Real.exp (lam * t) *
      (criticalAbelLogProfile t + lam * routePNativeMassPrefix t) ^ 2) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      ((continuous_criticalAbelLogProfile.add (continuous_const.mul mass_continuous)).pow 2)
  have ha : Continuous (fun t => Real.exp (lam * t) * criticalAbelLogProfile t ^ 2) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (continuous_criticalAbelLogProfile.pow 2)
  have hi : IntervalIntegrable (fun t => Real.exp (lam * t) *
      ((criticalAbelLogProfile t + lam * routePNativeMassPrefix t) ^ 2 -
        criticalAbelLogProfile t ^ 2)) volume 0 T := by
    simpa only [mul_sub, Pi.sub_def] using (hc.sub ha).intervalIntegrable 0 T
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => boundary_deriv lam t) hi
  simp only [mass_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, sub_zero] at h
  simp_rw [mul_sub] at h
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) (ha.intervalIntegrable _ _)] at h
  simp_rw [routePNativeMassCompensatedProfile, routePNativeCriticalProfile_eq_exp_mul_logProfile,
    weighted_square]
  dsimp only [lam] at h
  linarith only [h]

/-- Native zero-mass compensation does not repair the critical square
admission: even the compensated actual profile has infinite energy. -/
theorem not_integrableOn_routePNativeMassCompensatedProfile_sq :
    ¬ IntegrableOn (fun t => routePNativeMassCompensatedProfile 0 t ^ 2) (Ioi 0) := by
  intro hi
  let B := ∫ t in Ioi (0 : ℝ), routePNativeMassCompensatedProfile 0 t ^ 2
  obtain ⟨T, hT, hbig⟩ := routePNativeCritical_square_energy_cofinally_unbounded B 0
  have hbound : (∫ t in (0 : ℝ)..T, routePNativeMassCompensatedProfile 0 t ^ 2) ≤ B := by
    rw [intervalIntegral.integral_of_le hT]
    exact setIntegral_mono_set hi (Eventually.of_forall (fun _ => sq_nonneg _))
      (Eventually.of_forall (fun _ ht => ht.1))
  have he := routePNativeMassCompensatedProfile_energy 0 T
  simp only [sub_zero, neg_zero, zero_mul, Real.exp_zero, one_mul] at he
  have hnonneg : 0 ≤ Real.exp T * routePNativeMassPrefix T ^ 2 := by positivity
  linarith

end RHTower

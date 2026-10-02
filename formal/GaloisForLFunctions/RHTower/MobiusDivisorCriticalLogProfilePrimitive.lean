import GaloisForLFunctions.RHTower.MobiusDivisorCriticalLogProfile
import GaloisForLFunctions.RHTower.MobiusDivisorCriticalMovingHeadFiniteSource
import GaloisForLFunctions.RHTower.CriticalAbelRoutePAsymptoticBridge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Exact primitive of the critical log-profile velocity

The right derivative retains the arithmetic floor at integer jumps. Its
integral recovers the literal profile at every finite nonnegative clock,
which justifies the later finite-prime interchange and integration by parts.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower

private def unscaledLogSource (t : ℝ) : ℝ :=
  Real.exp (t / 2) * psiDefect ⌊Real.exp t⌋₊

private theorem unscaledLogSource_integrable (T : ℝ) :
    IntegrableOn unscaledLogSource (Icc (0 : ℝ) T) := by
  have hq : IntegrableOn criticalAbelLogDefect (Ioi (0 : ℝ)) := by
    simpa using integrableOn_criticalAbelLogDefect_moment 0
  have hi : IntegrableOn criticalAbelLogDefect (Icc (0 : ℝ) T) :=
    (integrableOn_Icc_iff_integrableOn_Ioc).mpr
      (hq.mono_set (fun _ hx => hx.1))
  have h := hi.mul_continuousOn
    ((Real.continuous_exp.comp ((continuous_const (y := (3 / 2 : ℝ))).mul continuous_id)).continuousOn)
    isCompact_Icc
  apply h.congr_fun _ measurableSet_Icc
  intro t _
  change criticalAbelLogDefect t * Real.exp ((3 / 2 : ℝ) * t) = unscaledLogSource t
  dsimp [criticalAbelLogDefect, unscaledLogSource]
  calc
    _ = (Real.exp (-t) * Real.exp ((3 / 2 : ℝ) * t)) * psiDefect ⌊Real.exp t⌋₊ := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

private theorem logProfile_eq_source_integral {t : ℝ} (ht : 0 ≤ t) :
    criticalAbelLogProfile t = Real.exp (-(3 / 2 : ℝ) * t) *
      ((∫ u in (0 : ℝ)..t, unscaledLogSource u) / 2) := by
  have h := criticalContinuousAbel_exp_eq_log_integral ht
  dsimp [criticalAbelLogProfile, unscaledLogSource]
  congr 1
  linarith

/-- Continuity of the actual profile on each finite source interval. -/
theorem continuousOn_criticalAbelLogProfile {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn criticalAbelLogProfile (Icc (0 : ℝ) T) := by
  have hi : IntegrableOn unscaledLogSource (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT] using unscaledLogSource_integrable T
  have hc := intervalIntegral.continuousOn_primitive_interval hi
  rw [uIcc_of_le hT] at hc
  apply (continuousOn_congr (fun t ht => logProfile_eq_source_integral ht.1)).mpr
  exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
    (hc.div_const 2)

/-- Actual right derivative, including clocks at arithmetic source jumps. -/
theorem criticalAbelLogProfile_hasDeriv_right {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt criticalAbelLogProfile (criticalAbelLogVelocity t) (Ioi t) t := by
  let k : ℕ := ⌊Real.exp t⌋₊
  have he0 := Real.exp_pos t
  have he1 : 1 ≤ Real.exp t := Real.one_le_exp ht
  have hk : 1 ≤ k := (Nat.le_floor_iff he0.le).mpr (by simpa using he1)
  have hklo : (k : ℝ) ≤ Real.exp t := Nat.floor_le he0.le
  have hkhi : Real.exp t < (k + 1 : ℕ) := by exact_mod_cast Nat.lt_floor_add_one (Real.exp t)
  let g : ℝ → ℝ := fun s => Real.exp (-(3 / 2 : ℝ) * s) *
    (criticalContinuousAbel k + (Real.exp (s / 2) - Real.sqrt k) * psiDefect k)
  have heq (s : ℝ) (hlo : (k : ℝ) ≤ Real.exp s) (hhi : Real.exp s ≤ (k + 1 : ℕ)) :
      criticalAbelLogProfile s = g s := by
    dsimp [criticalAbelLogProfile, g]
    rw [criticalContinuousAbel_between hk hlo hhi, Real.exp_half]
  have heqt := heq t hklo hkhi.le
  have hupper : ∀ᶠ s : ℝ in 𝓝[>] t, Real.exp s < (k + 1 : ℕ) :=
    ((Real.continuous_exp.tendsto t).eventually (eventually_lt_nhds hkhi)).filter_mono
      nhdsWithin_le_nhds
  have hevent : criticalAbelLogProfile =ᶠ[𝓝[>] t] g := by
    filter_upwards [hupper, self_mem_nhdsWithin] with s hs hts
    exact heq s (hklo.trans (Real.exp_le_exp.mpr (le_of_lt hts))) hs.le
  have hE := ((hasDerivAt_id t).const_mul (-(3 / 2 : ℝ))).exp
  have hH := ((hasDerivAt_id t).div_const 2).exp
  have hg := hE.mul (((hH.sub_const (Real.sqrt k)).mul_const (psiDefect k)).const_add
    (criticalContinuousAbel k))
  have hexp : Real.exp (-(3 / 2 : ℝ) * t) * Real.exp (t / 2) = Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hg' : HasDerivAt g (criticalAbelLogVelocity t) t := by
    have hgraw : HasDerivAt g
        ((Real.exp (-(3 / 2 : ℝ) * t) * (-(3 / 2 : ℝ))) *
          (criticalContinuousAbel k + (Real.exp (t / 2) - Real.sqrt k) * psiDefect k) +
          Real.exp (-(3 / 2 : ℝ) * t) * ((Real.exp (t / 2) * (1 / 2)) * psiDefect k)) t := by
      simpa only [g, id_eq, mul_one, Pi.mul_def] using hg
    convert hgraw using 1
    dsimp [criticalAbelLogVelocity, criticalAbelLogDefect]
    rw [heqt]
    dsimp [g]
    calc
      _ = Real.exp (-(3 / 2 : ℝ) * t) * Real.exp (t / 2) * psiDefect k / 2 -
          (3 / 2 : ℝ) * (Real.exp (-(3 / 2 : ℝ) * t) *
            (criticalContinuousAbel k + (Real.exp (t / 2) - Real.sqrt k) * psiDefect k)) := by
        rw [hexp]
      _ = _ := by ring
  exact hg'.hasDerivWithinAt.congr_of_eventuallyEq hevent heqt

/-- Absolute admission of the literal velocity on the whole positive ray. -/
theorem integrableOn_criticalAbelLogVelocity :
    IntegrableOn criticalAbelLogVelocity (Ioi (0 : ℝ)) := by
  have hm : Measurable criticalAbelLogVelocity :=
    (measurable_criticalAbelLogDefect.div_const 2).sub
      (measurable_const.mul measurable_criticalAbelLogProfile)
  apply integrableOn_criticalAbelLogVelocity_quadratic.norm.mono' hm.aestronglyMeasurable.restrict
  filter_upwards with t
  simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 + t ^ (2 : ℕ))]
  nlinarith [abs_nonneg (criticalAbelLogVelocity t), sq_nonneg t]

/-- Every finite log-profile value is the integral of its literal velocity. -/
theorem criticalAbelLogVelocity_integral {t : ℝ} (ht : 0 ≤ t) :
    (∫ u in (0 : ℝ)..t, criticalAbelLogVelocity u) = criticalAbelLogProfile t := by
  have hi : IntervalIntegrable criticalAbelLogVelocity volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr
      (integrableOn_criticalAbelLogVelocity.mono_set (fun _ hx => hx.1))
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
    (continuousOn_criticalAbelLogProfile ht)
    (fun u hu => criticalAbelLogProfile_hasDeriv_right hu.1.le) hi
  have hzero : criticalAbelLogProfile 0 = 0 := by
    simp only [criticalAbelLogProfile, mul_zero, Real.exp_zero, one_mul]
    exact criticalContinuousAbel_eq_zero_le_one le_rfl
  simpa only [hzero, sub_zero] using h

end RHTower

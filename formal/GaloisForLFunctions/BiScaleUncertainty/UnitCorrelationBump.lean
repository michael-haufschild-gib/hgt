import GaloisForLFunctions.BiScaleUncertainty.DistantCopyPolarTopology
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# A smooth source with exactly unit correlation support

A literal bump of outer radius one half has autocorrelation strictly positive
exactly on the open unit interval. Boundary lags vanish pointwise in the
correlation integrand; interior lags have a positive overlap at their midpoint.
-/

noncomputable section
open MeasureTheory Set
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty.SharpCycle
set_option autoImplicit false

def seedBump : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

def seed : C_c(ℝ, ℝ) := ⟨⟨seedBump, seedBump.continuous⟩, seedBump.hasCompactSupport⟩

theorem seed_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) (seed : ℝ → ℝ) := seedBump.contDiff

theorem seed_nonneg (x : ℝ) : 0 ≤ seed x := seedBump.nonneg

theorem seed_at_zero : seed 0 = 1 := by
  apply seedBump.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, dist_self] using seedBump.rIn_pos.le

theorem seed_ne_zero_iff (x : ℝ) : seed x ≠ 0 ↔ |x| < 1 / 2 := by
  change x ∈ Function.support (seedBump : ℝ → ℝ) ↔ _
  rw [seedBump.support_eq]
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero, seedBump]

theorem seed_pos_iff (x : ℝ) : 0 < seed x ↔ |x| < 1 / 2 := by
  constructor
  · intro h
    exact (seed_ne_zero_iff x).mp h.ne'
  · intro h
    exact lt_of_le_of_ne (seed_nonneg x) (Ne.symm ((seed_ne_zero_iff x).mpr h))

theorem seed_eq_zero_iff (x : ℝ) : seed x = 0 ↔ 1 / 2 ≤ |x| := by
  simpa only [not_not, not_lt] using not_congr (seed_ne_zero_iff x)

theorem seed_correlation_nonneg (x : ℝ) : 0 ≤ autocorr seed x :=
  integral_nonneg (fun u => mul_nonneg (seed_nonneg u) (seed_nonneg (u + x)))

private theorem correlation_zero_outside (x : ℝ) (hx : 1 ≤ |x|) :
    autocorr seed x = 0 := by
  have hz (u : ℝ) : seed u * seed (u + x) = 0 := by
    by_cases hu : seed u = 0
    · rw [hu, zero_mul]
    by_cases hv : seed (u + x) = 0
    · rw [hv, mul_zero]
    have hu' := (seed_ne_zero_iff u).mp hu
    have hv' := (seed_ne_zero_iff (u + x)).mp hv
    have ht : |x| ≤ |u + x| + |u| := by
      simpa only [add_sub_cancel_left] using abs_sub (u + x) u
    exfalso
    linarith
  simp only [autocorr, hz, integral_zero]

private theorem correlation_pos_inside (x : ℝ) (hx : |x| < 1) :
    0 < autocorr seed x := by
  have hs : |x / 2| < 1 / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hl : 0 < seed (-x / 2) :=
    (seed_pos_iff _).mpr (by simpa only [neg_div, abs_neg] using hs)
  have hr : 0 < seed (-x / 2 + x) :=
    (seed_pos_iff _).mpr (by rwa [show -x / 2 + x = x / 2 by ring])
  have hc := seed.continuous.mul (seed.continuous.comp (continuous_add_const x))
  exact hc.integral_pos_of_hasCompactSupport_nonneg_nonzero seed.hasCompactSupport.mul_right
      (fun u => mul_nonneg (seed_nonneg u) (seed_nonneg (u + x))) (x := -x / 2)
      (mul_pos hl hr).ne'

/-- The positivity region is exactly open, so unit-distance endpoint overlaps vanish. -/
theorem seed_correlation_pos_iff (x : ℝ) : 0 < autocorr seed x ↔ |x| < 1 := by
  constructor
  · intro h
    by_contra hx
    rw [correlation_zero_outside x (le_of_not_gt hx)] at h
    exact lt_irrefl _ h
  · exact correlation_pos_inside x

theorem seed_correlation_eq_zero_iff (x : ℝ) : autocorr seed x = 0 ↔ 1 ≤ |x| := by
  constructor
  · intro h
    by_contra hx
    have hp := correlation_pos_inside x (lt_of_not_ge hx)
    rw [h] at hp
    exact lt_irrefl _ hp
  · exact correlation_zero_outside x

theorem seed_correlation_ne_zero_iff (x : ℝ) : autocorr seed x ≠ 0 ↔ |x| < 1 := by
  simpa only [not_le] using not_congr (seed_correlation_eq_zero_iff x)

theorem seed_mass_pos : 0 < autocorr seed 0 :=
  (seed_correlation_pos_iff 0).mpr (by norm_num)

/-- The same literal seed has a strictly positive normalized polar moment. -/
theorem seed_polar_pos : 0 < normalizedPolarMoment seed := by
  have hm (s : ℝ) : 0 < ∫ u, seed u * Real.exp (s * u) := by
    apply (seed.continuous.mul (by fun_prop)).integral_pos_of_hasCompactSupport_nonneg_nonzero
      seed.hasCompactSupport.mul_right
      (fun u => mul_nonneg (seed_nonneg u) (Real.exp_pos _).le) (x := 0)
    change seed 0 * Real.exp (s * 0) ≠ 0
    rw [seed_at_zero]
    norm_num
  have hp := hm (1 / 2)
  have hn := hm (-(1 / 2))
  simp only [show ∀ u : ℝ, (1 / 2 : ℝ) * u = u / 2 by intro u; ring] at hp
  simp only [show ∀ u : ℝ, (-(1 / 2) : ℝ) * u = -u / 2 by intro u; ring] at hn
  have hwhole := two_mul_integral_autocorr_cosh (f := (seed : ℝ → ℝ))
    seedBump.contDiff seed.hasCompactSupport
  have hhalf : 0 < ∫ x in Ioi 0, autocorr seed x * Real.cosh (x / 2) := by
    have hh := mul_pos hp hn
    linarith only [hwhole, hh]
  exact div_pos hhalf seed_mass_pos

end GaloisForLFunctions.BiScaleUncertainty.SharpCycle

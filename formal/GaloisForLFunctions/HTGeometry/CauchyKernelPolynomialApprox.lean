import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Polynomial approximation of a Cauchy kernel with a far pole

If the pole `λ` lies outside a disc, the Cauchy kernel `1/(λ - z)` is the uniform limit on that disc
of the polynomials `∑_{n<N} z^n/λ^{n+1}`.  This is pole-pushing in its simplest form: a pole beyond
the disc can be moved to infinity, replacing the kernel by polynomials.

It is the engine of polynomial Runge approximation on a disc — the Cauchy integral formula writes a
holomorphic function as a superposition of such kernels, and each of them is polynomially
approximable.

* `HTGeometry.tsum_cauchyKernel_eq`;
* `HTGeometry.tendstoUniformlyOn_cauchyKernel_poly`.
-/

open Metric

namespace HTGeometry

/-- The Cauchy kernel expands geometrically when the pole is farther than the point. -/
theorem tsum_cauchyKernel_eq {lam z : ℂ} (h : ‖z‖ < ‖lam‖) :
    ∑' n : ℕ, z ^ n / lam ^ (n + 1) = 1 / (lam - z) := by
  have hlam : lam ≠ 0 := by
    intro hcon
    rw [hcon, norm_zero] at h
    exact absurd h (not_lt_of_ge (norm_nonneg z))
  have hratio : ‖z / lam‖ < 1 := by
    rw [norm_div, div_lt_one (by positivity)]
    exact h
  have hgeo : ∑' n : ℕ, (z / lam) ^ n = (1 - z / lam)⁻¹ :=
    tsum_geometric_of_norm_lt_one hratio
  have hterm : ∀ n : ℕ, z ^ n / lam ^ (n + 1) = lam⁻¹ * (z / lam) ^ n := by
    intro n
    rw [div_pow, pow_succ]
    field_simp
  have hne : lam - z ≠ 0 := by
    intro hcon
    have hz : z = lam := by linear_combination -hcon
    rw [hz] at h
    exact lt_irrefl _ h
  rw [tsum_congr hterm, tsum_mul_left, hgeo]
  field_simp

/-- **The Cauchy kernel is a uniform limit of polynomials on a disc missing its pole.** -/
theorem tendstoUniformlyOn_cauchyKernel_poly {R r : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    {lam : ℂ} (hlam : R ≤ ‖lam‖) :
    TendstoUniformlyOn (fun (N : Finset ℕ) (z : ℂ) => ∑ n ∈ N, z ^ n / lam ^ (n + 1))
      (fun z => 1 / (lam - z)) Filter.atTop (closedBall (0 : ℂ) r) := by
  have hR0 : 0 < R := lt_of_le_of_lt hr hrR
  have hlam0 : 0 < ‖lam‖ := lt_of_lt_of_le hR0 hlam
  have hu : Summable fun n : ℕ => r ^ n / R ^ (n + 1) := by
    have hgeo : Summable fun n : ℕ => (r / R) ^ n :=
      summable_geometric_of_lt_one (by positivity) (by rw [div_lt_one hR0]; exact hrR)
    have hmul := hgeo.mul_left R⁻¹
    refine hmul.congr fun n => ?_
    rw [div_pow, pow_succ]
    field_simp
  have hbound : ∀ (n : ℕ), ∀ z ∈ closedBall (0 : ℂ) r,
      ‖z ^ n / lam ^ (n + 1)‖ ≤ r ^ n / R ^ (n + 1) := by
    intro n z hz
    have hzr : ‖z‖ ≤ r := by simpa using mem_closedBall_zero_iff.1 hz
    rw [norm_div, norm_pow, norm_pow]
    have hnum : ‖z‖ ^ n ≤ r ^ n := pow_le_pow_left₀ (norm_nonneg z) hzr n
    have hden : R ^ (n + 1) ≤ ‖lam‖ ^ (n + 1) :=
      pow_le_pow_left₀ (le_of_lt hR0) hlam (n + 1)
    have hRpow : (0 : ℝ) < R ^ (n + 1) := by positivity
    have hlampow : (0 : ℝ) < ‖lam‖ ^ (n + 1) := by positivity
    rw [div_le_div_iff₀ hlampow hRpow]
    nlinarith [pow_nonneg (norm_nonneg z) n, pow_nonneg hr n]
  have hunif := tendstoUniformlyOn_tsum hu hbound
  refine hunif.congr_right fun z hz => ?_
  have hzr : ‖z‖ ≤ r := by simpa using mem_closedBall_zero_iff.1 hz
  exact tsum_cauchyKernel_eq (lt_of_le_of_lt hzr (lt_of_lt_of_le hrR hlam))

end HTGeometry

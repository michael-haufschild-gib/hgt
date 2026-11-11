import GaloisForLFunctions.RHTower.ZetaSquareStirlingCarrier
import Mathlib.Analysis.Complex.Liouville

/-!
# Scaled jets of the chi conductor error

The complex Stirling estimate bounds the conductor quotient minus one on
a fixed normalized disk. Cauchy's estimate transfers that bound to every
jet. Under logarithmic rescaling all error jets vanish, uniformly for
bounded moving centres and heights tending to infinity.
-/

open Complex Filter Metric Set Topology
open RHTower.ZetaNotch

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The reflected chi weight after removing its exact conductor exponential. -/
def scaledChiConductorError (L t : ℝ) (z : ℂ) : ℂ :=
  critConductorQuot t (z / (L : ℂ)) - 1

/-- The normalized error is holomorphic wherever the shifted heights stay nonzero. -/
theorem analyticAt_scaledChiConductorError {L t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : 2 * |(z / (L : ℂ)).im| < t) :
    AnalyticAt ℂ (scaledChiConductorError L t) z := by
  let U : Set ℂ := {w | 2 * |(w / (L : ℂ)).im| < t}
  have hU : IsOpen U := isOpen_lt (by fun_prop) continuous_const
  have hf : DifferentiableOn ℂ (scaledChiConductorError L t) U := by
    intro w hw
    have hh : 2 * |(w / (L : ℂ)).im| < t := hw
    exact (((hasDerivAt_critConductorQuot ht hh.le).differentiableAt.comp w
      (differentiableAt_id.div_const (L : ℂ))).sub_const 1).differentiableWithinAt
  exact hf.analyticOnNhd hU z hz

/-- Quantitative Cauchy bound on every normalized conductor-error jet. -/
theorem norm_scaledChiConductorError_jet_le {R L t : ℝ} (hR : 0 ≤ R)
    (hL : R + 2 ≤ L) (ht : 4 ≤ t) {C : ℂ} (hC : ‖C‖ ≤ R) (j : ℕ) :
    ‖iteratedDeriv j (scaledChiConductorError L t) C‖ ≤
      (j.factorial : ℝ) *
        (Real.exp (((R + 1) / L) * (20 * ((R + 1) / L) / t + 52 / t ^ 2)) - 1) := by
  have hL0 : 0 < L := by linarith only [hR, hL]
  have ht0 : 0 < t := by linarith only [ht]
  have hnorm {z : ℂ} (hz : ‖z - C‖ ≤ 2) : ‖z / (L : ℂ)‖ ≤ 1 := by
    have hh := norm_add_le (z - C) C
    rw [sub_add_cancel] at hh
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hL0.le]
    apply (div_le_one hL0).mpr
    linarith only [hh, hz, hC, hL]
  have hf : DifferentiableOn ℂ (scaledChiConductorError L t) (ball C 2) := by
    intro z hz
    have hz' : ‖z - C‖ ≤ 2 := (show ‖z - C‖ < 2 by simpa only [mem_ball, dist_eq_norm] using hz).le
    have him : 2 * |(z / (L : ℂ)).im| ≤ t := by
      have hh := (Complex.abs_im_le_norm (z / (L : ℂ))).trans (hnorm hz')
      linarith only [hh, ht]
    exact (((hasDerivAt_critConductorQuot ht0 him).differentiableAt.comp z
      (differentiableAt_id.div_const (L : ℂ))).sub_const 1).differentiableWithinAt
  have hsub : closedBall C 1 ⊆ ball C 2 := by
    intro z hz
    exact lt_of_le_of_lt hz (by norm_num : (1 : ℝ) < 2)
  have hb : ∀ z ∈ sphere C 1, ‖scaledChiConductorError L t z‖ ≤
      Real.exp (((R + 1) / L) * (20 * ((R + 1) / L) / t + 52 / t ^ 2)) - 1 := by
    intro z hz
    have hz1 : ‖z - C‖ = 1 := by simpa only [mem_sphere, dist_eq_norm] using hz
    have hzn : ‖z‖ ≤ R + 1 := by
      have hh := norm_add_le (z - C) C
      rw [sub_add_cancel, hz1] at hh
      linarith only [hh, hC]
    have hw : ‖z / (L : ℂ)‖ ≤ (R + 1) / L := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hL0.le]
      exact div_le_div_of_nonneg_right hzn hL0.le
    have ha0 : 0 ≤ (R + 1) / L := by positivity
    have ha1 : (R + 1) / L ≤ 1 := (div_le_one hL0).mpr (by linarith only [hL])
    have hre : |(z / (L : ℂ)).re| ≤ 1 :=
      (Complex.abs_re_le_norm _).trans (hw.trans ha1)
    have him : 2 * |(z / (L : ℂ)).im| ≤ t := by
      have hh := (Complex.abs_im_le_norm _).trans (hw.trans ha1)
      linarith only [hh, ht]
    refine (norm_critConductorQuot_sub_one_le ht hre him).trans ?_
    apply sub_le_sub_right
    apply Real.exp_le_exp.mpr
    apply mul_le_mul hw _ (by positivity) ha0
    exact add_le_add
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw (by norm_num)) ht0.le) le_rfl
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j zero_lt_one
    (hf.diffContOnCl_ball hsub) hb
  simpa only [one_pow, div_one] using hh

/-- All normalized error jets vanish along bounded centres and arbitrarily growing heights. -/
theorem tendsto_scaledChiConductorError_jet {ι : Type*} {l : Filter ι}
    {L t : ι → ℝ} (hL : Tendsto L l atTop)
    (ht : Tendsto t l atTop) {C : ι → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hC : ∀ᶠ N in l, ‖C N‖ ≤ R) (j : ℕ) :
    Tendsto (fun N => iteratedDeriv j (scaledChiConductorError (L N) (t N)) (C N))
      l (𝓝 0) := by
  have ha : Tendsto (fun N : ι => (R + 1) / L N) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop hL
  have h1 := (ha.const_mul 20).div_atTop ht
  have h2 : Tendsto (fun N => (52 : ℝ) / (t N) ^ 2) l (𝓝 0) := by
    have hh := ((tendsto_const_nhds : Tendsto (fun _ : ι => (52 : ℝ)) l (𝓝 52)).div_atTop ht).div_atTop ht
    simpa only [div_div, pow_two] using hh
  have hδ : Tendsto (fun N : ι => (j.factorial : ℝ) *
      (Real.exp (((R + 1) / L N) *
        (20 * ((R + 1) / L N) / t N + 52 / (t N) ^ 2)) - 1)) l (𝓝 0) := by
    have hexp := Real.continuous_exp.continuousAt.tendsto.comp (ha.mul (h1.add h2))
    have hh := (hexp.sub_const 1).const_mul (j.factorial : ℝ)
    simpa only [Function.comp_def, mul_zero, zero_add, Real.exp_zero, sub_self] using hh
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [hL.eventually_ge_atTop (R + 2), ht.eventually_ge_atTop 4,
    hC, hδ.eventually_lt_const hε] with N hLN htN hCN hsmall
  rw [dist_zero_right]
  exact (norm_scaledChiConductorError_jet_le hR hLN htN hCN j).trans_lt hsmall

end GaloisForLFunctions.MultiscaleMollifiedZetaField

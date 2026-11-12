import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailRightZeroConvolutionTails
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailRightTraceCutoffsHaveTheirLimit
import GaloisForLFunctions.RHTower.RieszMellinPair

/-!
# The full zero convolution converges when its boundary line is empty

At height cutoff `N`, both the finite-mode error and reciprocal exterior
mass decay with a subunit zero-count exponent. Harmonic convolution costs
only one logarithm. The finite main part then tends to its summable
constant contribution, with no uniform gap below the bounding zero line.
-/

noncomputable section

open Complex Finset Filter Topology
open _root_.RHTower

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ZeroConfigurationGeometry

/-- One subunit moment controls the full convolution error after its
actual finite main part is removed. -/
theorem exists_power_bound_rightZeroConvolution_sub_main {a σ : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hσ : 1 / 2 < σ)
    (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 - a) :
    ∃ p D : ℝ, 0 < p ∧ p < 1 ∧ 0 ≤ D ∧ ∀ N : ℕ, 1 ≤ N →
      ‖powerTailRightZeroConvolution a σ N -
        ∑ q ∈ powerTailRightZeroCutoff σ (N : ℝ), powerTailZeroConvolutionMain a N q‖ ≤
      D * (1 + Real.log N) * (N : ℝ) ^ (p - 1) := by
  obtain ⟨p, C, hp, hp1, hC, hcuts⟩ := exists_powerTailRightZeroCutoff_bounds hσ
  refine ⟨p, 16 * C, hp, hp1, by positivity, ?_⟩
  intro N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  let F := powerTailRightZeroCutoff σ (N : ℝ)
  have hF (q : XiZeroCopy) (hq : q ∈ F) : σ ≤ (q.1 : ℂ).re :=
    ((mem_powerTailRightZeroCutoff σ N q).mp hq).1
  have hc := hcuts (N : ℝ) hNp
  have houter : ‖powerTailRightZeroConvolution a σ N -
      powerTailFiniteRightZeroConvolution a σ N F‖ ≤
      2 * (1 + Real.log N) * (C * (N : ℝ) ^ (p - 1)) :=
    (norm_powerTailRightZeroConvolution_sub_finite_le ha ha1 hσ hβ hN F).trans
      (mul_le_mul_of_nonneg_left hc.2 (by positivity))
  have hmode := norm_sum_powerTailZeroConvolutionMode_sub_main_le (a := a) hN F
    (fun q hq => ⟨by linarith only [hσ, hF q hq, ha],
      by linarith only [hβ q]⟩)
  rw [← powerTailFiniteRightZeroConvolution_eq_sum_modes a σ N F hF] at hmode
  have hcore : ‖powerTailFiniteRightZeroConvolution a σ N F -
      ∑ q ∈ F, powerTailZeroConvolutionMain a N q‖ ≤ 14 * C * (N : ℝ) ^ (p - 1) := by
    calc
      _ ≤ 14 * (F.card : ℝ) / N := hmode
      _ ≤ 14 * (C * (N : ℝ) ^ p) / N :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hc.1 (by norm_num)) hNp.le
      _ = _ := by rw [Real.rpow_sub hNp, Real.rpow_one]; ring
  have habsorb : 14 * C * (N : ℝ) ^ (p - 1) ≤
      14 * C * (1 + Real.log N) * (N : ℝ) ^ (p - 1) :=
    mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (by positivity : 0 ≤ 14 * C) (by linarith only [hlog]))
      (Real.rpow_nonneg hNp.le _)
  calc
    _ = ‖(powerTailRightZeroConvolution a σ N - powerTailFiniteRightZeroConvolution a σ N F) +
        (powerTailFiniteRightZeroConvolution a σ N F -
          ∑ q ∈ F, powerTailZeroConvolutionMain a N q)‖ := by congr 1; ring
    _ ≤ ‖powerTailRightZeroConvolution a σ N - powerTailFiniteRightZeroConvolution a σ N F‖ +
        ‖powerTailFiniteRightZeroConvolution a σ N F -
          ∑ q ∈ F, powerTailZeroConvolutionMain a N q‖ := norm_add_le _ _
    _ ≤ 2 * (1 + Real.log N) * (C * (N : ℝ) ^ (p - 1)) +
        14 * C * (N : ℝ) ^ (p - 1) := add_le_add houter hcore
    _ ≤ 2 * (1 + Real.log N) * (C * (N : ℝ) ^ (p - 1)) +
        14 * C * (1 + Real.log N) * (N : ℝ) ^ (p - 1) := add_le_add le_rfl habsorb
    _ = _ := by ring

/-- The logarithmic harmonic loss is absorbed by the strict subunit
moment, so the full zero convolution retains its finite main part. -/
theorem tendsto_rightZeroConvolution_sub_main_zero {a σ : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hσ : 1 / 2 < σ)
    (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 - a) :
    Tendsto (fun N : ℕ => powerTailRightZeroConvolution a σ N -
      ∑ q ∈ powerTailRightZeroCutoff σ (N : ℝ), powerTailZeroConvolutionMain a N q)
      atTop (𝓝 0) := by
  obtain ⟨p, D, _, hp1, hD, hB⟩ :=
    exists_power_bound_rightZeroConvolution_sub_main ha ha1 hσ hβ
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun N : ℕ => Real.log (N : ℝ) * (N : ℝ) ^ (p - 1))
      atTop (𝓝 0) := by
    have hh := (GaloisForLFunctions.RHTower.tendsto_log_mul_rpow_neg (sub_pos.mpr hp1)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
    simpa only [Function.comp_def, neg_sub] using hh
  have hmajor : Tendsto (fun N : ℕ => (2 * D) * (Real.log N * (N : ℝ) ^ (p - 1)))
      atTop (𝓝 0) := by simpa only [mul_zero] using hsmall.const_mul (2 * D)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop 1, hlog.eventually (eventually_ge_atTop (1 : ℝ))]
    with N hN hlogN
  apply (hB N hN).trans
  calc
    _ ≤ D * (2 * Real.log N) * (N : ℝ) ^ (p - 1) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith only [hlogN] : 1 + Real.log N ≤ 2 * Real.log N) hD)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := by ring

/-- With summable contact amplitudes and an empty bounding line, the
actual complete zero convolution tends to its constant power-integral sum. -/
theorem tendsto_powerTailRightZeroConvolution {a σ : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hσ : 1 / 2 < σ)
    (hs : Summable (fun q => ‖powerTailRightZeroAmplitude a σ q‖))
    (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re < 1 - a) :
    Tendsto (powerTailRightZeroConvolution a σ) atTop
      (𝓝 (∑' q, powerTailRightZeroConstant a σ q)) := by
  have hh := (tendsto_rightZeroConvolution_sub_main_zero ha ha1 hσ (fun q => (hβ q).le)).add
    (tendsto_sum_powerTailZeroConvolutionMain hσ hs hβ)
  simp only [zero_add] at hh
  exact hh.congr fun N => sub_add_cancel _ _

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ

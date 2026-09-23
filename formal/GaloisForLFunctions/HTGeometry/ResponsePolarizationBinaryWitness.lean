import GaloisForLFunctions.HTGeometry.ResponsePolarizationFisherTailJeffreysEscape
import GaloisForLFunctions.HTGeometry.ExpRayL2
import GaloisForLFunctions.HTGeometry.TanhSubstitution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Sharp binary response-polarization witness

Equal weights and scores `0,1` realize total Fisher length `π` while reflected Jeffreys work
escapes as `2 t tanh(t/2)`.
-/

open Filter MeasureTheory Set Topology
open scoped Interval

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def binaryEscortWeight (_ : Fin 2) : ℝ := 1 / 2
def binaryEscortScore (x : Fin 2) : ℝ := x
def binaryFisherCoordinate (t : ℝ) : ℝ := 2 * Real.arctan (Real.exp (t / 2))

lemma binaryEscortWeight_sum : ∑ x, binaryEscortWeight x = 1 := by
  simp [binaryEscortWeight]

lemma binary_partition (t : ℝ) :
    finiteExpPartition binaryEscortWeight binaryEscortScore t =
      (1 + Real.exp t) / 2 := by
  simp [finiteExpPartition, binaryEscortWeight, binaryEscortScore, Fin.sum_univ_two]
  ring

lemma binary_mean (t : ℝ) :
    finiteTiltMean binaryEscortWeight binaryEscortScore t =
      Real.exp t / (1 + Real.exp t) := by
  rw [finiteTiltMean_eq_div]
  simp [finiteExpPartition, binaryEscortWeight, binaryEscortScore, Fin.sum_univ_two]
  field_simp [show (1 + Real.exp t) ≠ 0 by positivity]

lemma binary_variance (t : ℝ) :
    finiteTiltVariance binaryEscortWeight binaryEscortScore t =
    Real.exp t / (1 + Real.exp t) ^ (2 : ℕ) := by
  rw [finiteTiltVariance_eq_second_sub_sq
    (by simp [binaryEscortWeight]) binaryEscortWeight_sum]
  rw [finiteTiltSecondMoment_eq_div, finiteTiltMean_eq_div]
  simp [finiteExpPartition, binaryEscortWeight, binaryEscortScore, Fin.sum_univ_two]
  field_simp [show (1 + Real.exp t) ≠ 0 by positivity]
  ring_nf

lemma binary_variance_cosh (t : ℝ) :
    finiteTiltVariance binaryEscortWeight binaryEscortScore t =
    1 / (4 * Real.cosh (t / 2) ^ (2 : ℕ)) := by
  rw [binary_variance, Real.cosh_eq, Real.exp_neg]
  have hexp : Real.exp t = Real.exp (t / 2) ^ (2 : ℕ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp]
  field_simp [Real.exp_ne_zero (t / 2)]
  ring

private lemma tanh_eq_expTwoRatio (y : ℝ) :
    Real.tanh y = (Real.exp (2 * y) - 1) / (Real.exp (2 * y) + 1) := by
  rw [Real.tanh_eq, show Real.exp (2 * y) = Real.exp y * Real.exp y by
    rw [show 2 * y = y + y by ring, Real.exp_add], Real.exp_neg]
  have hden : Real.exp y ^ (2 : ℕ) + 1 ≠ 0 := by positivity
  field_simp [Real.exp_ne_zero y, hden]

lemma binary_mean_reflection (t : ℝ) :
    finiteTiltMean binaryEscortWeight binaryEscortScore t -
      finiteTiltMean binaryEscortWeight binaryEscortScore (-t) = Real.tanh (t / 2) := by
  rw [binary_mean, binary_mean, tanh_eq_expTwoRatio]
  rw [show 2 * (t / 2) = t by ring, Real.exp_neg]
  field_simp [Real.exp_ne_zero t, show Real.exp t + 1 ≠ 0 by positivity]
  ring

lemma binary_jeffreys_reflection (t : ℝ) :
    finiteTiltJeffreysReal binaryEscortWeight binaryEscortScore t (-t) =
      2 * t * Real.tanh (t / 2) := by
  rw [finiteTiltJeffreysReal_eq (by simp [binaryEscortWeight])
    binaryEscortWeight_sum, binary_mean_reflection]
  ring

lemma binary_sqrt_variance (t : ℝ) :
    √(finiteTiltVariance binaryEscortWeight binaryEscortScore t) =
    Real.exp (t / 2) / (1 + Real.exp t) := by
  rw [binary_variance]
  have hsquare : Real.exp t / (1 + Real.exp t) ^ (2 : ℕ) =
      (Real.exp (t / 2) / (1 + Real.exp t)) ^ (2 : ℕ) := by
    rw [show Real.exp t = Real.exp (t / 2) ^ (2 : ℕ) by
      rw [← Real.exp_nat_mul]
      congr 1
      ring]
    field_simp [show 1 + Real.exp (t / 2) ^ (2 : ℕ) ≠ 0 by positivity]
  rw [hsquare, Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]

lemma hasDerivAt_binaryFisherCoordinate (t : ℝ) :
    HasDerivAt binaryFisherCoordinate
      (Real.exp (t / 2) / (1 + Real.exp t)) t := by
  have hinner : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) t := by
    simpa using (hasDerivAt_id t).div_const 2
  have hexp := hinner.exp
  have hatan := (Real.hasDerivAt_arctan (Real.exp (t / 2))).comp t hexp
  have h := hatan.const_mul 2
  have hval : 2 * (1 / (1 + Real.exp (t / 2) ^ (2 : ℕ)) *
      (Real.exp (t / 2) * (1 / 2))) = Real.exp (t / 2) / (1 + Real.exp t) := by
    rw [show Real.exp t = Real.exp (t / 2) ^ (2 : ℕ) by
      rw [← Real.exp_nat_mul]
      congr 1
      ring]
    field_simp [show 1 + Real.exp (t / 2) ^ (2 : ℕ) ≠ 0 by positivity]
  rw [hval] at h
  change HasDerivAt (fun y : ℝ => 2 * Real.arctan (Real.exp (y / 2)))
    (Real.exp (t / 2) / (1 + Real.exp t)) t
  exact h

lemma hasDerivAt_binaryFisherCoordinate_sqrt_variance (t : ℝ) :
    HasDerivAt binaryFisherCoordinate
      (√(finiteTiltVariance binaryEscortWeight binaryEscortScore t)) t := by
  rw [binary_sqrt_variance]
  exact hasDerivAt_binaryFisherCoordinate t

lemma binary_fisher_interval (a b : ℝ) :
    (∫ t : ℝ in a..b,
      √(finiteTiltVariance binaryEscortWeight binaryEscortScore t)) =
        binaryFisherCoordinate b - binaryFisherCoordinate a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_binaryFisherCoordinate_sqrt_variance t)
    ((Real.continuous_sqrt.comp (by
      rw [show finiteTiltVariance binaryEscortWeight binaryEscortScore =
          fun t => Real.exp t / (1 + Real.exp t) ^ (2 : ℕ) by
        funext t
        exact binary_variance t]
      exact Real.continuous_exp.div
        ((continuous_const.add Real.continuous_exp).pow 2)
        (fun t => pow_ne_zero 2 (by positivity)))).intervalIntegrable a b)

lemma binaryFisherCoordinate_tendsto_atTop :
    Tendsto binaryFisherCoordinate atTop (𝓝 Real.pi) := by
  have hscale : Tendsto (fun T : ℝ => T / 2) atTop atTop := by
    simpa only [id_eq, div_eq_mul_inv, mul_comm] using
      tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
  have hexp := Real.tendsto_exp_atTop.comp hscale
  have hatan := Real.tendsto_arctan_atTop.comp hexp
  have hatan' : Tendsto (fun T : ℝ => Real.arctan (Real.exp (T / 2)))
      atTop (𝓝 (Real.pi / 2)) := hatan.mono_right nhdsWithin_le_nhds
  have h := hatan'.const_mul 2
  have hval : 2 * (Real.pi / 2) = Real.pi := by ring
  rw [hval] at h
  change Tendsto (fun T : ℝ => 2 * Real.arctan (Real.exp (T / 2)))
    atTop (𝓝 Real.pi)
  exact h

lemma binaryFisherCoordinate_neg_tendsto_atTop :
    Tendsto (fun T : ℝ => binaryFisherCoordinate (-T)) atTop (𝓝 0) := by
  have hexp : Tendsto (fun T : ℝ => Real.exp (-(1 / 2 * T))) atTop (𝓝 0) :=
    tendsto_exp_neg_mul_atTop_nhds_zero (by norm_num)
  have hexp' : Tendsto (fun T : ℝ => Real.exp (-T / 2)) atTop (𝓝 0) := by
    have heq : (fun T : ℝ => Real.exp (-T / 2)) =
        fun T : ℝ => Real.exp (-(1 / 2 * T)) := by
      funext T
      congr 1
      ring
    rw [heq]
    exact hexp
  have hatan := Real.continuous_arctan.continuousAt.tendsto.comp hexp'
  have h := hatan.const_mul 2
  change Tendsto (fun T : ℝ => 2 * Real.arctan (Real.exp (-T / 2))) atTop (𝓝 0)
  simpa only [Function.comp_apply, Real.arctan_zero, mul_zero] using h

lemma binary_total_fisher_tendsto_pi : Tendsto (fun T : ℝ =>
    ∫ t : ℝ in -T..T,
      √(finiteTiltVariance binaryEscortWeight binaryEscortScore t))
      atTop (𝓝 Real.pi) := by
  have hdiff := binaryFisherCoordinate_tendsto_atTop.sub
    binaryFisherCoordinate_neg_tendsto_atTop
  have hfun : (fun T : ℝ => ∫ t : ℝ in -T..T,
      √(finiteTiltVariance binaryEscortWeight binaryEscortScore t)) =
      fun T => binaryFisherCoordinate T - binaryFisherCoordinate (-T) := by
    funext T
    exact binary_fisher_interval (-T) T
  rw [hfun]
  simpa only [sub_zero] using hdiff

lemma binary_jeffreys_reflection_tendsto_atTop :
    Tendsto (fun t : ℝ =>
      finiteTiltJeffreysReal binaryEscortWeight binaryEscortScore t (-t))
      atTop atTop := by
  rw [show (fun t : ℝ =>
      finiteTiltJeffreysReal binaryEscortWeight binaryEscortScore t (-t)) =
      fun t : ℝ => 2 * t * Real.tanh (t / 2) by
    funext t
    exact binary_jeffreys_reflection t]
  rw [tendsto_atTop]
  intro B
  let c : ℝ := Real.tanh (1 / 2)
  have hc : 0 < c := by
    dsimp [c]
    have := HTGeometry.tanh_strictMono (show (0 : ℝ) < 1 / 2 by norm_num)
    simpa only [Real.tanh_zero] using this
  filter_upwards [eventually_ge_atTop (max 1 (B / (2 * c) + 1))] with t ht
  have ht1 : 1 ≤ t := (le_max_left 1 (B / (2 * c) + 1)).trans ht
  have htB : B / (2 * c) < t := by
    have := (le_max_right 1 (B / (2 * c) + 1)).trans ht
    linarith
  have htanh : c ≤ Real.tanh (t / 2) :=
    by
      change Real.tanh (1 / 2) ≤ Real.tanh (t / 2)
      exact HTGeometry.tanh_strictMono.monotone (by linarith)
  have hBc : B < 2 * t * c := by
    have h2c : 0 < 2 * c := by positivity
    simpa only [mul_assoc, mul_comm, mul_left_comm] using (div_lt_iff₀ h2c).mp htB
  nlinarith

end

end GaloisForLFunctions.HTGeometry

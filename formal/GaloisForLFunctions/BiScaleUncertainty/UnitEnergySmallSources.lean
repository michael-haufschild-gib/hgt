import GaloisForLFunctions.BiScaleUncertainty.FiniteSourceEnergyScalarization
import GaloisForLFunctions.BiScaleUncertainty.LogarithmicCompressionEnergy

/-!
# Unit-energy smooth sources of arbitrarily small mass

A concrete bump can be compressed inside any prescribed source interval. The
logarithmic increment bound makes its normalized energy arbitrarily large;
amplitude normalization then gives raw energy one and arbitrarily small mass.
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-- Literal source support gives twice that radius for the correlation. -/
theorem autocorr_eq_zero_of_source_radius {f : ℝ → ℝ} {b x : ℝ}
    (hs : ∀ u, b < |u| → f u = 0) (hx : 2 * b < |x|) : autocorr f x = 0 := by
  have hz : ∀ u, f u * f (u + x) = 0 := by
    intro u
    by_cases hu : f u = 0
    · simp [hu]
    by_cases hv : f (u + x) = 0
    · simp [hv]
    have hbu : |u| ≤ b := le_of_not_gt fun h => hu (hs u h)
    have hbv : |u + x| ≤ b := le_of_not_gt fun h => hv (hs (u + x) h)
    have ht : |x| ≤ |u + x| + |u| := by
      simpa only [show u + x - u = x by ring] using abs_sub (u + x) u
    exfalso
    linarith
  simp only [autocorr, hz, integral_zero]

/-- A nonzero smooth source exists in every positive source radius. -/
theorem exists_smooth_source_in_radius {b : ℝ} (hb : 0 < b) :
    ∃ f : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f ∧
      0 < autocorr f 0 ∧ ∀ u, b < |u| → f u = 0 := by
  let p : ContDiffBump (0 : ℝ) := ⟨b / 2, b, by positivity, by linarith⟩
  have hp0 : p 0 = 1 := p.one_of_mem_closedBall (by
    simpa only [Metric.mem_closedBall, dist_self] using p.rIn_pos.le)
  refine ⟨p, p.contDiff, p.hasCompactSupport, ?_, ?_⟩
  · unfold autocorr
    simp only [add_zero]
    exact (p.continuous.mul p.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
      p.hasCompactSupport.mul_right (fun x => mul_self_nonneg (p x)) (x := 0)
      (by rw [hp0]; norm_num)
  · intro u hu
    apply p.zero_of_le_dist
    simpa only [Real.dist_eq, sub_zero, p] using hu.le

/-- Positive raw energy admits exact unit-energy amplitude normalization. -/
theorem source_energy_normalization {f : ℝ → ℝ} (hJ : 0 < biScaleLevyEnergy f) :
    biScaleLevyEnergy (fun u => (Real.sqrt (biScaleLevyEnergy f))⁻¹ * f u) = 1 ∧
    autocorr (fun u => (Real.sqrt (biScaleLevyEnergy f))⁻¹ * f u) 0 =
      autocorr f 0 / biScaleLevyEnergy f := by
  have hs : (Real.sqrt (biScaleLevyEnergy f)) ^ 2 = biScaleLevyEnergy f := Real.sq_sqrt hJ.le
  constructor
  · rw [biScaleLevyEnergy_source_const_mul, inv_pow, hs, inv_mul_cancel₀ hJ.ne']
  · rw [autocorr_source_const_mul, inv_pow, hs]
    ring

/-- Actual unit-energy sources can have arbitrarily small positive mass in a fixed interval. -/
theorem exists_smooth_unit_energy_small_mass {b η : ℝ} (hb : 0 < b) (hη : 0 < η) :
    ∃ q : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) q ∧ HasCompactSupport q ∧
      0 < autocorr q 0 ∧ autocorr q 0 < η ∧ biScaleLevyEnergy q = 1 ∧
      ∀ u, b < |u| → q u = 0 := by
  obtain ⟨p, hp, hpc, hpR, hps⟩ := exists_smooth_source_in_radius hb
  let c : ℝ := Real.exp (-(1 / 2 : ℝ))
  have hc : 0 < c := Real.exp_pos _
  let T := 4 * (1 / η + 1) / c + 1
  have hT : 0 < T := by dsimp [T]; positivity
  let L := (2 * b + 1) * Real.exp T
  have hL1 : 1 ≤ L := by
    have he : 1 ≤ Real.exp T := Real.one_le_exp_iff.mpr hT.le
    dsimp [L]
    nlinarith
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  let g := sourceRescale p L
  have hg := contDiff_sourceRescale hp L
  have hgc := hasCompactSupport_sourceRescale hpc hL
  have hgR : 0 < autocorr g 0 := by
    dsimp [g]
    rw [autocorr_sourceRescale p hL, mul_zero]
    exact mul_pos (inv_pos.mpr hL) hpR
  have hgs : ∀ u, b < |u| → g u = 0 := by
    intro u hu
    apply hps
    rw [abs_mul, abs_of_pos hL]
    exact hu.trans_le (le_mul_of_one_le_left (abs_nonneg u) hL1)
  have hzero : autocorr g (Real.exp (-T)) = 0 := by
    dsimp [g]
    rw [autocorr_sourceRescale p hL]
    have heq : L * Real.exp (-T) = 2 * b + 1 := by
      dsimp [L]
      rw [mul_assoc, ← Real.exp_add]
      simp
    rw [heq, autocorr_eq_zero_of_source_radius hps (by
      rw [abs_of_pos (by linarith : 0 < 2 * b + 1)]; linarith), mul_zero]
  have hl := autocorr_increment_mul_log_le (hg.of_le (by
    exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) hgc
    (Real.exp_pos (-T)) (Real.exp_le_one_iff.mpr (by linarith : -T ≤ 0))
  rw [hzero, sub_zero, Real.log_exp, neg_neg] at hl
  have hTcost : 4 / η < c * T := by
    dsimp [T]
    field_simp
    nlinarith
  have hRJ : autocorr g 0 / η < biScaleLevyEnergy g := by
    have hm := mul_lt_mul_of_pos_right hTcost hgR
    rw [show 4 / η * autocorr g 0 = 4 * (autocorr g 0 / η) by ring] at hm
    change c * autocorr g 0 * T ≤ 4 * biScaleLevyEnergy g at hl
    nlinarith
  have hJ : 0 < biScaleLevyEnergy g := (div_pos hgR hη).trans hRJ
  let q := fun u => (Real.sqrt (biScaleLevyEnergy g))⁻¹ * g u
  have hnorm := source_energy_normalization hJ
  refine ⟨q, contDiff_const.mul hg, hgc.mul_left, ?_, ?_, hnorm.1, ?_⟩
  · rw [hnorm.2]
    exact div_pos hgR hJ
  · rw [hnorm.2]
    apply (div_lt_iff₀ hJ).mpr
    have he := (div_lt_iff₀ hη).mp hRJ
    nlinarith
  · intro u hu
    simp only [q, hgs u hu, mul_zero]

end

end GaloisForLFunctions.BiScaleUncertainty

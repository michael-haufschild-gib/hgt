import GaloisForLFunctions.BiScaleUncertainty.LinearKreinSmoothingAndInverseLinearGridTail
import GaloisForLFunctions.BiScaleUncertainty.FiniteSpectralEnvelopeRealization
import GaloisForLFunctions.BiScaleUncertainty.UnitCorrelationBump
import GaloisForLFunctions.RHTower.HardyZPhaseAsymptotic

/-!
# Sharpness of the linear logarithmic modulus

`LinearKreinSmoothingAndInverseLinearGridTail` proves
`log(1/d) |h(x) - h(x + d)| ≤ 32√e 𝒥(f) + 2h(0)` for every compact `C²` source. The rate
`1/log(1/d)` and the linear dependence on the energy are optimal together: at every scale
there is an actual source with

`𝒥(g) + h_g(0) ≤ 8 log(1/d) (h_g(0) - h_g(d))`.

The witnesses are the cosine/sine modulations of a fixed bump at frequency `ω = π/d`. Their
correlations sum to `h_φ(x) cos(ωx)`, so their two origin increments at `d` sum to
`h_φ(0) + h_φ(d) ≥ h_φ(0)`, while their energies sum to `h_φ(0)` times the frequency cost
`2θ'(ω) - 2θ'(0) ≤ log ω + O(1)` plus a bounded envelope error. One of the two sources
therefore carries half of the increment at energy `O(log ω)`.
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-- The frequency cost grows at most like `log ω`, with the explicit Stirling remainder. -/
theorem archFrequencyCost_le_log {ω : ℝ} (hω : 1 ≤ ω) :
    archFrequencyCost ω ≤
      Real.log ω + 33 / 8 + Real.pi - 2 * RHTower.gammaHardyPhaseRate 0 := by
  have hω0 : 0 < ω := by linarith
  rw [archFrequencyCost_eq_gammaBracket_sub_zero,
    RHTower.WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate,
    RHTower.WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate]
  have hb := (abs_le.mp (RHTower.gammaHardyPhaseRate_sub_log_conductor_bound hω0)).2
  have hlog : Real.log (ω / (2 * Real.pi)) ≤ Real.log ω :=
    Real.log_le_log (by positivity) (div_le_self hω0.le (by nlinarith [Real.pi_gt_three]))
  have hsq : 33 / (16 * ω ^ 2) ≤ 33 / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hpi : Real.pi / (2 * ω) ≤ Real.pi / 2 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith)
  linarith

/-- The modulated bump pair: origin increments at `d = π/ω` sum to at least `h_φ(0)`. -/
theorem cosine_sine_increment_sum_ge {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφn : ∀ x, 0 ≤ autocorr φ x) {ω : ℝ} (hω : ω ≠ 0) :
    autocorr φ 0 ≤
      (autocorr (cosineSource φ ω) 0 - autocorr (cosineSource φ ω) (Real.pi / ω)) +
        (autocorr (sineSource φ ω) 0 - autocorr (sineSource φ ω) (Real.pi / ω)) := by
  have h0 := autocorr_cosineSource_add_sineSource hφ hφc ω 0
  have hd := autocorr_cosineSource_add_sineSource hφ hφc ω (Real.pi / ω)
  rw [mul_zero, Real.cos_zero, mul_one] at h0
  rw [show ω * (Real.pi / ω) = Real.pi by field_simp, Real.cos_pi] at hd
  linarith [hφn (Real.pi / ω)]

/-- **Optimality of the linear logarithmic modulus.** At arbitrarily small displacements `d`
there is an actual compact `C²` source with `𝒥(g) + h_g(0) ≤ 8 log(1/d) (h_g(0) - h_g(d))`.
Together with `neg_log_mul_abs_autocorr_sub_le`, the increment at scale `d` is pinched between
`(𝒥 + h(0))/(8 log(1/d))` and `32√e(𝒥 + h(0))/log(1/d)` along this family. -/
theorem exists_source_energy_le_neg_log_mul_increment {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    ∃ d : ℝ, 0 < d ∧ d < δ₀ ∧ ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      0 < autocorr g 0 ∧
      biScaleLevyEnergy g + autocorr g 0 ≤ 8 * (-Real.log d) * (autocorr g 0 - autocorr g d) := by
  set φ : ℝ → ℝ := (SharpCycle.seed : ℝ → ℝ) with hφdef
  have hφs : ContDiff ℝ 2 φ := SharpCycle.seedBump.contDiff
  have hφc : HasCompactSupport φ := SharpCycle.seed.hasCompactSupport
  have hφn : ∀ x, 0 ≤ autocorr φ x := SharpCycle.seed_correlation_nonneg
  have H0 : 0 < autocorr φ 0 := SharpCycle.seed_mass_pos
  set Jφ : ℝ := biScaleLevyEnergy φ
  have hJφ : 0 ≤ Jφ := biScaleLevyEnergy_nonneg hφc hφs.continuous
  set K : ℝ := 33 / 8 + Real.pi - 2 * RHTower.gammaHardyPhaseRate 0
  -- choose a large logarithmic frequency
  set M : ℝ := |K| + 1 + 4 * Real.log Real.pi + Jφ / autocorr φ 0 + |Real.log (Real.pi / δ₀)| + 1
  have hlogpi : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  have hM1 : 1 ≤ M := by
    have : 0 ≤ Jφ / autocorr φ 0 := div_nonneg hJφ H0.le
    have := abs_nonneg K; have := abs_nonneg (Real.log (Real.pi / δ₀)); linarith
  set ω : ℝ := Real.exp M
  have hω1 : 1 ≤ ω := Real.one_le_exp_iff.mpr (by linarith)
  have hω0 : 0 < ω := Real.exp_pos M
  have hlogω : Real.log ω = M := Real.log_exp M
  set d : ℝ := Real.pi / ω
  have hd0 : 0 < d := div_pos Real.pi_pos hω0
  have hdlog : -Real.log d = M - Real.log Real.pi := by
    rw [Real.log_div Real.pi_pos.ne' hω0.ne', hlogω]; ring
  have hdδ : d < δ₀ := by
    have hlt : Real.log (Real.pi / δ₀) < M := by
      have := le_abs_self (Real.log (Real.pi / δ₀))
      have : 0 ≤ Jφ / autocorr φ 0 := div_nonneg hJφ H0.le
      linarith [abs_nonneg K]
    have h1 : Real.pi / δ₀ < ω := by
      rw [← Real.exp_log (div_pos Real.pi_pos hδ₀)]
      exact Real.exp_lt_exp.mpr hlt
    rw [div_lt_iff₀ hω0]
    rw [div_lt_iff₀ hδ₀] at h1
    linarith
  -- the energy budget of the modulated pair
  have hEsum := biScaleLevyEnergy_cosine_sine_eq hφs hφc ω
  have hErr := (abs_le.mp (abs_archEnvelopeError_le hφs hφc ω)).2
  have hA := archFrequencyCost_le_log hω1
  rw [hlogω] at hA
  have h0sum := autocorr_cosineSource_add_sineSource hφs.continuous hφc ω 0
  rw [mul_zero, Real.cos_zero, mul_one] at h0sum
  have hinc := cosine_sine_increment_sum_ge hφs.continuous hφc hφn hω0.ne'
  have hgc : ContDiff ℝ 2 (cosineSource φ ω) := contDiff_cosineSource hφs ω
  have hgs : ContDiff ℝ 2 (sineSource φ ω) := contDiff_sineSource hφs ω
  have hgcc : HasCompactSupport (cosineSource φ ω) := hφc.mul_right
  have hgsc : HasCompactSupport (sineSource φ ω) := hφc.mul_right
  set gc : ℝ → ℝ := cosineSource φ ω with hgcdef
  set gs : ℝ → ℝ := sineSource φ ω with hgsdef
  have hJc : 0 ≤ biScaleLevyEnergy gc := biScaleLevyEnergy_nonneg hgcc hgc.continuous
  have hJs : 0 ≤ biScaleLevyEnergy gs := biScaleLevyEnergy_nonneg hgsc hgs.continuous
  have hc0 : 0 ≤ autocorr gc 0 := autocorr_zero_nonneg gc
  have hs0 : 0 ≤ autocorr gs 0 := autocorr_zero_nonneg gs
  have hbudget : biScaleLevyEnergy gc + biScaleLevyEnergy gs + autocorr gc 0 + autocorr gs 0 ≤
      autocorr φ 0 * (M + K) + Jφ + autocorr φ 0 := by
    have := mul_le_mul_of_nonneg_left hA H0.le
    have hKd : K = 33 / 8 + Real.pi - 2 * RHTower.gammaHardyPhaseRate 0 := rfl
    have hJd : Jφ = biScaleLevyEnergy φ := rfl
    rw [hKd, hJd]
    linarith
  -- the increments
  have hdd : Real.pi / ω = d := rfl
  rw [hdd] at hinc
  have hic : 0 ≤ autocorr gc 0 - autocorr gc d := autocorr_sub_nonneg hgcc hgc.continuous d
  have his : 0 ≤ autocorr gs 0 - autocorr gs d := autocorr_sub_nonneg hgsc hgs.continuous d
  -- the logarithmic gain dominates the budget
  have hkey : autocorr φ 0 * (M + K) + Jφ + autocorr φ 0 ≤
      4 * (M - Real.log Real.pi) * autocorr φ 0 := by
    have hJdiv : Jφ = (Jφ / autocorr φ 0) * autocorr φ 0 := by field_simp
    have hK : K ≤ |K| := le_abs_self K
    have hl : 0 ≤ |Real.log (Real.pi / δ₀)| := abs_nonneg _
    have hMdef : M = |K| + 1 + 4 * Real.log Real.pi + Jφ / autocorr φ 0 +
        |Real.log (Real.pi / δ₀)| + 1 := rfl
    have : (M + K) + Jφ / autocorr φ 0 + 1 ≤ 4 * (M - Real.log Real.pi) := by
      have : 0 ≤ Jφ / autocorr φ 0 := div_nonneg hJφ H0.le
      nlinarith
    calc
      _ = ((M + K) + Jφ / autocorr φ 0 + 1) * autocorr φ 0 := by rw [hJdiv]; ring_nf; field_simp
      _ ≤ (4 * (M - Real.log Real.pi)) * autocorr φ 0 := mul_le_mul_of_nonneg_right this H0.le
      _ = _ := by ring
  have hpos : 0 ≤ M - Real.log Real.pi := by
    have : 0 ≤ Jφ / autocorr φ 0 := div_nonneg hJφ H0.le
    linarith [abs_nonneg K, abs_nonneg (Real.log (Real.pi / δ₀))]
  refine ⟨d, hd0, hdδ, ?_⟩
  rcases le_total (autocorr φ 0 / 2) (autocorr gc 0 - autocorr gc d) with hbig | hsmall
  · refine ⟨gc, hgc, hgcc, ?_, ?_⟩
    · have := autocorr_add_nonneg hgcc hgc.continuous d
      linarith
    · rw [hdlog]
      have := mul_le_mul_of_nonneg_left hbig (by linarith : (0 : ℝ) ≤ 8 * (M - Real.log Real.pi))
      nlinarith
  · have hbig : autocorr φ 0 / 2 ≤ autocorr gs 0 - autocorr gs d := by linarith
    refine ⟨gs, hgs, hgsc, ?_, ?_⟩
    · have := autocorr_add_nonneg hgsc hgs.continuous d
      linarith
    · rw [hdlog]
      have := mul_le_mul_of_nonneg_left hbig (by linarith : (0 : ℝ) ≤ 8 * (M - Real.log Real.pi))
      nlinarith

end

end GaloisForLFunctions.BiScaleUncertainty

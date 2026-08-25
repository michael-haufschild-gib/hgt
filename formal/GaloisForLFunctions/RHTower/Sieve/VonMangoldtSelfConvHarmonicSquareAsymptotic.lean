import GaloisForLFunctions.RHTower.Sieve.VonMangoldtSquareHyperbolaAsymptotic
import GaloisForLFunctions.RHTower.Sieve.VonMangoldtSquareProperPrimePowerCorrection
import GaloisForLFunctions.RHTower.LiRemoteQuartetAsymptotics

noncomputable section

open Filter Topology

namespace RHTower.Sieve

private theorem tendsto_logFourth_nat_atTop :
    Tendsto (fun N : ℕ => Real.log N ^ 4) atTop atTop :=
  (tendsto_pow_atTop (n := 4) (by norm_num)).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- Uniformly bounded proper-prime-power correction vanishes at logarithmic fourth-order scale. -/
theorem tendsto_vonMangoldtSelfConvSquareCorrection_div_logFourth :
    Tendsto (fun N : ℕ =>
      vonMangoldtSelfConvSquareCorrection N / Real.log N ^ 4)
      atTop (nhds 0) := by
  apply RHTower.tendsto_bounded_div_atTop_filter tendsto_logFourth_nat_atTop
  filter_upwards [] with N
  exact abs_vonMangoldtSelfConvSquareCorrection_le_tsum N

/-- Sharp unconditional fourth-logarithmic second moment of the von Mangoldt self-convolution. -/
theorem tendsto_vonMangoldtSelfConvHarmonicSquareSum_div_logFourth :
    Tendsto (fun N : ℕ =>
      vonMangoldtSelfConvHarmonicSquareSum N / Real.log N ^ 4)
      atTop (nhds (1 / 12 : ℝ)) := by
  have hmain := (tendsto_const_nhds (x := (2 : ℝ))).mul
    tendsto_vonMangoldtSquareHyperbolaMass_div_logFourth
  have hsum := hmain.add tendsto_vonMangoldtSelfConvSquareCorrection_div_logFourth
  have hfinal : Tendsto (fun N : ℕ =>
      2 * (vonMangoldtSquareHyperbolaMass N / Real.log N ^ 4) +
        vonMangoldtSelfConvSquareCorrection N / Real.log N ^ 4)
      atTop (nhds ((2 : ℝ) * (1 / 24) + 0)) := hsum
  convert hfinal using 1
  · funext N
    rw [vonMangoldtSelfConvHarmonicSquareSum_eq_hyperbola_add_correction]
    ring
  · norm_num

end RHTower.Sieve

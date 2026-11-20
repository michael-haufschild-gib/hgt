import GaloisForLFunctions.goldbach.LiLiu.SpectralScales
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # The critical-line scale is smaller than the main term -/

namespace GaloisForLFunctions.Goldbach.LiLiu
open Filter BezoutValuationIncidence
open scoped Topology
noncomputable section

/-- The uniform positive lower bound for the density suffices for the relative little-o. -/
theorem spectralScale_div_singularSeries_tendsto :
    Tendsto (fun N : ℕ => spectralScale N / singularSeries N) atTop (𝓝 0) := by
  let c := 2*twinPrimeConstant
  have hc : 0 < c := mul_pos (by norm_num) twinPrimeConstant_pos
  have hlog := (isLittleO_log_rpow_rpow_atTop 3 (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero
  have hnat : Tendsto (fun N : ℕ => Real.log N ^ 3 / N) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ← Real.rpow_natCast, Nat.cast_ofNat, Real.rpow_one] using
      hlog.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => Real.sqrt ((Real.log N ^ 3 / N) / c)) atTop (𝓝 0) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp (hnat.div_const c)
  apply squeeze_zero (fun N => div_nonneg (Real.sqrt_nonneg _) (singularSeries_pos N).le) _ hlim
  intro N
  have hS := singularSeries_pos N
  have hn : 0 ≤ Real.log N ^ 3 / N :=
    div_nonneg (pow_nonneg (Real.log_natCast_nonneg _) _) (Nat.cast_nonneg N)
  have he : spectralScale N / singularSeries N = Real.sqrt ((Real.log N ^ 3 / N) / singularSeries N) := by
    apply le_antisymm
    all_goals
      apply le_of_sq_le_sq _ (by first | exact Real.sqrt_nonneg _ | exact div_nonneg (Real.sqrt_nonneg _) hS.le)
      rw [div_pow, spectralScale_sq, Real.sq_sqrt (div_nonneg hn hS.le)]
      apply le_of_eq
    · field_simp [hS.ne']; ring
    · field_simp [hS.ne']; ring
  rw [he]
  exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hn hc (two_mul_twinPrimeConstant_le N))

#print axioms spectralScale_div_singularSeries_tendsto
end
end GaloisForLFunctions.Goldbach.LiLiu

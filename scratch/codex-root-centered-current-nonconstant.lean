import GaloisForLFunctions.RHTower.CriticalCenteredPrimeTailEulerPrimitive
import GaloisForLFunctions.HTGeometry.LSeriesRightLimit

noncomputable section
open Filter Topology LSeries ArithmeticFunction
namespace RHTower

private theorem centeredCurrent_farRight_zero :
    Tendsto (fun N : ℕ => centeredPrimeTailCurrentContinuation (N : ℂ))
      atTop (𝓝 0) := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) -
    zetaTailDirichletCoeff n
  have hs : LSeriesSummable f (2 : ℂ) := by
    simpa only [f, ← logMul_centeredPrimeTailEulerCoeff] using
      (centeredPrimeTailCurrentCoeff_summable (s := (2 : ℂ)) (by norm_num))
  have hnorm : Summable (fun n : ℕ => ‖LSeries.term f (2 : ℂ) n‖) := by
    rw [LSeriesSummable, ← summable_norm_iff] at hs
    exact hs
  have hre : Tendsto (fun N : ℕ => ((N : ℂ)).re) atTop atTop := by
    simpa using (tendsto_natCast_atTop_atTop :
      Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hlim := GaloisForLFunctions.HTGeometry.tendsto_LSeries_of_re_atTop hnorm hre
  have hf1 : f 1 = 0 := by
    simp [f, zetaTailDirichletCoeff]
  rw [hf1] at hlim
  have hneg : Tendsto (fun N : ℕ => -(LSeries f (N : ℂ))) atTop (𝓝 0) := by
    simpa using hlim.neg
  refine hneg.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hNR : 1 < ((N : ℂ)).re := by
    exact_mod_cast hN
  have hcoeff : LSeries.logMul centeredPrimeTailEulerCoeff = f := by
    funext n
    exact logMul_centeredPrimeTailEulerCoeff n
  have hcurrent := centeredPrimeTailCurrentContinuation_eq hNR
  have hseries := LSeries_logMul_centeredPrimeTailEulerCoeff_eq hNR
  rw [hcoeff] at hseries
  rw [hseries, ← infinitePrimeFlux_eq_vonMangoldtLSeries hNR,
    infinitePrimeFlux, hcurrent]
  ring

theorem centeredCurrent_not_constant_at_one :
    ¬ ∀ s : ℂ, centeredPrimeTailCurrentContinuation s =
      centeredPrimeTailCurrentContinuation 1 := by
  intro hconst
  have hγ : (0 : ℝ) < 2 * Real.eulerMascheroniConstant - 1 := by
    have := Real.one_half_lt_eulerMascheroniConstant
    linarith
  have hne : centeredPrimeTailCurrentContinuation 1 ≠ 0 := by
    rw [centeredPrimeTailCurrentContinuation_one]
    exact_mod_cast (ne_of_gt hγ)
  have hlim := centeredCurrent_farRight_zero
  have hconstlim : Tendsto (fun _ : ℕ => centeredPrimeTailCurrentContinuation 1)
      atTop (𝓝 0) := hlim.congr' (Eventually.of_forall fun N => hconst N)
  have hval : centeredPrimeTailCurrentContinuation 1 = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hconstlim
  exact hne hval

end RHTower

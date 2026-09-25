import GaloisForLFunctions.RHTower.CriticalCenteredPrimeTailEulerPrimitive
import GaloisForLFunctions.HTGeometry.LSeriesRightLimit

/-!
# The critical divisor Mellin source is a nonconstant centered Euler current gap

The pole-cancelled Mellin numerator of the complete Chebyshev defect is the
difference between the centered prime-tail current at `1` and at the safe
point `s`. The current is nonconstant: its pole value is `2γ-1>0`, whereas
its Dirichlet series tends to zero on the positive real ray. This proves
source-specific nontriviality, but not yet a finite-order pole jet or the
weighted prime-sampling asymptotic needed for the terminal energy no-go.
-/

noncomputable section
open Filter Topology LSeries ArithmeticFunction
namespace RHTower

/-- Safe-half-plane weld between the critical source Mellin numerator and
the centered prime-tail current's departure from its pole value. -/
theorem criticalSourceMellinNumerator_eq_centeredCurrentGap
    {s : ℂ} (hs : 1 < s.re) :
    -logDeriv riemannZeta s - riemannZeta s +
        2 * (Real.eulerMascheroniConstant : ℂ) =
      centeredPrimeTailCurrentContinuation 1 -
        centeredPrimeTailCurrentContinuation s := by
  rw [centeredPrimeTailCurrentContinuation_one,
    centeredPrimeTailCurrentContinuation_eq hs]
  ring

/-- The centered pole-cancelled current decays along the positive real ray. -/
theorem centeredCurrent_farRight_zero :
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

/-- The centered pole-cancelled current is not globally constant: its value
at `1` is positive, but it decays on the far real ray. -/
theorem centeredPrimeTailCurrentContinuation_not_constant_at_one :
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

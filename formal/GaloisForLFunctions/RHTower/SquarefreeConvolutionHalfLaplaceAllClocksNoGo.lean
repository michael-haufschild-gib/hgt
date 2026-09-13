import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfHeatMass
import GaloisForLFunctions.RHTower.PoleFactorTwoThirdsLowerBound
import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfLaplaceTwoClockNoGo

/-!
# Every cofinal two-clock heat proposal fails local boundedness

The signed heat source diverges at `s = 2/3` along every positive heat time tending to zero.
The actual pole-factor approximants stay bounded away from zero there once their degree is four.
Consequently no positive heat clock and cofinal pole-degree clock make the literal normalized
family locally bounded on `rightHalf`. In particular, arbitrarily sparse heat clocks do not escape.

This rejects this root producer, not the dyadic-root route or the possibility of analytic continuation
by a different, source-identified construction. The quantitative positive survivor is the complete
source-mass reserve in `SquarefreeConvolutionHalfHeatMass`.
-/

open Complex Filter Metric Set Topology
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

theorem tendsto_norm_squarefreeHalfLaplaceTimeSum_twoThirds_atTop :
    Tendsto (fun t => ‖squarefreeHalfLaplaceTimeSum t (2 / 3 : ℂ)‖)
      (𝓝[>] 0) atTop := by
  have heq (t : ℝ) : squarefreeHalfLaplaceTimeSum t (2 / 3 : ℂ) =
      coeffLaplaceProfile (LSeries.term squarefreeConvolutionHalf (2 / 3 : ℂ)) t := by
    unfold squarefreeHalfLaplaceTimeSum squarefreeHalfLaplaceTimeTerm coeffLaplaceProfile
    apply tsum_congr
    intro n
    push_cast
    ring
  simp_rw [heq]
  exact tendsto_atTop_mono (fun t => Complex.re_le_norm _)
    tendsto_re_squarefreeHalf_twoThirds_heat_atTop

/-- No choice of sparse positive heat clock and cofinal pole clock makes the actual family
locally bounded. This concerns this specific producer, not existence of global analytic roots. -/
theorem not_exists_locallyBounded_squarefreeHalfLaplace_cofinal_twoClocks :
    ¬ ∃ (κ : ℕ → ℕ) (τ : ℕ → ℝ),
      Tendsto κ atTop atTop ∧ (∀ N, 0 < τ N) ∧ Tendsto τ atTop (𝓝 0) ∧
        PoleClearedFirstTraceLaplaceTwoClockLocallyBounded κ τ := by
  rintro ⟨κ, τ, hκ, hpos, htend, hloc⟩
  have hs : (2 / 3 : ℂ) ∈ rightHalf := by norm_num [rightHalf]
  obtain ⟨R, hR, _, C, hC⟩ := hloc (2 / 3 : ℂ) hs
  have hbound (N : ℕ) := hC N (2 / 3 : ℂ) (mem_ball_self hR)
  have hdet : 0 < ‖squarefreeCarlemanHalfDet (2 / 3 : ℂ)‖ :=
    norm_pos_iff.mpr (squarefreeCarlemanHalfDet_ne_zero _)
  let K := 2 * (C * ‖squarefreeCarlemanHalfDet (2 / 3 : ℂ)‖)
  have hbounded : ∀ᶠ N in atTop, ‖squarefreeHalfLaplaceTimeSum (τ N) (2 / 3 : ℂ)‖ ≤ K := by
    filter_upwards [hκ.eventually (eventually_ge_atTop 4)] with N hN
    have hp := norm_poleFactorSqrtApprox_twoThirds_ge_half hN
    have hb := hbound N
    rw [poleClearedFirstTraceLaplaceTwoClockApprox, norm_div, norm_mul] at hb
    have hprod := (div_le_iff₀ hdet).mp hb
    dsimp [K]
    nlinarith [norm_nonneg (squarefreeHalfLaplaceTimeSum (τ N) (2 / 3 : ℂ))]
  have htzero : Tendsto τ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨htend, Eventually.of_forall hpos⟩
  have hdiv := tendsto_norm_squarefreeHalfLaplaceTimeSum_twoThirds_atTop.comp htzero
  obtain ⟨N, hN, hgt⟩ := (hbounded.and (hdiv.eventually (eventually_gt_atTop K))).exists
  exact (not_lt_of_ge hN) hgt

end RHTower


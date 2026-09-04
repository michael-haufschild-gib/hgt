import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfCesaroIteratedLogFrontier
import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfCesaroWeightedIdentity

/-!
# Cesàro source vanishing forced by every cofinal schedule

At `boundaryExteriorPoint = 6/11`, every cofinal Cayley pole-factor schedule has norm tending to
infinity.  Consequently local boundedness of the pole-cleared scheduled family forces the
underlying, schedule-independent triangular Cesàro mean to converge to zero there.  This isolates
one common arithmetic gate for all slow schedules.
-/

open Complex Filter Metric Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Any cofinal scheduled local bound forces the Cesàro source itself to vanish at `6/11`. -/
theorem tendsto_squarefreeHalfCesaroSum_boundaryExteriorPoint_zero_of_cofinal_locallyBounded
    {kappa : ℕ → ℕ} (hkappa : Tendsto kappa atTop atTop)
    (hloc : PoleClearedFirstTraceCesaroScheduledLocallyBounded kappa) :
    Tendsto (fun N => squarefreeHalfCesaroSum N boundaryExteriorPoint) atTop (𝓝 0) := by
  obtain ⟨R, hR, _, C, hC⟩ :=
    hloc boundaryExteriorPoint boundaryExteriorPoint_mem_rightHalf
  have hcenter : boundaryExteriorPoint ∈ ball boundaryExteriorPoint R := mem_ball_self hR
  have hbound : ∀ N : ℕ,
      ‖poleClearedFirstTraceCesaroScheduledApprox kappa N boundaryExteriorPoint‖ ≤ C :=
    fun N => hC N boundaryExteriorPoint hcenter
  have hCnonneg : 0 ≤ C :=
    (norm_nonneg
      (poleClearedFirstTraceCesaroScheduledApprox kappa 0 boundaryExteriorPoint)).trans (hbound 0)
  let K : ℝ := C * ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hdegree : ∀ᶠ N : ℕ in atTop, 24 ≤ kappa N :=
    hkappa.eventually (eventually_ge_atTop 24)
  have hweighted : ∀ᶠ N : ℕ in atTop,
      (5 : ℝ) ^ (kappa N - 24) *
        ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖ ≤ K := by
    filter_upwards [hdegree] with N hN
    have hfactor := norm_poleFactorSqrtApprox_boundaryExteriorPoint_five_pow hN
    have hdetpos : 0 < ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖ :=
      norm_pos_iff.mpr (squarefreeCarlemanHalfDet_ne_zero boundaryExteriorPoint)
    have hsource := hbound N
    have hprod :
        ‖poleFactorSqrtApprox (kappa N) boundaryExteriorPoint‖ *
            ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖ ≤ K := by
      rw [poleClearedFirstTraceCesaroScheduledApprox, norm_div, norm_mul] at hsource
      exact (div_le_iff₀ hdetpos).mp hsource
    exact (mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)).trans hprod
  have hsub : Tendsto (fun N : ℕ => kappa N - 24) atTop atTop := by
    refine Filter.tendsto_atTop.mpr ?_
    intro b
    filter_upwards [hkappa.eventually (eventually_ge_atTop (b + 24))] with N hN
    omega
  have hpow : Tendsto (fun N : ℕ => (5 : ℝ) ^ (kappa N - 24)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)).comp hsub
  have hinv : Tendsto (fun N : ℕ => ((5 : ℝ) ^ (kappa N - 24))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hpow
  have hmajor : Tendsto
      (fun N : ℕ => K * ((5 : ℝ) ^ (kappa N - 24))⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hinv
  have hnormBound : ∀ᶠ N : ℕ in atTop,
      ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖ ≤
        K * ((5 : ℝ) ^ (kappa N - 24))⁻¹ := by
    filter_upwards [hweighted] with N hN
    have hpowpos : 0 < (5 : ℝ) ^ (kappa N - 24) := by positivity
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ hpowpos).mpr (by simpa [mul_comm] using hN)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) hnormBound hmajor

/-- Refuting the common zero-limit gate rules out every chosen cofinal schedule. -/
theorem no_poleClearedFirstTraceCesaroScheduledLocallyBounded_of_not_tendsto_zero
    {kappa : ℕ → ℕ} (hkappa : Tendsto kappa atTop atTop)
    (hnot : ¬ Tendsto (fun N => squarefreeHalfCesaroSum N boundaryExteriorPoint)
      atTop (𝓝 0)) :
    ¬ PoleClearedFirstTraceCesaroScheduledLocallyBounded kappa :=
  fun hloc => hnot
    (tendsto_squarefreeHalfCesaroSum_boundaryExteriorPoint_zero_of_cofinal_locallyBounded
      hkappa hloc)

/-- Concrete reduction for the canonical iterated-logarithmic schedule. -/
theorem no_iteratedLogarithmicCesaroSchedule_locallyBounded_of_not_tendsto_zero
    (hnot : ¬ Tendsto (fun N => squarefreeHalfCesaroSum N boundaryExteriorPoint)
      atTop (𝓝 0)) :
    ¬ PoleClearedFirstTraceCesaroScheduledLocallyBounded
      iteratedLogarithmicCayleySchedule :=
  no_poleClearedFirstTraceCesaroScheduledLocallyBounded_of_not_tendsto_zero
    tendsto_iteratedLogarithmicCayleySchedule_atTop hnot

end

end RHTower

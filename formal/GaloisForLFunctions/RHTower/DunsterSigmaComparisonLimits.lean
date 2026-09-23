import GaloisForLFunctions.RHTower.DunsterSigmaComparison

/-!
# Free-data limits for the radial PSWF Liouville transformation

The exact multiplicative comparison of `DunsterSigmaComparison` is uniform up to the turning
point.  This leaf takes its asymptotic consequence: along any filter for which the turning
parameter tends to zero, the anchored phase ratio and fourth-power amplitude ratio tend to one at
every fixed exterior radius.  These are precisely the phase and amplitude assertions in equation
`(10)` of the radial leakage card, without any Bessel-envelope or PSWF-solution assumption.
-/

open Filter

namespace RHTower

noncomputable section

theorem radialPSWFTurningPhase_div_free_tendsto_one
    {ι : Type*} {l : Filter ι} {sigma : ι → ℝ}
    (hsigma : Tendsto sigma l (nhds 0)) {x : ℝ} (hx : 1 < x) :
    Tendsto (fun i => radialPSWFTurningPhase (sigma i) x / Real.sqrt (x ^ (2 : ℕ) - 1))
      l (nhds 1) := by
  have hfree : 0 < Real.sqrt (x ^ (2 : ℕ) - 1) := Real.sqrt_pos.mpr (by nlinarith)
  have hsquare : Tendsto (fun i => sigma i ^ (2 : ℕ)) l (nhds 0) := by
    simpa using hsigma.pow 2
  have honeSub : Tendsto (fun i => 1 - sigma i ^ (2 : ℕ)) l (nhds 1) := by
    simpa using (tendsto_const_nhds.sub hsquare :
      Tendsto (fun i => 1 - sigma i ^ (2 : ℕ)) l (nhds (1 - 0)))
  have hlower : Tendsto (fun i => Real.sqrt (1 - sigma i ^ (2 : ℕ))) l (nhds 1) := by
    rw [show (fun i => Real.sqrt (1 - sigma i ^ (2 : ℕ))) =
      Real.sqrt ∘ fun i => 1 - sigma i ^ (2 : ℕ) by rfl]
    simpa using (Real.continuous_sqrt.tendsto 1).comp honeSub
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds ?_ ?_
  · filter_upwards with i
    have h := (radialPSWFTurningPhase_mem_Icc (sigma i) x).1
    rw [le_div_iff₀ hfree]
    exact h
  · filter_upwards with i
    have h := (radialPSWFTurningPhase_mem_Icc (sigma i) x).2
    rw [div_le_one hfree]
    exact h

theorem radialPSWFAmplitudePow4_turning_ratio_tendsto_one
    {ι : Type*} {l : Filter ι} {sigma : ι → ℝ}
    (hsigma : Tendsto sigma l (nhds 0)) {x : ℝ} (hx : 1 < x) :
    Tendsto (fun i =>
      radialPSWFAmplitudePow4 (sigma i) (radialPSWFTurningPhase (sigma i) x) x /
        radialPSWFAmplitudePow4 0 (Real.sqrt (x ^ (2 : ℕ) - 1)) x) l (nhds 1) := by
  have hsquare : Tendsto (fun i => sigma i ^ (2 : ℕ)) l (nhds 0) := by
    simpa using hsigma.pow 2
  have honeSub : Tendsto (fun i => 1 - sigma i ^ (2 : ℕ)) l (nhds 1) := by
    simpa using tendsto_const_nhds.sub hsquare
  have hinv : Tendsto (fun i => (1 - sigma i ^ (2 : ℕ))⁻¹) l (nhds 1) := by
    simpa using honeSub.inv₀ one_ne_zero
  have hsmall : ∀ᶠ i in l, sigma i ^ (2 : ℕ) < 1 :=
    hsquare.eventually (eventually_lt_nhds zero_lt_one)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' honeSub hinv ?_ ?_
  · filter_upwards [hsmall] with i hi
    exact (radialPSWFAmplitudePow4_turning_ratio_mem_Icc hi hx).1
  · filter_upwards [hsmall] with i hi
    exact (radialPSWFAmplitudePow4_turning_ratio_mem_Icc hi hx).2

theorem radialPSWFTurning_liouville_data_tendsto_free
    {ι : Type*} {l : Filter ι} {sigma : ι → ℝ}
    (hsigma : Tendsto sigma l (nhds 0)) {x : ℝ} (hx : 1 < x) :
    Tendsto (fun i => radialPSWFTurningPhase (sigma i) x / Real.sqrt (x ^ (2 : ℕ) - 1))
        l (nhds 1) ∧
      Tendsto (fun i =>
        radialPSWFAmplitudePow4 (sigma i) (radialPSWFTurningPhase (sigma i) x) x /
          radialPSWFAmplitudePow4 0 (Real.sqrt (x ^ (2 : ℕ) - 1)) x) l (nhds 1) :=
  ⟨radialPSWFTurningPhase_div_free_tendsto_one hsigma hx,
    radialPSWFAmplitudePow4_turning_ratio_tendsto_one hsigma hx⟩

end

end RHTower


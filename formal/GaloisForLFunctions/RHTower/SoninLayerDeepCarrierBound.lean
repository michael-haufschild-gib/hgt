import GaloisForLFunctions.RHTower.SoninCouplingBranchEstimate

/-!
# The aperture layer only sees the failure to lie in a deeper carrier

Both projections of an aperture layer absorb the projection at any larger aperture, so the layer
annihilates the deeper carrier outright.  A vector is therefore seen by the layer only through its
distance to that carrier, and since the layer is a contraction the bound is with constant one.

This explains uniformly why the natural test families give nothing: any family that is
asymptotically inside a deeper Sonin carrier is asymptotically invisible to the layer, whatever its
support.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter Topology
open ContinuousLinearMap

/-- The aperture layer annihilates every deeper carrier. -/
theorem evenSoninApertureLayer_mul_evenCentralSoninProjection_eq_zero
    {a b s : ℝ} (hab : a ≤ b) (hbs : b ≤ s) :
    evenSoninApertureLayer a b * evenCentralSoninProjection s = 0 := by
  rcases evenCentralSoninProjection_mul_of_le (hab.trans hbs) with ⟨_, has'⟩
  rcases evenCentralSoninProjection_mul_of_le hbs with ⟨_, hbs'⟩
  unfold evenSoninApertureLayer
  rw [sub_mul, has', hbs', sub_self]

/-- **Deep-carrier bound.**  The aperture layer of a vector is bounded by its distance to the
carrier at any larger aperture. -/
theorem norm_evenSoninApertureLayer_apply_le_dist_deepCarrier
    {a b s : ℝ} (hab : a ≤ b) (hbs : b ≤ s) (v : evenSubspace) :
    ‖evenSoninApertureLayer a b v‖ ≤ ‖v - evenCentralSoninProjection s v‖ := by
  have hkill : evenSoninApertureLayer a b (evenCentralSoninProjection s v) = 0 := by
    have := congrArg (fun T : evenSubspace →L[ℂ] evenSubspace => T v)
      (evenSoninApertureLayer_mul_evenCentralSoninProjection_eq_zero hab hbs)
    simpa using this
  have hsplit : evenSoninApertureLayer a b v =
      evenSoninApertureLayer a b (v - evenCentralSoninProjection s v) := by
    rw [map_sub, hkill, sub_zero]
  rw [hsplit]
  exact norm_evenSoninApertureLayer_apply_le hab _

/-- A family that is asymptotically inside a deeper carrier is asymptotically invisible to the
aperture layer. -/
theorem tendsto_norm_evenSoninApertureLayer_apply_of_tendsto_deepCarrier
    {a b s : ℝ} (hab : a ≤ b) (hbs : b ≤ s) {v : ℕ → evenSubspace}
    (hv : Tendsto (fun n => ‖v n - evenCentralSoninProjection s (v n)‖)
      atTop (𝓝 0)) :
    Tendsto (fun n => ‖evenSoninApertureLayer a b (v n)‖) atTop (𝓝 0) := by
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hv
  exact norm_evenSoninApertureLayer_apply_le_dist_deepCarrier hab hbs (v n)

/-- The same statement for the layer composed with any bounded operator: only the failure of the
image to lie in a deeper carrier is visible. -/
theorem norm_evenSoninApertureLayer_comp_apply_le_dist_deepCarrier
    {a b s : ℝ} (hab : a ≤ b) (hbs : b ≤ s)
    (T : evenSubspace →L[ℂ] evenSubspace) (v : evenSubspace) :
    ‖evenSoninApertureLayer a b (T v)‖ ≤
      ‖T v - evenCentralSoninProjection s (T v)‖ :=
  norm_evenSoninApertureLayer_apply_le_dist_deepCarrier hab hbs (T v)

end RHTower

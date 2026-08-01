import GaloisForLFunctions.RHTower.SoninScaledPacketL2
import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry

/-!
# Physical cutoffs on the rescaled packet

The rescaled packet lives strictly between the radii `m - δ` and `m + δ`, so a physical cutoff at or
below the inner radius annihilates it and a cutoff at or above the outer radius fixes it.

These are the two hypotheses the two-branch estimate consumes, now for the family whose constants
are uniform in the annulus.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory ContinuousLinearMap

/-- The rescaled packet vanishes inside the inner radius. -/
theorem soninScaledPacket_eq_zero_of_abs_le (m δ κ : ℝ) (hδ : 0 < δ) {x : ℝ}
    (hx : |x| ≤ m - δ) : soninScaledPacket m δ κ x = 0 := by
  by_contra hne
  rcases soninScaledPacket_support_subset m δ κ hδ hne with h | h
  · rw [abs_lt] at h
    rcases abs_le.mp hx with ⟨h1, h2⟩
    linarith
  · rw [abs_lt] at h
    rcases abs_le.mp hx with ⟨h1, h2⟩
    linarith

/-- The rescaled packet vanishes outside the outer radius. -/
theorem soninScaledPacket_eq_zero_of_le_abs (m δ κ : ℝ) (hδ : 0 < δ) (hm : 0 ≤ m) {x : ℝ}
    (hx : m + δ ≤ |x|) : soninScaledPacket m δ κ x = 0 := by
  by_contra hne
  rcases soninScaledPacket_support_subset m δ κ hδ hne with h | h
  · rw [abs_lt] at h
    rcases le_abs.mp hx with h1 | h1 <;> linarith
  · rw [abs_lt] at h
    rcases le_abs.mp hx with h1 | h1 <;> linarith

/-- A physical cutoff at or below the inner radius annihilates the rescaled packet. -/
theorem evenIndicatorCutoff_soninScaledPacketEven_eq_zero
    (m δ κ : ℝ) (hδ : 0 < δ) (s : ℝ) (hs : s ≤ m - δ) :
    evenIndicatorCutoff s (soninScaledPacketEven m δ κ hδ) = 0 := by
  have hgoal : indicatorCutoff (centralInterval s) (measurableSet_centralInterval s)
      (soninScaledPacketL2 m δ κ hδ) = 0 := by
    apply Lp.ext
    filter_upwards [indicatorCutoff_ae (centralInterval s) (measurableSet_centralInterval s)
      (soninScaledPacketL2 m δ κ hδ), soninScaledPacketL2_coeFn m δ κ hδ,
      Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx hval hzero
    rw [hx, hzero]
    by_cases hmem : x ∈ centralInterval s
    · rw [Set.indicator_of_mem hmem, hval]
      have habs : |x| ≤ m - δ := le_trans (abs_le.mpr ⟨hmem.1, hmem.2⟩) hs
      rw [soninScaledPacket_eq_zero_of_abs_le m δ κ hδ habs]
      simp
    · rw [Set.indicator_of_notMem hmem]
      rfl
  apply Subtype.ext
  rw [coe_evenIndicatorCutoff_apply, coe_soninScaledPacketEven, hgoal]
  simp

/-- A physical cutoff at or above the outer radius fixes the rescaled packet. -/
theorem evenIndicatorCutoff_soninScaledPacketEven_eq_self
    (m δ κ : ℝ) (hδ : 0 < δ) (hm : 0 ≤ m) (s : ℝ) (hs : m + δ ≤ s) :
    evenIndicatorCutoff s (soninScaledPacketEven m δ κ hδ) =
      soninScaledPacketEven m δ κ hδ := by
  apply Subtype.ext
  rw [coe_evenIndicatorCutoff_apply, coe_soninScaledPacketEven]
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (centralInterval s) (measurableSet_centralInterval s)
    (soninScaledPacketL2 m δ κ hδ), soninScaledPacketL2_coeFn m δ κ hδ] with x hx hval
  rw [hx]
  by_cases hmem : x ∈ centralInterval s
  · rw [Set.indicator_of_mem hmem]
  · rw [Set.indicator_of_notMem hmem, hval]
    have habs : m + δ ≤ |x| := by
      have hs' : s ≤ |x| := by
        by_contra hlt
        push Not at hlt
        exact hmem (abs_le.mp hlt.le)
      linarith
    rw [soninScaledPacket_eq_zero_of_le_abs m δ κ hδ hm habs]
    simp

end RHTower

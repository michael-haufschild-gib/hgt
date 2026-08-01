import GaloisForLFunctions.RHTower.SoninChannelNormIdentity
import GaloisForLFunctions.RHTower.SoninBurnolConductorConcrete

/-!
# The channel read in the frequency variable

Reflecting the tower channel through the Fourier transform gives a step multiplier in the frequency
variable.  Because the reflection is an isometric involution, its energy on a vector is the energy
of the position channel on the transformed vector, and the layer masses become the frequency-band
masses of the original.

So the two-radius lower bound transports verbatim: the reflected channel is large on a vector whose
frequency mass sits between two tower radii.  This is the side on which the source packets do move —
their support is fixed but their frequency runs.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

/-- The tower channel reflected into the frequency variable. -/
def evenFourierLogShellChannel (a r : ℝ) (n : ℕ) : evenSubspace →L[ℂ] evenSubspace :=
  evenFourierTransform * evenLogShellChannel a r n * evenFourierTransform

/-- The reflected channel is the position channel read after the transform. -/
theorem evenFourierLogShellChannel_apply (a r : ℝ) (n : ℕ) (w : evenSubspace) :
    evenFourierLogShellChannel a r n w =
      evenFourierTransform (evenLogShellChannel a r n (evenFourierTransform w)) := rfl

theorem norm_evenFourierLogShellChannel_apply (a r : ℝ) (n : ℕ) (w : evenSubspace) :
    ‖evenFourierLogShellChannel a r n w‖ =
      ‖evenLogShellChannel a r n (evenFourierTransform w)‖ := by
  rw [evenFourierLogShellChannel_apply, evenFourierTransform_isometry]

/-- A physical cutoff after the transform is the frequency cutoff before it. -/
theorem norm_evenIndicatorCutoff_evenFourierTransform (t : ℝ) (w : evenSubspace) :
    ‖evenIndicatorCutoff t (evenFourierTransform w)‖ = ‖evenFourierCutoff t w‖ := by
  have hR : evenFourierCutoff t w =
      evenFourierTransform (evenIndicatorCutoff t (evenFourierTransform w)) := by
    rw [evenFourierCutoff_eq_reflectedCutoff t]
    rfl
  rw [hR, evenFourierTransform_isometry]

/-- The transported layer mass is a frequency-band mass. -/
theorem norm_evenIndicatorLayer_evenFourierTransform (s t : ℝ) (w : evenSubspace) :
    ‖evenIndicatorLayer s t (evenFourierTransform w)‖ =
      ‖evenFourierCutoff t w - evenFourierCutoff s w‖ := by
  have hs : evenFourierCutoff s w =
      evenFourierTransform (evenIndicatorCutoff s (evenFourierTransform w)) := by
    rw [evenFourierCutoff_eq_reflectedCutoff s]
    rfl
  have ht : evenFourierCutoff t w =
      evenFourierTransform (evenIndicatorCutoff t (evenFourierTransform w)) := by
    rw [evenFourierCutoff_eq_reflectedCutoff t]
    rfl
  rw [hs, ht, ← map_sub, evenFourierTransform_isometry]
  rfl

/-- **Two-radius lower bound in the frequency variable.**  The reflected channel's energy is at
least the smallest layer logarithm in a range, times the frequency mass the vector has between the
two radii of that range. -/
theorem sq_le_norm_sq_evenFourierLogShellChannel_apply
    (a r : ℝ) (ha : 0 < a) (hr : 1 < r) (n m : ℕ) (hmn : m ≤ n) (w : evenSubspace)
    (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ k, m ≤ k → k < n → L ≤ |Real.log (logShellRadius a r k)|) :
    L ^ 2 * (‖evenFourierCutoff (logShellRadius a r n) w -
          evenFourierCutoff (logShellRadius a r 0) w‖ ^ 2 -
        ‖evenFourierCutoff (logShellRadius a r m) w -
          evenFourierCutoff (logShellRadius a r 0) w‖ ^ 2) ≤
      ‖evenFourierLogShellChannel a r n w‖ ^ 2 := by
  have hbound := sq_le_norm_sq_evenLogShellChannel_apply a r ha hr n m hmn
    (evenFourierTransform w) L hL0 hL
  rw [norm_evenIndicatorLayer_evenFourierTransform, norm_evenIndicatorLayer_evenFourierTransform]
    at hbound
  rw [norm_evenFourierLogShellChannel_apply]
  exact hbound

end RHTower

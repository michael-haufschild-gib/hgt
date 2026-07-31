import GaloisForLFunctions.RHTower.SoninLayerDeepCarrierBound

/-!
# The coupling is a compression of the dilation outside the outer carrier

The aperture layer annihilates every deeper carrier, so it is unchanged by multiplying with the
complement of one.  Applying this on the left of the coupling, and the dual absorption on the
right, sandwiches the dilation between two copies of the complement of the outer carrier.

The coupling therefore never sees the dilation on the outer carrier itself: only the part of `D_r`
acting outside `K_c` contributes.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- The aperture layer is unchanged on the right by the complement of any deeper carrier. -/
theorem evenSoninApertureLayer_mul_one_sub_evenCentralSoninProjection
    {a b s : ℝ} (hab : a ≤ b) (hbs : b ≤ s) :
    evenSoninApertureLayer a b * (1 - evenCentralSoninProjection s) =
      evenSoninApertureLayer a b := by
  rw [mul_sub, mul_one,
    evenSoninApertureLayer_mul_evenCentralSoninProjection_eq_zero hab hbs, sub_zero]

/-- The aperture layer is unchanged on the left by the complement of its own outer carrier. -/
theorem one_sub_evenCentralSoninProjection_mul_evenSoninApertureLayer
    {b c : ℝ} (hbc : b ≤ c) :
    (1 - evenCentralSoninProjection c) * evenSoninApertureLayer b c =
      evenSoninApertureLayer b c := by
  rcases evenCentralSoninProjection_mul_of_le hbc with ⟨hcb, _⟩
  have hkill : evenCentralSoninProjection c * evenSoninApertureLayer b c = 0 := by
    unfold evenSoninApertureLayer
    rw [mul_sub, hcb]
    have hidem : evenCentralSoninProjection c * evenCentralSoninProjection c =
        evenCentralSoninProjection c := by
      rw [evenCentralSoninProjection_eq_starProjection]
      exact (evenCentralSoninCarrier c).isIdempotentElem_starProjection
    rw [hidem, sub_self]
  rw [sub_mul, one_mul, hkill, sub_zero]

/-- **Outer compression form of the coupling.**  The successive-layer coupling is the dilation
compressed on both sides by the complement of the outer carrier, between the two aperture layers.
Only the part of the dilation acting outside `K_c` contributes. -/
theorem evenSoninApertureSuccessiveLayerTransition_eq_outerCompression
    {a b c r : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hr : 1 < r) :
    evenSoninApertureSuccessiveLayerTransition a b c r hr =
      evenSoninApertureLayer a b * (1 - evenCentralSoninProjection c) *
        evenDilationSum r hr *
          ((1 - evenCentralSoninProjection c) * evenSoninApertureLayer b c) := by
  unfold evenSoninApertureSuccessiveLayerTransition
  rw [evenSoninApertureLayer_mul_one_sub_evenCentralSoninProjection hab hbc,
    one_sub_evenCentralSoninProjection_mul_evenSoninApertureLayer hbc]

/-- Consequently the coupling is bounded by the compressed dilation alone. -/
theorem norm_evenSoninApertureSuccessiveLayerTransition_apply_le_outerCompression
    {a b c r : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hr : 1 < r) (v : evenSubspace) :
    ‖evenSoninApertureSuccessiveLayerTransition a b c r hr v‖ ≤
      ‖(1 - evenCentralSoninProjection c)
        (evenDilationSum r hr
          ((1 - evenCentralSoninProjection c)
            (evenSoninApertureLayer b c v)))‖ := by
  have hform := evenSoninApertureSuccessiveLayerTransition_eq_outerCompression
    hab hbc hr
  have happ : evenSoninApertureSuccessiveLayerTransition a b c r hr v =
      evenSoninApertureLayer a b
        ((1 - evenCentralSoninProjection c)
          (evenDilationSum r hr
            ((1 - evenCentralSoninProjection c)
              (evenSoninApertureLayer b c v)))) := by
    have := congrArg (fun T : evenSubspace →L[ℂ] evenSubspace => T v) hform
    simpa using this
  rw [happ]
  exact norm_evenSoninApertureLayer_apply_le hab _

end RHTower

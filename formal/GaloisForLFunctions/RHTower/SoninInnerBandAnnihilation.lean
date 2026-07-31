import GaloisForLFunctions.RHTower.SoninApertureFourierParityNoGo

/-!
# Vectors inside the aperture window are annihilated by the Sonin projection

Every vector of the Sonin carrier at aperture `c` vanishes on the central window `[-c,c]`, so a
vector supported inside that window is orthogonal to the whole carrier and the Sonin projection
kills it exactly — not merely asymptotically.

This is the exact counterpart of the asymptotic statement that shells far outside the window are
nearly fixed by the projection, and it is what makes inner-band shells usable as test vectors for
the aperture layers.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

/-- A vector fixed by the physical cutoff at `c` is orthogonal to the Sonin carrier at `c`. -/
theorem inner_eq_zero_of_mem_evenCentralSoninCarrier_of_indicatorCutoff_eq_self
    (c : ℝ) {w : evenSubspace} (hw : evenIndicatorCutoff c w = w)
    {g : evenSubspace} (hg : g ∈ evenCentralSoninCarrier c) :
    inner ℂ g w = 0 := by
  have hgc : evenIndicatorCutoff c g = 0 :=
    ((mem_evenCentralSoninCarrier_iff_cutoffs_zero c g).mp hg).1
  have hadj : ContinuousLinearMap.adjoint (evenIndicatorCutoff c) =
      evenIndicatorCutoff c := adjoint_evenIndicatorCutoff c
  calc
    inner ℂ g w = inner ℂ g (evenIndicatorCutoff c w) := by rw [hw]
    _ = inner ℂ g (ContinuousLinearMap.adjoint (evenIndicatorCutoff c) w) := by rw [hadj]
    _ = inner ℂ (evenIndicatorCutoff c g) w :=
        ContinuousLinearMap.adjoint_inner_right (evenIndicatorCutoff c) g w
    _ = 0 := by rw [hgc, inner_zero_left]

/-- **Exact inner-band annihilation.**  The Sonin projection at aperture `c` annihilates every
vector supported inside the central window `[-c,c]`. -/
theorem evenCentralSoninProjection_eq_zero_of_indicatorCutoff_eq_self
    (c : ℝ) {w : evenSubspace} (hw : evenIndicatorCutoff c w = w) :
    evenCentralSoninProjection c w = 0 := by
  have hPP : evenCentralSoninProjection c * evenCentralSoninProjection c =
      evenCentralSoninProjection c := by
    rw [evenCentralSoninProjection_eq_starProjection]
    exact (evenCentralSoninCarrier c).isIdempotentElem_starProjection
  have hidem : evenCentralSoninProjection c (evenCentralSoninProjection c w) =
      evenCentralSoninProjection c w := by
    simpa using DFunLike.congr_fun hPP w
  have hmem : evenCentralSoninProjection c w ∈ evenCentralSoninCarrier c := by
    rw [evenCentralSoninProjection_eq_starProjection]
    exact Submodule.starProjection_apply_mem _ _
  have hadjP : ContinuousLinearMap.adjoint (evenCentralSoninProjection c) =
      evenCentralSoninProjection c := adjoint_evenCentralSoninProjection c
  have hself : inner ℂ (evenCentralSoninProjection c w)
      (evenCentralSoninProjection c w) =
      inner ℂ (evenCentralSoninProjection c w) w := by
    calc
      inner ℂ (evenCentralSoninProjection c w) (evenCentralSoninProjection c w) =
          inner ℂ (evenCentralSoninProjection c w)
            (ContinuousLinearMap.adjoint (evenCentralSoninProjection c) w) := by rw [hadjP]
      _ = inner ℂ (evenCentralSoninProjection c (evenCentralSoninProjection c w)) w :=
        ContinuousLinearMap.adjoint_inner_right (evenCentralSoninProjection c)
          (evenCentralSoninProjection c w) w
      _ = inner ℂ (evenCentralSoninProjection c w) w := by rw [hidem]
  have hzero : inner ℂ (evenCentralSoninProjection c w) w = 0 :=
    inner_eq_zero_of_mem_evenCentralSoninCarrier_of_indicatorCutoff_eq_self c hw hmem
  exact inner_self_eq_zero.mp (hself.trans hzero)

/-- Consequently the aperture-layer projection acts on an inner-band vector through the outer
aperture alone. -/
theorem evenSoninApertureLayer_eq_of_indicatorCutoff_eq_self
    (b c : ℝ) {w : evenSubspace} (hw : evenIndicatorCutoff c w = w) :
    evenSoninApertureLayer b c w = evenCentralSoninProjection b w := by
  unfold evenSoninApertureLayer
  rw [sub_apply,
    evenCentralSoninProjection_eq_zero_of_indicatorCutoff_eq_self c hw, sub_zero]

end RHTower

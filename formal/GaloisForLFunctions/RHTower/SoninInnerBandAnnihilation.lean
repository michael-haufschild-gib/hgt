import GaloisForLFunctions.RHTower.SoninApertureFourierParityNoGo
import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry

/-!
# Vectors inside either aperture window are annihilated by the Sonin projection

The Sonin projection at aperture `c` is orthogonal to both forbidden cutoffs, so it annihilates
every vector fixed by the physical cutoff and every vector fixed by the Fourier cutoff — exactly,
not asymptotically.  The two statements are duals of each other under the cosine Fourier
involution.

Physical-band vectors are the ones supported inside `[-c,c]`; Fourier-band vectors are the ones
band-limited to `[-c,c]`.  The second family lives in the Fourier tails, where the physical
geometry gives no information.
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

/-- A vector fixed by the Fourier cutoff at `c` is orthogonal to the Sonin carrier at `c`. -/
theorem inner_eq_zero_of_mem_evenCentralSoninCarrier_of_fourierCutoff_eq_self
    (c : ℝ) {w : evenSubspace} (hw : evenFourierCutoff c w = w)
    {g : evenSubspace} (hg : g ∈ evenCentralSoninCarrier c) :
    inner ℂ g w = 0 := by
  have hgc : evenFourierCutoff c g = 0 :=
    ((mem_evenCentralSoninCarrier_iff_cutoffs_zero c g).mp hg).2
  have hadj : ContinuousLinearMap.adjoint (evenFourierCutoff c) =
      evenFourierCutoff c := adjoint_evenFourierCutoff c
  calc
    inner ℂ g w = inner ℂ g (evenFourierCutoff c w) := by rw [hw]
    _ = inner ℂ g (ContinuousLinearMap.adjoint (evenFourierCutoff c) w) := by rw [hadj]
    _ = inner ℂ (evenFourierCutoff c g) w :=
        ContinuousLinearMap.adjoint_inner_right (evenFourierCutoff c) g w
    _ = 0 := by rw [hgc, inner_zero_left]

/-- **Exact physical-band annihilation.**  The Sonin projection at aperture `c` annihilates every
vector supported inside the central window. -/
theorem evenCentralSoninProjection_eq_zero_of_indicatorCutoff_eq_self
    (c : ℝ) {w : evenSubspace} (hw : evenIndicatorCutoff c w = w) :
    evenCentralSoninProjection c w = 0 := by
  calc
    evenCentralSoninProjection c w
        = evenCentralSoninProjection c (evenIndicatorCutoff c w) := by rw [hw]
    _ = (evenCentralSoninProjection c * evenIndicatorCutoff c) w := rfl
    _ = 0 := by rw [evenCentralSoninProjection_mul_evenIndicatorCutoff]; rfl

/-- **Exact Fourier-band annihilation.**  The Sonin projection at aperture `c` annihilates every
vector band-limited to the central window.  This is the dual of the physical statement and reaches
the vectors the physical geometry cannot see. -/
theorem evenCentralSoninProjection_eq_zero_of_fourierCutoff_eq_self
    (c : ℝ) {w : evenSubspace} (hw : evenFourierCutoff c w = w) :
    evenCentralSoninProjection c w = 0 := by
  calc
    evenCentralSoninProjection c w
        = evenCentralSoninProjection c (evenFourierCutoff c w) := by rw [hw]
    _ = (evenCentralSoninProjection c * evenFourierCutoff c) w := rfl
    _ = 0 := by rw [evenCentralSoninProjection_mul_evenFourierCutoff]; rfl

/-- On a physical-band vector the aperture layer sees only the outer aperture. -/
theorem evenSoninApertureLayer_eq_of_indicatorCutoff_eq_self
    (b c : ℝ) {w : evenSubspace} (hw : evenIndicatorCutoff c w = w) :
    evenSoninApertureLayer b c w = evenCentralSoninProjection b w := by
  unfold evenSoninApertureLayer
  rw [sub_apply,
    evenCentralSoninProjection_eq_zero_of_indicatorCutoff_eq_self c hw, sub_zero]

/-- On a Fourier-band vector the aperture layer sees only the outer aperture. -/
theorem evenSoninApertureLayer_eq_of_fourierCutoff_eq_self
    (b c : ℝ) {w : evenSubspace} (hw : evenFourierCutoff c w = w) :
    evenSoninApertureLayer b c w = evenCentralSoninProjection b w := by
  unfold evenSoninApertureLayer
  rw [sub_apply,
    evenCentralSoninProjection_eq_zero_of_fourierCutoff_eq_self c hw, sub_zero]

end RHTower

import GaloisForLFunctions.RHTower.SoninApertureRestrictionDefect
import GaloisForLFunctions.RHTower.TraceClassCompressionCurvature

/-!
# Negative trace law for Sonin aperture curvature

The principal aperture cocycle is flat, but literal path additivity leaves a Schatten-1
curvature.  Exact compressed functoriality identifies this curvature as compression minus the
identity on the earlier positive restriction defect.  General trace-class compression geometry
then turns its ordinary trace into minus a complementary Gram energy.  In particular its real
trace is always nonpositive.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- The aperture curvature is exactly compression-minus-identity of the first positive defect. -/
theorem evenSoninApertureRestrictionCurvature_eq_compression_sub_self
    {a b c r : ℝ} (hbc : b ≤ c) (hr : 1 < r) :
    evenSoninApertureRestrictionCurvature a b c r hr =
      evenCentralSoninProjection c *
          evenSoninApertureRestrictionDefect a b r hr *
            evenCentralSoninProjection c -
        evenSoninApertureRestrictionDefect a b r hr := by
  have h := evenSoninApertureRestrictionDefect_compressed_cocycle
    (a := a) hbc hr
  unfold evenSoninApertureRestrictionCurvature
  rw [h]
  abel

/-- Transition directly between two successive aperture layers.  This is the second fundamental
form of the nested Sonin carrier flag at the triple `a < b < c`. -/
def evenSoninApertureSuccessiveLayerTransition
    (a b c r : ℝ) (hr : 1 < r) : evenSubspace →L[ℂ] evenSubspace :=
  evenSoninApertureLayer a b * evenDilationSum r hr *
    evenSoninApertureLayer b c

/-- The successive-layer transition is exactly the part of the first lost transition removed by
the final carrier. -/
theorem evenSoninApertureSuccessiveLayerTransition_eq_boundary
    {a b c r : ℝ} (hbc : b ≤ c) (hr : 1 < r) :
    evenSoninApertureSuccessiveLayerTransition a b c r hr =
      evenSoninApertureLostTransition a b r hr *
        (1 - evenCentralSoninProjection c) := by
  rcases evenCentralSoninProjection_mul_of_le hbc with ⟨_, hbc'⟩
  unfold evenSoninApertureSuccessiveLayerTransition
  unfold evenSoninApertureLostTransition evenSoninApertureLayer
  have hright : evenCentralSoninProjection b *
      (1 - evenCentralSoninProjection c) =
        evenCentralSoninProjection b - evenCentralSoninProjection c := by
    rw [mul_sub, mul_one, hbc']
  rw [← hright]
  simp only [mul_assoc]

/-- Trace-class aperture curvature forces the successive-layer transition itself to be
Hilbert--Schmidt. -/
theorem evenSoninApertureSuccessiveLayerTransition_isHilbertSchmidt
    {a b c r : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hr : 1 < r) (hcr : c < r * a) :
    (evenSoninApertureSuccessiveLayerTransition a b c r hr).IsHilbertSchmidt := by
  let P := evenCentralSoninProjection c
  let T := evenSoninApertureRestrictionDefect a b r hr
  let Y := evenSoninApertureLostTransition a b r hr
  let Z := Y * (1 - P)
  have hP : P * P = P := by
    dsimp only [P]
    rw [evenCentralSoninProjection_eq_starProjection]
    exact (evenCentralSoninCarrier c).isIdempotentElem_starProjection
  have hPadj : ContinuousLinearMap.adjoint P = P := by
    simpa only [P] using adjoint_evenCentralSoninProjection c
  have hT : T = ContinuousLinearMap.adjoint Y * Y := by
    simpa only [T, Y, evenSoninApertureRestrictionDefect] using
      evenCentralSoninQuadraticCorner_restrictionDefect_eq_adjoint_mul hab.le hr
  have hcurv : evenSoninApertureRestrictionCurvature a b c r hr = P * T * P - T := by
    simpa only [P, T] using
      evenSoninApertureRestrictionCurvature_eq_compression_sub_self hbc.le hr
  have hK : MemSchattenClass 1 (P * T * P - T) := by
    rw [← hcurv]
    exact evenSoninApertureRestrictionCurvature_memSchattenClass_one
      ha hab hbc hr hcr
  have hB : MemSchattenClass 1 ((1 - P) * T * (1 - P)) :=
    complement_compression_memSchattenClass_one P T hP hK
  have hBgram : (1 - P) * T * (1 - P) =
      ContinuousLinearMap.adjoint Z * Z := by
    dsimp only [Z]
    rw [hT]
    change (1 - P) * (ContinuousLinearMap.adjoint Y * Y) * (1 - P) =
      ContinuousLinearMap.adjoint (Y ∘L (1 - P)) ∘L (Y ∘L (1 - P))
    rw [ContinuousLinearMap.adjoint_comp]
    change (1 - P) * (ContinuousLinearMap.adjoint Y * Y) * (1 - P) =
      ContinuousLinearMap.adjoint (1 - P) * ContinuousLinearMap.adjoint Y *
        (Y * (1 - P))
    rw [ContinuousLinearMap.adjoint.map_sub,
      ContinuousLinearMap.adjoint_one, hPadj]
    simp only [mul_assoc]
  have hZtc : MemSchattenClass 1 (ContinuousLinearMap.adjoint Z * Z) := by
    rw [← hBgram]
    exact hB
  have hZhs := isHilbertSchmidt_of_adjoint_mul_self_memSchattenClass_one Z hZtc
  rw [evenSoninApertureSuccessiveLayerTransition_eq_boundary hbc.le hr]
  simpa only [P, Y, Z] using hZhs

/-- **Exact scalar aperture-curvature law.** Its ordinary trace is minus the complementary
diagonal energy of the earlier positive restriction defect. -/
theorem opTrace_evenSoninApertureRestrictionCurvature_eq_neg_complement
    {a b c r : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hr : 1 < r) (hcr : c < r * a) :
    opTrace (evenSoninApertureRestrictionCurvature a b c r hr) =
      -opTrace
        ((1 - evenCentralSoninProjection c) *
          evenSoninApertureRestrictionDefect a b r hr *
            (1 - evenCentralSoninProjection c)) := by
  let P := evenCentralSoninProjection c
  let T := evenSoninApertureRestrictionDefect a b r hr
  have hP : P * P = P := by
    dsimp only [P]
    rw [evenCentralSoninProjection_eq_starProjection]
    exact (evenCentralSoninCarrier c).isIdempotentElem_starProjection
  have hcurv : evenSoninApertureRestrictionCurvature a b c r hr = P * T * P - T := by
    simpa only [P, T] using
      evenSoninApertureRestrictionCurvature_eq_compression_sub_self hbc.le hr
  have hK : MemSchattenClass 1 (P * T * P - T) := by
    rw [← hcurv]
    exact evenSoninApertureRestrictionCurvature_memSchattenClass_one
      ha hab hbc hr hcr
  rw [hcurv]
  simpa only [P, T] using
    opTrace_compression_sub_self_eq_neg_complement P T hP hK

/-- **Exact Sonin aperture-curvature energy law.**  The complete scalar curvature left after
principal mass conservation is minus the squared Hilbert--Schmidt norm of the coupling between
successive lost aperture layers. -/
theorem re_opTrace_evenSoninApertureRestrictionCurvature_eq_neg_hsNormSq
    {a b c r : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hr : 1 < r) (hcr : c < r * a) :
    (opTrace (evenSoninApertureRestrictionCurvature a b c r hr)).re =
      -hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c r hr) := by
  let P := evenCentralSoninProjection c
  let T := evenSoninApertureRestrictionDefect a b r hr
  let Y := evenSoninApertureLostTransition a b r hr
  have hP : P * P = P := by
    dsimp only [P]
    rw [evenCentralSoninProjection_eq_starProjection]
    exact (evenCentralSoninCarrier c).isIdempotentElem_starProjection
  have hPadj : ContinuousLinearMap.adjoint P = P := by
    simpa only [P] using adjoint_evenCentralSoninProjection c
  have hT : T = ContinuousLinearMap.adjoint Y * Y := by
    simpa only [T, Y, evenSoninApertureRestrictionDefect] using
      evenCentralSoninQuadraticCorner_restrictionDefect_eq_adjoint_mul hab.le hr
  have hcurv : evenSoninApertureRestrictionCurvature a b c r hr = P * T * P - T := by
    simpa only [P, T] using
      evenSoninApertureRestrictionCurvature_eq_compression_sub_self hbc.le hr
  have hK : MemSchattenClass 1 (P * T * P - T) := by
    rw [← hcurv]
    exact evenSoninApertureRestrictionCurvature_memSchattenClass_one
      ha hab hbc hr hcr
  rw [hcurv, evenSoninApertureSuccessiveLayerTransition_eq_boundary hbc.le hr]
  simpa only [P, T, Y] using
    re_opTrace_compression_sub_self_eq_neg_hsNormSq P T Y hP hPadj hT hK

/-- Vanishing aperture curvature is equivalent to absence of the coupling between the two
successive lost layers. -/
theorem evenSoninApertureRestrictionCurvature_eq_zero_iff_successiveLayerTransition_eq_zero
    {a b c r : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hr : 1 < r) (hcr : c < r * a) :
    evenSoninApertureRestrictionCurvature a b c r hr = 0 ↔
      evenSoninApertureSuccessiveLayerTransition a b c r hr = 0 := by
  let P := evenCentralSoninProjection c
  let T := evenSoninApertureRestrictionDefect a b r hr
  let Y := evenSoninApertureLostTransition a b r hr
  have hP : P * P = P := by
    dsimp only [P]
    rw [evenCentralSoninProjection_eq_starProjection]
    exact (evenCentralSoninCarrier c).isIdempotentElem_starProjection
  have hPadj : ContinuousLinearMap.adjoint P = P := by
    simpa only [P] using adjoint_evenCentralSoninProjection c
  have hT : T = ContinuousLinearMap.adjoint Y * Y := by
    simpa only [T, Y, evenSoninApertureRestrictionDefect] using
      evenCentralSoninQuadraticCorner_restrictionDefect_eq_adjoint_mul hab.le hr
  have hcurv : evenSoninApertureRestrictionCurvature a b c r hr = P * T * P - T := by
    simpa only [P, T] using
      evenSoninApertureRestrictionCurvature_eq_compression_sub_self hbc.le hr
  have hK : MemSchattenClass 1 (P * T * P - T) := by
    rw [← hcurv]
    exact evenSoninApertureRestrictionCurvature_memSchattenClass_one
      ha hab hbc hr hcr
  rw [hcurv, evenSoninApertureSuccessiveLayerTransition_eq_boundary hbc.le hr]
  simpa only [P, T, Y] using
    compression_sub_self_eq_zero_iff_boundary_zero P T Y hP hPadj hT hK

/-- **Scalar faithfulness.**  On the Sonin aperture cocycle the real ordinary trace detects the
entire curvature operator: zero scalar curvature is equivalent to literal functoriality. -/
theorem re_opTrace_evenSoninApertureRestrictionCurvature_eq_zero_iff
    {a b c r : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hr : 1 < r) (hcr : c < r * a) :
    (opTrace (evenSoninApertureRestrictionCurvature a b c r hr)).re = 0 ↔
      evenSoninApertureRestrictionCurvature a b c r hr = 0 := by
  let Z := evenSoninApertureSuccessiveLayerTransition a b c r hr
  have hZhs : Z.IsHilbertSchmidt := by
    simpa only [Z] using
      evenSoninApertureSuccessiveLayerTransition_isHilbertSchmidt
        ha hab hbc hr hcr
  have henergy :=
    re_opTrace_evenSoninApertureRestrictionCurvature_eq_neg_hsNormSq
      ha hab hbc hr hcr
  have hrigid :=
    evenSoninApertureRestrictionCurvature_eq_zero_iff_successiveLayerTransition_eq_zero
      ha hab hbc hr hcr
  constructor
  · intro hzero
    have hnorm : hsNormSq Z = 0 := by
      rw [hzero] at henergy
      dsimp only [Z]
      linarith
    exact hrigid.mpr ((hsNormSq_eq_zero_iff hZhs).mp hnorm)
  · intro hzero
    rw [hzero, opTrace_zero]
    rfl

/-- **Negative aperture-curvature law.** The complete scalar curvature left after principal mass
conservation is never positive: it is minus a trace-class Gram energy. -/
theorem re_opTrace_evenSoninApertureRestrictionCurvature_nonpos
    {a b c r : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hr : 1 < r) (hcr : c < r * a) :
    (opTrace (evenSoninApertureRestrictionCurvature a b c r hr)).re ≤ 0 := by
  rw [re_opTrace_evenSoninApertureRestrictionCurvature_eq_neg_hsNormSq
    ha hab hbc hr hcr]
  exact neg_nonpos.mpr (hsNormSq_nonneg _)

end RHTower

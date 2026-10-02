import GaloisForLFunctions.RHTower.SoninShellProductIdeal
import GaloisForLFunctions.RHTower.SoninAperturePacketCurvatureTrace

/-!
# Mixed-scale Sonin aperture curvature

The mixed quadratic corner restricts through a Gram product of two lost-layer transitions.
Its aperture curvature is compression minus the original Gram product. In a common crossing
chamber, both boundary transitions lie in the concrete Sonin relative ideal, so the whole
mixed curvature retains that provenance. Its complex trace is exactly the negative
Hilbert--Schmidt Gram pairing of the successive-layer transitions.

This retains the off-diagonal prime-scale terms as well as their phases. It does not identify
an archimedean completion or the cubic Hardy index.
-/

noncomputable section
namespace RHTower
open ContinuousLinearMap

/-- The concrete Sonin relative ideal is closed under adjoints. -/
theorem IsSoninPrincipalRelativeIdeal.adjoint
    {T : evenSubspace →L[ℂ] evenSubspace} (hT : IsSoninPrincipalRelativeIdeal T) :
    IsSoninPrincipalRelativeIdeal (ContinuousLinearMap.adjoint T) := by
  induction hT with
  | zero => simpa using IsSoninPrincipalRelativeIdeal.zero
  | projectionCorrection a ha =>
      have h := IsSoninPrincipalRelativeIdeal.projectionCorrection a ha
      simpa only [evenSoninProjectionCorrection, ContinuousLinearMap.adjoint.map_sub, adjoint_one,
        adjoint_evenCentralSoninProjection, adjoint_evenIndicatorCutoff,
        adjoint_evenFourierCutoff] using h
  | indicatorFourier s t hs =>
      rw [ContinuousLinearMap.mul_def, adjoint_comp,
        adjoint_evenFourierCutoff, adjoint_evenIndicatorCutoff]
      change IsSoninPrincipalRelativeIdeal (evenFourierCutoff t * evenIndicatorCutoff s)
      have h := (IsSoninPrincipalRelativeIdeal.fourierIndicator (max t 1) s
        (lt_of_lt_of_le zero_lt_one (le_max_right t 1))).leftMul (evenFourierCutoff t)
      simpa only [← mul_assoc, evenFourierCutoff_mul_of_le t (max t 1)
        (le_max_left t 1)] using h
  | fourierIndicator s t hs =>
      rw [ContinuousLinearMap.mul_def, adjoint_comp,
        adjoint_evenIndicatorCutoff, adjoint_evenFourierCutoff]
      change IsSoninPrincipalRelativeIdeal (evenIndicatorCutoff t * evenFourierCutoff s)
      have h := (IsSoninPrincipalRelativeIdeal.indicatorFourier (max t 1) s
        (lt_of_lt_of_le zero_lt_one (le_max_right t 1))).leftMul (evenIndicatorCutoff t)
      simpa only [← mul_assoc, evenIndicatorCutoff_mul_of_le t (max t 1)
        (le_max_left t 1)] using h
  | add hS hT ihS ihT => simpa only [map_add] using ihS.add ihT
  | @neg T hT ih =>
      rw [show -T = 0 - T by abel, adjoint_sub_clm]
      simpa only [ContinuousLinearMap.adjoint.map_zero, zero_sub] using ih.neg
  | leftMul L hT ih =>
      rw [ContinuousLinearMap.mul_def, adjoint_comp]
      exact ih.rightMul (ContinuousLinearMap.adjoint L)
  | rightMul hT R ih =>
      rw [ContinuousLinearMap.mul_def, adjoint_comp]
      exact ih.leftMul (ContinuousLinearMap.adjoint R)

/-- Actual mixed restriction defect of two Sonin dilation scales. -/
def evenSoninMixedApertureRestrictionDefect
    (a b p q : ℝ) (hp : 1 < p) (hq : 1 < q) : evenSubspace →L[ℂ] evenSubspace :=
  evenCentralSoninQuadraticCorner b p q hp hq -
    evenCentralSoninProjection b * evenCentralSoninQuadraticCorner a p q hp hq *
      evenCentralSoninProjection b

/-- Mixed curvature of the actual aperture restriction. -/
def evenSoninMixedApertureRestrictionCurvature
    (a b c p q : ℝ) (hp : 1 < p) (hq : 1 < q) : evenSubspace →L[ℂ] evenSubspace :=
  evenSoninMixedApertureRestrictionDefect a c p q hp hq -
    evenSoninMixedApertureRestrictionDefect a b p q hp hq -
      evenSoninMixedApertureRestrictionDefect b c p q hp hq

theorem evenSoninMixedApertureRestrictionDefect_eq_adjoint_mul
    {a b p q : ℝ} (hab : a ≤ b) (hp : 1 < p) (hq : 1 < q) :
    evenSoninMixedApertureRestrictionDefect a b p q hp hq =
      adjoint (evenSoninApertureLostTransition a b p hp) *
        evenSoninApertureLostTransition a b q hq := by
  rw [evenSoninMixedApertureRestrictionDefect,
    evenCentralSoninQuadraticCorner_restrictionDefect hab hp hq]
  have hadj : adjoint (evenSoninApertureLostTransition a b p hp) =
      evenCentralSoninProjection b * evenDilationSum p hp * evenSoninApertureLayer a b := by
    unfold evenSoninApertureLostTransition
    simp only [ContinuousLinearMap.mul_def, adjoint_comp,
      adjoint_evenCentralSoninProjection, adjoint_evenDilationSum,
      adjoint_evenSoninApertureLayer]
    rfl
  rw [hadj, evenSoninApertureLostTransition]
  calc
    _ = evenCentralSoninProjection b * evenDilationSum p hp *
        (evenSoninApertureLayer a b * evenSoninApertureLayer a b) *
          evenDilationSum q hq * evenCentralSoninProjection b := by
      rw [evenSoninApertureLayer_mul_self hab]
    _ = _ := by simp only [mul_assoc]

theorem evenSoninMixedApertureRestrictionDefect_compressed_cocycle
    {a b c p q : ℝ} (hbc : b ≤ c) (hp : 1 < p) (hq : 1 < q) :
    evenSoninMixedApertureRestrictionDefect a c p q hp hq =
      evenSoninMixedApertureRestrictionDefect b c p q hp hq +
        evenCentralSoninProjection c *
          evenSoninMixedApertureRestrictionDefect a b p q hp hq *
            evenCentralSoninProjection c := by
  rcases evenCentralSoninProjection_mul_of_le hbc with ⟨hcb, hbc'⟩
  have hcollapse : evenCentralSoninProjection c *
      (evenCentralSoninProjection b *
        evenCentralSoninQuadraticCorner a p q hp hq * evenCentralSoninProjection b) *
      evenCentralSoninProjection c =
      evenCentralSoninProjection c * evenCentralSoninQuadraticCorner a p q hp hq *
        evenCentralSoninProjection c := by
    calc
      _ = (evenCentralSoninProjection c * evenCentralSoninProjection b) *
          evenCentralSoninQuadraticCorner a p q hp hq *
          (evenCentralSoninProjection b * evenCentralSoninProjection c) := by
            simp only [mul_assoc]
      _ = _ := by rw [hcb, hbc']
  unfold evenSoninMixedApertureRestrictionDefect
  rw [mul_sub, sub_mul, hcollapse]
  abel

theorem evenSoninMixedApertureRestrictionCurvature_eq_compression_sub_self
    {a b c p q : ℝ} (hbc : b ≤ c) (hp : 1 < p) (hq : 1 < q) :
    evenSoninMixedApertureRestrictionCurvature a b c p q hp hq =
      evenCentralSoninProjection c *
        evenSoninMixedApertureRestrictionDefect a b p q hp hq *
          evenCentralSoninProjection c -
        evenSoninMixedApertureRestrictionDefect a b p q hp hq := by
  unfold evenSoninMixedApertureRestrictionCurvature
  rw [evenSoninMixedApertureRestrictionDefect_compressed_cocycle hbc hp hq]
  abel

private theorem mixed_gram_compression_boundary
    (P A B : evenSubspace →L[ℂ] evenSubspace) (hP : adjoint P = P) :
    P * (adjoint A * B) * P - adjoint A * B =
      -(adjoint (A * (1 - P)) * B) - P * adjoint A * (B * (1 - P)) := by
  simp only [adjoint_mul_clm, adjoint_sub_clm, hP,
    sub_mul, mul_sub, mul_one, mul_assoc]
  abel

/-- Both mixed curvature blocks factor through concrete successive-layer transitions. -/
theorem evenSoninMixedApertureRestrictionCurvature_eq_boundary
    {a b c p q : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hp : 1 < p) (hq : 1 < q) :
    evenSoninMixedApertureRestrictionCurvature a b c p q hp hq =
      -(adjoint (evenSoninApertureSuccessiveLayerTransition a b c p hp) *
          evenSoninApertureLostTransition a b q hq) -
        evenCentralSoninProjection c * adjoint (evenSoninApertureLostTransition a b p hp) *
          evenSoninApertureSuccessiveLayerTransition a b c q hq := by
  simp only [evenSoninMixedApertureRestrictionCurvature_eq_compression_sub_self hbc hp hq,
    evenSoninMixedApertureRestrictionDefect_eq_adjoint_mul hab hp hq,
    evenSoninApertureSuccessiveLayerTransition_eq_boundary hbc hp,
    evenSoninApertureSuccessiveLayerTransition_eq_boundary hbc hq]
  exact mixed_gram_compression_boundary (evenCentralSoninProjection c)
    (evenSoninApertureLostTransition a b p hp) (evenSoninApertureLostTransition a b q hq)
    (adjoint_evenCentralSoninProjection c)

/-- Every mixed curvature entry retains its concrete relative-ideal provenance. -/
theorem evenSoninMixedApertureRestrictionCurvature_mem_principalRelativeIdeal
    {a b c p q : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hp : 1 < p) (hq : 1 < q) (hcp : c ≤ p * a) (hcq : c ≤ q * a) :
    IsSoninPrincipalRelativeIdeal
      (evenSoninMixedApertureRestrictionCurvature a b c p q hp hq) := by
  have hb := ha.trans_le hab
  have hc := hb.trans_le hbc
  have hZp := evenSoninApertureSuccessiveLayerTransition_mem_principalRelativeIdeal
    ha hb hc hab hbc hp hcp
  have hZq := evenSoninApertureSuccessiveLayerTransition_mem_principalRelativeIdeal
    ha hb hc hab hbc hq hcq
  rw [evenSoninMixedApertureRestrictionCurvature_eq_boundary hab hbc hp hq]
  exact (hZp.adjoint.rightMul _).neg.sub (hZq.leftMul _)

private theorem trace_mixed_gram_compression
    (P A B : evenSubspace →L[ℂ] evenSubspace) (hP : P * P = P) (hPa : adjoint P = P)
    (hK : MemSchattenClass 1 (P * (adjoint A * B) * P - adjoint A * B)) :
    opTrace (P * (adjoint A * B) * P - adjoint A * B) =
      -hsInner (A * (1 - P)) (B * (1 - P)) := by
  rw [opTrace_compression_sub_self_eq_neg_complement P (adjoint A * B) hP hK]
  have hgram : (1 - P) * (adjoint A * B) * (1 - P) =
      adjoint (A * (1 - P)) * (B * (1 - P)) := by
    simp only [adjoint_mul_clm, adjoint_sub_clm, adjoint_one, hPa]
    simp only [mul_assoc]
  rw [hgram, ContinuousLinearMap.mul_def, opTrace_comp_eq_hsInner, adjoint_adjoint]

/-- Mixed aperture-curvature trace is exactly the negative Hilbert--Schmidt Gram kernel. -/
theorem opTrace_evenSoninMixedApertureRestrictionCurvature
    {a b c p q : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hp : 1 < p) (hq : 1 < q) (hcp : c ≤ p * a) (hcq : c ≤ q * a) :
    opTrace (evenSoninMixedApertureRestrictionCurvature a b c p q hp hq) =
      -hsInner (evenSoninApertureSuccessiveLayerTransition a b c p hp)
        (evenSoninApertureSuccessiveLayerTransition a b c q hq) := by
  have hK := (evenSoninMixedApertureRestrictionCurvature_mem_principalRelativeIdeal
    ha hab hbc hp hq hcp hcq).memSchattenClass_one
  simp only [evenSoninMixedApertureRestrictionCurvature_eq_compression_sub_self hbc hp hq,
    evenSoninMixedApertureRestrictionDefect_eq_adjoint_mul hab hp hq] at hK ⊢
  simp only [evenSoninApertureSuccessiveLayerTransition_eq_boundary hbc hp,
    evenSoninApertureSuccessiveLayerTransition_eq_boundary hbc hq]
  exact trace_mixed_gram_compression (evenCentralSoninProjection c)
    (evenSoninApertureLostTransition a b p hp) (evenSoninApertureLostTransition a b q hq)
    (evenCentralSoninProjection_mul_of_le (a := c) (b := c) le_rfl).1
    (adjoint_evenCentralSoninProjection c) hK

end RHTower

end

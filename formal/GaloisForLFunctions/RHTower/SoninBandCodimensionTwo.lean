import GaloisForLFunctions.HTGeometry.CodimensionTwoOrthogonalSum
import GaloisForLFunctions.RHTower.SoninExtendedOrthogonalBand
import GaloisForLFunctions.RHTower.SoninCarrierApertureChain

/-!
# The Sonine carrier has codimension two in the extended Sonine space

Burnol, arXiv:math/0203120, Prop. 4.5: `dim(L_a / K_a) = 2`.

His second proof identifies `K_a` as the perpendicular of `L²(0,a) + F₊(L²(0,a))` and `L_a` as the
perpendicular of the two-dimensionally smaller space `(L²(0,a) ∩ 1⊥) + F₊(L²(0,a) ∩ 1⊥)`.  The
perpendicular of a subspace inside a bigger one is literally the same set as the perpendicular of
the bigger one's perpendicular inside the smaller one's perpendicular, so the codimension-two law of
`CodimensionTwoOrthogonalSum` applies directly.

## Main results

* `norm_bandIndicator`, `bandIndicator_ne_zero`
* `orthogonal_centralSoninCarrier`
* `finrank_soninBandComplement_eq_two` — **Prop. 4.5** in the full-line model.
-/

noncomputable section

open MeasureTheory Set Complex
open scoped InnerProductSpace ENNReal

namespace RHTower

open GaloisForLFunctions.HTGeometry

theorem bandIndicator_ne_zero {a : ℝ} (ha : 0 < a) : bandIndicator a ≠ 0 := by
  intro h
  have hae : ((bandIndicator a : SoninL2) : ℝ → ℂ) =ᵐ[volume] 0 := by
    rw [h]
    exact Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))
  have hnot : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ centralInterval a := by
    filter_upwards [bandIndicator_coeFn a, hae] with x h1 h2 hmem
    rw [h1, Set.indicator_of_mem hmem] at h2
    exact one_ne_zero h2
  have hnull : (volume : Measure ℝ) (centralInterval a) = 0 := compl_mem_ae_iff.1 hnot
  rw [centralInterval, Real.volume_Icc] at hnull
  have hpos : (0 : ℝ) < a - -a := by linarith
  rw [ENNReal.ofReal_eq_zero] at hnull
  linarith

theorem bandIndicator_mem_centralPhysicalForbidden (a : ℝ) :
    bandIndicator a ∈ centralPhysicalForbidden a :=
  bandIndicator_mem_physicalForbidden a

/-- The Fourier partner of the band indicator. -/
def fourierBandIndicator (a : ℝ) : SoninL2 := fourierUnitary.symm (bandIndicator a)

theorem fourierBandIndicator_ne_zero {a : ℝ} (ha : 0 < a) : fourierBandIndicator a ≠ 0 := by
  intro h
  apply bandIndicator_ne_zero ha
  have := congrArg (fun x => fourierUnitary x) h
  simpa [fourierBandIndicator] using this

theorem fourierBandIndicator_mem (a : ℝ) :
    fourierBandIndicator a ∈ centralFourierForbidden a := by
  have hval : fourierUnitary (fourierBandIndicator a) = bandIndicator a := by
    rw [fourierBandIndicator, LinearIsometryEquiv.apply_symm_apply]
  have h : fourierUnitary (fourierBandIndicator a) ∈
      physicalForbidden (centralInterval a) (measurableSet_centralInterval a) := by
    rw [hval]
    exact bandIndicator_mem_physicalForbidden a
  exact (mem_fourierForbidden_iff (centralInterval a) (measurableSet_centralInterval a) _).2 h

/-- The orthogonal complement of the Sonine carrier is the sum of the two bands. -/
theorem orthogonal_centralSoninCarrier {a : ℝ} (ha : 0 < a) :
    (centralSoninCarrier a)ᗮ = centralPhysicalForbidden a ⊔ centralFourierForbidden a := by
  rw [centralSoninCarrier_eq_orthogonal_sup]
  haveI : CompleteSpace
      ((centralPhysicalForbidden a ⊔ centralFourierForbidden a : Submodule ℂ SoninL2)) :=
    (isClosed_centralPhysicalForbidden_sup_centralFourierForbidden a ha).completeSpace_coe
  haveI : (centralPhysicalForbidden a ⊔ centralFourierForbidden a :
      Submodule ℂ SoninL2).HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace _
  exact Submodule.orthogonal_orthogonal _

/-- **Burnol's Proposition 4.5** in the full-line model: removing the band constant from each of the
two bands drops the sum by exactly two dimensions, so the Sonine carrier has codimension two in the
extended Sonine space. -/
theorem finrank_soninBandComplement_eq_two {a : ℝ} (ha : 0 < a) :
    Module.finrank ℂ
      (((centralPhysicalForbidden a ⊔ centralFourierForbidden a) ⊓
        ((centralPhysicalForbidden a ⊓ (ℂ ∙ bandIndicator a)ᗮ) ⊔
          (centralFourierForbidden a ⊓ (ℂ ∙ fourierBandIndicator a)ᗮ))ᗮ :
            Submodule ℂ SoninL2)) = 2 := by
  refine finrank_inf_orthogonal_sub_sup_eq_two
    (physicalForbidden_inf_fourierForbidden_eq_bot a)
    (isClosed_of_hasOrthogonalProjection _) (isClosed_of_hasOrthogonalProjection _)
    (isClosed_centralPhysicalForbidden_sup_centralFourierForbidden a ha)
    (bandIndicator_mem_centralPhysicalForbidden a) (bandIndicator_ne_zero ha)
    (fourierBandIndicator_mem a) (fourierBandIndicator_ne_zero ha)

end RHTower

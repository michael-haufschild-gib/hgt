import GaloisForLFunctions.HTGeometry.HorizontalLayerLeakageLimit
import GaloisForLFunctions.HTGeometry.HardyPaleyWienerTransport
import GaloisForLFunctions.HTGeometry.FiniteExponentialHankel

open Complex Filter Topology
open scoped BigOperators InnerProductSpace

noncomputable section


namespace GaloisForLFunctions.HTGeometry

def paleyWienerOperatorTransport
    (T : UpperHardyL2 →L[ℂ] LowerHardyL2) :
    HalfLineExponentialL2 →L[ℂ] HalfLineExponentialL2 :=
  lowerHardyPaleyWienerUnitary.symm.toLinearIsometry.toContinuousLinearMap.comp
    (T.comp upperHardyPaleyWienerUnitary.toLinearIsometry.toContinuousLinearMap)

def paleyWienerOperatorTransportLinear :
    (UpperHardyL2 →L[ℂ] LowerHardyL2) →ₗ[ℂ]
      (HalfLineExponentialL2 →L[ℂ] HalfLineExponentialL2) where
  toFun := paleyWienerOperatorTransport
  map_add' S T := by
    ext f
    simp [paleyWienerOperatorTransport]
  map_smul' c T := by
    ext f
    simp [paleyWienerOperatorTransport]

theorem norm_paleyWienerOperatorTransport_le
    (T : UpperHardyL2 →L[ℂ] LowerHardyL2) :
    ‖paleyWienerOperatorTransport T‖ ≤ ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound
    (paleyWienerOperatorTransport T) (norm_nonneg T) ?_
  intro f
  calc
    ‖paleyWienerOperatorTransport T f‖ =
        ‖T (upperHardyPaleyWienerUnitary f)‖ := by
          change ‖lowerHardyPaleyWienerUnitary.symm
              (T (upperHardyPaleyWienerUnitary f))‖ = _
          rw [lowerHardyPaleyWienerUnitary.symm.norm_map]
    _ ≤ ‖T‖ * ‖upperHardyPaleyWienerUnitary f‖ := T.le_opNorm _
    _ = ‖T‖ * ‖f‖ := by rw [upperHardyPaleyWienerUnitary.norm_map]

def paleyWienerOperatorTransportCLM :
    (UpperHardyL2 →L[ℂ] LowerHardyL2) →L[ℂ]
      (HalfLineExponentialL2 →L[ℂ] HalfLineExponentialL2) :=
  LinearMap.mkContinuous paleyWienerOperatorTransportLinear 1 (fun
      (T : UpperHardyL2 →L[ℂ] LowerHardyL2) => by
    change ‖paleyWienerOperatorTransportLinear T‖ ≤ 1 * ‖T‖
    change ‖paleyWienerOperatorTransport T‖ ≤ 1 * ‖T‖
    simpa using norm_paleyWienerOperatorTransport_le T)

@[simp]
theorem paleyWienerOperatorTransportCLM_apply
    (T : UpperHardyL2 →L[ℂ] LowerHardyL2) :
    paleyWienerOperatorTransportCLM T = paleyWienerOperatorTransport T := rfl

theorem paleyWienerOperatorTransport_rankOne {a : ℝ} (ha : 0 < a) :
    paleyWienerOperatorTransport
        ((-(Real.pi : ℂ)⁻¹) •
          InnerProductSpace.rankOne ℂ (upperCauchyFeature a ha)
            (lowerCauchyFeature a ha)) =
      (2 : ℂ) • InnerProductSpace.rankOne ℂ (expFeature a ha)
        (expFeature a ha) := by
  apply ContinuousLinearMap.ext
  intro f
  apply lowerHardyPaleyWienerUnitary.injective
  change lowerHardyPaleyWienerUnitary
      (lowerHardyPaleyWienerUnitary.symm
        (((-(Real.pi : ℂ)⁻¹) •
          InnerProductSpace.rankOne ℂ (upperCauchyFeature a ha)
            (lowerCauchyFeature a ha))
          (upperHardyPaleyWienerUnitary f))) =
    lowerHardyPaleyWienerUnitary
      (((2 : ℂ) • InnerProductSpace.rankOne ℂ (expFeature a ha)
        (expFeature a ha)) f)
  rw [lowerHardyPaleyWienerUnitary.apply_symm_apply]
  exact paleyWiener_rankOne_intertwining ha f

theorem paleyWienerOperatorTransport_sum {ι : Type*} (s : Finset ι)
    (T : ι → (UpperHardyL2 →L[ℂ] LowerHardyL2)) :
    paleyWienerOperatorTransport (s.sum T) =
      s.sum fun i => paleyWienerOperatorTransport (T i) := by
  classical
  change paleyWienerOperatorTransportCLM (s.sum T) =
    s.sum fun i => paleyWienerOperatorTransportCLM (T i)
  exact map_sum paleyWienerOperatorTransportCLM T s

abbrev HorizontalLayerCopy {r : ℕ} (m : Fin r → ℕ) :=
  Σ j : Fin r, Fin (m j)

def horizontalLayerCopyRate {r : ℕ} (a : Fin r → ℝ) {m : Fin r → ℕ}
    (i : HorizontalLayerCopy m) : ℝ := a i.1

theorem finiteHorizontalLayerProjective_copies {r : ℕ} (a : Fin r → ℝ)
    (m : Fin r → ℕ) (ω : ℝ) :
    finiteHorizontalLayerProjective
        (Finset.univ : Finset (HorizontalLayerCopy m))
        (horizontalLayerCopyRate a) ω =
      ∏ j, horizontalLayerProjective (a j) ω ^ m j := by
  classical
  unfold finiteHorizontalLayerProjective horizontalLayerCopyRate
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro j hj
  change (∏ _ : Fin (m j), horizontalLayerProjective (a j) ω) =
    horizontalLayerProjective (a j) ω ^ m j
  simp

theorem sum_horizontalLayerCopies_rankOne_eq_finiteExponentialHankel
    {r : ℕ} (a : Fin r → ℝ) (ha : ∀ j, 0 < a j) (m : Fin r → ℕ) :
    ∑ i : HorizontalLayerCopy m,
        (2 : ℂ) • InnerProductSpace.rankOne ℂ
          (expFeature (a i.1) (ha i.1)) (expFeature (a i.1) (ha i.1)) =
      finiteExponentialHankel a ha m := by
  classical
  rw [Fintype.sum_sigma]
  unfold finiteExponentialHankel finiteRankProbe
  apply Finset.sum_congr rfl
  intro j hj
  change (∑ _ : Fin (m j),
      (2 : ℂ) • InnerProductSpace.rankOne ℂ
        (expFeature (a j) (ha j)) (expFeature (a j) (ha j))) =
    ((2 * m j : ℕ) : ℂ) • InnerProductSpace.rankOne ℂ
      (expFeature (a j) (ha j)) (expFeature (a j) (ha j))
  rw [Finset.sum_const, Finset.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  simp only [smul_smul]
  congr 1
  push_cast
  ring

def horizontalLayerPowerProduct {r : ℕ} (a : Fin r → ℝ) (m : Fin r → ℕ)
    (ω : ℝ) : ProjectiveBoundary :=
  ∏ j, horizontalLayerProjective (a j) ω ^ m j

def horizontalLayerPowerNormalizedProjective {r : ℕ} (a : Fin r → ℝ)
    (m : Fin r → ℕ) (ω : ℝ) : ProjectiveBoundary :=
  ((ω : ℂ)⁻¹) • (horizontalLayerPowerProduct a m ω - 1)

theorem finiteHorizontalLayerNormalizedProjective_copies {r : ℕ}
    (a : Fin r → ℝ) (m : Fin r → ℕ) (ω : ℝ) :
    finiteHorizontalLayerNormalizedProjective
        (Finset.univ : Finset (HorizontalLayerCopy m))
        (horizontalLayerCopyRate a) ω =
      horizontalLayerPowerNormalizedProjective a m ω := by
  rw [finiteHorizontalLayerNormalizedProjective,
    horizontalLayerPowerNormalizedProjective, horizontalLayerPowerProduct,
    finiteHorizontalLayerProjective_copies]

def horizontalLayerPaleyWienerNormalized {r : ℕ} (a : Fin r → ℝ)
    (m : Fin r → ℕ) (ω : ℝ) :
    HalfLineExponentialL2 →L[ℂ] HalfLineExponentialL2 :=
  paleyWienerOperatorTransport
    (hardyLeakage (projectiveBoundaryMul
      (horizontalLayerPowerNormalizedProjective a m ω)))

theorem paleyWienerOperatorTransport_finiteHorizontalLayerInfinitesimal
    {r : ℕ} (a : Fin r → ℝ) (ha : ∀ j, 0 < a j) (m : Fin r → ℕ) :
    paleyWienerOperatorTransport
        (hardyLeakage (projectiveBoundaryMul
          (finiteHorizontalLayerInfinitesimalProjective
            (Finset.univ : Finset (HorizontalLayerCopy m))
            (horizontalLayerCopyRate a)))) =
      finiteExponentialHankel a ha m := by
  rw [hardyLeakage_finiteHorizontalLayerInfinitesimalProjective
    (Finset.univ : Finset (HorizontalLayerCopy m))
    (horizontalLayerCopyRate a) (fun i => ha i.1)]
  calc
    paleyWienerOperatorTransport
        (∑ i : HorizontalLayerCopy m,
          (-(Real.pi : ℂ)⁻¹) •
            InnerProductSpace.rankOne ℂ
              (upperCauchyFeature (a i.1) (ha i.1))
              (lowerCauchyFeature (a i.1) (ha i.1))) =
      ∑ i : HorizontalLayerCopy m,
        paleyWienerOperatorTransport
          ((-(Real.pi : ℂ)⁻¹) •
            InnerProductSpace.rankOne ℂ
              (upperCauchyFeature (a i.1) (ha i.1))
              (lowerCauchyFeature (a i.1) (ha i.1))) := by
        exact paleyWienerOperatorTransport_sum Finset.univ _
    _ = ∑ i : HorizontalLayerCopy m,
        (2 : ℂ) • InnerProductSpace.rankOne ℂ
          (expFeature (a i.1) (ha i.1))
          (expFeature (a i.1) (ha i.1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact paleyWienerOperatorTransport_rankOne (ha i.1)
    _ = finiteExponentialHankel a ha m :=
      sum_horizontalLayerCopies_rankOne_eq_finiteExponentialHankel a ha m

theorem tendsto_horizontalLayerPaleyWienerNormalized {r : ℕ}
    (a : Fin r → ℝ) (ha : ∀ j, 0 < a j) (m : Fin r → ℕ) :
    Tendsto (horizontalLayerPaleyWienerNormalized a m) (𝓝[≠] 0)
      (𝓝 (finiteExponentialHankel a ha m)) := by
  have hcopy : ∀ i ∈ (Finset.univ : Finset (HorizontalLayerCopy m)),
      0 < horizontalLayerCopyRate a i := by
    intro i hi
    exact ha i.1
  have hhardy :=
    tendsto_hardyLeakage_finiteHorizontalLayerNormalizedProjective
      (Finset.univ : Finset (HorizontalLayerCopy m))
      (horizontalLayerCopyRate a) hcopy
  have htransport :=
    paleyWienerOperatorTransportCLM.continuous.continuousAt.tendsto.comp hhardy
  simp only [paleyWienerOperatorTransportCLM_apply] at htransport
  rw [paleyWienerOperatorTransport_finiteHorizontalLayerInfinitesimal a ha m]
    at htransport
  apply htransport.congr'
  exact Filter.Eventually.of_forall fun ω => by
    rw [horizontalLayerPaleyWienerNormalized,
      ← finiteHorizontalLayerNormalizedProjective_copies]
    exact paleyWienerOperatorTransportCLM_apply _

end GaloisForLFunctions.HTGeometry

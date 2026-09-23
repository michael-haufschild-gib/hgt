import GaloisForLFunctions.RHTower.CCMActualHeadMatchedPhaseProjectiveGaugeTraceClassOperator

open Complex MeasureTheory ContinuousLinearMap
open scoped BigOperators ComplexConjugate InnerProductSpace

noncomputable section
namespace RHTower

/-- Oriented exterior kernel of the two projective feature columns. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeChiralKernel (xi : ℝ) :
    CCMActualHeadMatchedPhaseProjectiveGaugeIndex →
      CCMActualHeadMatchedPhaseProjectiveGaugeIndex → ℂ :=
  fun a b =>
    ccmActualHeadMatchedPhaseProjectiveGaugeWeightFeature a *
        conj (ccmActualHeadMatchedPhaseProjectiveGaugeSourceFeature xi b) -
      ccmActualHeadMatchedPhaseProjectiveGaugeSourceFeature xi a *
        conj (ccmActualHeadMatchedPhaseProjectiveGaugeWeightFeature b)

/-- Antisymmetric rank-two Schatten frame retaining projective orientation. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator (xi : ℝ) :
    SchattenOneOperator CCMActualHeadMatchedPhaseProjectiveGaugeL2 :=
  rankOneSchattenOne
      ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector
      (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi) -
    rankOneSchattenOne
      (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi)
      ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector

theorem ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator_skewAdjoint
    (xi : ℝ) :
    adjoint
      (ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator xi :
        CCMActualHeadMatchedPhaseProjectiveGaugeL2 →L[ℂ]
          CCMActualHeadMatchedPhaseProjectiveGaugeL2) =
      -(ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator xi :
        CCMActualHeadMatchedPhaseProjectiveGaugeL2 →L[ℂ]
          CCMActualHeadMatchedPhaseProjectiveGaugeL2) := by
  change adjoint
      (InnerProductSpace.rankOne ℂ
          ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector
          (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi) -
        InnerProductSpace.rankOne ℂ
          (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi)
          ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector) =
    -(InnerProductSpace.rankOne ℂ
          ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector
          (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi) -
        InnerProductSpace.rankOne ℂ
          (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi)
          ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector)
  rw [map_sub, InnerProductSpace.adjoint_rankOne,
    InnerProductSpace.adjoint_rankOne]
  abel

theorem ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator_hasRankLE_two
    (xi : ℝ) :
    HasRankLE
      (ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator xi :
        CCMActualHeadMatchedPhaseProjectiveGaugeL2 →L[ℂ]
          CCMActualHeadMatchedPhaseProjectiveGaugeL2) 2 := by
  have hweightSource : HasRankLE
      (InnerProductSpace.rankOne ℂ
        ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector
        (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi)) 1 := by
    simpa [InnerProductSpace.rankOne_def] using
      deningerSmulRight_hasRankLE_one
        (innerSL ℂ (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi))
        ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector
  have hsourceWeight : HasRankLE
      (InnerProductSpace.rankOne ℂ
        (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi)
        ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector) 1 := by
    simpa [InnerProductSpace.rankOne_def] using
      deningerSmulRight_hasRankLE_one
        (innerSL ℂ ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector)
        (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi)
  have hnegSourceWeight : HasRankLE
      (-(InnerProductSpace.rankOne ℂ
        (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi)
        ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector)) 1 := by
    obtain ⟨V, hVfd, hVrank, hVmem⟩ := hsourceWeight
    exact ⟨V, hVfd, hVrank, fun x => by
      simpa using V.neg_mem (hVmem x)⟩
  change HasRankLE
    (InnerProductSpace.rankOne ℂ
        ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector
        (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi) -
      InnerProductSpace.rankOne ℂ
        (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi)
        ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector) 2
  simpa [sub_eq_add_neg] using hweightSource.add hnegSourceWeight

theorem norm_ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator_le
    (xi : ℝ) :
    ‖ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator xi‖ ≤
      2 * ‖ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector‖ *
        ‖ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi‖ := by
  calc
    ‖ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator xi‖ ≤
        ‖rankOneSchattenOne
          ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector
          (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi)‖ +
        ‖rankOneSchattenOne
          (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi)
          ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector‖ := norm_sub_le _ _
    _ = 2 * ‖ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector‖ *
        ‖ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi‖ := by
      rw [norm_rankOneSchattenOne, norm_rankOneSchattenOne]
      ring

theorem ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator_matrix
    (xi : ℝ) (a b : CCMActualHeadMatchedPhaseProjectiveGaugeIndex) :
    inner ℂ
        (lp.single 2 (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode a) 1)
        ((ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator xi :
          CCMActualHeadMatchedPhaseProjectiveGaugeL2 →L[ℂ]
            CCMActualHeadMatchedPhaseProjectiveGaugeL2)
          (lp.single 2
            (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode b) 1)) =
      ccmActualHeadMatchedPhaseProjectiveGaugeChiralKernel xi a b := by
  change inner ℂ
      (lp.single 2 (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode a) 1)
      ((InnerProductSpace.rankOne ℂ
          ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector
          (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi) -
        InnerProductSpace.rankOne ℂ
          (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi)
          ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector)
        (lp.single 2
          (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode b) 1)) = _
  simp only [sub_apply, InnerProductSpace.rankOne_apply, inner_sub_right,
    inner_smul_right, lp.inner_single_left, lp.inner_single_right,
    RCLike.inner_apply, starRingEnd_apply, one_mul,
    ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector,
    ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector]
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeWeightCoefficient_indexCode,
    ccmActualHeadMatchedPhaseProjectiveGaugeSourceCoefficient_indexCode,
    ccmActualHeadMatchedPhaseProjectiveGaugeSourceCoefficient_indexCode,
    ccmActualHeadMatchedPhaseProjectiveGaugeWeightCoefficient_indexCode]
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeChiralKernel]
  simp only [starRingEnd_apply, star_one, mul_one]
  ring

@[simp] theorem ccmActualHeadMatchedPhaseProjectiveGaugeChiralKernel_atom_weightAnchor
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeChiralKernel xi (.atom n) .weightAnchor =
      (-(ccmActualHeadMatchedPhaseProjectiveGauge n *
        (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re) : ℝ) := by
  simp [ccmActualHeadMatchedPhaseProjectiveGaugeChiralKernel,
    ccmActualHeadMatchedPhaseProjectiveGaugeWeightFeature,
    ccmActualHeadMatchedPhaseProjectiveGaugeSourceFeature]

@[simp] theorem ccmActualHeadMatchedPhaseProjectiveGaugeChiralKernel_atom_sourceAnchor
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeChiralKernel xi (.atom n) .sourceAnchor =
      (ccmActualHeadMatchedPhaseProjectiveGauge n : ℂ) := by
  simp [ccmActualHeadMatchedPhaseProjectiveGaugeChiralKernel,
    ccmActualHeadMatchedPhaseProjectiveGaugeWeightFeature,
    ccmActualHeadMatchedPhaseProjectiveGaugeSourceFeature]

/-- Total oriented-minor reporter. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeChiralReporter
    (xi : ℝ) (n : ℕ) : ℝ :=
  if criticalMellinAtomWeight n = 0 then 0
  else
    -(inner ℂ
      (lp.single 2
        (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode (.atom n)) 1)
      ((ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator xi :
        CCMActualHeadMatchedPhaseProjectiveGaugeL2 →L[ℂ]
          CCMActualHeadMatchedPhaseProjectiveGaugeL2)
        (lp.single 2
          (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode .weightAnchor) 1))).re /
    (inner ℂ
      (lp.single 2
        (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode (.atom n)) 1)
      ((ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator xi :
        CCMActualHeadMatchedPhaseProjectiveGaugeL2 →L[ℂ]
          CCMActualHeadMatchedPhaseProjectiveGaugeL2)
        (lp.single 2
          (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode .sourceAnchor) 1))).re

theorem ccmActualHeadMatchedPhaseProjectiveGaugeChiralReporter_eq_kernelReporter
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeChiralReporter xi n =
      ccmActualHeadMatchedPhaseProjectiveGaugeReporter xi n := by
  unfold ccmActualHeadMatchedPhaseProjectiveGaugeChiralReporter
    ccmActualHeadMatchedPhaseProjectiveGaugeReporter
  split_ifs
  · rfl
  · rw [ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator_matrix,
      ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator_matrix,
      ccmActualHeadMatchedPhaseProjectiveGaugeChiralKernel_atom_weightAnchor,
      ccmActualHeadMatchedPhaseProjectiveGaugeChiralKernel_atom_sourceAnchor,
      ccmActualHeadMatchedPhaseProjectiveGaugeKernel_atom_sourceAnchor,
      ccmActualHeadMatchedPhaseProjectiveGaugeKernel_atom_weightAnchor]
    norm_cast
    ring

theorem ccmActualHeadMatchedPhaseProjectiveGaugeChiralReporter_eq
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeChiralReporter xi n =
      (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re := by
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeChiralReporter_eq_kernelReporter,
    ccmActualHeadMatchedPhaseProjectiveGaugeReporter_eq]

/-- Self-adjoint trace-class orientation observable. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationOperator
    (xi : ℝ) : SchattenOneOperator CCMActualHeadMatchedPhaseProjectiveGaugeL2 :=
  I • ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator xi

theorem ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationOperator_isSelfAdjoint
    (xi : ℝ) :
    IsSelfAdjoint
      (ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationOperator xi :
        CCMActualHeadMatchedPhaseProjectiveGaugeL2 →L[ℂ]
          CCMActualHeadMatchedPhaseProjectiveGaugeL2) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  change adjoint
      (I • (ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator xi :
        CCMActualHeadMatchedPhaseProjectiveGaugeL2 →L[ℂ]
          CCMActualHeadMatchedPhaseProjectiveGaugeL2)) =
    I • (ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator xi :
      CCMActualHeadMatchedPhaseProjectiveGaugeL2 →L[ℂ]
        CCMActualHeadMatchedPhaseProjectiveGaugeL2)
  rw [ContinuousLinearMap.adjoint.map_smulₛₗ,
    ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator_skewAdjoint]
  simp

theorem ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationOperator_matrix
    (xi : ℝ) (a b : CCMActualHeadMatchedPhaseProjectiveGaugeIndex) :
    inner ℂ
        (lp.single 2 (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode a) 1)
        ((ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationOperator xi :
          CCMActualHeadMatchedPhaseProjectiveGaugeL2 →L[ℂ]
            CCMActualHeadMatchedPhaseProjectiveGaugeL2)
          (lp.single 2
            (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode b) 1)) =
      I * ccmActualHeadMatchedPhaseProjectiveGaugeChiralKernel xi a b := by
  change inner ℂ
      (lp.single 2 (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode a) 1)
      ((I • (ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator xi :
        CCMActualHeadMatchedPhaseProjectiveGaugeL2 →L[ℂ]
          CCMActualHeadMatchedPhaseProjectiveGaugeL2))
        (lp.single 2
          (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode b) 1)) = _
  rw [smul_apply, inner_smul_right,
    ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator_matrix]

/-- Total self-adjoint matrix reporter using imaginary anchor coefficients. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationReporter
    (xi : ℝ) (n : ℕ) : ℝ :=
  if criticalMellinAtomWeight n = 0 then 0
  else
    -(inner ℂ
      (lp.single 2
        (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode (.atom n)) 1)
      ((ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationOperator xi :
        CCMActualHeadMatchedPhaseProjectiveGaugeL2 →L[ℂ]
          CCMActualHeadMatchedPhaseProjectiveGaugeL2)
        (lp.single 2
          (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode .weightAnchor) 1))).im /
    (inner ℂ
      (lp.single 2
        (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode (.atom n)) 1)
      ((ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationOperator xi :
        CCMActualHeadMatchedPhaseProjectiveGaugeL2 →L[ℂ]
          CCMActualHeadMatchedPhaseProjectiveGaugeL2)
        (lp.single 2
          (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode .sourceAnchor) 1))).im

theorem ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationReporter_eq_chiral
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationReporter xi n =
      ccmActualHeadMatchedPhaseProjectiveGaugeChiralReporter xi n := by
  unfold ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationReporter
    ccmActualHeadMatchedPhaseProjectiveGaugeChiralReporter
  split_ifs
  · rfl
  · rw [ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationOperator_matrix,
      ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationOperator_matrix,
      ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator_matrix,
      ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator_matrix]
    rw [ccmActualHeadMatchedPhaseProjectiveGaugeChiralKernel_atom_weightAnchor,
      ccmActualHeadMatchedPhaseProjectiveGaugeChiralKernel_atom_sourceAnchor]
    simp [Complex.mul_im]

theorem ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationReporter_eq
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationReporter xi n =
      (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re := by
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationReporter_eq_chiral,
    ccmActualHeadMatchedPhaseProjectiveGaugeChiralReporter_eq]

def ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationFiniteReporter
    (F : Finset ℕ) (xi : ℝ) : ℝ :=
  ∑ n ∈ F,
    ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationReporter xi n

theorem ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationFiniteReporter_eq
    (F : Finset ℕ) (xi : ℝ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationFiniteReporter F xi =
      (ccmActualHeadMatchedOrientedPhaseFiniteSymbol F xi).re := by
  unfold ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationFiniteReporter
    ccmActualHeadMatchedOrientedPhaseFiniteSymbol
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationReporter_eq xi n

/-- Every finite actual matched block is a spectral integral of matrix ratios of one self-adjoint,
rank-at-most-two Schatten-one orientation observable. -/
theorem ccmActualHeadMatchedPrimePolarFiniteBlock_eq_hermitianOrientationSchattenOperator
    (F : Finset ℕ) (f : SoninL2) :
    ccmActualHeadMatchedPrimePolarFiniteBlock F f =
      -2 * ∫ xi : ℝ,
        ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationFiniteReporter F xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ) := by
  rw [ccmActualHeadMatchedPrimePolarFiniteBlock_eq_orientedPhaseFiniteSymbol]
  congr 2
  funext xi
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationFiniteReporter_eq]

end RHTower


import GaloisForLFunctions.HTGeometry.SourceGradeJordanDataProcessing
import GaloisForLFunctions.RHTower.SourceHorizontalEulerWoldIndependentKreinXiResidueTransport
import GaloisForLFunctions.RHTower.SourceHorizontalEulerGammaCubicNegativeRenormalizedBudget

/-!
# Nonlinear source-grade Jordan selection through completed Xi residue

Hahn--Jordan selection is applied to intrinsic Euler `(3,0)` and Wold `(0,3)` source jets before
linear grade forgetting or matrix transport. Negative and positive residuals retain the exact Euler
action and Wold regulator, reconstruct the full signed current, and strictly dominate the variation
visible after compression. Both legs then use the already-proved common Gamma/polar residue and
four-orientation block. Prime labels, Euler depth `k²`, Xi multiplicity, BV endpoint defect, and the
literal primitive-source budget remain explicit. No operator spectrum or Loewner projection is used.
-/

open Complex Filter Function Set WithTop Topology MeasureTheory
open scoped BigOperators ComplexOrder
open scoped Matrix.Norms.L2Operator
open GaloisForLFunctions

namespace RHTower

noncomputable section

abbrev SourceHorizontalEulerWoldJordanAtom (N : ℕ) :=
  Sum (Fin (N + 1)) (Fin (N + 1))

def sourceHorizontalEulerJordanAtomMass (N : ℕ) (n : Fin (N + 1)) : ℝ :=
  2 * sourceHorizontalEulerGammaCubicAtom (nthPrimeSubtype n) /
    xiMassNthPrimeLogHeight N ^ (3 : ℕ)

def sourceHorizontalWoldJordanAtomMass (N : ℕ) (n : Fin (N + 1)) : ℝ :=
  2 * (woldCoeff 1 (nthPrimeSubtype n) * xiMassNthPrimeLogHeight n ^ (2 : ℕ)) /
    xiMassNthPrimeLogHeight N ^ (3 : ℕ)

theorem sourceHorizontalEulerJordanAtomMass_pos (N : ℕ) (n : Fin (N + 1)) :
    0 < sourceHorizontalEulerJordanAtomMass N n := by
  exact div_pos (mul_pos (by norm_num)
    (sourceHorizontalEulerGammaCubicAtom_pos (nthPrimeSubtype n)))
    (pow_pos (xiMassNthPrimeLogHeight_pos N) 3)

theorem sourceHorizontalWoldJordanAtomMass_pos (N : ℕ) (n : Fin (N + 1)) :
    0 < sourceHorizontalWoldJordanAtomMass N n := by
  exact div_pos (mul_pos (by norm_num)
    (mul_pos (woldCoeff_pos 1 (nthPrimeSubtype n))
      (sq_pos_of_pos (xiMassNthPrimeLogHeight_pos n))))
    (pow_pos (xiMassNthPrimeLogHeight_pos N) 3)

/-- Literal prime-labelled signed current before source-grade compression. -/
def sourceHorizontalEulerWoldJordanSignedDensity (N : ℕ) :
    SourceHorizontalEulerWoldJordanAtom N → ℝ :=
  GaloisForLFunctions.HTGeometry.signedSourceGradeDensity
    (sourceHorizontalEulerJordanAtomMass N)
    (sourceHorizontalWoldJordanAtomMass N)

@[simp] theorem sourceHorizontalEulerWoldJordanSignedDensity_inl
    (N : ℕ) (n : Fin (N + 1)) :
    sourceHorizontalEulerWoldJordanSignedDensity N (Sum.inl n) =
      -sourceHorizontalEulerJordanAtomMass N n := by
  rfl

@[simp] theorem sourceHorizontalEulerWoldJordanSignedDensity_inr
    (N : ℕ) (n : Fin (N + 1)) :
    sourceHorizontalEulerWoldJordanSignedDensity N (Sum.inr n) =
      sourceHorizontalWoldJordanAtomMass N n := by
  rfl

theorem sourceHorizontalEulerWoldJordanSignedDensity_reconstruct
    (N : ℕ) (x : SourceHorizontalEulerWoldJordanAtom N) :
    GaloisForLFunctions.HTGeometry.sourceJordanPositivePart
        (sourceHorizontalEulerWoldJordanSignedDensity N x) -
      GaloisForLFunctions.HTGeometry.sourceJordanNegativePart
        (sourceHorizontalEulerWoldJordanSignedDensity N x) =
      sourceHorizontalEulerWoldJordanSignedDensity N x :=
  GaloisForLFunctions.HTGeometry.sourceJordanPositivePart_sub_negativePart _

@[simp] theorem sourceHorizontalEulerWoldJordanNegativePart_inl
    (N : ℕ) (n : Fin (N + 1)) :
    GaloisForLFunctions.HTGeometry.sourceJordanNegativePart
        (sourceHorizontalEulerWoldJordanSignedDensity N (Sum.inl n)) =
      sourceHorizontalEulerJordanAtomMass N n := by
  exact HTGeometry.sourceJordanNegativePart_signedSourceGradeDensity_inl _ _ _
      (sourceHorizontalEulerJordanAtomMass_pos N n).le

@[simp] theorem sourceHorizontalEulerWoldJordanPositivePart_inl
    (N : ℕ) (n : Fin (N + 1)) :
    GaloisForLFunctions.HTGeometry.sourceJordanPositivePart
        (sourceHorizontalEulerWoldJordanSignedDensity N (Sum.inl n)) = 0 := by
  exact HTGeometry.sourceJordanPositivePart_signedSourceGradeDensity_inl _ _ _
      (sourceHorizontalEulerJordanAtomMass_pos N n).le

@[simp] theorem sourceHorizontalEulerWoldJordanNegativePart_inr
    (N : ℕ) (n : Fin (N + 1)) :
    GaloisForLFunctions.HTGeometry.sourceJordanNegativePart
        (sourceHorizontalEulerWoldJordanSignedDensity N (Sum.inr n)) = 0 := by
  exact HTGeometry.sourceJordanNegativePart_signedSourceGradeDensity_inr _ _ _
      (sourceHorizontalWoldJordanAtomMass_pos N n).le

@[simp] theorem sourceHorizontalEulerWoldJordanPositivePart_inr
    (N : ℕ) (n : Fin (N + 1)) :
    GaloisForLFunctions.HTGeometry.sourceJordanPositivePart
        (sourceHorizontalEulerWoldJordanSignedDensity N (Sum.inr n)) =
      sourceHorizontalWoldJordanAtomMass N n := by
  exact HTGeometry.sourceJordanPositivePart_signedSourceGradeDensity_inr _ _ _
      (sourceHorizontalWoldJordanAtomMass_pos N n).le

/-- Jordan selection preserves every labelled Euler prime-power depth and its literal `k²` weight. -/
theorem sourceHorizontalEulerWoldJordanSelectedEulerAtom_eq_depthSum
    (N : ℕ) (n : Fin (N + 1)) :
    -sourceHorizontalEulerJordanAtomMass N n =
      ∑' k : ℕ,
        -(2 * (Real.log (nthPrimeSubtype n : ℝ) ^ (3 : ℕ) * (k : ℝ) ^ (2 : ℕ) *
          ((nthPrimeSubtype n : ℝ)⁻¹) ^ k) /
            xiMassNthPrimeLogHeight N ^ (3 : ℕ)) := by
  rw [sourceHorizontalEulerJordanAtomMass]
  have h := sourceHorizontalEulerGammaCubicNegativeAtom_eq_depthSum
    (nthPrimeSubtype n)
  calc
    -(2 * sourceHorizontalEulerGammaCubicAtom (nthPrimeSubtype n) /
        xiMassNthPrimeLogHeight N ^ (3 : ℕ)) =
        (2 / xiMassNthPrimeLogHeight N ^ (3 : ℕ)) *
          (-sourceHorizontalEulerGammaCubicAtom (nthPrimeSubtype n)) := by ring
    _ = (2 / xiMassNthPrimeLogHeight N ^ (3 : ℕ)) *
        (∑' k : ℕ, -(Real.log (nthPrimeSubtype n : ℝ) ^ (3 : ℕ) * (k : ℝ) ^ (2 : ℕ) *
          ((nthPrimeSubtype n : ℝ)⁻¹) ^ k)) := congrArg _ h
    _ = ∑' k : ℕ, (2 / xiMassNthPrimeLogHeight N ^ (3 : ℕ)) *
        -(Real.log (nthPrimeSubtype n : ℝ) ^ (3 : ℕ) * (k : ℝ) ^ (2 : ℕ) *
          ((nthPrimeSubtype n : ℝ)⁻¹) ^ k) := tsum_mul_left.symm
    _ = ∑' k : ℕ,
        -(2 * (Real.log (nthPrimeSubtype n : ℝ) ^ (3 : ℕ) * (k : ℝ) ^ (2 : ℕ) *
          ((nthPrimeSubtype n : ℝ)⁻¹) ^ k) /
            xiMassNthPrimeLogHeight N ^ (3 : ℕ)) := by
          apply tsum_congr
          intro k
          ring

def sourceHorizontalEulerWoldJordanNegativeMass (N : ℕ) : ℝ :=
  ∑ x : SourceHorizontalEulerWoldJordanAtom N,
    GaloisForLFunctions.HTGeometry.sourceJordanNegativePart
      (sourceHorizontalEulerWoldJordanSignedDensity N x)

def sourceHorizontalEulerWoldJordanPositiveMass (N : ℕ) : ℝ :=
  ∑ x : SourceHorizontalEulerWoldJordanAtom N,
    GaloisForLFunctions.HTGeometry.sourceJordanPositivePart
      (sourceHorizontalEulerWoldJordanSignedDensity N x)

theorem sourceHorizontalEulerWoldJordanNegativeMass_eq (N : ℕ) :
    sourceHorizontalEulerWoldJordanNegativeMass N =
      2 * sourceHorizontalEulerGammaCubicMoment N /
        xiMassNthPrimeLogHeight N ^ (3 : ℕ) := by
  rw [sourceHorizontalEulerWoldJordanNegativeMass, Fintype.sum_sum_type]
  simp only [sourceHorizontalEulerWoldJordanNegativePart_inl,
    sourceHorizontalEulerWoldJordanNegativePart_inr, Finset.sum_const_zero, add_zero]
  rw [show (∑ x : Fin (N + 1), sourceHorizontalEulerJordanAtomMass N x) =
      ∑ n ∈ Finset.range (N + 1),
        2 * sourceHorizontalEulerGammaCubicAtom (nthPrimeSubtype n) /
          xiMassNthPrimeLogHeight N ^ (3 : ℕ) by
    simpa [sourceHorizontalEulerJordanAtomMass] using
      (Fin.sum_univ_eq_sum_range
        (fun n : ℕ => 2 * sourceHorizontalEulerGammaCubicAtom (nthPrimeSubtype n) /
          xiMassNthPrimeLogHeight N ^ (3 : ℕ)) (N + 1))]
  rw [sourceHorizontalEulerGammaCubicMoment, ← Finset.sum_div, ← Finset.mul_sum]

theorem sourceHorizontalEulerWoldJordanPositiveMass_eq (N : ℕ) :
    sourceHorizontalEulerWoldJordanPositiveMass N =
      2 * sourceHorizontalWoldCubicCountertermMoment N /
        xiMassNthPrimeLogHeight N ^ (3 : ℕ) := by
  rw [sourceHorizontalEulerWoldJordanPositiveMass, Fintype.sum_sum_type]
  simp only [sourceHorizontalEulerWoldJordanPositivePart_inl,
    sourceHorizontalEulerWoldJordanPositivePart_inr, Finset.sum_const_zero, zero_add]
  rw [show (∑ x : Fin (N + 1), sourceHorizontalWoldJordanAtomMass N x) =
      ∑ n ∈ Finset.range (N + 1),
        2 * (woldCoeff 1 (nthPrimeSubtype n) * xiMassNthPrimeLogHeight n ^ (2 : ℕ)) /
          xiMassNthPrimeLogHeight N ^ (3 : ℕ) by
    simpa [sourceHorizontalWoldJordanAtomMass] using
      (Fin.sum_univ_eq_sum_range
        (fun n : ℕ =>
          2 * (woldCoeff 1 (nthPrimeSubtype n) * xiMassNthPrimeLogHeight n ^ (2 : ℕ)) /
            xiMassNthPrimeLogHeight N ^ (3 : ℕ)) (N + 1))]
  rw [sourceHorizontalWoldCubicCountertermMoment, ← Finset.sum_div, ← Finset.mul_sum]

theorem sourceHorizontalEulerWoldJordanNegativeMass_pos (N : ℕ) :
    0 < sourceHorizontalEulerWoldJordanNegativeMass N := by
  rw [sourceHorizontalEulerWoldJordanNegativeMass_eq]
  exact div_pos (mul_pos (by norm_num)
    (sourceHorizontalEulerGammaCubicMoment_pos N))
    (pow_pos (xiMassNthPrimeLogHeight_pos N) 3)

theorem sourceHorizontalEulerWoldJordanPositiveMass_pos (N : ℕ) :
    0 < sourceHorizontalEulerWoldJordanPositiveMass N := by
  rw [sourceHorizontalEulerWoldJordanPositiveMass_eq]
  exact div_pos (mul_pos (by norm_num)
    (sourceHorizontalWoldCubicCountertermMoment_pos N))
    (pow_pos (xiMassNthPrimeLogHeight_pos N) 3)

def sourceHorizontalEulerWoldJordanPreCompressionVariation (N : ℕ) : ℝ :=
  GaloisForLFunctions.HTGeometry.twoGradePreCompressionVariation
    (sourceHorizontalEulerWoldJordanNegativeMass N)
    (sourceHorizontalEulerWoldJordanPositiveMass N)

def sourceHorizontalEulerWoldJordanPostCompressionVariation (N : ℕ) : ℝ :=
  GaloisForLFunctions.HTGeometry.twoGradePostCompressionVariation
    (sourceHorizontalEulerWoldJordanNegativeMass N)
    (sourceHorizontalEulerWoldJordanPositiveMass N)

theorem sourceHorizontalEulerWoldJordanNegativeMass_sub_positiveMass_eq (N : ℕ) :
    sourceHorizontalEulerWoldJordanNegativeMass N -
        sourceHorizontalEulerWoldJordanPositiveMass N =
      2 * sourceHorizontalEulerGammaWoldCubicDefectMoment N /
        xiMassNthPrimeLogHeight N ^ (3 : ℕ) := by
  rw [sourceHorizontalEulerWoldJordanNegativeMass_eq,
    sourceHorizontalEulerWoldJordanPositiveMass_eq,
    sourceHorizontalWoldCubicCountertermMoment_add_defect]
  ring

theorem sourceHorizontalEulerWoldJordanPositiveMass_le_negativeMass (N : ℕ) :
    sourceHorizontalEulerWoldJordanPositiveMass N ≤
      sourceHorizontalEulerWoldJordanNegativeMass N := by
  have hdiff : 0 < sourceHorizontalEulerWoldJordanNegativeMass N -
      sourceHorizontalEulerWoldJordanPositiveMass N := by
    rw [sourceHorizontalEulerWoldJordanNegativeMass_sub_positiveMass_eq]
    exact div_pos (mul_pos (by norm_num)
      (sourceHorizontalEulerGammaWoldCubicDefectMoment_pos N))
      (pow_pos (xiMassNthPrimeLogHeight_pos N) 3)
  linarith

theorem sourceHorizontalEulerWoldJordanPostCompressionVariation_eq (N : ℕ) :
    sourceHorizontalEulerWoldJordanPostCompressionVariation N =
      2 * sourceHorizontalEulerGammaWoldCubicDefectMoment N /
        xiMassNthPrimeLogHeight N ^ (3 : ℕ) := by
  rw [sourceHorizontalEulerWoldJordanPostCompressionVariation,
    GaloisForLFunctions.HTGeometry.twoGradePostCompressionVariation,
    abs_of_nonpos (sub_nonpos.mpr
      (sourceHorizontalEulerWoldJordanPositiveMass_le_negativeMass N))]
  rw [neg_sub]
  exact sourceHorizontalEulerWoldJordanNegativeMass_sub_positiveMass_eq N

theorem sourceHorizontalEulerWoldJordanCompression_loss_eq (N : ℕ) :
    sourceHorizontalEulerWoldJordanPreCompressionVariation N -
        sourceHorizontalEulerWoldJordanPostCompressionVariation N =
      4 * sourceHorizontalWoldCubicCountertermMoment N /
        xiMassNthPrimeLogHeight N ^ (3 : ℕ) := by
  rw [sourceHorizontalEulerWoldJordanPreCompressionVariation,
    sourceHorizontalEulerWoldJordanPostCompressionVariation]
  rw [GaloisForLFunctions.HTGeometry.twoGradeCompression_loss_eq_twice_regulator
    (sourceHorizontalEulerWoldJordanPositiveMass_pos N).le
    (sourceHorizontalEulerWoldJordanPositiveMass_le_negativeMass N)]
  rw [sourceHorizontalEulerWoldJordanPositiveMass_eq]
  ring

theorem sourceHorizontalEulerWoldJordanPostCompressionVariation_lt_pre (N : ℕ) :
    sourceHorizontalEulerWoldJordanPostCompressionVariation N <
      sourceHorizontalEulerWoldJordanPreCompressionVariation N := by
  exact GaloisForLFunctions.HTGeometry.twoGradePostCompressionVariation_lt_pre
    (sourceHorizontalEulerWoldJordanPositiveMass_pos N)
    (sourceHorizontalEulerWoldJordanPositiveMass_le_negativeMass N)

def sourceHorizontalEulerWoldJordanSelectedPhysicalAction
    (c : ℂ) (N : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((-sourceHorizontalEulerWoldJordanNegativeMass N : ℝ) : ℂ) •
    routePJuliaSharedOrientationOrbitBlock c

def sourceHorizontalEulerWoldJordanSelectedRegulator
    (c : ℂ) (N : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((sourceHorizontalEulerWoldJordanPositiveMass N : ℝ) : ℂ) •
    routePJuliaSharedOrientationOrbitBlock c

theorem sourceHorizontalEulerWoldJordanSelectedPhysicalAction_eq_landing
    (c : ℂ) (N : ℕ) :
    sourceHorizontalEulerWoldJordanSelectedPhysicalAction c N =
      sourceHorizontalEulerGammaPolarPureSelectedLanding c N := by
  rw [sourceHorizontalEulerWoldJordanSelectedPhysicalAction,
    sourceHorizontalEulerWoldJordanNegativeMass_eq,
    sourceHorizontalEulerGammaPolarPureSelectedLanding_eq]
  congr 1
  push_cast
  ring

theorem sourceHorizontalEulerWoldJordanSelectedRegulator_eq_landing
    (c : ℂ) (N : ℕ) :
    sourceHorizontalEulerWoldJordanSelectedRegulator c N =
      sourceHorizontalWoldGammaPolarPureSelectedLanding c N := by
  rw [sourceHorizontalEulerWoldJordanSelectedRegulator,
    sourceHorizontalEulerWoldJordanPositiveMass_eq,
    sourceHorizontalWoldGammaPolarPureSelectedLanding_eq]

theorem sourceHorizontalEulerWoldJordanSelected_reconstruct
    (c : ℂ) (N : ℕ) :
    sourceHorizontalEulerWoldJordanSelectedPhysicalAction c N +
        sourceHorizontalEulerWoldJordanSelectedRegulator c N =
      sourceHorizontalEulerWoldGammaPolarCombinedSelectedLanding c N := by
  rw [sourceHorizontalEulerWoldJordanSelectedPhysicalAction_eq_landing,
    sourceHorizontalEulerWoldJordanSelectedRegulator_eq_landing]
  rfl

theorem tendsto_sourceHorizontalEulerWoldJordanNegativeMass :
    Tendsto sourceHorizontalEulerWoldJordanNegativeMass atTop (nhds (2 / 3 : ℝ)) := by
  rw [show sourceHorizontalEulerWoldJordanNegativeMass =
      fun N => 2 * sourceHorizontalEulerGammaCubicNormalizedMoment N by
    funext N
    rw [sourceHorizontalEulerWoldJordanNegativeMass_eq,
      sourceHorizontalEulerGammaCubicNormalizedMoment]
    ring]
  convert tendsto_sourceHorizontalEulerGammaCubicNormalizedMoment.const_mul 2 using 1
  norm_num

theorem tendsto_sourceHorizontalEulerWoldJordanPositiveMass :
    Tendsto sourceHorizontalEulerWoldJordanPositiveMass atTop (nhds (2 / 3 : ℝ)) := by
  have h := tendsto_sourceHorizontalEulerWoldJordanNegativeMass.sub
    (tendsto_sourceHorizontalEulerGammaWoldCubicDefectMoment_normalized_zero.const_mul 2)
  convert h using 1
  · funext N
    rw [sourceHorizontalEulerWoldJordanNegativeMass_eq,
      sourceHorizontalEulerWoldJordanPositiveMass_eq,
      sourceHorizontalWoldCubicCountertermMoment_add_defect]
    ring
  · norm_num

theorem tendsto_sourceHorizontalEulerWoldJordanPreCompressionVariation :
    Tendsto sourceHorizontalEulerWoldJordanPreCompressionVariation atTop
      (nhds (4 / 3 : ℝ)) := by
  have h := tendsto_sourceHorizontalEulerWoldJordanNegativeMass.add
    tendsto_sourceHorizontalEulerWoldJordanPositiveMass
  convert h using 1
  · funext N
    rfl
  · norm_num

theorem tendsto_sourceHorizontalEulerWoldJordanPostCompressionVariation_zero :
    Tendsto sourceHorizontalEulerWoldJordanPostCompressionVariation atTop (nhds 0) := by
  rw [show sourceHorizontalEulerWoldJordanPostCompressionVariation = fun N =>
      2 * (sourceHorizontalEulerGammaWoldCubicDefectMoment N /
        xiMassNthPrimeLogHeight N ^ (3 : ℕ)) by
    funext N
    rw [sourceHorizontalEulerWoldJordanPostCompressionVariation_eq]
    ring]
  convert tendsto_sourceHorizontalEulerGammaWoldCubicDefectMoment_normalized_zero.const_mul 2
    using 1
  norm_num

theorem tendsto_sourceHorizontalEulerWoldJordanSelectedPhysicalAction
    (c : ℂ) :
    Tendsto (sourceHorizontalEulerWoldJordanSelectedPhysicalAction c) atTop
      (nhds (((-(2 / 3 : ℝ) : ℝ) : ℂ) • routePJuliaSharedOrientationOrbitBlock c)) := by
  exact tendsto_sourceHorizontalEulerWoldJordanNegativeMass.neg.ofReal.smul_const _

theorem tendsto_sourceHorizontalEulerWoldJordanSelectedRegulator
    (c : ℂ) :
    Tendsto (sourceHorizontalEulerWoldJordanSelectedRegulator c) atTop
      (nhds ((((2 / 3 : ℝ) : ℝ) : ℂ) • routePJuliaSharedOrientationOrbitBlock c)) := by
  exact tendsto_sourceHorizontalEulerWoldJordanPositiveMass.ofReal.smul_const _

def sourceHorizontalEulerWoldJordanSelectedBundle
    (c : ℂ) (_q : XiRightZeroCopy) (N : ℕ) :
    Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![sourceHorizontalWoldBVKreinSignedLanding c N,
    sourceHorizontalEulerWoldJordanSelectedPhysicalAction c N,
    sourceHorizontalEulerWoldJordanSelectedRegulator c N]

@[simp] theorem sourceHorizontalEulerWoldJordanSelectedBundle_bv
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) :
    sourceHorizontalEulerWoldJordanSelectedBundle c q N 0 =
      sourceHorizontalWoldBVKreinSignedLanding c N := by
  rfl

theorem sourceHorizontalEulerWoldJordanSelectedBundle_actualFiber_sum
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) :
    (∑ r : XiRightSupportFiber q,
      sourceHorizontalEulerWoldJordanSelectedBundle c r.1 N) =
      xiSupportMultiplicity q.1.1 •
        sourceHorizontalEulerWoldJordanSelectedBundle c q N := by
  rw [show (∑ r : XiRightSupportFiber q,
      sourceHorizontalEulerWoldJordanSelectedBundle c r.1 N) =
      Fintype.card (XiRightSupportFiber q) •
        sourceHorizontalEulerWoldJordanSelectedBundle c q N by
    simp [sourceHorizontalEulerWoldJordanSelectedBundle]]
  rw [routePPrimitiveGammaJuliaXiActualSupportFiber_card]

theorem sourceHorizontalEulerWoldJordanSelectedPhysicalAction_zero_zero_re
    (c : ℂ) (N : ℕ) :
    (sourceHorizontalEulerWoldJordanSelectedPhysicalAction c N 0 0).re =
      -8 * Complex.normSq c * sourceHorizontalEulerGammaCubicNormalizedMoment N := by
  rw [sourceHorizontalEulerWoldJordanSelectedPhysicalAction,
    routePJuliaSharedOrientationOrbitBlock_eq_diagonal]
  norm_num
  rw [sourceHorizontalEulerWoldJordanNegativeMass_eq,
    sourceHorizontalEulerGammaCubicNormalizedMoment]
  ring

theorem sourceHorizontalEulerWoldJordanSelectedBudget_eq_compensated
    (c : ℂ) (N : ℕ) :
    sourceHorizontalWoldBVKreinSignedSplitEnergy c N +
        (sourceHorizontalEulerWoldJordanSelectedPhysicalAction c N 0 0).re =
      sourceHorizontalWoldBVKreinEulerGammaCubicCompensatedEnergy c N := by
  rw [sourceHorizontalEulerWoldJordanSelectedPhysicalAction_zero_zero_re]
  rw [sourceHorizontalWoldBVKreinEulerGammaCubicCompensatedEnergy]
  ring

theorem eventually_sourceHorizontalEulerWoldJordanSelectedBudget_lt_sourceBudget
    {c : ℂ} (hc : c ≠ 0) :
    ∀ᶠ N : ℕ in atTop,
      sourceHorizontalWoldBVKreinSignedSplitEnergy c N +
          (sourceHorizontalEulerWoldJordanSelectedPhysicalAction c N 0 0).re <
        sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c := by
  filter_upwards
    [eventually_sourceHorizontalWoldBVKreinEulerGammaCubicCompensatedEnergy_lt_sourceBudget hc]
    with N hN
  rw [sourceHorizontalEulerWoldJordanSelectedBudget_eq_compensated]
  exact hN

/-- Capstone nonlinear/non-spectral producer: intrinsic Jordan selection preserves both source
grades through Xi selection, strictly beats grade-forgetting, and carries the primitive budget. -/
theorem sourceHorizontalEulerWoldJordanResidualSelection
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) :
    (∀ x : SourceHorizontalEulerWoldJordanAtom N,
      GaloisForLFunctions.HTGeometry.sourceJordanPositivePart
          (sourceHorizontalEulerWoldJordanSignedDensity N x) -
        GaloisForLFunctions.HTGeometry.sourceJordanNegativePart
          (sourceHorizontalEulerWoldJordanSignedDensity N x) =
        sourceHorizontalEulerWoldJordanSignedDensity N x) ∧
    (∀ n : Fin (N + 1),
      -sourceHorizontalEulerJordanAtomMass N n =
        ∑' k : ℕ,
          -(2 * (Real.log (nthPrimeSubtype n : ℝ) ^ (3 : ℕ) * (k : ℝ) ^ (2 : ℕ) *
            ((nthPrimeSubtype n : ℝ)⁻¹) ^ k) /
              xiMassNthPrimeLogHeight N ^ (3 : ℕ))) ∧
    sourceHorizontalEulerWoldJordanPostCompressionVariation N <
      sourceHorizontalEulerWoldJordanPreCompressionVariation N ∧
    sourceHorizontalEulerWoldJordanSelectedPhysicalAction c N =
      sourceHorizontalEulerGammaPolarPureSelectedLanding c N ∧
    sourceHorizontalEulerWoldJordanSelectedRegulator c N =
      sourceHorizontalWoldGammaPolarPureSelectedLanding c N ∧
    sourceHorizontalEulerWoldJordanSelectedPhysicalAction c N +
        sourceHorizontalEulerWoldJordanSelectedRegulator c N =
      sourceHorizontalEulerWoldGammaPolarCombinedSelectedLanding c N ∧
    sourceHorizontalEulerWoldJordanSelectedBundle c q N 0 =
      sourceHorizontalWoldBVKreinSignedLanding c N ∧
    (∑ r : XiRightSupportFiber q,
      sourceHorizontalEulerWoldJordanSelectedBundle c r.1 N) =
      xiSupportMultiplicity q.1.1 •
        sourceHorizontalEulerWoldJordanSelectedBundle c q N ∧
    Tendsto sourceHorizontalEulerWoldJordanPreCompressionVariation atTop
      (nhds (4 / 3 : ℝ)) ∧
    Tendsto sourceHorizontalEulerWoldJordanPostCompressionVariation atTop (nhds 0) ∧
    Tendsto (sourceHorizontalEulerWoldJordanSelectedPhysicalAction c) atTop
      (nhds (((-(2 / 3 : ℝ) : ℝ) : ℂ) • routePJuliaSharedOrientationOrbitBlock c)) ∧
    Tendsto (sourceHorizontalEulerWoldJordanSelectedRegulator c) atTop
      (nhds ((((2 / 3 : ℝ) : ℝ) : ℂ) • routePJuliaSharedOrientationOrbitBlock c)) ∧
    (c ≠ 0 → ∀ᶠ M : ℕ in atTop,
      sourceHorizontalWoldBVKreinSignedSplitEnergy c M +
          (sourceHorizontalEulerWoldJordanSelectedPhysicalAction c M 0 0).re <
        sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c) := by
  exact ⟨sourceHorizontalEulerWoldJordanSignedDensity_reconstruct N,
    sourceHorizontalEulerWoldJordanSelectedEulerAtom_eq_depthSum N,
    sourceHorizontalEulerWoldJordanPostCompressionVariation_lt_pre N,
    sourceHorizontalEulerWoldJordanSelectedPhysicalAction_eq_landing c N,
    sourceHorizontalEulerWoldJordanSelectedRegulator_eq_landing c N,
    sourceHorizontalEulerWoldJordanSelected_reconstruct c N,
    sourceHorizontalEulerWoldJordanSelectedBundle_bv c q N,
    sourceHorizontalEulerWoldJordanSelectedBundle_actualFiber_sum c q N,
    tendsto_sourceHorizontalEulerWoldJordanPreCompressionVariation,
    tendsto_sourceHorizontalEulerWoldJordanPostCompressionVariation_zero,
    tendsto_sourceHorizontalEulerWoldJordanSelectedPhysicalAction c,
    tendsto_sourceHorizontalEulerWoldJordanSelectedRegulator c,
    eventually_sourceHorizontalEulerWoldJordanSelectedBudget_lt_sourceBudget⟩

end

end RHTower

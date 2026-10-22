import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedPhaseProjectiveGaugeSummableKernel
import GaloisForLFunctions.HTGeometry.SchattenOneBanach
import GaloisForLFunctions.RHTower.NuclearRankOneSchatten

open Complex
open scoped ComplexConjugate InnerProductSpace

noncomputable section
namespace RHTower

abbrev CCMActualHeadMatchedPhaseProjectiveGaugeL2 :=
  lp (fun _ : ℕ => ℂ) 2

def ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode :
    CCMActualHeadMatchedPhaseProjectiveGaugeIndex → ℕ
  | .weightAnchor => 0
  | .sourceAnchor => 1
  | .atom n => n + 2

theorem ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode_injective :
    Function.Injective ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode := by
  intro a b h
  cases a <;> cases b
  all_goals simp [ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode] at h ⊢
  omega

def ccmActualHeadMatchedPhaseProjectiveGaugeWeightCoefficient (k : ℕ) : ℂ :=
  if k = 0 then 1
  else if k = 1 then 0
  else ccmActualHeadMatchedPhaseProjectiveGauge (k - 2)

def ccmActualHeadMatchedPhaseProjectiveGaugeSourceCoefficient
    (xi : ℝ) (k : ℕ) : ℂ :=
  if k = 0 then 0
  else if k = 1 then 1
  else ccmActualHeadMatchedPhaseProjectiveGauge (k - 2) *
    (ccmActualHeadMatchedOrientedPhaseSymbol (k - 2) xi).re

@[simp] theorem ccmActualHeadMatchedPhaseProjectiveGaugeWeightCoefficient_indexCode
    (a : CCMActualHeadMatchedPhaseProjectiveGaugeIndex) :
    ccmActualHeadMatchedPhaseProjectiveGaugeWeightCoefficient
        (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode a) =
      ccmActualHeadMatchedPhaseProjectiveGaugeWeightFeature a := by
  cases a <;> simp [ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode,
    ccmActualHeadMatchedPhaseProjectiveGaugeWeightCoefficient,
    ccmActualHeadMatchedPhaseProjectiveGaugeWeightFeature]

@[simp] theorem ccmActualHeadMatchedPhaseProjectiveGaugeSourceCoefficient_indexCode
    (xi : ℝ) (a : CCMActualHeadMatchedPhaseProjectiveGaugeIndex) :
    ccmActualHeadMatchedPhaseProjectiveGaugeSourceCoefficient xi
        (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode a) =
      ccmActualHeadMatchedPhaseProjectiveGaugeSourceFeature xi a := by
  cases a <;> simp [ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode,
    ccmActualHeadMatchedPhaseProjectiveGaugeSourceCoefficient,
    ccmActualHeadMatchedPhaseProjectiveGaugeSourceFeature]

theorem summable_norm_sq_ccmActualHeadMatchedPhaseProjectiveGaugeWeightAtom :
    Summable (fun n : ℕ =>
      ‖(ccmActualHeadMatchedPhaseProjectiveGauge n : ℂ)‖ ^ (2 : ℕ)) := by
  apply summable_criticalMellinAtomWeight_sq_div_exp_half_log.congr
  intro n
  norm_cast
  rw [Real.norm_eq_abs, sq_abs,
    ccmActualHeadMatchedPhaseProjectiveGauge_sq]

theorem summable_norm_sq_ccmActualHeadMatchedPhaseProjectiveGaugeSourceAtom
    (xi : ℝ) :
    Summable (fun n : ℕ =>
      ‖(ccmActualHeadMatchedPhaseProjectiveGauge n *
        (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re : ℂ)‖ ^ (2 : ℕ)) := by
  apply Summable.of_norm_bounded
    (summable_ccmActualHeadMatchedPhaseProjectiveGaugeArithmeticDiagonal xi)
  intro n
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  norm_cast
  rw [Real.norm_eq_abs, sq_abs,
    ccmActualHeadMatchedPhaseProjectiveGaugeArithmeticDiagonal,
    ccmActualHeadMatchedPhaseProjectiveGaugeKernel_atom_diagonal]
  exact le_add_of_nonneg_left (sq_nonneg _)

theorem summable_norm_sq_ccmActualHeadMatchedPhaseProjectiveGaugeWeightCoefficient :
    Summable (fun k : ℕ =>
      ‖ccmActualHeadMatchedPhaseProjectiveGaugeWeightCoefficient k‖ ^ (2 : ℕ)) := by
  apply (summable_nat_add_iff 2).1
  simpa [ccmActualHeadMatchedPhaseProjectiveGaugeWeightCoefficient] using
    summable_norm_sq_ccmActualHeadMatchedPhaseProjectiveGaugeWeightAtom

theorem summable_norm_sq_ccmActualHeadMatchedPhaseProjectiveGaugeSourceCoefficient
    (xi : ℝ) :
    Summable (fun k : ℕ =>
      ‖ccmActualHeadMatchedPhaseProjectiveGaugeSourceCoefficient xi k‖ ^ (2 : ℕ)) := by
  apply (summable_nat_add_iff 2).1
  simpa [ccmActualHeadMatchedPhaseProjectiveGaugeSourceCoefficient] using
    summable_norm_sq_ccmActualHeadMatchedPhaseProjectiveGaugeSourceAtom xi

def ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector :
    CCMActualHeadMatchedPhaseProjectiveGaugeL2 :=
  ⟨ccmActualHeadMatchedPhaseProjectiveGaugeWeightCoefficient,
    HilbertSchmidt.memℓp_of_sq
      summable_norm_sq_ccmActualHeadMatchedPhaseProjectiveGaugeWeightCoefficient⟩

def ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector (xi : ℝ) :
    CCMActualHeadMatchedPhaseProjectiveGaugeL2 :=
  ⟨ccmActualHeadMatchedPhaseProjectiveGaugeSourceCoefficient xi,
    HilbertSchmidt.memℓp_of_sq
      (summable_norm_sq_ccmActualHeadMatchedPhaseProjectiveGaugeSourceCoefficient xi)⟩

def ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassOperator (xi : ℝ) :
    SchattenOneOperator CCMActualHeadMatchedPhaseProjectiveGaugeL2 :=
  positiveRankOneSchattenOne
      ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector +
    positiveRankOneSchattenOne
      (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi)

theorem ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassOperator_isPositive
    (xi : ℝ) :
    ((ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassOperator xi :
      CCMActualHeadMatchedPhaseProjectiveGaugeL2 →L[ℂ]
        CCMActualHeadMatchedPhaseProjectiveGaugeL2)).IsPositive := by
  change (InnerProductSpace.rankOne ℂ
      ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector
      ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector +
    InnerProductSpace.rankOne ℂ
      (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi)
      (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi)).IsPositive
  exact (InnerProductSpace.isPositive_rankOne_self
    ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector).add
      (InnerProductSpace.isPositive_rankOne_self
        (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi))

theorem ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassOperator_hasRankLE_two
    (xi : ℝ) :
    HasRankLE
      (ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassOperator xi :
        CCMActualHeadMatchedPhaseProjectiveGaugeL2 →L[ℂ]
          CCMActualHeadMatchedPhaseProjectiveGaugeL2) 2 := by
  change HasRankLE
    (InnerProductSpace.rankOne ℂ
        ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector
        ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector +
      InnerProductSpace.rankOne ℂ
        (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi)
        (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi)) (1 + 1)
  have hweight : HasRankLE
      (InnerProductSpace.rankOne ℂ
        ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector
        ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector) 1 := by
    simpa [InnerProductSpace.rankOne_def] using
      deningerSmulRight_hasRankLE_one
        (innerSL ℂ ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector)
        ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector
  have hsource : HasRankLE
      (InnerProductSpace.rankOne ℂ
        (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi)
        (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi)) 1 := by
    simpa [InnerProductSpace.rankOne_def] using
      deningerSmulRight_hasRankLE_one
        (innerSL ℂ (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi))
        (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi)
  exact hweight.add hsource

theorem ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassOperator_matrix
    (xi : ℝ) (a b : CCMActualHeadMatchedPhaseProjectiveGaugeIndex) :
    inner ℂ
        (lp.single 2 (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode a) 1)
        ((ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassOperator xi :
          CCMActualHeadMatchedPhaseProjectiveGaugeL2 →L[ℂ]
            CCMActualHeadMatchedPhaseProjectiveGaugeL2)
          (lp.single 2
            (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode b) 1)) =
      ccmActualHeadMatchedPhaseProjectiveGaugeKernel xi a b := by
  change inner ℂ
      (lp.single 2 (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode a) 1)
      ((InnerProductSpace.rankOne ℂ
          ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector
          ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector +
        InnerProductSpace.rankOne ℂ
          (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi)
          (ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector xi))
        (lp.single 2
          (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode b) 1)) = _
  simp only [add_apply, InnerProductSpace.rankOne_apply, inner_add_right,
    inner_smul_right, lp.inner_single_left, lp.inner_single_right,
    RCLike.inner_apply, starRingEnd_apply, one_mul,
    ccmActualHeadMatchedPhaseProjectiveGaugeWeightVector,
    ccmActualHeadMatchedPhaseProjectiveGaugeSourceVector]
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeWeightCoefficient_indexCode,
    ccmActualHeadMatchedPhaseProjectiveGaugeWeightCoefficient_indexCode,
    ccmActualHeadMatchedPhaseProjectiveGaugeSourceCoefficient_indexCode,
    ccmActualHeadMatchedPhaseProjectiveGaugeSourceCoefficient_indexCode]
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeKernel]
  simp only [starRingEnd_apply, star_one, mul_one]
  ring

/-- Total nonlinear matrix-coefficient reporter of the trace-class operator. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassReporter
    (xi : ℝ) (n : ℕ) : ℝ :=
  if criticalMellinAtomWeight n = 0 then 0
  else
    (inner ℂ
      (lp.single 2
        (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode (.atom n)) 1)
      ((ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassOperator xi :
        CCMActualHeadMatchedPhaseProjectiveGaugeL2 →L[ℂ]
          CCMActualHeadMatchedPhaseProjectiveGaugeL2)
        (lp.single 2
          (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode .sourceAnchor) 1))).re /
    (inner ℂ
      (lp.single 2
        (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode (.atom n)) 1)
      ((ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassOperator xi :
        CCMActualHeadMatchedPhaseProjectiveGaugeL2 →L[ℂ]
          CCMActualHeadMatchedPhaseProjectiveGaugeL2)
        (lp.single 2
          (ccmActualHeadMatchedPhaseProjectiveGaugeIndexCode .weightAnchor) 1))).re

theorem ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassReporter_eq_kernelReporter
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassReporter xi n =
      ccmActualHeadMatchedPhaseProjectiveGaugeReporter xi n := by
  unfold ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassReporter
    ccmActualHeadMatchedPhaseProjectiveGaugeReporter
  split_ifs
  · rfl
  · rw [ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassOperator_matrix,
      ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassOperator_matrix]

/-- The nonlinear matrix reporter recovers the complete oriented source without premises. -/
theorem ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassReporter_eq
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassReporter xi n =
      (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re := by
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassReporter_eq_kernelReporter,
    ccmActualHeadMatchedPhaseProjectiveGaugeReporter_eq]

def ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassFiniteReporter
    (F : Finset ℕ) (xi : ℝ) : ℝ :=
  ∑ n ∈ F, ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassReporter xi n

theorem ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassFiniteReporter_eq
    (F : Finset ℕ) (xi : ℝ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassFiniteReporter F xi =
      (ccmActualHeadMatchedOrientedPhaseFiniteSymbol F xi).re := by
  unfold ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassFiniteReporter
    ccmActualHeadMatchedOrientedPhaseFiniteSymbol
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassReporter_eq xi n

/-- Every finite actual matched block is the spectral integral of a nonlinear reporter of one
positive rank-at-most-two Schatten-one operator. -/
theorem ccmActualHeadMatchedPrimePolarFiniteBlock_eq_projectiveGaugeTraceClassOperator
    (F : Finset ℕ) (f : SoninL2) :
    ccmActualHeadMatchedPrimePolarFiniteBlock F f =
      -2 * ∫ xi : ℝ,
        ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassFiniteReporter F xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ) := by
  rw [ccmActualHeadMatchedPrimePolarFiniteBlock_eq_orientedPhaseFiniteSymbol]
  congr 2
  funext xi
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassFiniteReporter_eq]

end RHTower

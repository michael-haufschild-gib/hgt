import GaloisForLFunctions.HTGeometry.FourierMultiplierTruncation
import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier
import GaloisForLFunctions.HTGeometry.PointedFisherCutoffWardTrace
import GaloisForLFunctions.HTGeometry.SeparableBuresPositiveReporterLaw
import GaloisForLFunctions.RHTower.NuclearRankOneSchatten
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Nuclear circle model for the CCM trace cocycle

The source proof of the archimedean trace formula invokes the diagonal of a trace-class kernel
without proving a diagonal trace theorem.  This file replaces that step by an absolutely
convergent Fourier matrix calculation.  The positive and negative Hardy crossblocks are indexed
by the two frequency quadrants.  A first absolute Fourier moment is exactly the nuclear budget:

`sum_(r,s >= 0) |b_hat(r+s+1)| = sum_(d >= 1) d |b_hat(d)|`,

and likewise at negative frequencies.  Thus every trace below is the ordinary operator trace of
an actual Schatten-one operator, not a formal diagonal integral.

This is classical trace-cocycle infrastructure and carries no novelty claim.
-/

noncomputable section

open Complex MeasureTheory
open scoped ENNReal InnerProductSpace Real

namespace RHTower

abbrev CCMCircleL2 :=
  Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))

/-- A bounded measurable circle symbol, with all analytic data intrinsic to the object. -/
structure CCMCircleBoundedSymbol where
  toFun : AddCircle (1 : ℝ) → ℂ
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  measurable : Measurable toFun
  norm_le : ∀ z, ‖toFun z‖ ≤ bound

instance : CoeFun CCMCircleBoundedSymbol (fun _ => AddCircle (1 : ℝ) → ℂ) :=
  ⟨CCMCircleBoundedSymbol.toFun⟩

/-- Circle symbols whose positive and negative first Fourier moments are absolutely summable.
This is the sharp Besov-type regularity needed by the nuclear Hardy commutator calculation. -/
structure CCMCircleTraceSymbol extends CCMCircleBoundedSymbol where
  positiveMoment : Summable fun n : ℕ =>
    ((n + 1 : ℕ) : ℝ) * ‖fourierCoeff toFun ((n + 1 : ℕ) : ℤ)‖
  negativeMoment : Summable fun n : ℕ =>
    ((n + 1 : ℕ) : ℝ) * ‖fourierCoeff toFun (-((n + 1 : ℕ) : ℤ))‖

instance : CoeFun CCMCircleTraceSymbol (fun _ => AddCircle (1 : ℝ) → ℂ) :=
  ⟨fun b => b.toFun⟩

/-- Literal bounded multiplication by a circle symbol. -/
def ccmCircleMultiplier (a : CCMCircleBoundedSymbol) :
    CCMCircleL2 →L[ℂ] CCMCircleL2 :=
  lpBoundedMulCLM (p := 2) (μ := AddCircle.haarAddCircle (T := (1 : ℝ)))
    a.measurable a.bound_nonneg a.norm_le

@[simp] theorem ccmCircleMultiplier_fourierCoeff (a : CCMCircleBoundedSymbol)
    (j l : ℤ) :
    fourierCoeff
        ((ccmCircleMultiplier a (fourierLp (T := (1 : ℝ)) 2 j) : CCMCircleL2) :
          AddCircle (1 : ℝ) → ℂ) l =
      fourierCoeff a.toFun (l - j) := by
  exact GaloisForLFunctions.fourierCoeff_lpBoundedMulCLM_fourierLp
    a.measurable a.bound_nonneg a.norm_le j l

private theorem inner_fourierLp_ccmCircleMultiplier_fourierLp
    (a : CCMCircleBoundedSymbol) (j l : ℤ) :
    inner ℂ (fourierLp (T := (1 : ℝ)) 2 l : CCMCircleL2)
        (ccmCircleMultiplier a
          (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2)) =
      fourierCoeff a.toFun (l - j) := by
  rw [GaloisForLFunctions.inner_fourierLp_eq_fourierCoeff,
    ccmCircleMultiplier_fourierCoeff]

/-! ## Literal circle Hardy projection -/

/-- Fourier-side indicator of the nonnegative frequencies. -/
def ccmCircleHardyIndicator (n : ℤ) : ℂ := if 0 ≤ n then 1 else 0

theorem norm_ccmCircleHardyIndicator_le_one (n : ℤ) :
    ‖ccmCircleHardyIndicator n‖ ≤ 1 := by
  by_cases hn : 0 ≤ n <;> simp [ccmCircleHardyIndicator, hn]

/-- Literal nonnegative-frequency Hardy projection on circle `L²`. -/
def ccmCircleHardyProjection : CCMCircleL2 →L[ℂ] CCMCircleL2 :=
  conjugateOperator
    (fourierBasis (T := (1 : ℝ))).repr.toContinuousLinearEquiv
    (GaloisForLFunctions.lpDiagonalCLM ccmCircleHardyIndicator zero_le_one
      norm_ccmCircleHardyIndicator_le_one)

@[simp] theorem ccmCircleHardyProjection_fourierLp (j : ℤ) :
    ccmCircleHardyProjection (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2) =
      if 0 ≤ j then fourierLp (T := (1 : ℝ)) 2 j else 0 := by
  have hbasis : (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2) =
      (fourierBasis (T := (1 : ℝ))) j := by rw [coe_fourierBasis]
  rw [hbasis, ccmCircleHardyProjection, conjugateOperator]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [HilbertBasis.repr_self, GaloisForLFunctions.lpDiagonalCLM_single]
  by_cases hj : 0 ≤ j
  · rw [if_pos hj, ccmCircleHardyIndicator, if_pos hj]
    simp
  · rw [if_neg hj, ccmCircleHardyIndicator, if_neg hj]
    simp

theorem ccmCircleHardyProjection_idempotent :
    IsIdempotentElem ccmCircleHardyProjection := by
  rw [isIdempotentElem_iff]
  have hdense : Dense ((Submodule.span ℂ (Set.range
      (fourierBasis (T := (1 : ℝ))))) : Set CCMCircleL2) := by
    rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
      (fourierBasis (T := (1 : ℝ))).dense_span]
    rfl
  apply ContinuousLinearMap.ext_on hdense
  rintro _ ⟨j, rfl⟩
  rw [coe_fourierBasis]
  simp only [mul_apply_eq_comp]
  by_cases hj : 0 ≤ j <;> simp [hj]

theorem inner_fourierLp_ccmCircleHardyProjection (l : ℤ) (v : CCMCircleL2) :
    inner ℂ (fourierLp (T := (1 : ℝ)) 2 l : CCMCircleL2)
        (ccmCircleHardyProjection v) =
      if 0 ≤ l then
        inner ℂ (fourierLp (T := (1 : ℝ)) 2 l : CCMCircleL2) v
      else 0 := by
  have hb : (fourierLp (T := (1 : ℝ)) 2 l : CCMCircleL2) =
      (fourierBasis (T := (1 : ℝ))) l := by rw [coe_fourierBasis]
  rw [hb]
  calc
    inner ℂ ((fourierBasis (T := (1 : ℝ))) l)
        (ccmCircleHardyProjection v) =
        (fourierBasis (T := (1 : ℝ))).repr
          (ccmCircleHardyProjection v) l :=
      ((fourierBasis (T := (1 : ℝ))).repr_apply_apply _ _).symm
    _ = GaloisForLFunctions.lpDiagonalCLM ccmCircleHardyIndicator zero_le_one
        norm_ccmCircleHardyIndicator_le_one
        ((fourierBasis (T := (1 : ℝ))).repr v) l := by
      unfold ccmCircleHardyProjection conjugateOperator
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
      exact congrArg (fun w : lp (fun _ : ℤ => ℂ) 2 => w l)
        ((fourierBasis (T := (1 : ℝ))).repr.apply_symm_apply
          (GaloisForLFunctions.lpDiagonalCLM ccmCircleHardyIndicator zero_le_one
            norm_ccmCircleHardyIndicator_le_one
            ((fourierBasis (T := (1 : ℝ))).repr v)))
    _ = ccmCircleHardyIndicator l *
        (fourierBasis (T := (1 : ℝ))).repr v l := rfl
    _ = if 0 ≤ l then inner ℂ ((fourierBasis (T := (1 : ℝ))) l) v else 0 := by
      rw [(fourierBasis (T := (1 : ℝ))).repr_apply_apply]
      by_cases hl : 0 ≤ l <;> simp [ccmCircleHardyIndicator, hl]

/-- Literal circle quantized differential `2[Q,M_b]`. -/
def ccmCircleQuantizedDifferential (b : CCMCircleTraceSymbol) :
    CCMCircleL2 →L[ℂ] CCMCircleL2 :=
  (2 : ℂ) •
    (ccmCircleHardyProjection * ccmCircleMultiplier b.toCCMCircleBoundedSymbol -
      ccmCircleMultiplier b.toCCMCircleBoundedSymbol * ccmCircleHardyProjection)

/-- Literal positive-to-negative Hardy crossblock on circle `L²`. -/
def ccmCircleUpperCrossBlock (b : CCMCircleTraceSymbol) :
    CCMCircleL2 →L[ℂ] CCMCircleL2 :=
  ccmCircleHardyProjection * ccmCircleMultiplier b.toCCMCircleBoundedSymbol *
    (1 - ccmCircleHardyProjection)

/-- Literal negative-to-positive Hardy crossblock on circle `L²`. -/
def ccmCircleLowerCrossBlock (b : CCMCircleTraceSymbol) :
    CCMCircleL2 →L[ℂ] CCMCircleL2 :=
  (1 - ccmCircleHardyProjection) * ccmCircleMultiplier b.toCCMCircleBoundedSymbol *
    ccmCircleHardyProjection

theorem inner_fourierLp_one_sub_ccmCircleHardyProjection (l : ℤ) (v : CCMCircleL2) :
    inner ℂ (fourierLp (T := (1 : ℝ)) 2 l : CCMCircleL2)
        ((1 - ccmCircleHardyProjection) v) =
      if l < 0 then
        inner ℂ (fourierLp (T := (1 : ℝ)) 2 l : CCMCircleL2) v
      else 0 := by
  rw [sub_apply, one_apply_eq_self, inner_sub_right,
    inner_fourierLp_ccmCircleHardyProjection]
  by_cases hl : l < 0
  · have hln : ¬0 ≤ l := not_le.mpr hl
    rw [if_pos hl, if_neg hln, sub_zero]
  · have hln : 0 ≤ l := le_of_not_gt hl
    rw [if_neg hl, if_pos hln, sub_self]

theorem inner_fourierLp_ccmCircleUpperCrossBlock
    (b : CCMCircleTraceSymbol) (l j : ℤ) :
    inner ℂ (fourierLp (T := (1 : ℝ)) 2 l : CCMCircleL2)
        (ccmCircleUpperCrossBlock b
          (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2)) =
      if 0 ≤ l ∧ j < 0 then fourierCoeff b.toFun (l - j) else 0 := by
  change inner ℂ (fourierLp (T := (1 : ℝ)) 2 l : CCMCircleL2)
    (ccmCircleHardyProjection
      (ccmCircleMultiplier b.toCCMCircleBoundedSymbol
        ((1 - ccmCircleHardyProjection)
          (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2)))) = _
  rw [inner_fourierLp_ccmCircleHardyProjection]
  by_cases hl : 0 ≤ l
  · rw [if_pos hl]
    by_cases hj : 0 ≤ j
    · rw [show (1 - ccmCircleHardyProjection)
          (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2) = 0 by
          simp [ccmCircleHardyProjection_fourierLp, hj]]
      simp [hj]
    · have hjlt : j < 0 := lt_of_not_ge hj
      rw [show (1 - ccmCircleHardyProjection)
          (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2) =
            (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2) by
          simp [ccmCircleHardyProjection_fourierLp, hj]]
      rw [inner_fourierLp_ccmCircleMultiplier_fourierLp, if_pos ⟨hl, hjlt⟩]
  · rw [if_neg hl, if_neg (fun h => hl h.1)]

theorem inner_fourierLp_ccmCircleLowerCrossBlock
    (b : CCMCircleTraceSymbol) (l j : ℤ) :
    inner ℂ (fourierLp (T := (1 : ℝ)) 2 l : CCMCircleL2)
        (ccmCircleLowerCrossBlock b
          (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2)) =
      if l < 0 ∧ 0 ≤ j then fourierCoeff b.toFun (l - j) else 0 := by
  change inner ℂ (fourierLp (T := (1 : ℝ)) 2 l : CCMCircleL2)
    ((1 - ccmCircleHardyProjection)
      (ccmCircleMultiplier b.toCCMCircleBoundedSymbol
        (ccmCircleHardyProjection
          (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2)))) = _
  rw [inner_fourierLp_one_sub_ccmCircleHardyProjection]
  by_cases hl : l < 0
  · rw [if_pos hl]
    by_cases hj : 0 ≤ j
    · rw [ccmCircleHardyProjection_fourierLp, if_pos hj,
        inner_fourierLp_ccmCircleMultiplier_fourierLp, if_pos ⟨hl, hj⟩]
    · rw [ccmCircleHardyProjection_fourierLp, if_neg hj]
      simp [hj]
  · rw [if_neg hl, if_neg (fun h => hl h.1)]

/-! ## The two nuclear crossblocks -/

/-- Positive Hardy row belonging to the quadrant index `(r,s)`. -/
def ccmCirclePositiveRow (p : ℕ × ℕ) : ℤ := (p.1 : ℤ)

/-- Negative Hardy column belonging to the quadrant index `(r,s)`. -/
def ccmCircleNegativeColumn (p : ℕ × ℕ) : ℤ := -((p.2 + 1 : ℕ) : ℤ)

/-- Strictly positive frequency difference attached to a quadrant index. -/
def ccmCircleCrossFrequency (p : ℕ × ℕ) : ℤ :=
  ((p.1 + p.2 + 1 : ℕ) : ℤ)

theorem ccmCirclePositiveRow_sub_negativeColumn (p : ℕ × ℕ) :
    ccmCirclePositiveRow p - ccmCircleNegativeColumn p =
      ccmCircleCrossFrequency p := by
  simp [ccmCirclePositiveRow, ccmCircleNegativeColumn, ccmCircleCrossFrequency]
  omega

/-- One positive-to-negative Fourier matrix unit, bundled in the Schatten-one Banach carrier. -/
def ccmCircleUpperNuclearTerm (b : CCMCircleTraceSymbol) (p : ℕ × ℕ) :
    SchattenOneOperator CCMCircleL2 :=
  fourierCoeff b.toFun (ccmCircleCrossFrequency p) •
    rankOneSchattenOne
      (fourierLp (T := (1 : ℝ)) 2 (ccmCirclePositiveRow p) : CCMCircleL2)
      (fourierLp (T := (1 : ℝ)) 2 (ccmCircleNegativeColumn p) : CCMCircleL2)

/-- One negative-to-positive Fourier matrix unit. -/
def ccmCircleLowerNuclearTerm (b : CCMCircleTraceSymbol) (p : ℕ × ℕ) :
    SchattenOneOperator CCMCircleL2 :=
  fourierCoeff b.toFun (-ccmCircleCrossFrequency p) •
    rankOneSchattenOne
      (fourierLp (T := (1 : ℝ)) 2 (ccmCircleNegativeColumn p) : CCMCircleL2)
      (fourierLp (T := (1 : ℝ)) 2 (ccmCirclePositiveRow p) : CCMCircleL2)

@[simp] theorem norm_ccmCircleUpperNuclearTerm (b : CCMCircleTraceSymbol)
    (p : ℕ × ℕ) :
    ‖ccmCircleUpperNuclearTerm b p‖ =
      ‖fourierCoeff b.toFun (ccmCircleCrossFrequency p)‖ := by
  rw [ccmCircleUpperNuclearTerm, norm_smul, norm_rankOneSchattenOne,
    GaloisForLFunctions.norm_fourierLp_eq_one,
    GaloisForLFunctions.norm_fourierLp_eq_one]
  ring

@[simp] theorem norm_ccmCircleLowerNuclearTerm (b : CCMCircleTraceSymbol)
    (p : ℕ × ℕ) :
    ‖ccmCircleLowerNuclearTerm b p‖ =
      ‖fourierCoeff b.toFun (-ccmCircleCrossFrequency p)‖ := by
  rw [ccmCircleLowerNuclearTerm, norm_smul, norm_rankOneSchattenOne,
    GaloisForLFunctions.norm_fourierLp_eq_one,
    GaloisForLFunctions.norm_fourierLp_eq_one]
  ring

private theorem summable_cross_quadrant_of_moment
    (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n)
    (haMoment : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) * a n) :
    Summable fun p : ℕ × ℕ => a (p.1 + p.2) := by
  have ha : Summable a := by
    refine Summable.of_nonneg_of_le ha0 (fun n => ?_) haMoment
    have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by norm_num
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hn (ha0 n)
  have htails : Summable fun n : ℕ => ∑' k : ℕ, a (k + n) :=
    summable_tsum_nat_add_of_summable_succ_mul a ha0 haMoment
  rw [summable_prod_of_nonneg (fun p => ha0 (p.1 + p.2))]
  constructor
  · intro n
    simpa [add_comm] using (summable_nat_add_iff n).2 ha
  · simpa [add_comm] using htails

theorem summable_ccmCircleUpperNuclearTerm (b : CCMCircleTraceSymbol) :
    Summable (ccmCircleUpperNuclearTerm b) := by
  apply Summable.of_norm
  simp_rw [norm_ccmCircleUpperNuclearTerm, ccmCircleCrossFrequency]
  exact summable_cross_quadrant_of_moment
    (fun n => ‖fourierCoeff b.toFun ((n + 1 : ℕ) : ℤ)‖)
    (fun _ => norm_nonneg _) b.positiveMoment

theorem summable_ccmCircleLowerNuclearTerm (b : CCMCircleTraceSymbol) :
    Summable (ccmCircleLowerNuclearTerm b) := by
  apply Summable.of_norm
  simp_rw [norm_ccmCircleLowerNuclearTerm, ccmCircleCrossFrequency]
  exact summable_cross_quadrant_of_moment
    (fun n => ‖fourierCoeff b.toFun (-((n + 1 : ℕ) : ℤ))‖)
    (fun _ => norm_nonneg _) b.negativeMoment

/-- Actual Schatten-one sum of the positive-to-negative crossblock matrix. -/
def ccmCircleUpperNuclearBlock (b : CCMCircleTraceSymbol) :
    SchattenOneOperator CCMCircleL2 :=
  ∑' p : ℕ × ℕ, ccmCircleUpperNuclearTerm b p

/-- Actual Schatten-one sum of the negative-to-positive crossblock matrix. -/
def ccmCircleLowerNuclearBlock (b : CCMCircleTraceSymbol) :
    SchattenOneOperator CCMCircleL2 :=
  ∑' p : ℕ × ℕ, ccmCircleLowerNuclearTerm b p

/-- The nuclear circle quantized differential `2(U-L)`. -/
def ccmCircleNuclearQuantizedDifferential (b : CCMCircleTraceSymbol) :
    SchattenOneOperator CCMCircleL2 :=
  (2 : ℂ) • (ccmCircleUpperNuclearBlock b - ccmCircleLowerNuclearBlock b)

private theorem schattenOneTracePairing_rankOne
    (A : CCMCircleL2 →L[ℂ] CCMCircleL2) (c : ℂ) (x y : CCMCircleL2) :
    schattenOneTracePairingCLM A (c • rankOneSchattenOne x y) =
      c * inner ℂ y (A x) := by
  rw [map_smul, schattenOneTracePairingCLM_apply,
    rankOneSchattenOne_coe, InnerProductSpace.rankOne_comp,
    GaloisForLFunctions.HTGeometry.opTrace_rankOne,
    ContinuousLinearMap.adjoint_inner_left]
  simp only [smul_eq_mul]

/-! ## Identification with the literal Hardy crossblocks -/

private def ccmCircleMatrixReporter (l j : ℤ) :
    CCMCircleL2 →L[ℂ] CCMCircleL2 :=
  InnerProductSpace.rankOne ℂ
    (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2)
    (fourierLp (T := (1 : ℝ)) 2 l : CCMCircleL2)

private theorem schattenOneTracePairing_matrixReporter
    (T : SchattenOneOperator CCMCircleL2) (l j : ℤ) :
    schattenOneTracePairingCLM (ccmCircleMatrixReporter l j) T =
      inner ℂ (fourierLp (T := (1 : ℝ)) 2 l : CCMCircleL2)
        ((T : CCMCircleL2 →L[ℂ] CCMCircleL2)
          (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2)) := by
  rw [schattenOneTracePairingCLM_apply, ccmCircleMatrixReporter,
    InnerProductSpace.comp_rankOne,
    GaloisForLFunctions.HTGeometry.opTrace_rankOne]

private theorem schattenOneTracePairing_matrixReporter_upperTerm
    (b : CCMCircleTraceSymbol) (p : ℕ × ℕ) (l j : ℤ) :
    schattenOneTracePairingCLM (ccmCircleMatrixReporter l j)
        (ccmCircleUpperNuclearTerm b p) =
      fourierCoeff b.toFun (ccmCircleCrossFrequency p) *
        (if ccmCircleNegativeColumn p = j then 1 else 0) *
        (if l = ccmCirclePositiveRow p then 1 else 0) := by
  rw [ccmCircleUpperNuclearTerm, schattenOneTracePairing_rankOne]
  simp only [ccmCircleMatrixReporter, InnerProductSpace.rankOne_apply,
    inner_smul_right]
  rw [GaloisForLFunctions.inner_fourierLp_fourierLp,
    GaloisForLFunctions.inner_fourierLp_fourierLp]
  split_ifs <;> simp_all

private theorem schattenOneTracePairing_matrixReporter_lowerTerm
    (b : CCMCircleTraceSymbol) (p : ℕ × ℕ) (l j : ℤ) :
    schattenOneTracePairingCLM (ccmCircleMatrixReporter l j)
        (ccmCircleLowerNuclearTerm b p) =
      fourierCoeff b.toFun (-ccmCircleCrossFrequency p) *
        (if ccmCirclePositiveRow p = j then 1 else 0) *
        (if l = ccmCircleNegativeColumn p then 1 else 0) := by
  rw [ccmCircleLowerNuclearTerm, schattenOneTracePairing_rankOne]
  simp only [ccmCircleMatrixReporter, InnerProductSpace.rankOne_apply,
    inner_smul_right]
  rw [GaloisForLFunctions.inner_fourierLp_fourierLp,
    GaloisForLFunctions.inner_fourierLp_fourierLp]
  split_ifs <;> simp_all

private theorem exists_unique_ccmCircleUpperIndex (l j : ℤ) (hl : 0 ≤ l) (hj : j < 0) :
    ∃! p : ℕ × ℕ,
      ccmCirclePositiveRow p = l ∧ ccmCircleNegativeColumn p = j := by
  let p : ℕ × ℕ := (l.toNat, (-j - 1).toNat)
  have hsub : 0 ≤ -j - 1 := by omega
  have hp : ccmCirclePositiveRow p = l ∧ ccmCircleNegativeColumn p = j := by
    constructor
    · simp [p, ccmCirclePositiveRow, Int.toNat_of_nonneg hl]
    · simp [p, ccmCircleNegativeColumn]
      omega
  refine ⟨p, hp, fun q hq => ?_⟩
  apply Prod.ext
  · have := hq.1.trans hp.1.symm
    simp only [ccmCirclePositiveRow] at this
    exact_mod_cast this
  · have := hq.2.trans hp.2.symm
    simp [ccmCircleNegativeColumn] at this
    omega

private theorem exists_unique_ccmCircleLowerIndex (l j : ℤ) (hl : l < 0) (hj : 0 ≤ j) :
    ∃! p : ℕ × ℕ,
      ccmCircleNegativeColumn p = l ∧ ccmCirclePositiveRow p = j := by
  obtain ⟨p, hp, huniq⟩ := exists_unique_ccmCircleUpperIndex j l hj hl
  exact ⟨p, hp.symm, fun q hq => huniq q hq.symm⟩

theorem schattenOneTracePairing_matrixReporter_upperBlock
    (b : CCMCircleTraceSymbol) (l j : ℤ) :
    schattenOneTracePairingCLM (ccmCircleMatrixReporter l j)
        (ccmCircleUpperNuclearBlock b) =
      if 0 ≤ l ∧ j < 0 then fourierCoeff b.toFun (l - j) else 0 := by
  rw [ccmCircleUpperNuclearBlock,
    (schattenOneTracePairingCLM (ccmCircleMatrixReporter l j)).map_tsum
      (summable_ccmCircleUpperNuclearTerm b)]
  simp_rw [schattenOneTracePairing_matrixReporter_upperTerm]
  by_cases hcross : 0 ≤ l ∧ j < 0
  · rw [if_pos hcross]
    obtain ⟨p, hp, huniq⟩ :=
      exists_unique_ccmCircleUpperIndex l j hcross.1 hcross.2
    rw [tsum_eq_single p]
    · rw [if_pos hp.2, if_pos hp.1.symm, mul_one, mul_one,
        ← ccmCirclePositiveRow_sub_negativeColumn p, hp.1, hp.2]
    · intro q hqp
      by_cases hc : ccmCircleNegativeColumn q = j
      · by_cases hr : l = ccmCirclePositiveRow q
        · exact (hqp (huniq q ⟨hr.symm, hc⟩)).elim
        · simp [hc, hr]
      · simp [hc]
  · rw [if_neg hcross]
    have hzero : (fun p : ℕ × ℕ =>
        fourierCoeff b.toFun (ccmCircleCrossFrequency p) *
          (if ccmCircleNegativeColumn p = j then 1 else 0) *
          (if l = ccmCirclePositiveRow p then 1 else 0)) = 0 := by
      funext p
      by_cases hc : ccmCircleNegativeColumn p = j
      · by_cases hr : l = ccmCirclePositiveRow p
        · exfalso
          apply hcross
          constructor
          · rw [hr]
            simp [ccmCirclePositiveRow]
          · rw [← hc]
            simp [ccmCircleNegativeColumn]
            omega
        · simp [hc, hr]
      · simp [hc]
    rw [hzero]
    change (∑' _p : ℕ × ℕ, (0 : ℂ)) = 0
    exact tsum_zero

theorem schattenOneTracePairing_matrixReporter_lowerBlock
    (b : CCMCircleTraceSymbol) (l j : ℤ) :
    schattenOneTracePairingCLM (ccmCircleMatrixReporter l j)
        (ccmCircleLowerNuclearBlock b) =
      if l < 0 ∧ 0 ≤ j then fourierCoeff b.toFun (l - j) else 0 := by
  rw [ccmCircleLowerNuclearBlock,
    (schattenOneTracePairingCLM (ccmCircleMatrixReporter l j)).map_tsum
      (summable_ccmCircleLowerNuclearTerm b)]
  simp_rw [schattenOneTracePairing_matrixReporter_lowerTerm]
  by_cases hcross : l < 0 ∧ 0 ≤ j
  · rw [if_pos hcross]
    obtain ⟨p, hp, huniq⟩ :=
      exists_unique_ccmCircleLowerIndex l j hcross.1 hcross.2
    rw [tsum_eq_single p]
    · rw [if_pos hp.2, if_pos hp.1.symm, mul_one, mul_one]
      congr 1
      rw [← ccmCirclePositiveRow_sub_negativeColumn p, hp.1, hp.2]
      ring
    · intro q hqp
      by_cases hc : ccmCirclePositiveRow q = j
      · by_cases hr : l = ccmCircleNegativeColumn q
        · exact (hqp (huniq q ⟨hr.symm, hc⟩)).elim
        · simp [hc, hr]
      · simp [hc]
  · rw [if_neg hcross]
    have hzero : (fun p : ℕ × ℕ =>
        fourierCoeff b.toFun (-ccmCircleCrossFrequency p) *
          (if ccmCirclePositiveRow p = j then 1 else 0) *
          (if l = ccmCircleNegativeColumn p then 1 else 0)) = 0 := by
      funext p
      by_cases hc : ccmCirclePositiveRow p = j
      · by_cases hr : l = ccmCircleNegativeColumn p
        · exfalso
          apply hcross
          constructor
          · rw [hr]
            simp [ccmCircleNegativeColumn]
            omega
          · rw [← hc]
            simp [ccmCirclePositiveRow]
        · simp [hc, hr]
      · simp [hc]
    rw [hzero]
    change (∑' _p : ℕ × ℕ, (0 : ℂ)) = 0
    exact tsum_zero

theorem inner_fourierLp_ccmCircleUpperNuclearBlock
    (b : CCMCircleTraceSymbol) (l j : ℤ) :
    inner ℂ (fourierLp (T := (1 : ℝ)) 2 l : CCMCircleL2)
        ((ccmCircleUpperNuclearBlock b : CCMCircleL2 →L[ℂ] CCMCircleL2)
          (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2)) =
      if 0 ≤ l ∧ j < 0 then fourierCoeff b.toFun (l - j) else 0 := by
  rw [← schattenOneTracePairing_matrixReporter]
  exact schattenOneTracePairing_matrixReporter_upperBlock b l j

theorem inner_fourierLp_ccmCircleLowerNuclearBlock
    (b : CCMCircleTraceSymbol) (l j : ℤ) :
    inner ℂ (fourierLp (T := (1 : ℝ)) 2 l : CCMCircleL2)
        ((ccmCircleLowerNuclearBlock b : CCMCircleL2 →L[ℂ] CCMCircleL2)
          (fourierLp (T := (1 : ℝ)) 2 j : CCMCircleL2)) =
      if l < 0 ∧ 0 ≤ j then fourierCoeff b.toFun (l - j) else 0 := by
  rw [← schattenOneTracePairing_matrixReporter]
  exact schattenOneTracePairing_matrixReporter_lowerBlock b l j

private theorem dense_span_ccmCircleFourierBasis :
    Dense ((Submodule.span ℂ (Set.range
      (fourierBasis (T := (1 : ℝ))))) : Set CCMCircleL2) := by
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
    (fourierBasis (T := (1 : ℝ))).dense_span]
  rfl

/-- The absolutely convergent nuclear upper matrix is the literal Hardy upper crossblock. -/
theorem ccmCircleUpperNuclearBlock_coe_eq_crossBlock (b : CCMCircleTraceSymbol) :
    (ccmCircleUpperNuclearBlock b : CCMCircleL2 →L[ℂ] CCMCircleL2) =
      ccmCircleUpperCrossBlock b := by
  apply ContinuousLinearMap.ext_on dense_span_ccmCircleFourierBasis
  rintro _ ⟨j, rfl⟩
  rw [coe_fourierBasis]
  apply (fourierBasis (T := (1 : ℝ))).repr.injective
  ext l
  rw [(fourierBasis (T := (1 : ℝ))).repr_apply_apply,
    (fourierBasis (T := (1 : ℝ))).repr_apply_apply, coe_fourierBasis]
  exact (inner_fourierLp_ccmCircleUpperNuclearBlock b l j).trans
    (inner_fourierLp_ccmCircleUpperCrossBlock b l j).symm

/-- The absolutely convergent nuclear lower matrix is the literal Hardy lower crossblock. -/
theorem ccmCircleLowerNuclearBlock_coe_eq_crossBlock (b : CCMCircleTraceSymbol) :
    (ccmCircleLowerNuclearBlock b : CCMCircleL2 →L[ℂ] CCMCircleL2) =
      ccmCircleLowerCrossBlock b := by
  apply ContinuousLinearMap.ext_on dense_span_ccmCircleFourierBasis
  rintro _ ⟨j, rfl⟩
  rw [coe_fourierBasis]
  apply (fourierBasis (T := (1 : ℝ))).repr.injective
  ext l
  rw [(fourierBasis (T := (1 : ℝ))).repr_apply_apply,
    (fourierBasis (T := (1 : ℝ))).repr_apply_apply, coe_fourierBasis]
  exact (inner_fourierLp_ccmCircleLowerNuclearBlock b l j).trans
    (inner_fourierLp_ccmCircleLowerCrossBlock b l j).symm

/-- The nuclear Schatten-one differential is exactly the literal circle commutator. -/
theorem ccmCircleNuclearQuantizedDifferential_coe_eq_quantizedDifferential
    (b : CCMCircleTraceSymbol) :
    (ccmCircleNuclearQuantizedDifferential b : CCMCircleL2 →L[ℂ] CCMCircleL2) =
      ccmCircleQuantizedDifferential b := by
  rw [ccmCircleNuclearQuantizedDifferential, SchattenOneOperator.coe_smul,
    SchattenOneOperator.coe_sub,
    ccmCircleUpperNuclearBlock_coe_eq_crossBlock,
    ccmCircleLowerNuclearBlock_coe_eq_crossBlock]
  unfold ccmCircleQuantizedDifferential ccmCircleUpperCrossBlock ccmCircleLowerCrossBlock
  noncomm_ring

/-! ## Exact ordinary traces of the nuclear blocks -/

theorem schattenOneTracePairing_ccmCircleUpperNuclearTerm
    (a : CCMCircleBoundedSymbol) (b : CCMCircleTraceSymbol) (p : ℕ × ℕ) :
    schattenOneTracePairingCLM (ccmCircleMultiplier a)
        (ccmCircleUpperNuclearTerm b p) =
      fourierCoeff b.toFun (ccmCircleCrossFrequency p) *
        fourierCoeff a.toFun (-ccmCircleCrossFrequency p) := by
  rw [ccmCircleUpperNuclearTerm, schattenOneTracePairing_rankOne,
    inner_fourierLp_ccmCircleMultiplier_fourierLp]
  congr 2
  simp [ccmCirclePositiveRow, ccmCircleNegativeColumn, ccmCircleCrossFrequency]
  omega

theorem schattenOneTracePairing_ccmCircleLowerNuclearTerm
    (a : CCMCircleBoundedSymbol) (b : CCMCircleTraceSymbol) (p : ℕ × ℕ) :
    schattenOneTracePairingCLM (ccmCircleMultiplier a)
        (ccmCircleLowerNuclearTerm b p) =
      fourierCoeff b.toFun (-ccmCircleCrossFrequency p) *
        fourierCoeff a.toFun (ccmCircleCrossFrequency p) := by
  rw [ccmCircleLowerNuclearTerm, schattenOneTracePairing_rankOne,
    inner_fourierLp_ccmCircleMultiplier_fourierLp]
  congr 2

/-- Exact tested trace of the actual nuclear circle quantized differential.  The right side is an
absolutely convergent double Fourier series over the two crossing Hardy quadrants. -/
theorem opTrace_ccmCircleMultiplier_mul_nuclearQuantizedDifferential
    (a : CCMCircleBoundedSymbol) (b : CCMCircleTraceSymbol) :
    ContinuousLinearMap.opTrace
        (ccmCircleMultiplier a *
          (ccmCircleNuclearQuantizedDifferential b : CCMCircleL2 →L[ℂ] CCMCircleL2)) =
      (2 : ℂ) *
        ((∑' p : ℕ × ℕ,
            fourierCoeff b.toFun (ccmCircleCrossFrequency p) *
              fourierCoeff a.toFun (-ccmCircleCrossFrequency p)) -
          ∑' p : ℕ × ℕ,
            fourierCoeff b.toFun (-ccmCircleCrossFrequency p) *
              fourierCoeff a.toFun (ccmCircleCrossFrequency p)) := by
  let A := ccmCircleMultiplier a
  let U := ccmCircleUpperNuclearBlock b
  let L := ccmCircleLowerNuclearBlock b
  have hU := summable_ccmCircleUpperNuclearTerm b
  have hL := summable_ccmCircleLowerNuclearTerm b
  have htraceU : schattenOneTracePairingCLM A U =
      ∑' p : ℕ × ℕ,
        fourierCoeff b.toFun (ccmCircleCrossFrequency p) *
          fourierCoeff a.toFun (-ccmCircleCrossFrequency p) := by
    change schattenOneTracePairingCLM A (ccmCircleUpperNuclearBlock b) = _
    rw [ccmCircleUpperNuclearBlock,
      (schattenOneTracePairingCLM A).map_tsum hU]
    exact tsum_congr fun p =>
      schattenOneTracePairing_ccmCircleUpperNuclearTerm a b p
  have htraceL : schattenOneTracePairingCLM A L =
      ∑' p : ℕ × ℕ,
        fourierCoeff b.toFun (-ccmCircleCrossFrequency p) *
          fourierCoeff a.toFun (ccmCircleCrossFrequency p) := by
    change schattenOneTracePairingCLM A (ccmCircleLowerNuclearBlock b) = _
    rw [ccmCircleLowerNuclearBlock,
      (schattenOneTracePairingCLM A).map_tsum hL]
    exact tsum_congr fun p =>
      schattenOneTracePairing_ccmCircleLowerNuclearTerm a b p
  have hmem : MemSchattenClass 1
      (ccmCircleNuclearQuantizedDifferential b : CCMCircleL2 →L[ℂ] CCMCircleL2) :=
    (ccmCircleNuclearQuantizedDifferential b).property
  have hcyc := hmem.one_opTrace_comp_comm A
  change ContinuousLinearMap.opTrace
      (A * (ccmCircleNuclearQuantizedDifferential b : CCMCircleL2 →L[ℂ] CCMCircleL2)) = _
  rw [show ContinuousLinearMap.opTrace
        (A * (ccmCircleNuclearQuantizedDifferential b : CCMCircleL2 →L[ℂ] CCMCircleL2)) =
      ContinuousLinearMap.opTrace
        ((ccmCircleNuclearQuantizedDifferential b : CCMCircleL2 →L[ℂ] CCMCircleL2) * A) by
      simpa only [ContinuousLinearMap.mul_def] using hcyc]
  change schattenOneTracePairingCLM A (ccmCircleNuclearQuantizedDifferential b) = _
  rw [ccmCircleNuclearQuantizedDifferential, map_smul, map_sub,
    show ccmCircleUpperNuclearBlock b = U from rfl,
    show ccmCircleLowerNuclearBlock b = L from rfl,
    htraceU, htraceL]
  simp only [smul_eq_mul]

/-- Exact tested trace of the literal circle Hardy commutator.  This is the rigorous replacement
for the source's unproved appeal to the integral of the kernel diagonal. -/
theorem opTrace_ccmCircleMultiplier_mul_quantizedDifferential_doubleSeries
    (a : CCMCircleBoundedSymbol) (b : CCMCircleTraceSymbol) :
    ContinuousLinearMap.opTrace
        (ccmCircleMultiplier a * ccmCircleQuantizedDifferential b) =
      (2 : ℂ) *
        ((∑' p : ℕ × ℕ,
            fourierCoeff b.toFun (ccmCircleCrossFrequency p) *
              fourierCoeff a.toFun (-ccmCircleCrossFrequency p)) -
          ∑' p : ℕ × ℕ,
            fourierCoeff b.toFun (-ccmCircleCrossFrequency p) *
              fourierCoeff a.toFun (ccmCircleCrossFrequency p)) := by
  rw [← ccmCircleNuclearQuantizedDifferential_coe_eq_quantizedDifferential]
  exact opTrace_ccmCircleMultiplier_mul_nuclearQuantizedDifferential a b

private theorem tsum_complex_eq_tsum_sum_antidiagonal
    {T : ℕ × ℕ → ℂ} (hT : Summable T) :
    (∑' p : ℕ × ℕ, T p) =
      ∑' m : ℕ, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) m, T p := by
  have hsig : Summable fun x : Σ m : ℕ,
      Finset.HasAntidiagonal.antidiagonal (A := ℕ) m =>
      T (x.2 : ℕ × ℕ) :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr hT
  have hfib : ∀ m : ℕ, Summable fun p :
      Finset.HasAntidiagonal.antidiagonal (A := ℕ) m =>
      T (p : ℕ × ℕ) := fun _ => (hasSum_fintype _).summable
  have hsigma := hsig.tsum_sigma' hfib
  have hprod : (∑' p : ℕ × ℕ, T p) =
      ∑' x : Σ m : ℕ, Finset.HasAntidiagonal.antidiagonal (A := ℕ) m,
        T (x.2 : ℕ × ℕ) :=
    (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq T).symm
  calc
    (∑' p : ℕ × ℕ, T p) =
        ∑' x : Σ m : ℕ, Finset.HasAntidiagonal.antidiagonal (A := ℕ) m,
          T (x.2 : ℕ × ℕ) := hprod
    _ = ∑' m : ℕ, ∑' p : Finset.HasAntidiagonal.antidiagonal (A := ℕ) m,
        T (p : ℕ × ℕ) := hsigma
    _ = ∑' m : ℕ,
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) m, T p := by
      refine tsum_congr fun m => ?_
      rw [tsum_fintype, Finset.sum_coe_sort]

theorem tsum_ccmCirclePositiveCross_eq_firstMoment
    (a : CCMCircleBoundedSymbol) (b : CCMCircleTraceSymbol) :
    (∑' p : ℕ × ℕ,
        fourierCoeff b.toFun (ccmCircleCrossFrequency p) *
          fourierCoeff a.toFun (-ccmCircleCrossFrequency p)) =
      ∑' n : ℕ, (((n + 1 : ℕ) : ℂ) *
        (fourierCoeff b.toFun ((n + 1 : ℕ) : ℤ) *
          fourierCoeff a.toFun (-((n + 1 : ℕ) : ℤ)))) := by
  have hs : Summable fun p : ℕ × ℕ =>
      fourierCoeff b.toFun (ccmCircleCrossFrequency p) *
        fourierCoeff a.toFun (-ccmCircleCrossFrequency p) := by
    have hmap := (schattenOneTracePairingCLM (ccmCircleMultiplier a)).summable
      (summable_ccmCircleUpperNuclearTerm b)
    simpa only [schattenOneTracePairing_ccmCircleUpperNuclearTerm] using hmap
  rw [tsum_complex_eq_tsum_sum_antidiagonal hs]
  refine tsum_congr fun n => ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc
    (∑ k ∈ Finset.range (n + 1),
        fourierCoeff b.toFun (ccmCircleCrossFrequency (k, n - k)) *
          fourierCoeff a.toFun (-ccmCircleCrossFrequency (k, n - k))) =
        ∑ _k ∈ Finset.range (n + 1),
          (fourierCoeff b.toFun ((n + 1 : ℕ) : ℤ) *
            fourierCoeff a.toFun (-((n + 1 : ℕ) : ℤ))) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      simp [ccmCircleCrossFrequency, Nat.add_sub_of_le hkn]
    _ = (((n + 1 : ℕ) : ℂ) *
        (fourierCoeff b.toFun ((n + 1 : ℕ) : ℤ) *
          fourierCoeff a.toFun (-((n + 1 : ℕ) : ℤ)))) := by
      simp [nsmul_eq_mul]

theorem tsum_ccmCircleNegativeCross_eq_firstMoment
    (a : CCMCircleBoundedSymbol) (b : CCMCircleTraceSymbol) :
    (∑' p : ℕ × ℕ,
        fourierCoeff b.toFun (-ccmCircleCrossFrequency p) *
          fourierCoeff a.toFun (ccmCircleCrossFrequency p)) =
      ∑' n : ℕ, (((n + 1 : ℕ) : ℂ) *
        (fourierCoeff b.toFun (-((n + 1 : ℕ) : ℤ)) *
          fourierCoeff a.toFun ((n + 1 : ℕ) : ℤ))) := by
  have hs : Summable fun p : ℕ × ℕ =>
      fourierCoeff b.toFun (-ccmCircleCrossFrequency p) *
        fourierCoeff a.toFun (ccmCircleCrossFrequency p) := by
    have hmap := (schattenOneTracePairingCLM (ccmCircleMultiplier a)).summable
      (summable_ccmCircleLowerNuclearTerm b)
    simpa only [schattenOneTracePairing_ccmCircleLowerNuclearTerm] using hmap
  rw [tsum_complex_eq_tsum_sum_antidiagonal hs]
  refine tsum_congr fun n => ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc
    (∑ k ∈ Finset.range (n + 1),
        fourierCoeff b.toFun (-ccmCircleCrossFrequency (k, n - k)) *
          fourierCoeff a.toFun (ccmCircleCrossFrequency (k, n - k))) =
        ∑ _k ∈ Finset.range (n + 1),
          (fourierCoeff b.toFun (-((n + 1 : ℕ) : ℤ)) *
            fourierCoeff a.toFun ((n + 1 : ℕ) : ℤ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      simp [ccmCircleCrossFrequency, Nat.add_sub_of_le hkn]
    _ = (((n + 1 : ℕ) : ℂ) *
        (fourierCoeff b.toFun (-((n + 1 : ℕ) : ℤ)) *
          fourierCoeff a.toFun ((n + 1 : ℕ) : ℤ))) := by
      simp [nsmul_eq_mul]

/-- **Circle trace cocycle in first-moment form.**  The literal tested commutator trace is the
absolutely convergent signed first Fourier moment. -/
theorem opTrace_ccmCircleMultiplier_mul_quantizedDifferential
    (a : CCMCircleBoundedSymbol) (b : CCMCircleTraceSymbol) :
    ContinuousLinearMap.opTrace
        (ccmCircleMultiplier a * ccmCircleQuantizedDifferential b) =
      (2 : ℂ) *
        ((∑' n : ℕ, (((n + 1 : ℕ) : ℂ) *
            (fourierCoeff b.toFun ((n + 1 : ℕ) : ℤ) *
              fourierCoeff a.toFun (-((n + 1 : ℕ) : ℤ))))) -
          ∑' n : ℕ, (((n + 1 : ℕ) : ℂ) *
            (fourierCoeff b.toFun (-((n + 1 : ℕ) : ℤ)) *
              fourierCoeff a.toFun ((n + 1 : ℕ) : ℤ)))) := by
  rw [opTrace_ccmCircleMultiplier_mul_quantizedDifferential_doubleSeries,
    tsum_ccmCirclePositiveCross_eq_firstMoment,
    tsum_ccmCircleNegativeCross_eq_firstMoment]

end RHTower

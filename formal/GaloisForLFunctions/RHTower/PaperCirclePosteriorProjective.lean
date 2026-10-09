import GaloisForLFunctions.RHTower.PaperCircleSplitBitPosterior
import GaloisForLFunctions.HTGeometry.ProjectiveQuantumFisherValue

/-! # Projective geometry of actual posterior branch probabilities

Square roots of the native posterior branch probabilities form a unit vector.
Reflecting its right coordinate gives another unit vector whose inner product is
the posterior contrast. The corpus's projective Gram energy is exactly four times
the binary variance. Averaging gives the source Fisher overlap, so classical split
information and this projective energy sum to one.
-/

open scoped BigOperators NNReal InnerProductSpace
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

def paperCircleHistoryBitState (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (z : Grid (l+r+10)) : EuclideanSpace ℝ Bool :=
  WithLp.toLp 2 fun b => Real.sqrt (paperCircleHistorySplitBitPosterior a l r k i s t z b)

def paperCircleHistoryBitReflection (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (z : Grid (l+r+10)) : EuclideanSpace ℝ Bool :=
  WithLp.toLp 2 fun b => if b then
    -Real.sqrt (paperCircleHistorySplitBitPosterior a l r k i s t z b) else
    Real.sqrt (paperCircleHistorySplitBitPosterior a l r k i s t z b)

theorem paperCircleHistoryBitState_norm (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (z : Grid (l+r+10)) : ‖paperCircleHistoryBitState a l r k i s t z‖ = 1 := by
  let Q := paperCircleHistorySplitBitPosterior a l r k i s t z
  have h : ‖paperCircleHistoryBitState a l r k i s t z‖^2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ b, (Real.sqrt (Q b))^2) = 1
    simp_rw [Real.sq_sqrt (Q.nonneg _)]
    exact Q.total
  nlinarith [norm_nonneg (paperCircleHistoryBitState a l r k i s t z)]

theorem paperCircleHistoryBitReflection_norm (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (z : Grid (l+r+10)) : ‖paperCircleHistoryBitReflection a l r k i s t z‖ = 1 := by
  let Q := paperCircleHistorySplitBitPosterior a l r k i s t z
  have ht := Q.total
  simp only [Fintype.sum_bool] at ht
  have h : ‖paperCircleHistoryBitReflection a l r k i s t z‖^2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_bool]
    change (-Real.sqrt (Q true))^2 + (Real.sqrt (Q false))^2 = 1
    nlinarith [Real.sq_sqrt (Q.nonneg true), Real.sq_sqrt (Q.nonneg false)]
  nlinarith [norm_nonneg (paperCircleHistoryBitReflection a l r k i s t z)]

theorem paperCircleHistoryBit_inner (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (z : Grid (l+r+10)) :
    inner ℝ (paperCircleHistoryBitState a l r k i s t z)
      (paperCircleHistoryBitReflection a l r k i s t z) =
      paperCircleHistorySplitBitPosterior a l r k i s t z false -
        paperCircleHistorySplitBitPosterior a l r k i s t z true := by
  let Q := paperCircleHistorySplitBitPosterior a l r k i s t z
  unfold paperCircleHistoryBitState paperCircleHistoryBitReflection
  rw [EuclideanSpace.inner_toLp_toLp]
  change (∑ b : Bool, (if b then -Real.sqrt (Q b) else Real.sqrt (Q b)) *
    Real.sqrt (Q b)) = Q false - Q true
  rw [Fintype.sum_bool]
  change -Real.sqrt (Q true) * Real.sqrt (Q true) +
    Real.sqrt (Q false) * Real.sqrt (Q false) = Q false - Q true
  nlinarith [Real.sq_sqrt (Q.nonneg true), Real.sq_sqrt (Q.nonneg false)]

/-- Existing projective Gram geometry applied to the actual binary posterior. -/
theorem paperCircleHistoryBit_projective_energy (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (z : Grid (l+r+10)) :
    _root_.HTGeometry.projectiveGramTangentEnergy (𝕜 := ℝ)
      (paperCircleHistoryBitState a l r k i s t z)
      (paperCircleHistoryBitReflection a l r k i s t z) =
      4 * (paperCircleHistorySplitBitPosterior a l r k i s t z false *
        paperCircleHistorySplitBitPosterior a l r k i s t z true) := by
  rw [_root_.HTGeometry.projectiveGramTangentEnergy_eq_unit_projectiveDefect
    (paperCircleHistoryBitState_norm a l r k i s t z)
    (paperCircleHistoryBitReflection_norm a l r k i s t z),
    paperCircleHistoryBit_inner, Real.norm_eq_abs, sq_abs]
  have ht := (paperCircleHistorySplitBitPosterior a l r k i s t z).total
  simp only [Fintype.sum_bool] at ht
  have hs := congrArg (fun x : ℝ => x^2) ht
  nlinarith [hs]

theorem paperCircleHistoryBit_projective_energy_pos (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (z : Grid (l+r+10)) :
    0 < _root_.HTGeometry.projectiveGramTangentEnergy (𝕜 := ℝ)
      (paperCircleHistoryBitState a l r k i s t z)
      (paperCircleHistoryBitReflection a l r k i s t z) := by
  rw [paperCircleHistoryBit_projective_energy]
  exact mul_pos (by norm_num) (mul_pos
    (paperCircleHistorySplitBitPosterior_pos a l r k i s t z false)
    (paperCircleHistorySplitBitPosterior_pos a l r k i s t z true))

theorem paperCircleHistorySplit_projective_energy (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) :
    ((paperCircleHistoryCellPosterior a l r k i s).through
      (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t))).Ex
      (fun z => _root_.HTGeometry.projectiveGramTangentEnergy (𝕜 := ℝ)
        (paperCircleHistoryBitState a l r k i s t z)
        (paperCircleHistoryBitReflection a l r k i s t z)) =
      paperCircleHistorySplitOverlap a l r k i s t := by
  simp_rw [paperCircleHistoryBit_projective_energy]
  rw [Law.Ex_lmul]
  exact (paperCircleHistorySplit_overlap_posterior_variance a l r k i s t).symm

/-- Classical split information and mean projective ambiguity exactly exhaust unit mass. -/
theorem paperCircleHistorySplit_fisher_projective_balance (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) :
    paperCircleHistorySplitFisher a l r k i s t +
      ((paperCircleHistoryCellPosterior a l r k i s).through
        (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t))).Ex
        (fun z => _root_.HTGeometry.projectiveGramTangentEnergy (𝕜 := ℝ)
          (paperCircleHistoryBitState a l r k i s t z)
          (paperCircleHistoryBitReflection a l r k i s t z)) = 1 := by
  rw [paperCircleHistorySplit_projective_energy]
  exact paperCircleHistorySplit_fisher_add_overlap a l r k i s t

/-- The corpus's static quantum-Fisher value on the realized unit-vector Gram data. -/
theorem paperCircleHistoryBit_quantumFisher_value (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (z : Grid (l+r+10)) :
    _root_.HTGeometry.pureStateQuantumFisherValue 1
      (inner ℝ (paperCircleHistoryBitState a l r k i s t z)
        (paperCircleHistoryBitReflection a l r k i s t z)) 1 =
      4 * _root_.HTGeometry.projectiveGramTangentEnergy (𝕜 := ℝ)
        (paperCircleHistoryBitState a l r k i s t z)
        (paperCircleHistoryBitReflection a l r k i s t z) := by
  simp only [_root_.HTGeometry.pureStateQuantumFisherValue,
    _root_.HTGeometry.projectiveQuantumTangentValue,
    _root_.HTGeometry.projectiveGramTangentEnergy,
    paperCircleHistoryBitState_norm, paperCircleHistoryBitReflection_norm,
    one_pow, one_mul, div_one, Real.norm_eq_abs, sq_abs]

theorem paperCircleHistorySplit_quantumFisher_mean (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) :
    ((paperCircleHistoryCellPosterior a l r k i s).through
      (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t))).Ex
      (fun z => _root_.HTGeometry.pureStateQuantumFisherValue 1
        (inner ℝ (paperCircleHistoryBitState a l r k i s t z)
          (paperCircleHistoryBitReflection a l r k i s t z)) 1) =
      4 * paperCircleHistorySplitOverlap a l r k i s t := by
  simp_rw [paperCircleHistoryBit_quantumFisher_value]
  rw [Law.Ex_lmul, paperCircleHistorySplit_projective_energy]

end
end RHTower

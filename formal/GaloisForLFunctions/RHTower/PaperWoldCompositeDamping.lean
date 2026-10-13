import GaloisForLFunctions.RHTower.PaperWoldCompositeDomain
import GaloisForLFunctions.HTGeometry.PaperDiagonalStrongConvergence
import GaloisForLFunctions.HTGeometry.LaplaceFormationCompletionTopology

/-! # The exact row-damping semigroup of the composite Wold family

The original composite row coordinates give the multipliers `(2n+3)^(-r)`.
Their complete diagonal operators form a strongly continuous contraction
semigroup, with exact norm `3^(-r)` and compactness at every positive time.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal

def paperWoldCompositeDampingWeight (r : ℝ≥0) (n : ℕ) : ℝ :=
  (2 * (n : ℝ) + 3) ^ (-(r : ℝ))

theorem paperWoldCompositeDampingWeight_pos (r : ℝ≥0) (n : ℕ) :
    0 < paperWoldCompositeDampingWeight r n := Real.rpow_pos_of_pos (by positivity) _

theorem paperWoldCompositeDampingWeight_norm (r : ℝ≥0) (n : ℕ) :
    ‖(paperWoldCompositeDampingWeight r n : ℂ)‖ = paperWoldCompositeDampingWeight r n := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (paperWoldCompositeDampingWeight_pos r n)]

theorem paperWoldCompositeDampingWeight_le_one (r : ℝ≥0) (n : ℕ) :
    paperWoldCompositeDampingWeight r n ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos
    (by linarith [Nat.cast_nonneg (α := ℝ) n]) (neg_nonpos.mpr r.property)

theorem paperWoldCompositeDampingWeight_norm_le (r : ℝ≥0) (n : ℕ) :
    ‖(paperWoldCompositeDampingWeight r n : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (paperWoldCompositeDampingWeight_pos r n)]
  exact paperWoldCompositeDampingWeight_le_one r n

def paperWoldCompositeDamping (r : ℝ≥0) : PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  lpDiagonalCLM (fun n => (paperWoldCompositeDampingWeight r n : ℂ)) zero_le_one
    (paperWoldCompositeDampingWeight_norm_le r)

theorem paperWoldCompositeDamping_apply (r : ℝ≥0) (f : PaperWoldHistory) (n : ℕ) :
    paperWoldCompositeDamping r f n = (paperWoldCompositeDampingWeight r n : ℂ) * f n := rfl

theorem paperWoldCompositeDamping_zero :
    paperWoldCompositeDamping 0 = ContinuousLinearMap.id ℂ PaperWoldHistory := by
  ext f n
  simp only [paperWoldCompositeDamping_apply, paperWoldCompositeDampingWeight, NNReal.coe_zero,
    neg_zero, Real.rpow_zero, Complex.ofReal_one, one_mul, ContinuousLinearMap.id_apply]

theorem paperWoldCompositeDamping_add (r s : ℝ≥0) :
    paperWoldCompositeDamping (r + s) = paperWoldCompositeDamping r ∘L paperWoldCompositeDamping s := by
  ext f n
  simp only [ContinuousLinearMap.comp_apply, paperWoldCompositeDamping_apply,
    paperWoldCompositeDampingWeight, NNReal.coe_add, neg_add,
    Real.rpow_add (by positivity : 0 < 2 * (n : ℝ) + 3), Complex.ofReal_mul, mul_assoc]

theorem paperWoldCompositeDamping_norm (r : ℝ≥0) :
    ‖paperWoldCompositeDamping r‖ = (3 : ℝ) ^ (-(r : ℝ)) := by
  have hb (n : ℕ) : ‖(paperWoldCompositeDampingWeight r n : ℂ)‖ ≤ (3 : ℝ) ^ (-(r : ℝ)) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (paperWoldCompositeDampingWeight_pos r n)]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num)
      (by linarith [Nat.cast_nonneg (α := ℝ) n]) (neg_nonpos.mpr r.property)
  apply le_antisymm
  · have he : paperWoldCompositeDamping r = lpDiagonalCLM
        (fun n => (paperWoldCompositeDampingWeight r n : ℂ)) (by positivity) hb := by
      ext f n
      rfl
    rw [he]
    exact norm_lpDiagonalCLM_le _ _ _
  · have h := (paperWoldCompositeDamping r).le_opNorm (lp.single 2 0 (1 : ℂ))
    simp only [paperWoldCompositeDamping, lpDiagonalCLM_single,
      lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), norm_one, mul_one,
      paperWoldCompositeDampingWeight_norm] at h
    simpa only [paperWoldCompositeDamping, paperWoldCompositeDampingWeight,
      Nat.cast_zero, mul_zero, zero_add] using h

theorem paperWoldCompositeDampingWeight_continuous (n : ℕ) :
    Continuous (fun r : ℝ≥0 => (paperWoldCompositeDampingWeight r n : ℂ)) :=
  Complex.continuous_ofReal.comp
    ((Real.continuous_const_rpow (by positivity : 2 * (n : ℝ) + 3 ≠ 0)).comp
      NNReal.continuous_coe.neg)

/-- Strong continuity acts on every complete history, including infinite support. -/
theorem paperWoldCompositeDamping_strong_continuous (f : PaperWoldHistory) :
    Continuous (fun r : ℝ≥0 => paperWoldCompositeDamping r f) := by
  apply continuous_iff_seqContinuous.mpr
  intro r s hrs
  exact paperLpDiagonal_strong_tendsto
    (fun k n => (paperWoldCompositeDampingWeight (r k) n : ℂ))
    (fun n => (paperWoldCompositeDampingWeight s n : ℂ)) 1 zero_le_one
    (fun k => paperWoldCompositeDampingWeight_norm_le (r k))
    (paperWoldCompositeDampingWeight_norm_le s)
    (fun n => ((paperWoldCompositeDampingWeight_continuous n).tendsto s).comp hrs) f

/-- Every positive damping time gives an actual compact diagonal on the full history space. -/
theorem paperWoldCompositeDamping_compact (r : {r : ℝ≥0 // 0 < r}) :
    IsCompactOperator (paperWoldCompositeDamping r) := by
  apply isCompactOperator_lpDiagonalCLM
  have hbase : Tendsto (fun n : ℕ => 2 * (n : ℝ) + 3) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num : (0 : ℝ) < 2) |>.atTop_add
      (tendsto_const_nhds (x := (3 : ℝ)))
  have h := (tendsto_rpow_neg_atTop (show (0 : ℝ) < (r.val : ℝ) from r.property)).comp hbase
  simp_rw [paperWoldCompositeDampingWeight_norm]
  exact h

end
end RHTower

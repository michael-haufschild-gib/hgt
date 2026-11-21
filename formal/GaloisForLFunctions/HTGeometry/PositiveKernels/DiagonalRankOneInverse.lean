import GaloisForLFunctions.HTGeometry.PositiveKernels.DiagonalRankOneResponse
import Mathlib.Analysis.Real.Sqrt

/-!
# Inversion of a positive rank-one perturbation from one eigenpair

For a known diagonal and a symmetric positive rank-one correction, the
eigenpair determines the weighted residual vector. Its pairing with the
eigenvector supplies the normalization of the unknown coupling.
-/

open Finset Matrix Set
open scoped NNReal

namespace GaloisForLFunctions.HTGeometry.EntrywisePositiveKernel

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

private theorem diagonalGap_pos (d : ι → ℝ≥0) (z : Ioi (diagonalCeiling d)) (i : ι) :
    0 < (z : ℝ) - (d i : ℝ) := sub_pos.mpr ((le_diagonalCeiling d i).trans_lt z.2)

private theorem eigenvectorQuadratic_pos (d : ι → ℝ≥0) (z : Ioi (diagonalCeiling d))
    (x : ι → Ioi (0 : ℝ)) : 0 < ∑ i, ((z : ℝ) - (d i : ℝ)) * (x i : ℝ) ^ 2 :=
  sum_pos (fun i _ => mul_pos (diagonalGap_pos d z i) (pow_pos (x i).2 _)) univ_nonempty

/-- Recover the coupling from the displaced eigenvector, normalized by the
square root of its pairing with the measured eigenvector. -/
def diagonalRankOneReconstruction (d : ι → ℝ≥0) (z : Ioi (diagonalCeiling d)) (x : ι → Ioi (0 : ℝ))
    (i : ι) : Ioi (0 : ℝ) :=
  ⟨((z : ℝ) - (d i : ℝ)) * (x i : ℝ) / Real.sqrt (∑ j, ((z : ℝ) - (d j : ℝ)) * (x j : ℝ) ^ 2),
    div_pos (mul_pos (diagonalGap_pos d z i) (x i).2) (Real.sqrt_pos.mpr (eigenvectorQuadratic_pos d z x))⟩

variable [DecidableEq ι]

/-- A positive vector solves the specified eigenpair exactly when the
symmetric rank-one coupling is its reconstructed value. -/
theorem diagonalRankOneSymmetric_eigenpair_iff (d : ι → ℝ≥0) (z : Ioi (diagonalCeiling d))
    (x w : ι → Ioi (0 : ℝ)) :
    (diagonalRankOneKernel d w w ⟨1, mem_Ioi.mpr zero_lt_one⟩).val *ᵥ (fun i => (x i : ℝ)) =
      (z : ℝ) • (fun i => (x i : ℝ)) ↔ w = diagonalRankOneReconstruction d z x := by
  let b (i : ι) := (z : ℝ) - (d i : ℝ)
  let Q := ∑ i, (w i : ℝ) * (x i : ℝ)
  let C := ∑ i, b i * (x i : ℝ) ^ 2
  let S := Real.sqrt C
  have hC : 0 < C := eigenvectorQuadratic_pos d z x
  have hS : 0 < S := Real.sqrt_pos.mpr hC
  have hrows : (diagonalRankOneKernel d w w ⟨1, mem_Ioi.mpr zero_lt_one⟩).val *ᵥ (fun i => (x i : ℝ)) =
      (z : ℝ) • (fun i => (x i : ℝ)) ↔ ∀ i, b i * (x i : ℝ) = (w i : ℝ) * Q := by
    have hrow (i : ι) : ((diagonalRankOneKernel d w w ⟨1, mem_Ioi.mpr zero_lt_one⟩).val *ᵥ
        (fun j => (x j : ℝ))) i = (d i : ℝ) * (x i : ℝ) + (w i : ℝ) * Q := by
      rw [diagonalRankOneKernel_mulVec]
      change _ + (1 * (w i : ℝ)) * Q = _
      rw [one_mul]
    constructor
    · intro h i
      have he := congrFun h i
      rw [hrow] at he
      change (d i : ℝ) * (x i : ℝ) + (w i : ℝ) * Q = (z : ℝ) * (x i : ℝ) at he
      dsimp only [b]
      rw [sub_mul]
      linarith only [he]
    · intro h
      funext i
      rw [hrow]
      change (d i : ℝ) * (x i : ℝ) + (w i : ℝ) * Q = (z : ℝ) * (x i : ℝ)
      rw [← h i]
      dsimp only [b]
      ring
  rw [hrows]
  constructor
  · intro h
    have hQpos : 0 < Q := sum_pos (fun i _ => mul_pos (w i).2 (x i).2) univ_nonempty
    have hQsq : Q ^ 2 = C := calc
      Q ^ 2 = ∑ i, Q * ((w i : ℝ) * (x i : ℝ)) := by rw [pow_two, ← mul_sum]
      _ = C := by
        apply sum_congr rfl
        intro i _
        calc
          _ = ((w i : ℝ) * Q) * (x i : ℝ) := by ring
          _ = b i * (x i : ℝ) ^ 2 := by rw [← h i]; ring
    have hQ : Q = S := by
      change Q = Real.sqrt C
      rw [← hQsq, Real.sqrt_sq_eq_abs, abs_of_pos hQpos]
    funext i
    apply Subtype.ext
    change (w i : ℝ) = b i * (x i : ℝ) / S
    apply (eq_div_iff hS.ne').mpr
    rw [← hQ]
    exact (h i).symm
  · intro h
    have hw (i : ι) : (w i : ℝ) = b i * (x i : ℝ) / S := congrArg Subtype.val (congrFun h i)
    have hQ : Q = S := calc
      Q = C / S := by
        change (∑ i, (w i : ℝ) * (x i : ℝ)) = (∑ i, b i * (x i : ℝ) ^ 2) / S
        rw [div_eq_mul_inv, Finset.sum_mul]
        apply sum_congr rfl
        intro i _
        rw [hw i]
        ring
      _ = S := (div_eq_iff hS.ne').mpr (by rw [← pow_two]; exact (Real.sq_sqrt hC.le).symm)
    intro i
    rw [hw i, hQ, div_mul_cancel₀ _ hS.ne']

/-- Every positive eigenvector and every level above the diagonal edge
are realized by exactly one positive symmetric rank-one correction. -/
theorem existsUnique_diagonalRankOneSymmetric_of_eigenpair (d : ι → ℝ≥0) (z : Ioi (diagonalCeiling d))
    (x : ι → Ioi (0 : ℝ)) :
    ∃! w : ι → Ioi (0 : ℝ), (diagonalRankOneKernel d w w ⟨1, mem_Ioi.mpr zero_lt_one⟩).val *ᵥ
      (fun i => (x i : ℝ)) = (z : ℝ) • (fun i => (x i : ℝ)) :=
  ⟨diagonalRankOneReconstruction d z x, (diagonalRankOneSymmetric_eigenpair_iff d z x _).mpr rfl,
    fun w hw => (diagonalRankOneSymmetric_eigenpair_iff d z x w).mp hw⟩

/-- Two observed coordinates determine their coupling ratio without the
unobserved coordinates or the scale of the measured eigenvector. -/
theorem diagonalRankOneSymmetric_coupling_ratio (d : ι → ℝ≥0) (z : Ioi (diagonalCeiling d))
    (x w : ι → Ioi (0 : ℝ))
    (h : (diagonalRankOneKernel d w w ⟨1, mem_Ioi.mpr zero_lt_one⟩).val *ᵥ (fun i => (x i : ℝ)) =
      (z : ℝ) • (fun i => (x i : ℝ))) (i j : ι) :
    (w i : ℝ) / (w j : ℝ) = (((z : ℝ) - (d i : ℝ)) * (x i : ℝ)) /
      (((z : ℝ) - (d j : ℝ)) * (x j : ℝ)) := by
  let C := ∑ k, ((z : ℝ) - (d k : ℝ)) * (x k : ℝ) ^ 2
  have hS : 0 < Real.sqrt C := Real.sqrt_pos.mpr (eigenvectorQuadratic_pos d z x)
  rw [(diagonalRankOneSymmetric_eigenpair_iff d z x w).mp h]
  change ((((z : ℝ) - (d i : ℝ)) * (x i : ℝ)) / Real.sqrt C) /
    ((((z : ℝ) - (d j : ℝ)) * (x j : ℝ)) / Real.sqrt C) = _
  rw [div_div_div_cancel_right₀ hS.ne']

#print axioms diagonalRankOneSymmetric_eigenpair_iff
#print axioms existsUnique_diagonalRankOneSymmetric_of_eigenpair
#print axioms diagonalRankOneSymmetric_coupling_ratio

end

end GaloisForLFunctions.HTGeometry.EntrywisePositiveKernel

import GaloisForLFunctions.FiniteFreeProbability.TwoShiftThetaTuranForms
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRadauFourMomentBoundary
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Exact rank of the two-shift theta Turán kernel

The order-d binomial contrast pairs two moment matrices across a signed
antidiagonal. Every consecutive block of size d+1 has positive determinant,
even when its two starting shifts differ. Such a block reconstructs the
kernel at arbitrary row and column indices.
-/

open Finset Matrix RHTower GaloisForLFunctions.SignAlternation
namespace FiniteFreeProbability

noncomputable section

/-- Two independent lists of shifts sampled in the order-d theta Turán form. -/
def thetaTuranMatrix {m n : ℕ} (d : ℕ) (r : Fin m → ℕ) (s : Fin n → ℕ) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => thetaTuranForm (r i) (s j) d

private def momentRows {m : ℕ} (d : ℕ) (r : Fin m → ℕ) : Matrix (Fin m) (Fin (d+1)) ℝ :=
  fun i j => thetaCuspRawEvenMoment (r i+j)

private def signedReverse {n : ℕ} (w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i.rev = j then (-1)^(i : ℕ)*w i else 0

/-- The cofactor signs of reversal cancel exactly against the alternating row signs. -/
private theorem signedReverse_det (n : ℕ) (w : Fin n → ℝ) : (signedReverse w).det = ∏ i, w i := by
  induction n with
  | zero => simp [Matrix.det_isEmpty]
  | succ n ih =>
    have hm : (signedReverse w).submatrix (Fin.last n).succAbove Fin.succ =
        signedReverse (fun i => w (Fin.castSucc i)) := by
      ext i j
      simp [signedReverse, Fin.rev_castSucc]
    rw [Matrix.det_succ_column_zero, Finset.sum_eq_single (Fin.last n)]
    · rw [hm, ih, Fin.prod_univ_castSucc w]
      simp only [signedReverse, Fin.rev_last, if_true, Fin.val_last]
      rw [←mul_assoc, ←mul_pow]
      simp [mul_comm]
    · intro i _ h
      have hn : i.rev ≠ 0 := fun he => h (by simpa using congrArg Fin.rev he)
      simp [signedReverse, hn]
    · simp

private def binomWeights (d : ℕ) (j : Fin (d+1)) : ℝ := d.choose j.val

private def central (d : ℕ) := signedReverse (binomWeights d)

private theorem central_pos (d : ℕ) : 0 < (central d).det := by
  rw [central, signedReverse_det]
  exact Finset.prod_pos fun i _ => Nat.cast_pos.mpr (Nat.choose_pos (Nat.le_of_lt_succ i.isLt))

private theorem core_times_rows {n : ℕ} (d : ℕ) (s : Fin n → ℕ) (i : Fin (d+1)) (j : Fin n) :
    (central d * (momentRows d s)ᵀ) i j =
      (-1 : ℝ)^i.val * binomWeights d i * thetaCuspRawEvenMoment (s j + (d-i.val)) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev]
  · simp [central, signedReverse, momentRows, Fin.rev]
  · intro k _ h
    simp [central, signedReverse, Ne.symm h]
  · simp

private theorem factorization {m n : ℕ} (d : ℕ) (r : Fin m → ℕ) (s : Fin n → ℕ) :
    thetaTuranMatrix d r s = momentRows d r * central d * (momentRows d s)ᵀ := by
  rw [Matrix.mul_assoc]
  ext i j
  simp only [thetaTuranMatrix, thetaTuranForm, Matrix.mul_apply (momentRows d r),
    core_times_rows, momentRows, binomWeights]
  rw [Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro k _
  ring

private def consecutive (d a : ℕ) (j : Fin (d+1)) : ℕ := a+j

private theorem consecutive_rows (a d : ℕ) :
    momentRows d (consecutive d a) = HTGeometry.momentHankelMatrix
      (fun k => thetaCuspRawEvenMoment (k+a)) (d+1) := by
  ext i j
  dsimp [momentRows,consecutive,HTGeometry.momentHankelMatrix]
  congr 1
  omega

/-- Exact determinant for any pair of consecutive sets of d+1 shifts. -/
theorem thetaTuran_consecutive_det (a b d : ℕ) :
    (thetaTuranMatrix d (fun i : Fin (d+1) => a+i) (fun j : Fin (d+1) => b+j)).det =
      (HTGeometry.momentHankelMatrix (fun k => thetaCuspRawEvenMoment (k+a)) (d+1)).det *
      (∏ i : Fin (d+1), (d.choose i.val : ℝ)) *
      (HTGeometry.momentHankelMatrix (fun k => thetaCuspRawEvenMoment (k+b)) (d+1)).det := by
  change (thetaTuranMatrix d (consecutive d a) (consecutive d b)).det = _
  rw [factorization, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, consecutive_rows,
    consecutive_rows, central, signedReverse_det]
  rfl

/-- All maximal consecutive minors are positive at every contrast order, including odd orders. -/
theorem thetaTuran_consecutive_det_pos (a b d : ℕ) :
    0 < (thetaTuranMatrix d (fun i : Fin (d+1) => a+i) (fun j : Fin (d+1) => b+j)).det := by
  rw [thetaTuran_consecutive_det]
  exact mul_pos (mul_pos (thetaCuspRawEvenMoment_offsetHankel_posDef _ _).det_pos
    (prod_pos fun i _ => Nat.cast_pos.mpr (Nat.choose_pos (Nat.le_of_lt_succ i.isLt))))
    (thetaCuspRawEvenMoment_offsetHankel_posDef _ _).det_pos

/-- The rank bound holds at arbitrary shifts and is attained by every sufficiently large
rectangular block of consecutive shifts. -/
theorem thetaTuran_rank_le {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ) (d : ℕ) :
    (thetaTuranMatrix d r s).rank ≤ d+1 := by
  rw [factorization,Matrix.mul_assoc]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

theorem thetaTuran_rectangular_rank (p q a b d : ℕ) :
    (thetaTuranMatrix d (fun i : Fin (d+1+p) => a+i) (fun j : Fin (d+1+q) => b+j)).rank = d+1 := by
  let K := thetaTuranMatrix d (fun i : Fin (d+1+p) => a+i) (fun j : Fin (d+1+q) => b+j)
  let I (t : ℕ) (i : Fin (d+1)) : Fin (d+1+t) := ⟨i.val, by have := i.isLt; omega⟩
  apply (thetaTuran_rank_le _ _ d).antisymm
  have h := K.rank_submatrix_le (I p) (I q)
  have hu : IsUnit (K.submatrix (I p) (I q)) := Matrix.isUnit_iff_isUnit_det.mpr
      (isUnit_iff_ne_zero.mpr (thetaTuran_consecutive_det_pos a b d).ne')
  rwa [Matrix.rank_of_isUnit _ hu, Fintype.card_fin] at h

/-- A single consecutive block and its sampled rows and columns recover every entry.
The row and column blocks may start at different shifts. -/
theorem thetaTuran_reconstruct {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ) (a b d : ℕ) :
    thetaTuranMatrix d r s =
      thetaTuranMatrix d r (fun i : Fin (d+1) => b+i) *
      (thetaTuranMatrix d (fun i : Fin (d+1) => a+i) (fun j : Fin (d+1) => b+j))⁻¹ *
      thetaTuranMatrix d (fun i : Fin (d+1) => a+i) s := by
  let A := momentRows d (consecutive d a)
  let B := (momentRows d (consecutive d b))ᵀ
  let J := central d
  have hA : IsUnit A.det := by
    dsimp [A]
    rw [consecutive_rows]
    exact isUnit_iff_ne_zero.mpr (thetaCuspRawEvenMoment_offsetHankel_posDef _ _).det_pos.ne'
  have hB : IsUnit B.det := by
    dsimp [B]
    rw [Matrix.det_transpose, consecutive_rows]
    exact isUnit_iff_ne_zero.mpr (thetaCuspRawEvenMoment_offsetHankel_posDef _ _).det_pos.ne'
  have hJ : IsUnit J.det := isUnit_iff_ne_zero.mpr (central_pos d).ne'
  simp only [factorization]
  change _ = (momentRows d r * J * B) * (A * J * B)⁻¹ * (A * J * (momentRows d s)ᵀ)
  simp only [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left B _ hB,
    Matrix.nonsing_inv_mul_cancel_left A _ hA, Matrix.nonsing_inv_mul_cancel_left J _ hJ]


end

end FiniteFreeProbability

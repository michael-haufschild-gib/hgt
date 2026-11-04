import GaloisForLFunctions.ThetaCuspSections.FifthEvenInheritedLoadBoundary
import GaloisForLFunctions.RHTower.FiniteDegreeReciprocalPerturbation
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Complete native fifth-section positivity at scale seven

Exact Schur coordinates diagonalize the first-atom form. After normalizing
its diagonal, retained two-atom and Cauchy bounds leave a uniform positive
quadratic floor for the complete native source. The coordinate matrix is
upper triangular with positive diagonal, so positivity transfers to the
original fifth even block.
-/

noncomputable section
open Matrix RHTower Polynomial RHTower.ThetaCuspGaussianLimit
namespace GaloisForLFunctions.ThetaCuspSections.EvenFiveScaleSevenNative

private def moment (k : ℕ) : ℝ := (thetaPairRadialEvenPolynomial 49 k).eval 14/121
-- Eliminate the first two moments, then diagonalize the remaining Schur form.
private def headDelta : ℝ := moment 0*moment 2-moment 1^2
private def headPair (a b c e : ℝ) : ℝ :=
  moment 2*a*c-moment 1*(a*e+b*c)+moment 0*b*e
private def tailSchur (i j : Fin 3) : ℝ :=
  headDelta*moment (i.val+j.val+4)-
    headPair (moment (i.val+2)) (moment (i.val+3)) (moment (j.val+2)) (moment (j.val+3))
private def middleDelta : ℝ := tailSchur 0 0*tailSchur 1 1-tailSchur 0 1^2
private def tailColumn (i j : Fin 3) : ℝ :=
  if i.val=0 then (if j.val=0 then 1 else 0)
  else if i.val=1 then (if j.val=0 then -tailSchur 0 1/tailSchur 0 0 else if j.val=1 then 1 else 0)
  else if j.val=0 then -(tailSchur 1 1*tailSchur 0 2-tailSchur 0 1*tailSchur 1 2)/middleDelta
  else if j.val=1 then (tailSchur 0 1*tailSchur 0 2-tailSchur 0 0*tailSchur 1 2)/middleDelta
  else 1
private def headCross (i : Fin 3) (k : ℕ) : ℝ :=
  ∑ j : Fin 3, tailColumn i j*moment (j.val+2+k)
private def fullVector (i : Fin 5) (k : Fin 5) : ℝ :=
  if i.val=0 then (if k.val=0 then 1 else 0)
  else if i.val=1 then (if k.val=0 then -moment 1 else if k.val=1 then 1 else 0)
  else
    let j : Fin 3 := ⟨i.val-2,by omega⟩
    if k.val=0 then -(moment 2*headCross j 0-moment 1*headCross j 1)/headDelta
    else if k.val=1 then (moment 1*headCross j 0-moment 0*headCross j 1)/headDelta
    else tailColumn j ⟨k.val-2,by omega⟩
private def fullGramPolynomial (a X : ℝ) (i j : Fin 5) : ℝ :=
  ∑ u : Fin 5, ∑ v : Fin 5, fullVector i u*fullVector j v*
    (thetaPairRadialEvenPolynomial a (u.val+v.val)).eval X
private def fullTailError (i j : Fin 5) : ℝ :=
  ∑ u : Fin 5, ∑ v : Fin 5, |fullVector i u| * |fullVector j v| *
    ((2*(u.val+v.val)).factorial:ℝ)/(10000000000000*(3/20:ℝ)^(2*(u.val+v.val)))
private def fullError (i j : Fin 5) : ℝ :=
  ((8/1000000000)*|fullGramPolynomial 196 35 i j|+
    (16/1000000000^2)*|fullGramPolynomial 784 56 i j|)/121+fullTailError i j
private theorem radial_eight_coeff (a : ℝ) (k : ℕ) :
 radialCoeffs a 8 k = radialStepCoeff a (radialCoeffs a 7) k := rfl
private theorem radial_seven_zero_16 (a : ℝ) : radialCoeffs a 7 16=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_17 (a : ℝ) : radialCoeffs a 7 17=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_18 (a : ℝ) : radialCoeffs a 7 18=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_19 (a : ℝ) : radialCoeffs a 7 19=0 :=
 radialCoeffs_eq_zero a (by norm_num)

local macro "norm_full_source" : tactic =>
  `(tactic| norm_num [fullError,  fullTailError,  fullGramPolynomial,  fullVector,  headCross,  tailColumn,
    middleDelta,  tailSchur,  headDelta,  headPair,  moment,  Fin.sum_univ_succ, Nat.factorial,
    eval_thetaPairRadialEvenPolynomial, Finset.sum_range_succ, radialCoeffs_0_0,
    radialCoeffs_0_1, radialCoeffs_1_0, radialCoeffs_1_1, radialCoeffs_1_2, radialCoeffs_1_3,
    radialCoeffs_2_0, radialCoeffs_2_1, radialCoeffs_2_2, radialCoeffs_2_3, radialCoeffs_2_4,
    radialCoeffs_2_5, radialCoeffs_3_0, radialCoeffs_3_1, radialCoeffs_3_2, radialCoeffs_3_3,
    radialCoeffs_3_4, radialCoeffs_3_5, radialCoeffs_3_6, radialCoeffs_3_7, radialCoeffs_4_0,
    radialCoeffs_4_1, radialCoeffs_4_2, radialCoeffs_4_3, radialCoeffs_4_4, radialCoeffs_4_5,
    radialCoeffs_4_6, radialCoeffs_4_7, radialCoeffs_4_8, radialCoeffs_4_9, radialCoeffs_5_0,
    radialCoeffs_5_1, radialCoeffs_5_2, radialCoeffs_5_3, radialCoeffs_5_4, radialCoeffs_5_5,
    radialCoeffs_5_6, radialCoeffs_5_7, radialCoeffs_5_8, radialCoeffs_5_9, radialCoeffs_5_10,
    radialCoeffs_5_11, radialCoeffs_6_0, radialCoeffs_6_1, radialCoeffs_6_2, radialCoeffs_6_3,
    radialCoeffs_6_4, radialCoeffs_6_5, radialCoeffs_6_6, radialCoeffs_6_7, radialCoeffs_6_8,
    radialCoeffs_6_9, radialCoeffs_6_10, radialCoeffs_6_11, radialCoeffs_6_12,
    radialCoeffs_6_13, radialCoeffs_7_0, radialCoeffs_7_1, radialCoeffs_7_2, radialCoeffs_7_3,
    radialCoeffs_7_4, radialCoeffs_7_5, radialCoeffs_7_6, radialCoeffs_7_7, radialCoeffs_7_8,
    radialCoeffs_7_9, radialCoeffs_7_10, radialCoeffs_7_11, radialCoeffs_7_12,
    radialCoeffs_7_13, radialCoeffs_7_14, radialCoeffs_7_15, radial_eight_coeff,
    radial_seven_zero_16, radial_seven_zero_17, radial_seven_zero_18, radial_seven_zero_19,
    radialStepCoeff, radialInnerCoeff])

-- The last Gram-Schmidt direction tests the remaining native Schur pivot.
private theorem last_core_positive : 0 < fullGramPolynomial 49 14 4 4 := by
  norm_full_source

private theorem last_mixed_relative : (8/1000000000)*|fullGramPolynomial 196 35 4 4| ≤
    fullGramPolynomial 49 14 4 4/2 := by
  norm_full_source

private theorem last_second_relative : (16/1000000000^2)*|fullGramPolynomial 784 56 4 4| ≤
    fullGramPolynomial 49 14 4 4/100 := by
  norm_full_source

private theorem last_tail_relative : fullTailError 4 4 ≤ fullGramPolynomial 49 14 4 4/12100 := by
  norm_full_source

private theorem core_positive_0 : 0 < fullGramPolynomial 49 14 0 0 := by
  norm_full_source

private theorem mixed_relative_0 : (8/1000000000)*|fullGramPolynomial 196 35 0 0| ≤ fullGramPolynomial 49 14 0 0/2 := by
  norm_full_source

private theorem second_relative_0 : (16/1000000000^2)*|fullGramPolynomial 784 56 0 0| ≤ fullGramPolynomial 49 14 0 0/100 := by
  norm_full_source

private theorem tail_relative_0 : fullTailError 0 0 ≤ fullGramPolynomial 49 14 0 0/12100 := by
  norm_full_source

private theorem core_positive_1 : 0 < fullGramPolynomial 49 14 1 1 := by
  norm_full_source

private theorem mixed_relative_1 : (8/1000000000)*|fullGramPolynomial 196 35 1 1| ≤ fullGramPolynomial 49 14 1 1/2 := by
  norm_full_source

private theorem second_relative_1 : (16/1000000000^2)*|fullGramPolynomial 784 56 1 1| ≤ fullGramPolynomial 49 14 1 1/100 := by
  norm_full_source

private theorem tail_relative_1 : fullTailError 1 1 ≤ fullGramPolynomial 49 14 1 1/12100 := by
  norm_full_source

private theorem core_positive_2 : 0 < fullGramPolynomial 49 14 2 2 := by
  norm_full_source

private theorem mixed_relative_2 : (8/1000000000)*|fullGramPolynomial 196 35 2 2| ≤ fullGramPolynomial 49 14 2 2/2 := by
  norm_full_source

private theorem second_relative_2 : (16/1000000000^2)*|fullGramPolynomial 784 56 2 2| ≤ fullGramPolynomial 49 14 2 2/100 := by
  norm_full_source

private theorem tail_relative_2 : fullTailError 2 2 ≤ fullGramPolynomial 49 14 2 2/12100 := by
  norm_full_source

private theorem core_positive_3 : 0 < fullGramPolynomial 49 14 3 3 := by
  norm_full_source

private theorem mixed_relative_3 : (8/1000000000)*|fullGramPolynomial 196 35 3 3| ≤ fullGramPolynomial 49 14 3 3/2 := by
  norm_full_source

private theorem second_relative_3 : (16/1000000000^2)*|fullGramPolynomial 784 56 3 3| ≤ fullGramPolynomial 49 14 3 3/100 := by
  norm_full_source

private theorem tail_relative_3 : fullTailError 3 3 ≤ fullGramPolynomial 49 14 3 3/12100 := by
  norm_full_source

private theorem off_diagonal_relative_0_1 : fullError 0 1^2 ≤ (fullGramPolynomial 49 14 0 0/121)*(fullGramPolynomial 49 14 1 1/121)/400 := by
  norm_full_source

private theorem off_diagonal_relative_0_2 : fullError 0 2^2 ≤ (fullGramPolynomial 49 14 0 0/121)*(fullGramPolynomial 49 14 2 2/121)/400 := by
  norm_full_source

private theorem off_diagonal_relative_0_3 : fullError 0 3^2 ≤ (fullGramPolynomial 49 14 0 0/121)*(fullGramPolynomial 49 14 3 3/121)/400 := by
  norm_full_source

private theorem off_diagonal_relative_0_4 : fullError 0 4^2 ≤ (fullGramPolynomial 49 14 0 0/121)*(fullGramPolynomial 49 14 4 4/121)/400 := by
  norm_full_source

private theorem off_diagonal_relative_1_2 : fullError 1 2^2 ≤ (fullGramPolynomial 49 14 1 1/121)*(fullGramPolynomial 49 14 2 2/121)/400 := by
  norm_full_source

private theorem off_diagonal_relative_1_3 : fullError 1 3^2 ≤ (fullGramPolynomial 49 14 1 1/121)*(fullGramPolynomial 49 14 3 3/121)/400 := by
  norm_full_source

private theorem off_diagonal_relative_1_4 : fullError 1 4^2 ≤ (fullGramPolynomial 49 14 1 1/121)*(fullGramPolynomial 49 14 4 4/121)/400 := by
  norm_full_source

private theorem off_diagonal_relative_2_3 : fullError 2 3^2 ≤ (fullGramPolynomial 49 14 2 2/121)*(fullGramPolynomial 49 14 3 3/121)/400 := by
  norm_full_source

private theorem off_mixed_2_4 : ((8/1000000000)*|fullGramPolynomial 196 35 2 4|/121)^2 ≤ (fullGramPolynomial 49 14 2 2/121)*(fullGramPolynomial 49 14 4 4/121)/625 := by
  norm_full_source

private theorem off_second_2_4 : ((16/1000000000^2)*|fullGramPolynomial 784 56 2 4|/121)^2 ≤ (fullGramPolynomial 49 14 2 2/121)*(fullGramPolynomial 49 14 4 4/121)/40000 := by
  norm_full_source

private theorem off_tail_2_4 : (fullTailError 2 4)^2 ≤ (fullGramPolynomial 49 14 2 2/121)*(fullGramPolynomial 49 14 4 4/121)/40000 := by
  norm_full_source

private theorem off_diagonal_relative_2_4 : fullError 2 4^2 ≤ (fullGramPolynomial 49 14 2 2/121)*(fullGramPolynomial 49 14 4 4/121)/400 := by
  have h1 := sq_nonneg (((8/1000000000)*|fullGramPolynomial 196 35 2 4|/121)-8*((16/1000000000^2)*|fullGramPolynomial 784 56 2 4|/121))
  have h2 := sq_nonneg (((8/1000000000)*|fullGramPolynomial 196 35 2 4|/121)-8*(fullTailError 2 4))
  have h3 := sq_nonneg (((16/1000000000^2)*|fullGramPolynomial 784 56 2 4|/121)-(fullTailError 2 4))
  unfold fullError
  nlinarith only [off_mixed_2_4,off_second_2_4,off_tail_2_4,h1,h2,h3]

private theorem off_mixed_3_4 : ((8/1000000000)*|fullGramPolynomial 196 35 3 4|/121)^2 ≤ (fullGramPolynomial 49 14 3 3/121)*(fullGramPolynomial 49 14 4 4/121)/625 := by
  norm_full_source

private theorem off_second_3_4 : ((16/1000000000^2)*|fullGramPolynomial 784 56 3 4|/121)^2 ≤ (fullGramPolynomial 49 14 3 3/121)*(fullGramPolynomial 49 14 4 4/121)/40000 := by
  norm_full_source

private theorem diagonal_product_34 :
    (fullGramPolynomial 49 14 3 3/121)*(fullGramPolynomial 49 14 4 4/121) =
      (tailSchur 0 0*(tailSchur 1 1*tailSchur 2 2-tailSchur 1 2^2)-
        tailSchur 0 1*(tailSchur 0 1*tailSchur 2 2-tailSchur 0 2*tailSchur 1 2)+
        tailSchur 0 2*(tailSchur 0 1*tailSchur 1 2-tailSchur 0 2*tailSchur 1 1)) /
        (headDelta^2*tailSchur 0 0) := by
  norm_full_source

private theorem off_tail_3_4 : (fullTailError 3 4)^2 ≤ (fullGramPolynomial 49 14 3 3/121)*(fullGramPolynomial 49 14 4 4/121)/40000 := by
  rw [diagonal_product_34]
  norm_full_source

private theorem off_diagonal_relative_3_4 : fullError 3 4^2 ≤ (fullGramPolynomial 49 14 3 3/121)*(fullGramPolynomial 49 14 4 4/121)/400 := by
  have h1 := sq_nonneg (((8/1000000000)*|fullGramPolynomial 196 35 3 4|/121)-8*((16/1000000000^2)*|fullGramPolynomial 784 56 3 4|/121))
  have h2 := sq_nonneg (((8/1000000000)*|fullGramPolynomial 196 35 3 4|/121)-8*(fullTailError 3 4))
  have h3 := sq_nonneg (((16/1000000000^2)*|fullGramPolynomial 784 56 3 4|/121)-(fullTailError 3 4))
  unfold fullError
  nlinarith only [off_mixed_3_4,off_second_3_4,off_tail_3_4,h1,h2,h3]



private theorem first_atom_orthogonal_0_1 : fullGramPolynomial 49 14 0 1=0 := by
  norm_full_source

private theorem first_atom_orthogonal_0_2 : fullGramPolynomial 49 14 0 2=0 := by
  norm_full_source

private theorem first_atom_orthogonal_0_3 : fullGramPolynomial 49 14 0 3=0 := by
  norm_full_source

private theorem first_atom_orthogonal_0_4 : fullGramPolynomial 49 14 0 4=0 := by
  norm_full_source

private theorem first_atom_orthogonal_1_2 : fullGramPolynomial 49 14 1 2=0 := by
  norm_full_source

private theorem first_atom_orthogonal_1_3 : fullGramPolynomial 49 14 1 3=0 := by
  norm_full_source

private theorem first_atom_orthogonal_1_4 : fullGramPolynomial 49 14 1 4=0 := by
  norm_full_source

private theorem first_atom_orthogonal_2_3 : fullGramPolynomial 49 14 2 3=0 := by
  norm_full_source

private theorem first_atom_orthogonal_2_4 : fullGramPolynomial 49 14 2 4=0 := by
  norm_full_source

private theorem first_atom_orthogonal_3_4 : fullGramPolynomial 49 14 3 4=0 := by
  norm_full_source


private theorem core_positive (i : Fin 5) : 0 < fullGramPolynomial 49 14 i i := by
  fin_cases i
  · exact core_positive_0
  · exact core_positive_1
  · exact core_positive_2
  · exact core_positive_3
  · exact last_core_positive

private theorem mixed_relative (i : Fin 5) : (8/1000000000)*|fullGramPolynomial 196 35 i i| ≤ fullGramPolynomial 49 14 i i/2 := by
  fin_cases i
  · exact mixed_relative_0
  · exact mixed_relative_1
  · exact mixed_relative_2
  · exact mixed_relative_3
  · exact last_mixed_relative

private theorem second_relative (i : Fin 5) : (16/1000000000^2)*|fullGramPolynomial 784 56 i i| ≤ fullGramPolynomial 49 14 i i/100 := by
  fin_cases i
  · exact second_relative_0
  · exact second_relative_1
  · exact second_relative_2
  · exact second_relative_3
  · exact last_second_relative

private theorem tail_relative (i : Fin 5) : fullTailError i i ≤ fullGramPolynomial 49 14 i i/12100 := by
  fin_cases i
  · exact tail_relative_0
  · exact tail_relative_1
  · exact tail_relative_2
  · exact tail_relative_3
  · exact last_tail_relative

private theorem diagonal_error (i : Fin 5) :
    fullError i i ≤ (13/25)*(fullGramPolynomial 49 14 i i/121) := by
  unfold fullError
  nlinarith only [mixed_relative i,second_relative i,tail_relative i]

private theorem first_atom_orthogonal (i j : Fin 5) (hij : i < j) : fullGramPolynomial 49 14 i j=0 := by
  fin_cases i <;> fin_cases j <;> norm_num at hij
  · exact first_atom_orthogonal_0_1
  · exact first_atom_orthogonal_0_2
  · exact first_atom_orthogonal_0_3
  · exact first_atom_orthogonal_0_4
  · exact first_atom_orthogonal_1_2
  · exact first_atom_orthogonal_1_3
  · exact first_atom_orthogonal_1_4
  · exact first_atom_orthogonal_2_3
  · exact first_atom_orthogonal_2_4
  · exact first_atom_orthogonal_3_4

private theorem off_diagonal_relative (i j : Fin 5) (hij : i < j) : fullError i j^2 ≤ (fullGramPolynomial 49 14 i i/121)*(fullGramPolynomial 49 14 j j/121)/400 := by
  fin_cases i <;> fin_cases j <;> norm_num at hij
  · exact off_diagonal_relative_0_1
  · exact off_diagonal_relative_0_2
  · exact off_diagonal_relative_0_3
  · exact off_diagonal_relative_0_4
  · exact off_diagonal_relative_1_2
  · exact off_diagonal_relative_1_3
  · exact off_diagonal_relative_1_4
  · exact off_diagonal_relative_2_3
  · exact off_diagonal_relative_2_4
  · exact off_diagonal_relative_3_4


private def firstDiagonal (i : Fin 5) : ℝ := fullGramPolynomial 49 14 i i/121

private theorem firstDiagonal_pos (i : Fin 5) : 0 < firstDiagonal i :=
  div_pos (core_positive i) (by norm_num)

/-- Unit first-atom coordinates for the complete native fifth section. -/
def nativeBasis : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => fullVector j i/Real.sqrt (firstDiagonal j)

/-- The complete native form in normalized first-atom coordinates. -/
def nativeGram : Matrix (Fin 5) (Fin 5) ℝ :=
  nativeBasisᴴ * nativeShiftedMatrix 5 0 EvenFiveBoundary.witnessCenter * nativeBasis

private theorem nativeGram_entry (i j : Fin 5) : nativeGram i j =
    EvenFiveBoundary.scaleSevenEnergy (fullVector i) (fullVector j) EvenFiveBoundary.witnessCenter /
      (Real.sqrt (firstDiagonal i)*Real.sqrt (firstDiagonal j)) := by
  simp only [nativeGram,Matrix.mul_apply,Matrix.conjTranspose_apply,nativeBasis,star_trivial,
    Finset.sum_mul,EvenFiveBoundary.scaleSevenEnergy,nativeShiftedMatrix,add_zero,Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  simp only [div_eq_mul_inv,_root_.mul_inv_rev]
  ring

private theorem nativeGram_hermitian : nativeGram.IsHermitian := by
  unfold nativeGram
  apply Matrix.isHermitian_conjTranspose_mul_mul nativeBasis
  rw [Matrix.IsHermitian]
  ext i j
  simp [nativeShiftedMatrix,add_comm]

private theorem nativeGram_diagonal (i : Fin 5) :
    (12/25:ℝ)*thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1^2 ≤ nativeGram i i := by
  have hsource := neg_le_of_abs_le
    (EvenFiveBoundary.scaleSeven_bilinear_error (fullVector i) (fullVector i))
  have herror := mul_le_mul_of_nonneg_right (diagonal_error i)
    (sq_nonneg (thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1))
  have hroot : Real.sqrt (firstDiagonal i)*Real.sqrt (firstDiagonal i) = firstDiagonal i := by
    nlinarith only [Real.sq_sqrt (firstDiagonal_pos i).le]
  rw [nativeGram_entry,hroot]
  apply (le_div_iff₀ (firstDiagonal_pos i)).mpr
  change - (fullError i i*thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1^2) ≤
    EvenFiveBoundary.scaleSevenEnergy (fullVector i) (fullVector i) EvenFiveBoundary.witnessCenter-
      thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1^2/121*fullGramPolynomial 49 14 i i at hsource
  dsimp only [firstDiagonal]
  nlinarith only [hsource,herror]

private theorem nativeGram_upper_bound (i j : Fin 5) (hij : i < j) :
    |nativeGram i j| ≤ (1/20:ℝ)*thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1^2 := by
  let t := Real.sqrt (firstDiagonal i)*Real.sqrt (firstDiagonal j)
  have ht : 0 < t := mul_pos (Real.sqrt_pos.2 (firstDiagonal_pos i))
    (Real.sqrt_pos.2 (firstDiagonal_pos j))
  have ht2 : t^2 = firstDiagonal i*firstDiagonal j := by
    dsimp only [t]
    rw [mul_pow,Real.sq_sqrt (firstDiagonal_pos i).le,Real.sq_sqrt (firstDiagonal_pos j).le]
  have he : fullError i j ≤ t/20 := by
    have hsq := off_diagonal_relative i j hij
    change fullError i j^2 ≤ firstDiagonal i*firstDiagonal j/400 at hsq
    by_contra h
    have hd : 0 < fullError i j-t/20 := sub_pos.mpr (lt_of_not_ge h)
    have hs : 0 < fullError i j+t/20 := by linarith only [hd,ht]
    have hp := mul_pos hd hs
    nlinarith only [hp,hsq,ht2]
  have hsource := EvenFiveBoundary.scaleSeven_bilinear_error (fullVector i) (fullVector j)
  change |EvenFiveBoundary.scaleSevenEnergy (fullVector i) (fullVector j) EvenFiveBoundary.witnessCenter-
    thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1^2/121*fullGramPolynomial 49 14 i j| ≤
      fullError i j*thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1^2 at hsource
  rw [first_atom_orthogonal i j hij,mul_zero,sub_zero] at hsource
  rw [nativeGram_entry,abs_div,abs_of_pos ht]
  apply (div_le_iff₀ ht).mpr
  have hmul := mul_le_mul_of_nonneg_right he
    (sq_nonneg (thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1))
  nlinarith only [hsource,hmul]

private theorem nativeGram_off_diagonal (i j : Fin 5) (hij : i ≠ j) :
    |nativeGram i j| ≤ (1/20:ℝ)*thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1^2 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact nativeGram_upper_bound i j h
  · have he : nativeGram i j = nativeGram j i := by
      have hh := congrFun (congrFun nativeGram_hermitian i) j
      simpa only [Matrix.conjTranspose_apply,star_trivial] using hh.symm
    rw [he]
    exact nativeGram_upper_bound j i h

private theorem nativeBasis_triangular : nativeBasis.BlockTriangular id := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals norm_num [nativeBasis,fullVector,tailColumn]

private theorem nativeBasis_diagonal (i : Fin 5) :
    nativeBasis i i = 1/Real.sqrt (firstDiagonal i) := by
  fin_cases i <;> norm_num [nativeBasis,fullVector,tailColumn]

private theorem nativeBasis_det_pos : 0 < nativeBasis.det := by
  rw [Matrix.det_of_upperTriangular nativeBasis_triangular]
  apply Finset.prod_pos
  intro i hi
  rw [nativeBasis_diagonal]
  exact div_pos (by norm_num) (Real.sqrt_pos.2 (firstDiagonal_pos i))

private theorem nativeBasis_inverse : nativeBasis*nativeBasis⁻¹ = 1 :=
  Matrix.mul_nonsing_inv nativeBasis (isUnit_iff_ne_zero.mpr nativeBasis_det_pos.ne')

private theorem first_mass_pos : 0 < thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1 := by
  apply thetaCuspSourceTerm_pos_of_pos_of_nat_pos
  · unfold EvenFiveBoundary.witnessCenter
    apply div_pos
    · apply Real.log_pos
      exact (lt_div_iff₀ Real.pi_pos).mpr (by nlinarith only [Real.pi_lt_four])
    · norm_num
  · norm_num

/-- The complete native fifth-section form has an explicit positive quadratic floor. -/
theorem nativeGram_coercive (v : Fin 5 → ℝ) :
    (23/100:ℝ)*thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1^2*∑ i, v i^2 ≤
      v ⬝ᵥ (nativeGram *ᵥ v) := by
  let B : Matrix (Fin 5) (Fin 5) ℝ := Matrix.diagonal (fun i => nativeGram i i)
  let P := nativeGram-B
  have hB : (12/25:ℝ)*thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1^2*∑ i, v i^2 ≤
      v ⬝ᵥ (B *ᵥ v) := by
    simp only [B, dotProduct, Matrix.mulVec_diagonal, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_right (nativeGram_diagonal i) (sq_nonneg (v i))
    nlinarith only [h]
  have hbound : ∀ i j, |P i j| ≤ (1/20:ℝ)*thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1^2 := by
    intro i j
    by_cases h : i = j
    · subst j
      simp only [P,B,Matrix.sub_apply,Matrix.diagonal_apply_eq,sub_self,abs_zero]
      positivity
    · simpa only [P,B,Matrix.sub_apply,Matrix.diagonal_apply_ne _ h,sub_zero] using
        nativeGram_off_diagonal i j h
  have hP := neg_le_of_abs_le (RHTower.abs_dotProduct_mulVec_le P (by positivity) hbound v)
  have he : v ⬝ᵥ (nativeGram *ᵥ v) = v ⬝ᵥ (B *ᵥ v)+v ⬝ᵥ (P *ᵥ v) := by
    simp [P, Matrix.sub_mulVec, dotProduct_sub]
  norm_num only [Fintype.card_fin, Nat.cast_ofNat] at hP
  rw [he]
  linarith only [hB,hP]

/-- The complete native fifth-section form is positive definite at scale seven. -/
theorem nativeGram_posDef : nativeGram.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos nativeGram_hermitian fun v hv => ?_
  have hs : 0 < ∑ i, v i^2 := by
    obtain ⟨i,hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨i,Finset.mem_univ i,?_⟩
    rw [← sq_abs]
    exact pow_pos (abs_pos.mpr hi) 2
  have hp : 0 < (23/100:ℝ)*thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1^2*∑ i, v i^2 :=
    mul_pos (mul_pos (by norm_num) (sq_pos_of_pos first_mass_pos)) hs
  simpa only [star_trivial] using hp.trans_le (nativeGram_coercive v)

/-- The complete native fifth even source is positive definite at scale seven. -/
theorem native_scale_seven_posDef :
    (nativeShiftedMatrix 5 0 EvenFiveBoundary.witnessCenter).PosDef := by
  have hinj : Function.Injective (nativeBasis⁻¹).mulVec := by
    intro v w h
    have hh := congrArg (fun u => nativeBasis *ᵥ u) h
    simpa only [Matrix.mulVec_mulVec,nativeBasis_inverse,Matrix.one_mulVec] using hh
  have hback := nativeGram_posDef.conjTranspose_mul_mul_same hinj
  have hb : (nativeBasis⁻¹)ᴴ * nativeGram * nativeBasis⁻¹ =
      nativeShiftedMatrix 5 0 EvenFiveBoundary.witnessCenter := by
    unfold nativeGram
    calc
      _ = (nativeBasis*nativeBasis⁻¹)ᴴ *
          nativeShiftedMatrix 5 0 EvenFiveBoundary.witnessCenter *
          (nativeBasis*nativeBasis⁻¹) := by
        simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = _ := by rw [nativeBasis_inverse]; simp
  rwa [hb] at hback

end GaloisForLFunctions.ThetaCuspSections.EvenFiveScaleSevenNative

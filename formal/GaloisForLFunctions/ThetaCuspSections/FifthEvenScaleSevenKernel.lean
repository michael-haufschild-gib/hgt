import GaloisForLFunctions.ThetaCuspSections.FifthEvenOriginObstruction
import GaloisForLFunctions.RHTower.FiniteDegreeReciprocalPerturbation

/-!
# Complete common-kernel positivity at scale seven

The two coupled flux directions leave a three-dimensional common kernel.
An adapted basis diagonalizes its first-atom form. Exact radial inequalities,
the retained two-atom expansion and the Cauchy remainder give a positive
quadratic floor for the complete native source on this kernel.
-/

noncomputable section
open Matrix RHTower Polynomial RHTower.ThetaCuspGaussianLimit
namespace GaloisForLFunctions.ThetaCuspSections.EvenFiveScaleSeven

private def m (k : ℕ) : ℝ := (thetaPairRadialEvenPolynomial 49 k).eval 14 / 121
private def d : ℝ := m 0*m 2-m 1^2
private def b0 : ℝ := -420*m 2+m 3-m 4/1568
private def b1 : ℝ := -420*m 3+m 4-m 5/1568
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

private def headZero : ℝ := -(m 2*b0-m 1*b1)/d
private def headOne : ℝ := (m 1*b0-m 0*b1)/d
private def adapted (i : Fin 3) (k : Fin 5) : ℝ :=
 if i.val=0 then (if k.val=0 then 1 else 0)
 else if i.val=1 then (if k.val=0 then -m 1/100 else if k.val=1 then 1/100 else 0)
 else (if k.val=0 then headZero/1000000 else if k.val=1 then headOne/1000000
  else if k.val=2 then -420/1000000 else if k.val=3 then 1/1000000 else -1/(1568*1000000))
private def gramPoly (a X : ℝ) (i j : Fin 3) : ℝ :=
 ∑ u : Fin 5, ∑ v : Fin 5, adapted i u*adapted j v*(thetaPairRadialEvenPolynomial a (u.val+v.val)).eval X
private def cauchyError (i j : Fin 3) : ℝ :=
 ∑ u : Fin 5, ∑ v : Fin 5, |adapted i u| * |adapted j v| * ((2*(u.val+v.val)).factorial:ℝ) /
   (10000000000000*(3/20:ℝ)^(2*(u.val+v.val)))
private def errorBound (i j : Fin 3) : ℝ :=
 ((8/1000000000)*|gramPoly 196 35 i j|+(16/1000000000^2)*|gramPoly 784 56 i j|)/121+cauchyError i j

-- Finite radial coefficients reduce the Gram and error inequalities to rational arithmetic.
local macro "norm_kernel" : tactic =>
  `(tactic| norm_num [gramPoly, errorBound, cauchyError, adapted, headZero, headOne, b0, b1, d, m, Fin.sum_univ_succ,
    Nat.factorial, eval_thetaPairRadialEvenPolynomial, Finset.sum_range_succ, radialCoeffs_0_0,
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
    radialStepCoeff, radialInnerCoeff] at *)

private theorem core_diagonal (i : Fin 3) : (1/100:ℝ) < gramPoly 49 14 i i/121 := by
  fin_cases i
  all_goals norm_kernel

private theorem core_off_diagonal (i j : Fin 3) (h : i ≠ j) : gramPoly 49 14 i j=0 := by
  fin_cases i <;> fin_cases j
  all_goals norm_kernel

private theorem error_0_0 : errorBound 0 0 ≤ 1/1000 := by
  norm_kernel

private theorem error_0_1 : errorBound 0 1 ≤ 1/1000 := by
  norm_kernel

private theorem error_0_2 : errorBound 0 2 ≤ 1/1000 := by
  norm_kernel

private theorem error_1_0 : errorBound 1 0 ≤ 1/1000 := by
  norm_kernel

private theorem error_1_1 : errorBound 1 1 ≤ 1/1000 := by
  norm_kernel

private theorem error_1_2 : errorBound 1 2 ≤ 1/1000 := by
  norm_kernel

private theorem error_2_0 : errorBound 2 0 ≤ 1/1000 := by
  norm_kernel

private theorem error_2_1 : errorBound 2 1 ≤ 1/1000 := by
  norm_kernel

private theorem mixed_diagonal_relative_bound : (8/1000000000)*|gramPoly 196 35 2 2|/121 ≤ gramPoly 49 14 2 2/242 := by
  norm_kernel

private theorem error_two_last : ((16/1000000000^2)*|gramPoly 784 56 2 2|)/121 ≤ 1/3000 := by
  norm_kernel

private theorem error_two_tail : cauchyError 2 2 ≤ 1/3000 := by
  norm_kernel

private theorem small_entry_error (i j : Fin 3) (h : i ≠ 2 ∨ j ≠ 2) : errorBound i j ≤ 1/1000 := by
  fin_cases i <;> fin_cases j
  · exact error_0_0
  · exact error_0_1
  · exact error_0_2
  · exact error_1_0
  · exact error_1_1
  · exact error_1_2
  · exact error_2_0
  · exact error_2_1
  · rcases h with h | h <;> exact False.elim (h rfl)



private theorem error_two_relative_bound : errorBound 2 2 ≤ gramPoly 49 14 2 2/242+1/1500 := by
  unfold errorBound
  linarith only [mixed_diagonal_relative_bound,error_two_last,error_two_tail]

/-- Adapted coordinates diagonalize the first-atom form on the common kernel. -/
def kernelBasis : Matrix (Fin 5) (Fin 3) ℝ := fun i j => adapted j i

/-- The complete source restricted to the adapted common kernel at scale seven. -/
def kernelGram : Matrix (Fin 3) (Fin 3) ℝ :=
  kernelBasisᴴ * nativeShiftedMatrix 5 0 EvenFiveBoundary.witnessCenter * kernelBasis

private theorem gram_entry (i j : Fin 3) : kernelGram i j =
    EvenFiveBoundary.scaleSevenEnergy (adapted i) (adapted j) EvenFiveBoundary.witnessCenter := by
  simp only [kernelGram, Matrix.mul_apply, Matrix.conjTranspose_apply, kernelBasis, star_trivial,
    EvenFiveBoundary.scaleSevenEnergy, Finset.sum_mul, nativeShiftedMatrix, add_zero]
  rw [Finset.sum_comm]

private theorem gram_hermitian : kernelGram.IsHermitian := by
  unfold kernelGram
  apply Matrix.isHermitian_conjTranspose_mul_mul kernelBasis
  rw [Matrix.IsHermitian]
  ext i j
  simp [nativeShiftedMatrix, add_comm]

private theorem first_mass_pos : 0 < thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1 := by
  apply thetaCuspSourceTerm_pos_of_pos_of_nat_pos
  · unfold EvenFiveBoundary.witnessCenter
    apply div_pos
    · apply Real.log_pos
      exact (lt_div_iff₀ Real.pi_pos).mpr (by nlinarith only [Real.pi_lt_four])
    · norm_num
  · norm_num

private theorem gram_error (i j : Fin 3) :
    |kernelGram i j-thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1^2/121*gramPoly 49 14 i j| ≤
      errorBound i j*thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1^2 := by
  rw [gram_entry]
  exact EvenFiveBoundary.scaleSeven_bilinear_error (adapted i) (adapted j)

private theorem diagonal_lower (i : Fin 3) :
    (1/250:ℝ)*thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1^2 ≤ kernelGram i i := by
  have he := neg_le_of_abs_le (gram_error i i)
  have hm := mul_le_mul_of_nonneg_right (core_diagonal i).le
    (sq_nonneg (thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1))
  have hs := sq_nonneg (thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1)
  by_cases hi : i = 2
  · subst i
    have hb := mul_le_mul_of_nonneg_right error_two_relative_bound
      (sq_nonneg (thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1))
    nlinarith only [he,hm,hb,hs]
  · have hb := mul_le_mul_of_nonneg_right (small_entry_error i i (Or.inl hi))
      (sq_nonneg (thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1))
    nlinarith only [he,hm,hb,hs]

private theorem off_diagonal_bound (i j : Fin 3) (h : i ≠ j) :
    |kernelGram i j| ≤ (1/1000:ℝ)*thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1^2 := by
  have he := gram_error i j
  rw [core_off_diagonal i j h,mul_zero,sub_zero] at he
  have hi : i ≠ 2 ∨ j ≠ 2 := by
    by_cases hi : i = 2
    · exact Or.inr (fun hj => h (hi.trans hj.symm))
    · exact Or.inl hi
  exact he.trans (mul_le_mul_of_nonneg_right (small_entry_error i j hi) (sq_nonneg _))

/-- The complete common-kernel form has an explicit positive quadratic floor. -/
theorem kernelGram_coercive (v : Fin 3 → ℝ) :
    (1/1000:ℝ)*thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1^2*∑ i, v i^2 ≤
      v ⬝ᵥ (kernelGram *ᵥ v) := by
  let B : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal (fun i => kernelGram i i)
  let P := kernelGram-B
  have hB : (1/250:ℝ)*thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1^2*∑ i, v i^2 ≤
      v ⬝ᵥ (B *ᵥ v) := by
    simp only [B, dotProduct, Matrix.mulVec_diagonal, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_right (diagonal_lower i) (sq_nonneg (v i))
    nlinarith only [h]
  have hbound : ∀ i j, |P i j| ≤ (1/1000:ℝ)*thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1^2 := by
    intro i j
    by_cases h : i = j
    · subst j
      simp only [P,B,Matrix.sub_apply,Matrix.diagonal_apply_eq,sub_self,abs_zero]
      positivity
    · simpa only [P,B,Matrix.sub_apply,Matrix.diagonal_apply_ne _ h,sub_zero] using
        off_diagonal_bound i j h
  have hP := neg_le_of_abs_le (RHTower.abs_dotProduct_mulVec_le P (by positivity) hbound v)
  have he : v ⬝ᵥ (kernelGram *ᵥ v) = v ⬝ᵥ (B *ᵥ v)+v ⬝ᵥ (P *ᵥ v) := by
    simp [P, Matrix.sub_mulVec, dotProduct_sub]
  norm_num only [Fintype.card_fin, Nat.cast_ofNat] at hP
  rw [he]
  linarith only [hB,hP]

/-- The complete common-kernel form is positive definite at scale seven. -/
theorem kernelGram_posDef : kernelGram.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos gram_hermitian fun v hv => ?_
  have hs : 0 < ∑ i, v i^2 := by
    obtain ⟨i,hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨i,Finset.mem_univ i,?_⟩
    rw [← sq_abs]
    exact pow_pos (abs_pos.mpr hi) 2
  have hp : 0 < (1/1000:ℝ)*thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1^2*∑ i, v i^2 :=
    mul_pos (mul_pos (by norm_num) (sq_pos_of_pos first_mass_pos)) hs
  simpa only [star_trivial] using hp.trans_le (kernelGram_coercive v)

private def changeBasis : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1,-m 1/100,headZero/1000000; 0,1/100,headOne/1000000; 0,0,1/1000000]

private def inverseChangeBasis : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1,m 1,-m 1*headOne-headZero; 0,100,-100*headOne; 0,0,1000000]

private theorem basis_factor : kernelBasis = EvenFiveOrigin.coherentKernelBasis*changeBasis := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [kernelBasis,adapted,EvenFiveOrigin.coherentKernelBasis,changeBasis,Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

private theorem basis_inverse : changeBasis*inverseChangeBasis = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [changeBasis,inverseChangeBasis,Matrix.mul_apply,Fin.sum_univ_succ,
      Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Matrix.one_apply] <;> ring

/-- The native source is strictly positive on the common kernel of both coupled loads. -/
theorem coherentKernel_scale_seven_posDef :
    (EvenFiveOrigin.coherentKernel EvenFiveBoundary.witnessCenter).PosDef := by
  have he : kernelGram = changeBasisᴴ *
      EvenFiveOrigin.coherentKernel EvenFiveBoundary.witnessCenter * changeBasis := by
    simp only [kernelGram,basis_factor,EvenFiveOrigin.coherentKernel,
      Matrix.conjTranspose_mul,Matrix.mul_assoc]
  have hinj : Function.Injective inverseChangeBasis.mulVec := by
    intro v w h
    have hh := congrArg (fun u => changeBasis *ᵥ u) h
    simpa only [Matrix.mulVec_mulVec,basis_inverse,Matrix.one_mulVec] using hh
  have hback := kernelGram_posDef.conjTranspose_mul_mul_same hinj
  have hb : inverseChangeBasisᴴ * kernelGram * inverseChangeBasis =
      EvenFiveOrigin.coherentKernel EvenFiveBoundary.witnessCenter := by
    rw [he]
    calc
      _ = (changeBasis*inverseChangeBasis)ᴴ *
          EvenFiveOrigin.coherentKernel EvenFiveBoundary.witnessCenter *
          (changeBasis*inverseChangeBasis) := by
        simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = _ := by rw [basis_inverse]; simp
  rwa [hb] at hback

end GaloisForLFunctions.ThetaCuspSections.EvenFiveScaleSeven

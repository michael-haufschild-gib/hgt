import GaloisForLFunctions.RHTower.ThetaSourceGlobalStrictLogConvexity
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor

/-!
# Strict shifted Hankel matrices of the completed theta source

The even raw theta moments are the even moments of the full, reflected theta measure.
Taking odd polynomial indices in its strictly positive definite moment Hankel matrix
gives the shifted even-moment Hankel matrices. Normalization preserves determinant
positivity, including the exact size-two and size-three inequalities needed by K-RVM.
-/

open MeasureTheory Set
namespace RHTower
noncomputable section

/-- The full even theta moment equals the raw even moment defined on the positive half-line. -/
theorem thetaTiltMoment_zero_even_eq_raw (j : ℕ) :
    thetaTiltMoment 0 (2*j) = thetaCuspRawEvenMoment j := by
  let f : ℝ → ℝ := fun x => x^(2*j)*thetaCuspFullSource x
  have hf : Integrable f := by
    simpa only [f, zero_mul, Real.exp_zero, mul_one] using
      (integrable_thetaTiltIntegrand_global 0 (2*j))
  have heven : ∀ x : ℝ, f (-x) = f x := by
    intro x
    dsimp [f]
    rw [thetaCuspFullSource_neg]
    simp [pow_mul]
  have hsplit : (∫ x : ℝ, f x) =
      (∫ x : ℝ in Iic 0, f x) + (∫ x : ℝ in Ioi 0, f x) :=
    (intervalIntegral.integral_Iic_add_Ioi (b := 0) hf.integrableOn hf.integrableOn).symm
  calc
    thetaTiltMoment 0 (2*j) = ∫ x : ℝ, f x := by
      simp only [thetaTiltMoment, f, zero_mul, Real.exp_zero, mul_one]
    _ = (∫ x : ℝ in Iic 0, f x) + (∫ x : ℝ in Ioi 0, f x) := hsplit
    _ = (∫ x : ℝ in Ioi 0, f x) + (∫ x : ℝ in Ioi 0, f x) := by
      have hneg : (∫ x : ℝ in Iic 0, f x) = ∫ x : ℝ in Ioi 0, f x := by
        simpa only [neg_zero, heven] using (integral_comp_neg_Ioi 0 f).symm
      rw [hneg]
    _ = thetaCuspRawEvenMoment j := by
      rw [thetaCuspRawEvenMoment]
      dsimp [f]
      ring

/-- Every shifted raw even-moment Hankel matrix of the literal theta source is positive definite. -/
theorem thetaCuspRawEvenMoment_shiftedHankel_posDef (n : ℕ) :
    (HTGeometry.momentHankelMatrix
      (fun k => thetaCuspRawEvenMoment (k + 1)) n).PosDef := by
  classical
  let N : ℕ := 2*n+1
  let e : Fin n → Fin N := fun i => ⟨2*(i : ℕ)+1, by
    dsimp [N]
    omega⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    have hval := congrArg Fin.val hij
    dsimp [e] at hval
    omega
  let H : Matrix (Fin N) (Fin N) ℝ :=
    HTGeometry.momentHankelMatrix (thetaTiltMoment 0) N
  have hH : H.PosDef :=
    HTGeometry.momentHankelMatrix_posDef_of_infiniteSupport
      (thetaTiltMoment 0) (fun k => thetaTiltMoment_eq_integral_measure k)
      (integrable_pow_thetaTiltMeasure_global 0)
      (thetaTiltMeasure_compl_finset_pos 0) N
  have hS : (H.submatrix e e).PosDef := hH.submatrix he
  have hEq : H.submatrix e e =
      HTGeometry.momentHankelMatrix
        (fun k => thetaCuspRawEvenMoment (k + 1)) n := by
    ext i j
    change thetaTiltMoment 0 ((2*(i : ℕ)+1)+(2*(j : ℕ)+1)) =
      thetaCuspRawEvenMoment ((i : ℕ)+(j : ℕ)+1)
    rw [show (2*(i : ℕ)+1)+(2*(j : ℕ)+1) =
      2*((i : ℕ)+(j : ℕ)+1) by omega,
      thetaTiltMoment_zero_even_eq_raw]
  rwa [hEq] at hS

/-- Every shifted normalized even-moment Hankel determinant is strictly positive. -/
theorem thetaCuspNormalizedEvenMoment_shiftedHankel_det_pos (n : ℕ) :
    0 < (HTGeometry.momentHankelMatrix
      (fun k => thetaCuspNormalizedEvenMoment (k + 1)) n).det := by
  let R : Matrix (Fin n) (Fin n) ℝ :=
    HTGeometry.momentHankelMatrix
      (fun k => thetaCuspRawEvenMoment (k + 1)) n
  let T : Matrix (Fin n) (Fin n) ℝ :=
    HTGeometry.momentHankelMatrix
      (fun k => thetaCuspNormalizedEvenMoment (k + 1)) n
  have hR : 0 < R.det :=
    (thetaCuspRawEvenMoment_shiftedHankel_posDef n).det_pos
  have hEq : T = (thetaCuspRawEvenMoment 0)⁻¹ • R := by
    ext i j
    change thetaCuspRawEvenMoment ((i : ℕ)+(j : ℕ)+1) /
        thetaCuspRawEvenMoment 0 =
      (thetaCuspRawEvenMoment 0)⁻¹ *
        thetaCuspRawEvenMoment ((i : ℕ)+(j : ℕ)+1)
    rw [div_eq_mul_inv]
    ring
  change 0 < T.det
  rw [hEq, Matrix.det_smul]
  exact mul_pos (pow_pos (inv_pos.mpr thetaCuspRawEvenMoment_zero_pos) _) hR

/-- Strict shifted size-two determinant. -/
theorem thetaCuspNormalizedEvenMoment_shifted_q_pos :
    0 < thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 3 -
      thetaCuspNormalizedEvenMoment 2 ^ 2 := by
  have h := thetaCuspNormalizedEvenMoment_shiftedHankel_det_pos 2
  simpa [HTGeometry.momentHankelMatrix, Matrix.det_fin_two, pow_two] using h

/-- Strict shifted size-three determinant, the fifth-moment residual in K-RVM. -/
theorem thetaCuspNormalizedEvenMoment_shifted_delta_pos :
    0 < (thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 3 -
      thetaCuspNormalizedEvenMoment 2 ^ 2) * thetaCuspNormalizedEvenMoment 5 -
      (thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 4 ^ 2 -
        2 * thetaCuspNormalizedEvenMoment 2 * thetaCuspNormalizedEvenMoment 3 *
          thetaCuspNormalizedEvenMoment 4 +
        thetaCuspNormalizedEvenMoment 3 ^ 3) := by
  have h := thetaCuspNormalizedEvenMoment_shiftedHankel_det_pos 3
  convert h using 1
  simp [HTGeometry.momentHankelMatrix, Matrix.det_fin_three]
  ring

end
end RHTower

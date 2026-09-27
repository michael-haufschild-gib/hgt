import GaloisForLFunctions.RHTower.XiGaussianCofactorPhaseTransfer
import GaloisForLFunctions.RHTower.XiGaussianDerivativeOrientation

/-!
# Signed Gaussian derivatives transferred to critical nodal energy

Each cofactor polynomial is differentiated together with its heat factor.
The complete amplitude is reconstructed before weighted nodal comparison.
-/

open scoped Real BigOperators
open Complex GaloisForLFunctions.HTGeometry
noncomputable section

namespace RHTower

def xiGaussianDerivativeCofactorEnvelope {N : ℕ} (x : Fin N → ℝ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) : ℝ :=
  ∑ i, xiGaussianDerivativeRootEnvelope
    (∑ j, Polynomial.C ((Matrix.vandermonde x).adjugate j i) * Polynomial.X ^ (j : ℕ)) s t *
      Real.exp (t * x i)

theorem xiGaussianDerivativeCofactorEnvelope_nonneg {N : ℕ} (x : Fin N → ℝ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) : 0 ≤ xiGaussianDerivativeCofactorEnvelope x s t :=
  Finset.sum_nonneg fun _ _ => mul_nonneg
    (xiGaussianDerivativeRootEnvelope_nonneg _ s t) (Real.exp_pos _).le

theorem xiGaussianDerivativeCofactorEnvelope_eq_sum {N : ℕ} (x : Fin N → ℝ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) :
    xiGaussianDerivativeCofactorEnvelope x s t =
      ∑ i, xiGaussianDerivativeRootEnvelope
        (∑ j, Polynomial.C ((Matrix.vandermonde x).adjugate j i) * Polynomial.X ^ (j : ℕ)) s t *
          Real.exp (t * x i) := rfl

/-- The complete imaginary atom is transferred to its actual nodal energy before summing. -/
theorem xiGaussianImaginaryAtom_le_derivative_cofactor_orientation {N : ℕ}
    (F : Finset XiZeroCopy) (x a : Fin N → ℝ) (s : {s : ℝ // 0 < s})
    (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)}) (q : XiZeroCopy) :
    (Matrix.vandermonde x).det ^ 2 * xiGaussianImaginaryChannelAtom
      (∑ j, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)) t.1 q ≤
      ((∑ i, ((∑ j, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)).eval (x i)) ^ 2 *
          Real.exp (-((t.1 : ℝ) * x i))) *
        Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
          xiGaussianDerivativeCofactorEnvelope x s t.1) * (xiZeroCopyReciprocalSquare q).im ^ 2 := by
  let M := Matrix.vandermonde x
  let h : Fin N → ℝ := fun j =>
    (heatPhaseAmplitude ((xiSpectralPoint q ^ 2) ^ (j : ℕ)) t.1 (xiSpectralPoint q ^ 2)).im
  let E := ∑ i, (M.mulVec a i) ^ 2 * Real.exp (-((t.1 : ℝ) * x i))
  let e := Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F))
  let u := (xiZeroCopyReciprocalSquare q).im
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hb (i : Fin N) : (∑ j, M.adjugate j i * h j) ^ 2 ≤
      (e * xiGaussianDerivativeRootEnvelope
        (∑ j, Polynomial.C (M.adjugate j i) * Polynomial.X ^ (j : ℕ)) s t.1) * u ^ 2 := by
    have h := xiGaussianImaginaryAtom_le_derivative_orientation F
      (∑ j, Polynomial.C (M.adjugate j i) * Polynomial.X ^ (j : ℕ)) s t q
    rwa [xiGaussianImaginaryChannelAtom_finSum_eq] at h
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_right (hb i) (Real.exp_pos ((t.1 : ℝ) * x i)).le
  have hsum : (∑ i, (∑ j, M.adjugate j i * h j) ^ 2 * Real.exp ((t.1 : ℝ) * x i)) ≤
      e * xiGaussianDerivativeCofactorEnvelope x s t.1 * u ^ 2 := by
    refine hs.trans_eq ?_
    rw [xiGaussianDerivativeCofactorEnvelope_eq_sum, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have htransfer := real_adjugate_heat_phase_bound M a h x t.1
  have hfinal := htransfer.trans (mul_le_mul_of_nonneg_left hsum hE)
  rw [xiGaussianImaginaryChannelAtom_finSum_eq]
  change M.det ^ 2 * (∑ j, a j * h j) ^ 2 ≤ _
  calc
    _ ≤ E * (e * xiGaussianDerivativeCofactorEnvelope x s t.1 * u ^ 2) := hfinal
    _ = _ := by
      dsimp only [E, M, e, u]
      simp only [real_vandermonde_mulVec_eq_eval]
      ring

/-- A new coefficient-uniform phase bound relative to the full weighted nodal energy. -/
theorem xiGaussianImaginaryChannel_le_derivative_cofactor_budget {N : ℕ}
    (F : Finset XiZeroCopy) (x a : Fin N → ℝ) (s : {s : ℝ // 0 < s})
    (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)}) :
    (Matrix.vandermonde x).det ^ 2 *
      (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom
        (∑ j, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)) t.1 q) ≤
      ((∑ i, ((∑ j, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)).eval (x i)) ^ 2 *
          Real.exp (-((t.1 : ℝ) * x i))) *
        Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
          xiGaussianDerivativeCofactorEnvelope x s t.1) * xiResidualOrientationBudget F := by
  let Q : Polynomial ℝ := ∑ j, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)
  let C := (∑ i, Q.eval (x i) ^ 2 * Real.exp (-((t.1 : ℝ) * x i))) *
    Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
      xiGaussianDerivativeCofactorEnvelope x s t.1
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg
    (Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      (Real.exp_pos _).le) (xiGaussianDerivativeCofactorEnvelope_nonneg x s t.1)
  have h := ((summable_xiGaussianImaginaryChannelAtom Q t.1).mul_left
    ((Matrix.vandermonde x).det ^ 2)).tsum_le_tsum
      (xiGaussianImaginaryAtom_le_derivative_cofactor_orientation F x a s t)
      (summable_xiThermalOrientationTerm.mul_left C)
  rw [tsum_mul_left, tsum_mul_left] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (xiThermalOrientationEnergy_le_residualOrientationBudget F) hC)

end RHTower

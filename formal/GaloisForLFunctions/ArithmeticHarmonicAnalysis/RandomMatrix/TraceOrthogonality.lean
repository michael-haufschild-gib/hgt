import GaloisForLFunctions.HTGeometry.FiniteUnitaryHaarMeasureLaw
import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryRotatedLogNullhomotopy

/-!
# Homogeneous trace words under unitary Haar measure

The trace generating functions in arXiv:2611.05000 split into homogeneous
degrees. Central rotations make unequal degrees orthogonal under
normalized finite-unitary Haar measure. This applies to arbitrary
products of power traces, including every term in a trace-sum coefficient.
-/

noncomputable section

open Finset MeasureTheory Complex
open GaloisForLFunctions.HTGeometry
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.RandomMatrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A product of power traces, homogeneous of degree `∑ j, a j`. -/
def traceWord {r : ℕ} (a : Fin r → ℕ) (U : Matrix.unitaryGroup ι ℂ) : ℂ :=
  ∏ j, Matrix.trace ((U : Matrix ι ι ℂ) ^ a j)

theorem continuous_traceWord {r : ℕ} (a : Fin r → ℕ) :
    Continuous (traceWord (ι := ι) a) := by
  unfold traceWord Matrix.trace
  fun_prop

/-- These Haar moments are integrable because their integrands are continuous on a compact group. -/
theorem integrable_traceWord_pair {r s : ℕ} (a : Fin r → ℕ) (b : Fin s → ℕ) :
    Integrable (fun U : Matrix.unitaryGroup ι ℂ =>
      traceWord a U * (starRingEnd ℂ) (traceWord b U)) (finiteUnitaryHaar ι) := by
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  exact (continuous_traceWord a).mul ((continuous_traceWord b).star)

theorem traceWord_rotate {r : ℕ} (a : Fin r → ℕ) (t : ℝ)
    (U : Matrix.unitaryGroup ι ℂ) :
    traceWord a (scalarPhaseUnitaryMatrix (iota := ι) t * U) =
      Complex.exp (Complex.I * t * (∑ j, a j)) * traceWord a U := by
  have hmat : ((scalarPhaseUnitaryMatrix (iota := ι) t * U : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) =
      Complex.exp (Complex.I * t) • (U : Matrix ι ι ℂ) := by
    change (scalarPhaseUnitaryMatrix (iota := ι) t : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ) = _
    rw [scalarPhaseUnitaryMatrix_coe, Matrix.smul_mul, one_mul]
  simp only [traceWord, hmat, smul_pow, Matrix.trace_smul, smul_eq_mul, prod_mul_distrib]
  congr 1
  simp only [← Complex.exp_nat_mul, ← Complex.exp_sum]
  congr 1
  rw [Nat.cast_sum, mul_sum]
  exact sum_congr rfl fun j _ => mul_comm _ _

/-- Central covariance of two trace words records their difference in degrees. -/
theorem traceWord_pair_rotate {r s : ℕ} (a : Fin r → ℕ) (b : Fin s → ℕ)
    (t : ℝ) (U : Matrix.unitaryGroup ι ℂ) :
    traceWord a (scalarPhaseUnitaryMatrix (iota := ι) t * U) *
        (starRingEnd ℂ) (traceWord b (scalarPhaseUnitaryMatrix (iota := ι) t * U)) =
      Complex.exp (Complex.I * t * ((∑ j, a j : ℕ) - (∑ j, b j : ℕ) : ℂ)) *
        (traceWord a U * (starRingEnd ℂ) (traceWord b U)) := by
  rw [traceWord_rotate, traceWord_rotate, map_mul, ← Complex.exp_conj]
  have hc : (starRingEnd ℂ) (Complex.I * t * (∑ j, b j : ℕ)) =
      -(Complex.I * t * (∑ j, b j : ℕ)) := by simp
  rw [hc]
  rw [show Complex.I * t * ((∑ j, a j : ℕ) - (∑ j, b j : ℕ) : ℂ) =
      Complex.I * t * (∑ j, a j : ℕ) + -(Complex.I * t * (∑ j, b j : ℕ)) by ring,
    Complex.exp_add]
  ring

/-- Different total powers are exactly orthogonal, in every matrix dimension. -/
theorem integral_traceWord_pair_eq_zero {r s : ℕ} (a : Fin r → ℕ) (b : Fin s → ℕ)
    (hab : ∑ j, a j ≠ ∑ j, b j) :
    (∫ U : Matrix.unitaryGroup ι ℂ, traceWord a U * (starRingEnd ℂ) (traceWord b U)
      ∂finiteUnitaryHaar ι) = 0 := by
  have hD : ((∑ j, a j : ℕ) : ℝ) - (∑ j, b j : ℕ) ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hab)
  let t : ℝ := Real.pi / (((∑ j, a j : ℕ) : ℝ) - (∑ j, b j : ℕ))
  have hphase : Complex.exp (Complex.I * t *
      ((∑ j, a j : ℕ) - (∑ j, b j : ℕ) : ℂ)) = -1 := by
    have hangle : Complex.I * t * ((∑ j, a j : ℕ) - (∑ j, b j : ℕ) : ℂ) =
        (Real.pi : ℂ) * Complex.I := by
      have hdc : (((∑ j, a j : ℕ) : ℂ) - (∑ j, b j : ℕ)) ≠ 0 := by
        exact_mod_cast hD
      dsimp [t]
      push_cast at hdc ⊢
      field_simp [hdc]
    rw [hangle, Complex.exp_pi_mul_I]
  have hinv : (∫ U : Matrix.unitaryGroup ι ℂ,
      traceWord a (scalarPhaseUnitaryMatrix (iota := ι) t * U) *
        (starRingEnd ℂ) (traceWord b (scalarPhaseUnitaryMatrix (iota := ι) t * U)) ∂finiteUnitaryHaar ι) =
      ∫ U : Matrix.unitaryGroup ι ℂ, traceWord a U * (starRingEnd ℂ) (traceWord b U)
        ∂finiteUnitaryHaar ι := by
    unfold finiteUnitaryHaar
    exact integral_mul_left_eq_self _ (scalarPhaseUnitaryMatrix (iota := ι) t)
  simp_rw [traceWord_pair_rotate, hphase] at hinv
  rw [integral_const_mul] at hinv
  linear_combination (-1 / 2 : ℂ) * hinv

/-- Distinct power traces are orthogonal in every finite-unitary Haar space. -/
theorem integral_trace_pow_pair_eq_zero (m n : ℕ) (hmn : m ≠ n) :
    (∫ U : Matrix.unitaryGroup ι ℂ,
      Matrix.trace ((U : Matrix ι ι ℂ) ^ m) *
        (starRingEnd ℂ) (Matrix.trace ((U : Matrix ι ι ℂ) ^ n)) ∂finiteUnitaryHaar ι) = 0 := by
  simpa [traceWord] using integral_traceWord_pair_eq_zero (ι := ι)
    (fun _ : Fin 1 => m) (fun _ : Fin 1 => n) (by simpa using hmn)

#print axioms integral_traceWord_pair_eq_zero
#print axioms integral_trace_pow_pair_eq_zero

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.RandomMatrix

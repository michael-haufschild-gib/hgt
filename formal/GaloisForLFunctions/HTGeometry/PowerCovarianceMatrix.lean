import Mathlib.Probability.Moments.Variance
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Ring

/-! The quadratic form of the power covariance matrix is the variance of a power sum. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable def powerCovarianceMatrix {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => covariance (fun x => f x ^ ((i : ℕ) + 1))
    (fun x => f x ^ ((j : ℕ) + 1)) μ

theorem powerCovarianceMatrix_isHermitian {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (n : ℕ) :
    (powerCovarianceMatrix μ f n).IsHermitian := by
  apply Matrix.IsHermitian.ext_iff.mpr
  intro i j
  simp only [powerCovarianceMatrix, star_trivial]
  exact covariance_comm _ _

theorem powerCovarianceMatrix_quadraticForm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (n : ℕ) (c : Fin n → ℝ)
    (hf : ∀ i : Fin n, MemLp (fun x => f x ^ ((i : ℕ) + 1)) 2 μ) :
    star c ⬝ᵥ (powerCovarianceMatrix μ f n).mulVec c =
      variance (fun x => ∑ i : Fin n, c i * f x ^ ((i : ℕ) + 1)) μ := by
  have hmem : MemLp (fun x => ∑ i : Fin n, c i * f x ^ ((i : ℕ) + 1)) 2 μ :=
    memLp_finsetSum Finset.univ fun i _ => (hf i).const_mul (c i)
  rw [← covariance_self hmem.aemeasurable,
    covariance_fun_sum_fun_sum (fun i => (hf i).const_mul (c i))
      (fun i => (hf i).const_mul (c i))]
  simp only [star_trivial, powerCovarianceMatrix, Matrix.mulVec, dotProduct, Finset.mul_sum,
    covariance_const_mul_left, covariance_const_mul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end GaloisForLFunctions.HTGeometry

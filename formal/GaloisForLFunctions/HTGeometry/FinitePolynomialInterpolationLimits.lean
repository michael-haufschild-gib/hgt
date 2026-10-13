import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.Algebra.Order.Field

/-! # Finite interpolation preserves pointwise limits of data -/

namespace GaloisForLFunctions.HTGeometry

open Filter
open scoped Topology BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : Type*} [Field K] [TopologicalSpace K] [ContinuousAdd K] [ContinuousMul K]

theorem tendsto_lagrange_interpolate_eval (x : ι → K) (u : ℕ → ι → K) (v : ι → K)
    (h : ∀ i, Tendsto (fun n => u n i) atTop (𝓝 (v i))) (z : K) :
    Tendsto (fun n => (Lagrange.interpolate Finset.univ x (u n)).eval z)
      atTop (𝓝 ((Lagrange.interpolate Finset.univ x v).eval z)) := by
  simp only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C]
  exact tendsto_finsetSum _ (fun i _ => (h i).mul_const _)

theorem tendsto_lagrange_interpolate_coeff (x : ι → K) (u : ℕ → ι → K) (v : ι → K)
    (h : ∀ i, Tendsto (fun n => u n i) atTop (𝓝 (v i))) (j : ℕ) :
    Tendsto (fun n => (Lagrange.interpolate Finset.univ x (u n)).coeff j)
      atTop (𝓝 ((Lagrange.interpolate Finset.univ x v).coeff j)) := by
  simp only [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  exact tendsto_finsetSum _ (fun i _ => (h i).mul_const _)

end GaloisForLFunctions.HTGeometry

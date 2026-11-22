import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Pi

/-! Trace decomposition along finite families of vector spaces. -/

open Finset Function

namespace UpperTheory.Cb

/-- The trace on a finite dependent product is the sum of the traces of the diagonal blocks. -/
theorem trace_pi_eq_sum_diagonal {k : Type*} [Field k] {J : Type*}
    [Fintype J] [DecidableEq J] {V : J → Type*} [∀ j, AddCommGroup (V j)]
    [∀ j, Module k (V j)] [∀ j, FiniteDimensional k (V j)]
    (f : Module.End k (∀ j, V j)) :
    LinearMap.trace k (∀ j, V j) f =
      ∑ j, LinearMap.trace k (V j) (LinearMap.proj j ∘ₗ f ∘ₗ LinearMap.single k V j) := by
  let b (j : J) := Module.finBasis k (V j)
  rw [LinearMap.trace_eq_matrix_trace k (Pi.basis b) f, Matrix.trace, Fintype.sum_sigma]
  refine sum_congr rfl fun j _ => ?_
  rw [LinearMap.trace_eq_matrix_trace k (b j), Matrix.trace]
  refine sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basis_apply, Pi.basis_repr,
    LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply]

/-- Coordinate isomorphisms preserve traces, so only diagonal maps contribute to the trace. -/
theorem trace_eq_sum_diagonal_of_coordinates {k : Type*} [Field k] {J : Type*}
    [Fintype J] [DecidableEq J] {M : Type*} [AddCommGroup M] [Module k M]
    {V : J → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module k (V j)]
    [∀ j, FiniteDimensional k (V j)] (P : ∀ j, M →ₗ[k] V j)
    (hP : Bijective (LinearMap.pi P)) (f : Module.End k M) (B : ∀ i j, V j →ₗ[k] V i)
    (hB : ∀ i x, P i (f x) = ∑ j, B i j (P j x)) :
    FiniteDimensional k M ∧ LinearMap.trace k M f = ∑ j, LinearMap.trace k (V j) (B j j) := by
  let e := LinearEquiv.ofBijective (LinearMap.pi P) hP
  haveI : FiniteDimensional k M := LinearEquiv.finiteDimensional e.symm
  refine ⟨inferInstance, ?_⟩
  rw [← LinearMap.trace_conj' f e, trace_pi_eq_sum_diagonal]
  refine sum_congr rfl fun j _ => ?_
  congr 1
  refine LinearMap.ext fun y => ?_
  have hcoord (l : J) : P l (e.symm (Pi.single j y)) = Pi.single j y l :=
    congrFun (e.apply_symm_apply (Pi.single j y)) l
  change P j (f (e.symm (Pi.single j y))) = B j j y
  rw [hB, sum_eq_single j]
  · rw [hcoord, Pi.single_eq_same]
  · intro l _ hlj
    rw [hcoord, Pi.single_eq_of_ne hlj, map_zero]
  · simp

end UpperTheory.Cb

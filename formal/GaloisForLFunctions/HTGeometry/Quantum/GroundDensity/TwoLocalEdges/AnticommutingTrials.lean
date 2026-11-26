import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic.Linarith

/-! # Spectral trial directions from anticommuting real isometries -/

open Finset
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.HTGeometry.TwoLocalEdges
noncomputable section
variable {I V : Type*} [Fintype I] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Pairwise anticommuting symmetric real isometries produce an
orthonormal family from any unit vector. Real scalars allow linear and
antilinear quantum symmetries to be used in the same family. -/
theorem orthonormal_trials (A : I→V≃ₗᵢ[ℝ]V)
    (hs : ∀ i (v w : V), ⟪A i v,w⟫_ℝ=⟪v,A i w⟫_ℝ)
    (ha : ∀ i j, i≠j → ∀ v : V, A i (A j v)= -A j (A i v))
    (v : V) (hv : ‖v‖=1) : Orthonormal ℝ (fun i => A i v) := by
  refine ⟨fun i => ((A i).norm_map v).trans hv,?_⟩
  intro i j hij
  have h : ⟪A i v,A j v⟫_ℝ= -⟪A j v,A i v⟫_ℝ := by
    rw [hs i,ha i j hij,inner_neg_right,←hs j]
  rw [real_inner_comm (A j v)] at h
  linarith

/-- The squared expectation values of these observables share unit
total mass, including a spin-reversal overlap when represented over ℝ. -/
theorem sum_sq_expectation_le_one (A : I→V≃ₗᵢ[ℝ]V)
    (hs : ∀ i (v w : V), ⟪A i v,w⟫_ℝ=⟪v,A i w⟫_ℝ)
    (ha : ∀ i j, i≠j → ∀ v : V, A i (A j v)= -A j (A i v))
    (v : V) (hv : ‖v‖=1) : (∑ i, ⟪A i v,v⟫_ℝ^2)≤1 := by
  have h := (orthonormal_trials A hs ha v hv).sum_inner_products_le (s:=univ) (x:=v)
  simpa only [Real.norm_eq_abs,sq_abs,hv,one_pow] using h

#print axioms orthonormal_trials
#print axioms sum_sq_expectation_le_one
end
end GaloisForLFunctions.HTGeometry.TwoLocalEdges

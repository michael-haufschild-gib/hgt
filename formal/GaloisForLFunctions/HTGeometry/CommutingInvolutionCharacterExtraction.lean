import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp

/-!
# Extracting sign-graded components from an invariant subspace

A family of operators acting on a finite list of vectors by signs separates those vectors whenever
distinct indices carry distinct sign patterns.  Averaging one separating operator at a time removes
one vector from the sum while keeping the distinguished vector, so a subspace invariant under the
family and containing the total sum contains every summand.  Only invertibility of `2` is used;
neither commutation of the operators nor orthogonality of the vectors is needed.
-/

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 V ι κ : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- **Sign-graded extraction.**  If distinct components carry distinct sign characters under a
family preserving the subspace, membership of their sum forces membership of each. -/
theorem mem_of_sum_mem_of_separating [Fintype ι] [DecidableEq ι] (htwo : (2 : 𝕜) ≠ 0)
    (U : Submodule 𝕜 V) (C : κ → V →ₗ[𝕜] V) (hUinv : ∀ k, ∀ u ∈ U, C k u ∈ U)
    (x : ι → V) (χ : ι → κ → 𝕜)
    (hχ : ∀ i k, C k (x i) = χ i k • x i)
    (hsq : ∀ i k, χ i k * χ i k = 1)
    (hsep : ∀ i j, i ≠ j → ∃ k, χ i k * χ j k = -1)
    (hsum : (∑ i, x i) ∈ U) (i₀ : ι) : x i₀ ∈ U := by
  classical
  have key : ∀ S : Finset ι, i₀ ∉ S → ∀ c : ι → 𝕜,
      (x i₀ + ∑ i ∈ S, c i • x i) ∈ U → x i₀ ∈ U := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        intro _ c h
        simpa using h
    | insert j S' hj ih =>
        intro hi₀ c h
        have hij : i₀ ≠ j := fun hc => hi₀ (hc ▸ Finset.mem_insert_self j S')
        have hi₀' : i₀ ∉ S' := fun hc => hi₀ (Finset.mem_insert_of_mem hc)
        obtain ⟨k, hk⟩ := hsep i₀ j hij
        have hCw : C k (x i₀ + ∑ i ∈ insert j S', c i • x i) =
            χ i₀ k • x i₀ + ∑ i ∈ insert j S', (c i * χ i k) • x i := by
          rw [map_add, map_sum, hχ i₀ k]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smul, hχ i k, smul_smul]
        have hcomb : (x i₀ + ∑ i ∈ insert j S', c i • x i) +
              χ i₀ k • C k (x i₀ + ∑ i ∈ insert j S', c i • x i) =
            (2 : 𝕜) • x i₀ + ∑ i ∈ insert j S', (c i * (1 + χ i₀ k * χ i k)) • x i := by
          rw [hCw, smul_add, Finset.smul_sum, smul_smul, hsq i₀ k, one_smul,
            add_add_add_comm, ← Finset.sum_add_distrib, two_smul]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul, ← add_smul]
          congr 1
          ring
        have hmemU : ((2 : 𝕜)⁻¹ • ((x i₀ + ∑ i ∈ insert j S', c i • x i) +
            χ i₀ k • C k (x i₀ + ∑ i ∈ insert j S', c i • x i))) ∈ U :=
          Submodule.smul_mem _ _ (Submodule.add_mem _ h
            (Submodule.smul_mem _ _ (hUinv k _ h)))
        rw [hcomb, smul_add, Finset.smul_sum, smul_smul, inv_mul_cancel₀ htwo, one_smul,
          Finset.sum_insert hj] at hmemU
        have hjzero : ((2 : 𝕜)⁻¹ * (c j * (1 + χ i₀ k * χ j k))) • x j = 0 := by
          rw [hk]
          simp
        rw [smul_smul, hjzero, zero_add] at hmemU
        refine ih hi₀' (fun i => (2 : 𝕜)⁻¹ * (c i * (1 + χ i₀ k * χ i k))) ?_
        convert hmemU using 2
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul]
  refine key (Finset.univ.erase i₀) (Finset.notMem_erase _ _) (fun _ => 1) ?_
  have hsplit : (∑ i, x i) = x i₀ + ∑ i ∈ Finset.univ.erase i₀, (1 : 𝕜) • x i := by
    simp only [one_smul]
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
  rwa [hsplit] at hsum

end GaloisForLFunctions.HTGeometry

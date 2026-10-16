import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! # Faithfulness of full lowering chains

No slot of a lowering chain with nonzero bottom can disappear. Distinct
generalized eigenspaces then keep any finite family of such chains faithful.
-/

noncomputable section
open Set

namespace GaloisForLFunctions.HTGeometry

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem loweringChain_linearIndependent (N : Module.End K V) (v : ℕ → V)
    (hv : v 0 ≠ 0) (h0 : N (v 0) = 0) (hs : ∀ n, N (v (n+1)) = v n) (m : ℕ) :
    LinearIndependent K (fun j : Fin m => v j.val) := by
  induction m with
  | zero => exact linearIndependent_empty_type
  | succ m ih =>
      rw [Fintype.linearIndependent_iff] at ih ⊢
      intro c hc j
      have hN := congrArg N hc
      simp only [map_add, map_sum, map_smul, map_zero, Fin.sum_univ_succ, Fin.val_zero,
        h0, smul_zero, zero_add, Fin.val_succ, hs] at hN
      have hcs (i : Fin m) : c i.succ = 0 := ih (fun i => c i.succ) hN i
      have hc0 : c 0 = 0 := by
        rw [Fin.sum_univ_succ] at hc
        simp only [hcs, zero_smul, Finset.sum_const_zero, add_zero, Fin.val_zero] at hc
        exact (smul_eq_zero.mp hc).resolve_right hv
      exact Fin.cases hc0 hcs j

theorem loweringChain_pow_succ (N : Module.End K V) (v : ℕ → V)
    (h0 : N (v 0) = 0) (hs : ∀ n, N (v (n+1)) = v n) (n : ℕ) :
    (N ^ (n+1)) (v n) = 0 := by
  induction n with
  | zero => simpa using h0
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, hs]
      exact ih

/-- Entire chains at different spectral points remain independent together. -/
theorem generalizedLoweringChains_linearIndependent
    {ι : Type*} (A : Module.End K V) (lam : ι → K) (hlam : Function.Injective lam)
    (v : ι → ℕ → V) (m : ι → ℕ)
    (h0 : ∀ i, (A - lam i • LinearMap.id : Module.End K V) (v i 0) = 0)
    (hs : ∀ i n, (A - lam i • LinearMap.id : Module.End K V) (v i (n+1)) = v i n)
    (hv : ∀ i, v i 0 ≠ 0) :
    LinearIndependent K (fun q : Σ i, Fin (m i) => v q.1 q.2.val) := by
  have hmem (i : ι) (j : Fin (m i)) : v i j.val ∈ A.genEigenspace (lam i) ⊤ := by
    rw [Module.End.mem_genEigenspace_top]
    exact ⟨j.val+1, loweringChain_pow_succ _ (v i) (h0 i) (hs i) j.val⟩
  have hle (i : ι) : Submodule.span K (range fun j : Fin (m i) => v i j.val) ≤
      A.genEigenspace (lam i) ⊤ := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hmem i j
  have hind := ((A.independent_genEigenspace ⊤).comp hlam).mono hle
  apply linearIndependent_iUnion_finite
    (fun i => loweringChain_linearIndependent _ (v i) (hv i) (h0 i) (hs i) (m i))
  intro i t _ hit
  exact hind.disjoint_biSup hit

/-- A nonresonant scalar shift preserves the faithfulness of all full chains. -/
theorem generalizedLoweringChains_shift_linearIndependent
    {ι : Type*} (A : Module.End K V) (lam : ι → K) (hlam : Function.Injective lam)
    (v : ι → ℕ → V) (m : ι → ℕ)
    (h0 : ∀ i, (A - lam i • LinearMap.id : Module.End K V) (v i 0) = 0)
    (hs : ∀ i n, (A - lam i • LinearMap.id : Module.End K V) (v i (n+1)) = v i n)
    (hv : ∀ i, v i 0 ≠ 0) (w : K) (hw : ∀ i, lam i - w ≠ 0) :
    LinearIndependent K (fun q : Σ i, Fin (m i) =>
      (A - w • LinearMap.id : Module.End K V) (v q.1 q.2.val)) := by
  let B : Module.End K V := A - w • LinearMap.id
  have hc (i : ι) (x : V) :
      (A - lam i • LinearMap.id : Module.End K V) (B x) =
        B ((A - lam i • LinearMap.id : Module.End K V) x) := by
    simp only [B, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      map_sub, map_smul, smul_sub, smul_smul]
    rw [mul_comm (lam i) w]
    abel
  apply generalizedLoweringChains_linearIndependent A lam hlam
    (fun i n => B (v i n)) m
  · intro i
    rw [hc, h0, map_zero]
  · intro i n
    rw [hc, hs]
  · intro i
    have ha : A (v i 0) = lam i • v i 0 := by
      have h := h0 i
      simpa only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero] using h
    have hb : B (v i 0) = (lam i-w) • v i 0 := by
      simp only [B, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, ha,
        sub_smul]
    rw [hb]
    exact smul_ne_zero (hw i) (hv i)

end GaloisForLFunctions.HTGeometry

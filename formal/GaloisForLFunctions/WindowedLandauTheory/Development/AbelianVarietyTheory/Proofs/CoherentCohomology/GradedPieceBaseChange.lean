import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedPresentations
import Mathlib.RingTheory.IsTensorProduct

/-! A base-change map preserving the gradings changes base on each homogeneous piece. -/

open DirectSum TensorProduct

namespace GlobalTheory

private noncomputable def pieceProjection {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (D : ℤ → Submodule R M) [Decomposition D] (n : ℤ) : M →ₗ[R] D n :=
  DirectSum.component R ℤ (fun j => D j) n ∘ₗ (decomposeLinearEquiv D).toLinearMap

theorem isBaseChange_gradedPiece {B R M N : Type} [CommRing B] [CommRing R] [Algebra B R]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] [Module R N] [IsScalarTower B R N]
    (D : ℤ → Submodule B M) [Decomposition D] (E : ℤ → Submodule R N) [Decomposition E]
    (f : M →ₗ[B] N) (n : ℤ) [Module B (E n)] [IsScalarTower B R (E n)]
    (φ : D n →ₗ[B] E n) (h : IsBaseChange R f)
    (hf : ∀ j, ∀ x ∈ D j, f x ∈ E j) (hφ : ∀ x : D n, (φ x : N) = f x) :
    IsBaseChange R φ := by
  let p := pieceProjection D n
  let q := pieceProjection E n
  have hp (x : D n) : p (x : M) = x := Subtype.ext (decompose_of_mem_same D x.2)
  have hq (x : E n) : q (x : N) = x := Subtype.ext (decompose_of_mem_same E x.2)
  have hproj (x : M) : φ (p x) = q (f x) := by
    induction x using Decomposition.inductionOn D with
    | zero => simp only [map_zero]
    | @homogeneous j x =>
      by_cases e : j = n
      · subst j
        rw [hp, ← hφ, hq]
      · have hp' : p (x : M) = 0 := Subtype.ext (decompose_of_mem_ne D x.2 e)
        have hq' : q (f x) = 0 := Subtype.ext (decompose_of_mem_ne E (hf j x x.2) e)
        rw [hp', hq', map_zero]
    | add a b ha hb => simp only [map_add, ha, hb]
  let L : R ⊗[B] D n →ₗ[R] E n := φ.liftBaseChange R
  have hL (x : R ⊗[B] M) : L (p.baseChange R x) = q (h.equiv x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul r x => simp [L, IsBaseChange.equiv_tmul, hproj]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hval (x : R ⊗[B] D n) : (L x : N) = h.equiv ((D n).subtype.baseChange R x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, Submodule.coe_zero]
    | tmul r x => simp [L, IsBaseChange.equiv_tmul, hφ]
    | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
  have hret (x : R ⊗[B] D n) : p.baseChange R ((D n).subtype.baseChange R x) = x := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul r x => simp [hp]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hLbij : Function.Bijective L := by
    constructor
    · intro x y e
      have hv := congrArg (fun a : E n => (a : N)) e
      rw [hval, hval] at hv
      rw [← hret x, h.equiv.injective hv, hret]
    · intro y
      refine ⟨p.baseChange R (h.equiv.symm (y : N)), ?_⟩
      rw [hL, LinearEquiv.apply_symm_apply, hq]
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective L hLbij) fun x => by simp [L]

end GlobalTheory

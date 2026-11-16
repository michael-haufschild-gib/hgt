import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Module
import Mathlib.Tactic.Abel

/-!
# Even and odd kernels of a swap-equivariant block map

For the map `(x,y) ↦ (Ax+By,Bx+Ay)`, sum and difference coordinates identify
its kernel with `ker(A+B) × ker(A-B)`. Rank and nullity split exactly,
including for rectangular block matrices. Inverting two is essential to
the inverse coordinate change.

This is an explicit linear-algebra application of the even/odd splitting
used in Yin's quadratic-twist Selmer sequence. It asserts no Selmer-group
or Iwasawa-theoretic identification.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
variable {K V W : Type*} [Field K] [NeZero (2 : K)]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The coupled map commuting with the swap of its two coordinates. -/
def swapBlock (A B : V →ₗ[K] W) : V × V →ₗ[K] W × W :=
  (A.coprod B).prod (B.coprod A)

private theorem half_double (x : V) : (2 : K)⁻¹ • ((2 : K) • x) = x := by
  rw [smul_smul, inv_mul_cancel₀ (NeZero.ne (2 : K)), one_smul]

/-- Sum and difference identify the coupled kernel with its even and odd kernels. -/
def swapBlockKernelEquiv (A B : V →ₗ[K] W) :
    LinearMap.ker (swapBlock A B) ≃ₗ[K] (LinearMap.ker (A + B) × LinearMap.ker (A - B)) where
  toFun z :=
    (⟨z.1.1 + z.1.2, by
      have h1 : A z.1.1 + B z.1.2 = 0 := congrArg Prod.fst z.2
      have h2 : B z.1.1 + A z.1.2 = 0 := congrArg Prod.snd z.2
      change A (z.1.1 + z.1.2) + B (z.1.1 + z.1.2) = 0
      rw [map_add, map_add]
      calc
        _ = (A z.1.1 + B z.1.2) + (B z.1.1 + A z.1.2) := by abel
        _ = 0 := by rw [h1, h2, add_zero]⟩,
     ⟨z.1.1 - z.1.2, by
      have h1 : A z.1.1 + B z.1.2 = 0 := congrArg Prod.fst z.2
      have h2 : B z.1.1 + A z.1.2 = 0 := congrArg Prod.snd z.2
      change A (z.1.1 - z.1.2) - B (z.1.1 - z.1.2) = 0
      rw [map_sub, map_sub]
      calc
        _ = (A z.1.1 + B z.1.2) - (B z.1.1 + A z.1.2) := by abel
        _ = 0 := by rw [h1, h2, sub_self]⟩)
  invFun z := ⟨((2 : K)⁻¹ • (z.1.1 + z.2.1), (2 : K)⁻¹ • (z.1.1 - z.2.1)), by
    have h1 : A z.1.1 + B z.1.1 = 0 := z.1.2
    have h2 : A z.2.1 - B z.2.1 = 0 := z.2.2
    change (A ((2 : K)⁻¹ • (z.1.1 + z.2.1)) + B ((2 : K)⁻¹ • (z.1.1 - z.2.1)),
      B ((2 : K)⁻¹ • (z.1.1 + z.2.1)) + A ((2 : K)⁻¹ • (z.1.1 - z.2.1))) = (0, 0)
    simp only [map_smul, map_add, map_sub]
    apply Prod.ext
    · calc
        _ = (2 : K)⁻¹ • ((A z.1.1 + B z.1.1) + (A z.2.1 - B z.2.1)) := by module
        _ = 0 := by rw [h1, h2, add_zero, smul_zero]
    · calc
        _ = (2 : K)⁻¹ • ((A z.1.1 + B z.1.1) - (A z.2.1 - B z.2.1)) := by module
        _ = 0 := by rw [h1, h2, sub_self, smul_zero]⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · change (2 : K)⁻¹ • ((z.1.1 + z.1.2) + (z.1.1 - z.1.2)) = z.1.1
      calc
        _ = (2 : K)⁻¹ • ((2 : K) • z.1.1) := by congr 1; module
        _ = _ := half_double _
    · change (2 : K)⁻¹ • ((z.1.1 + z.1.2) - (z.1.1 - z.1.2)) = z.1.2
      calc
        _ = (2 : K)⁻¹ • ((2 : K) • z.1.2) := by congr 1; module
        _ = _ := half_double _
  right_inv z := by
    apply Prod.ext <;> apply Subtype.ext
    · change (2 : K)⁻¹ • (z.1.1 + z.2.1) + (2 : K)⁻¹ • (z.1.1 - z.2.1) = z.1.1
      calc
        _ = (2 : K)⁻¹ • ((2 : K) • z.1.1) := by module
        _ = _ := half_double _
    · change (2 : K)⁻¹ • (z.1.1 + z.2.1) - (2 : K)⁻¹ • (z.1.1 - z.2.1) = z.2.1
      calc
        _ = (2 : K)⁻¹ • ((2 : K) • z.2.1) := by module
        _ = _ := half_double _
  map_add' z w := by
    apply Prod.ext <;> apply Subtype.ext
    · change (z.1.1 + w.1.1) + (z.1.2 + w.1.2) = (z.1.1 + z.1.2) + (w.1.1 + w.1.2)
      abel
    · change (z.1.1 + w.1.1) - (z.1.2 + w.1.2) = (z.1.1 - z.1.2) + (w.1.1 - w.1.2)
      abel
  map_smul' c z := by
    apply Prod.ext <;> apply Subtype.ext
    · exact (smul_add c z.1.1 z.1.2).symm
    · exact (smul_sub c z.1.1 z.1.2).symm

variable [FiniteDimensional K V]
/-- The nullities of the two parity sectors add without overlap. -/
theorem finrank_swapBlock_kernel (A B : V →ₗ[K] W) :
    Module.finrank K (LinearMap.ker (swapBlock A B)) =
      Module.finrank K (LinearMap.ker (A + B)) + Module.finrank K (LinearMap.ker (A - B)) := by
  rw [(swapBlockKernelEquiv A B).finrank_eq, Module.finrank_prod]

/-- Rank-nullity transfers the kernel splitting to an exact rank sum. -/
theorem finrank_swapBlock_range (A B : V →ₗ[K] W) :
    Module.finrank K (LinearMap.range (swapBlock A B)) =
      Module.finrank K (LinearMap.range (A + B)) + Module.finrank K (LinearMap.range (A - B)) := by
  have h := LinearMap.finrank_range_add_finrank_ker (swapBlock A B)
  have hp := LinearMap.finrank_range_add_finrank_ker (A + B)
  have hm := LinearMap.finrank_range_add_finrank_ker (A - B)
  rw [finrank_swapBlock_kernel, Module.finrank_prod] at h
  omega

section Matrix
variable {m n : Type*} [Fintype n]

omit [NeZero (2 : K)] in
private theorem swapBlock_mulVecLin (A B : Matrix m n K) :
    swapBlock A.mulVecLin B.mulVecLin =
      ((LinearEquiv.sumArrowLequivProdArrow m m K K).toLinearMap.comp
        (Matrix.fromBlocks A B B A).mulVecLin).comp
          (LinearEquiv.sumArrowLequivProdArrow n n K K).symm.toLinearMap := by
  apply LinearMap.ext
  intro v
  change (A.mulVec v.1 + B.mulVec v.2, B.mulVec v.1 + A.mulVec v.2) = _
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply,
    Matrix.fromBlocks_mulVec]
  rfl

/-- A rectangular swap-symmetric block matrix has exactly the sum of the parity ranks. -/
theorem rank_fromBlocks_swap (A B : Matrix m n K) :
    (Matrix.fromBlocks A B B A).rank = (A + B).rank + (A - B).rank := by
  have h := finrank_swapBlock_range A.mulVecLin B.mulVecLin
  rw [swapBlock_mulVecLin,
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr
      (LinearEquiv.sumArrowLequivProdArrow n n K K).symm.surjective),
    LinearMap.range_comp, LinearEquiv.finrank_map_eq] at h
  have hsub : (A - B).mulVecLin = A.mulVecLin - B.mulVecLin :=
    LinearMap.ext (Matrix.sub_mulVec A B)
  rw [← Matrix.mulVecLin_add, ← hsub] at h
  exact h

end Matrix

#print axioms swapBlockKernelEquiv
#print axioms finrank_swapBlock_kernel
#print axioms finrank_swapBlock_range
#print axioms rank_fromBlocks_swap

end GaloisForLFunctions.RepresentationLifting

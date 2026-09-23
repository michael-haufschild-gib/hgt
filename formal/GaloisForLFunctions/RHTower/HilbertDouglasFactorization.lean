import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Douglas factorization for Hilbert-space operators

This file proves the contractive normalization of Douglas' range-inclusion theorem directly for
bounded operators between arbitrary complex Hilbert spaces.  The construction extends the map
`B† y ↦ A† y` from the range of `B†` to its closure and makes it zero on the orthogonal complement.
No compactness, finite-dimensionality, or closed-range hypothesis is used.
-/

open Complex Real
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace RHTower

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Positivity of `B B† - A A†` is exactly the pointwise adjoint-norm domination needed by
Douglas' construction. -/
theorem adjoint_norm_le_of_gram_sub_gram_isPositive
    (A B : E →L[ℂ] F)
    (hpos : (B ∘L ContinuousLinearMap.adjoint B -
      A ∘L ContinuousLinearMap.adjoint A).IsPositive)
    (y : F) :
    ‖ContinuousLinearMap.adjoint A y‖ ≤
      ‖ContinuousLinearMap.adjoint B y‖ := by
  have hq := (ContinuousLinearMap.isPositive_def'.mp hpos).2 y
  have hB :
      (⟪(B ∘L ContinuousLinearMap.adjoint B) y, y⟫_ℂ).re =
        ‖ContinuousLinearMap.adjoint B y‖ ^ (2 : ℕ) := by
    have hinner :
        ⟪(B ∘L ContinuousLinearMap.adjoint B) y, y⟫_ℂ =
          ⟪ContinuousLinearMap.adjoint B y,
            ContinuousLinearMap.adjoint B y⟫_ℂ := by
      exact (ContinuousLinearMap.adjoint_inner_right B _ _).symm
    rw [hinner]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hA :
      (⟪(A ∘L ContinuousLinearMap.adjoint A) y, y⟫_ℂ).re =
        ‖ContinuousLinearMap.adjoint A y‖ ^ (2 : ℕ) := by
    have hinner :
        ⟪(A ∘L ContinuousLinearMap.adjoint A) y, y⟫_ℂ =
          ⟪ContinuousLinearMap.adjoint A y,
            ContinuousLinearMap.adjoint A y⟫_ℂ := by
      exact (ContinuousLinearMap.adjoint_inner_right A _ _).symm
    rw [hinner]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  change 0 ≤
    (⟪((B ∘L ContinuousLinearMap.adjoint B) -
      (A ∘L ContinuousLinearMap.adjoint A)) y, y⟫_ℂ).re at hq
  rw [sub_apply, inner_sub_left, Complex.sub_re, hB, hA] at hq
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith)

/-- **Douglas factorization theorem, contractive form.**  Gram order `A A† ≤ B B†` supplies a
right factor `A = B C` with `‖C‖ ≤ 1`. -/
theorem exists_contractive_rightFactor_of_gram_sub_gram_isPositive
    (A B : E →L[ℂ] F)
    (hpos : (B ∘L ContinuousLinearMap.adjoint B -
      A ∘L ContinuousLinearMap.adjoint A).IsPositive) :
    ∃ C : E →L[ℂ] E, ‖C‖ ≤ 1 ∧ A = B ∘L C := by
  let Bstar : F →L[ℂ] E := ContinuousLinearMap.adjoint B
  let Astar : F →L[ℂ] E := ContinuousLinearMap.adjoint A
  let N : Submodule ℂ E := LinearMap.range Bstar.toLinearMap
  let M : Submodule ℂ E := N.topologicalClosure
  let i : N →L[ℂ] M := N.subtypeL.codRestrict M
    (fun x => N.le_topologicalClosure x.property)
  let rB : F →L[ℂ] N := Bstar.rangeRestrict
  let eL : F →L[ℂ] M := i ∘L rB
  let e : F →ₗ[ℂ] M := eL.toLinearMap
  have hi : DenseRange i := by
    change DenseRange (Set.inclusion N.le_topologicalClosure)
    apply (denseRange_inclusion_iff N.le_topologicalClosure).2
    simpa only [M, Submodule.topologicalClosure_coe] using
      (subset_rfl : closure (N : Set E) ⊆ closure (N : Set E))
  have hrB : DenseRange rB :=
    (LinearMap.surjective_rangeRestrict Bstar.toLinearMap).denseRange
  have heL : DenseRange eL := hi.comp hrB i.continuous
  have he : DenseRange e := heL
  have hbound : ∀ y : F, ‖Astar y‖ ≤ (1 : ℝ) * ‖e y‖ := by
    intro y
    rw [one_mul]
    change ‖ContinuousLinearMap.adjoint A y‖ ≤
      ‖ContinuousLinearMap.adjoint B y‖
    exact adjoint_norm_le_of_gram_sub_gram_isPositive A B hpos y
  let D : M →L[ℂ] E := Astar.toLinearMap.extendOfNorm e
  have hD : ‖D‖ ≤ 1 :=
    LinearMap.opNorm_extendOfNorm_le he zero_le_one hbound
  let P : E →L[ℂ] M := M.orthogonalProjectionOnto
  let Dfull : E →L[ℂ] E := D ∘L P
  have hDfull : ‖Dfull‖ ≤ 1 := by
    calc
      ‖Dfull‖ ≤ ‖D‖ * ‖P‖ := ContinuousLinearMap.opNorm_comp_le D P
      _ ≤ 1 * 1 := mul_le_mul hD M.orthogonalProjectionOnto_norm_le
        (norm_nonneg P) zero_le_one
      _ = 1 := one_mul 1
  have hcomp : Dfull ∘L Bstar = Astar := by
    apply ContinuousLinearMap.ext
    intro y
    change D (M.orthogonalProjectionOnto (Bstar y)) = Astar y
    have hmem : Bstar y ∈ M :=
      N.le_topologicalClosure (LinearMap.mem_range_self Bstar.toLinearMap y)
    have hproj : M.orthogonalProjectionOnto (Bstar y) = e y := by
      have hfix := M.orthogonalProjectionOnto_mem_subspace_eq_self
        (⟨Bstar y, hmem⟩ : M)
      exact hfix
    rw [hproj]
    exact LinearMap.extendOfNorm_eq he ⟨1, hbound⟩ y
  let C : E →L[ℂ] E := ContinuousLinearMap.adjoint Dfull
  refine ⟨C, ?_, ?_⟩
  · change ‖ContinuousLinearMap.adjoint Dfull‖ ≤ 1
    rw [LinearIsometryEquiv.norm_map]
    exact hDfull
  · have hadj := congrArg ContinuousLinearMap.adjoint hcomp
    rw [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.adjoint_adjoint] at hadj
    exact hadj.symm

/-- Douglas factorization when concrete maps have already been identified as the two adjoints.
This interface avoids replacing useful explicit adjoint formulas by opaque `adjoint` terms. -/
theorem exists_contractive_rightFactor_of_explicitAdjoint_gram_isPositive
    (A B : E →L[ℂ] F) (Astar Bstar : F →L[ℂ] E)
    (hAstar : ContinuousLinearMap.adjoint A = Astar)
    (hBstar : ContinuousLinearMap.adjoint B = Bstar)
    (hpos : (B ∘L Bstar - A ∘L Astar).IsPositive) :
    ∃ C : E →L[ℂ] E, ‖C‖ ≤ 1 ∧ A = B ∘L C := by
  rw [← hAstar, ← hBstar] at hpos
  exact exists_contractive_rightFactor_of_gram_sub_gram_isPositive A B hpos

end RHTower

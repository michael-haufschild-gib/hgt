import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The cone of positive definite real symmetric matrices

The real symmetric matrices form a linear subspace, and inside it the positive definite ones form an
**open convex cone**.  Openness is the tube argument: the quadratic form is continuous on the
product with the unit sphere, the sphere is compact, so the matrices failing positivity somewhere on
the sphere form a closed set.

This is the space on which arithmetic groups act, and by
`isFinitelyPresented_of_macbeath_convex` an open convex domain is all the topology Macbeath's
criterion needs.

* `symmMatrices` : the symmetric matrices, as a submodule.
* `posDefCone` : the positive definite ones.
* `convex_posDefCone`, `isOpen_posDefCone`, `posDefCone_nonempty` : **open, convex, nonempty.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- The real symmetric matrices, as a submodule. -/
def symmMatrices (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {A | Aᵀ = A}
  add_mem' := by
    intro A B hA hB
    show (A + B)ᵀ = A + B
    rw [Matrix.transpose_add, hA, hB]
  zero_mem' := Matrix.transpose_zero
  smul_mem' := by
    intro c A hA
    show (c • A)ᵀ = c • A
    rw [Matrix.transpose_smul, hA]

theorem mem_symmMatrices_iff {A : Matrix (Fin n) (Fin n) ℝ} : A ∈ symmMatrices n ↔ Aᵀ = A :=
  Iff.rfl

theorem isHermitian_of_mem_symmMatrices {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ symmMatrices n) : A.IsHermitian := by
  show Aᴴ = A
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  exact hA

/-- The positive definite cone inside the symmetric matrices. -/
def posDefCone (n : ℕ) : Set (symmMatrices n) :=
  {A | (A : Matrix (Fin n) (Fin n) ℝ).PosDef}

theorem posDefCone_nonempty : (posDefCone n).Nonempty := by
  refine ⟨⟨(1 : Matrix (Fin n) (Fin n) ℝ), ?_⟩, ?_⟩
  · show (1 : Matrix (Fin n) (Fin n) ℝ)ᵀ = 1
    exact Matrix.transpose_one
  · exact Matrix.PosDef.one

theorem convex_posDefCone : Convex ℝ (posDefCone n) := by
  intro A hA B hB a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hB
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simpa [hb0, ha1] using hA
  have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbPos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  show ((a • A + b • B : symmMatrices n) : Matrix (Fin n) (Fin n) ℝ).PosDef
  have hval : ((a • A + b • B : symmMatrices n) : Matrix (Fin n) (Fin n) ℝ)
      = a • (A : Matrix (Fin n) (Fin n) ℝ) + b • (B : Matrix (Fin n) (Fin n) ℝ) := rfl
  rw [hval]
  exact (hA.smul haPos).add (hB.smul hbPos)

/-- Positive definiteness of a symmetric matrix is a condition on the unit sphere. -/
theorem posDef_iff_sphere {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    A.PosDef ↔ ∀ x : Fin n → ℝ, ‖x‖ = 1 → 0 < x ⬝ᵥ (A *ᵥ x) := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨-, hpos⟩ x hx
    have hxne : x ≠ 0 := by
      intro hcon
      rw [hcon, norm_zero] at hx
      exact zero_ne_one hx
    simpa using hpos hxne
  · intro hsph
    refine ⟨hA, ?_⟩
    intro x hxne
    simp only [star_trivial]
    have hnorm : ‖x‖ ≠ 0 := by simpa using hxne
    have hy : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnorm]
    have hpos := hsph _ hy
    have hscale : ((‖x‖⁻¹ : ℝ) • x) ⬝ᵥ (A *ᵥ ((‖x‖⁻¹ : ℝ) • x))
        = (‖x‖⁻¹) ^ (2 : ℕ) * (x ⬝ᵥ (A *ᵥ x)) := by
      rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        smul_eq_mul, ← mul_assoc, ← pow_two]
    rw [hscale] at hpos
    have hsq : (0 : ℝ) < (‖x‖⁻¹) ^ (2 : ℕ) := by positivity
    nlinarith [hpos, hsq]

/-- **The positive definite cone is open.** -/
theorem isOpen_posDefCone : IsOpen (posDefCone n) := by
  classical
  haveI : CompactSpace (Metric.sphere (0 : Fin n → ℝ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  have hcont : Continuous
      (fun p : Matrix (Fin n) (Fin n) ℝ × (Metric.sphere (0 : Fin n → ℝ) 1) =>
        ((p.2 : Fin n → ℝ)) ⬝ᵥ (p.1 *ᵥ ((p.2 : Fin n → ℝ)))) := by
    simp only [dotProduct, Matrix.mulVec]
    refine continuous_finsetSum _ fun i _ => ?_
    refine Continuous.mul ((continuous_apply i).comp
      (continuous_subtype_val.comp continuous_snd)) ?_
    refine continuous_finsetSum _ fun j _ => ?_
    exact Continuous.mul ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst))
      ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd))
  have hbadclosed : IsClosed
      {A : Matrix (Fin n) (Fin n) ℝ |
        ∃ x : Metric.sphere (0 : Fin n → ℝ) 1, ((x : Fin n → ℝ)) ⬝ᵥ (A *ᵥ (x : Fin n → ℝ)) ≤ 0} := by
    have hclosedset : IsClosed {p : Matrix (Fin n) (Fin n) ℝ × (Metric.sphere (0 : Fin n → ℝ) 1) |
        ((p.2 : Fin n → ℝ)) ⬝ᵥ (p.1 *ᵥ ((p.2 : Fin n → ℝ))) ≤ 0} :=
      IsClosed.preimage hcont (isClosed_Iic (a := (0 : ℝ)))
    have himg := isClosedMap_fst_of_compactSpace _ hclosedset
    convert himg using 1
    ext A
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨(A, x), hx, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.2, hp⟩
  have hopen : IsOpen {A : Matrix (Fin n) (Fin n) ℝ |
      ∀ x : Fin n → ℝ, ‖x‖ = 1 → 0 < x ⬝ᵥ (A *ᵥ x)} := by
    rw [show {A : Matrix (Fin n) (Fin n) ℝ | ∀ x : Fin n → ℝ, ‖x‖ = 1 → 0 < x ⬝ᵥ (A *ᵥ x)}
        = {A : Matrix (Fin n) (Fin n) ℝ |
          ∃ x : Metric.sphere (0 : Fin n → ℝ) 1,
            ((x : Fin n → ℝ)) ⬝ᵥ (A *ᵥ (x : Fin n → ℝ)) ≤ 0}ᶜ from ?_]
    · exact hbadclosed.isOpen_compl
    · ext A
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_exists, not_le]
      constructor
      · intro h x
        exact h _ (mem_sphere_zero_iff_norm.mp x.2)
      · intro h x hx
        exact h ⟨x, mem_sphere_zero_iff_norm.mpr hx⟩
  have hpre : posDefCone n = Subtype.val ⁻¹'
      {A : Matrix (Fin n) (Fin n) ℝ | ∀ x : Fin n → ℝ, ‖x‖ = 1 → 0 < x ⬝ᵥ (A *ᵥ x)} := by
    ext A
    exact posDef_iff_sphere (isHermitian_of_mem_symmMatrices A.2)
  rw [hpre]
  exact hopen.preimage continuous_subtype_val

/-- The symmetric matrices form a locally path connected space: as a submodule of a finite product
of copies of `ℝ` it is a normed space. -/
instance locallyPathConnectedSpace_symmMatrices (n : ℕ) :
    LocallyPathConnectedSpace (symmMatrices n) := by
  let S : Submodule ℝ (Fin n → Fin n → ℝ) := symmMatrices n
  exact (inferInstance : LocallyPathConnectedSpace S)

end GaloisForLFunctions.HTGeometry

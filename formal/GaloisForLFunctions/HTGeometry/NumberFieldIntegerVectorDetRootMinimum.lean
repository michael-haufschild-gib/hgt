import GaloisForLFunctions.HTGeometry.NumberFieldIntegerVectorLatticeBasis
import GaloisForLFunctions.HTGeometry.DeterminantOneLatticeShortVector

/-!
# Determinant-root short vectors over a number ring

Minkowski reduction in canonical real coordinates returns a point of an abstract integer span.
The canonical lattice-basis equality converts that point back to a literal nonzero vector over the
number ring, without leaving any coordinate or lattice premise at the theorem boundary.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField Module
open scoped Classical NumberField

noncomputable section

/-- A single determinant-root radius controls a nonzero number-ring vector under every invertible
real deformation of the canonical mixed coordinates. -/
theorem exists_uniform_numberFieldIntegerVectorEmbedding_linearEquiv_norm_le_detRoot
    (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (hn : 0 < n) :
    ∃ R : ℝ, 0 < R ∧
      ∀ T : (Fin (n * Module.finrank ℚ K) → ℝ) ≃L[ℝ]
          (Fin (n * Module.finrank ℚ K) → ℝ),
        ∃ a : Fin n → RingOfIntegers K, a ≠ 0 ∧
          ‖T (numberFieldMixedVectorContinuousLinearEquiv K n
            (numberFieldIntegerVectorEmbedding K a))‖ ≤
            R * Real.rpow
              |LinearMap.det
                (T : (Fin (n * Module.finrank ℚ K) → ℝ) →ₗ[ℝ]
                  (Fin (n * Module.finrank ℚ K) → ℝ))|
              ((Fintype.card (Fin (n * Module.finrank ℚ K)) : ℝ)⁻¹) := by
  let e := numberFieldMixedVectorContinuousLinearEquiv K n
  let b := (numberFieldMixedVectorBasis K n).map e.toLinearEquiv
  have hdim : 0 < n * Module.finrank ℚ K :=
    Nat.mul_pos hn Module.finrank_pos
  letI : Nonempty (Fin (n * Module.finrank ℚ K)) :=
    Fin.pos_iff_nonempty.mp hdim
  obtain ⟨R, hR, hbound⟩ :=
    exists_uniform_ne_zero_zspan_linearEquiv_norm_le_detRoot b
  refine ⟨R, hR, ?_⟩
  intro T
  obtain ⟨x, hxspan, hx0, hxbound⟩ := hbound T
  have hzspan : e.symm x ∈
      Submodule.span ℤ (Set.range (numberFieldMixedVectorBasis K n)) := by
    refine Submodule.span_induction (p := fun x _ ↦ e.symm x ∈
      Submodule.span ℤ (Set.range (numberFieldMixedVectorBasis K n))) ?_ ?_ ?_ ?_ hxspan
    · intro y hy
      obtain ⟨r, rfl⟩ := hy
      exact Submodule.subset_span ⟨r, by simp [b, e]⟩
    · simp
    · intro x y hx hy hx' hy'
      simpa using Submodule.add_mem _ hx' hy'
    · intro z x hx hx'
      rw [← Int.cast_smul_eq_zsmul ℝ z x, map_smul,
        Int.cast_smul_eq_zsmul ℝ z (e.symm x)]
      exact Submodule.smul_mem
        (Submodule.span ℤ (Set.range (numberFieldMixedVectorBasis K n))) z hx'
  have hzlat : e.symm x ∈ numberFieldIntegerVectorLattice K n := by
    rwa [numberFieldIntegerVectorLattice_eq_span_mixedVectorBasis]
  choose a ha using fun i ↦ hzlat i (Set.mem_univ i)
  have hza : e.symm x = numberFieldIntegerVectorEmbedding K a := by
    funext i
    exact (ha i).symm
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hx0
    apply e.symm.injective
    rw [hza, ha0]
    have hemb0 : numberFieldIntegerVectorEmbedding K
        (0 : Fin n → RingOfIntegers K) = 0 := by
      funext i
      simp [numberFieldIntegerVectorEmbedding]
    rw [hemb0, map_zero]
  have hx : x = e (numberFieldIntegerVectorEmbedding K a) := by
    calc
      x = e (e.symm x) := (e.apply_symm_apply x).symm
      _ = e (numberFieldIntegerVectorEmbedding K a) := congrArg e hza
  refine ⟨a, ha0, ?_⟩
  rwa [← hx]

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.RepresentationLifting.Lattices.AbelianMovingRealLattice
import GaloisForLFunctions.RepresentationLifting.Lattices.AbelianAugmentationLattice

/-!
# Euclidean augmentation-square lattices

For any finite abelian group, the integral augmentation square embeds as a full,
discrete lattice in the real zero-sum hyperplane. Its index in the integral
zero-sum lattice is the group order. Thus its covolume is `|G| * sqrt(|G|)`,
and its squared covolume is `|G|^3`.
-/

open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open HTGeometry
variable (G : Type) [CommGroup G] [Fintype G]

/-- The Euclidean map from the augmentation square. -/
def abelianAugmentationRealMap : AbelianAugmentationLattice G →ₗ[ℤ] AbelianRealHyperplane G :=
  (abelianMovingRealMap G).comp (AbelianAugmentationLattice G).subtype

/-- The actual integral image inside the Euclidean zero-sum hyperplane. -/
def abelianAugmentationRealLattice : Submodule ℤ (AbelianRealHyperplane G) :=
  (AbelianAugmentationLattice G).map (abelianMovingRealMap G)

theorem abelianAugmentationRealLattice_le :
    abelianAugmentationRealLattice G ≤ abelianMovingRealLattice G := by
  rintro v ⟨w, _, hw⟩
  exact ⟨w, hw⟩

theorem abelianAugmentationRealMap_injective : Function.Injective (abelianAugmentationRealMap G) :=
  (abelianMovingRealMap_injective G).comp Subtype.val_injective

theorem card_smul_mem_abelianAugmentation (v : CyclicIntegralMoving G) :
    Fintype.card G • v ∈ AbelianAugmentationLattice G := by
  change cyclicMovingFirstMoment G (Fintype.card G • v) = 0
  rw [map_nsmul]
  change (cyclicMovingFirstMoment G v).toMul ^ Fintype.card G = 1
  exact pow_card_eq_one

variable [DecidableEq G]

instance : DiscreteTopology (abelianAugmentationRealLattice G) := by
  let f : abelianAugmentationRealLattice G → abelianMovingRealLattice G :=
    fun v => ⟨v.val, abelianAugmentationRealLattice_le G v.property⟩
  have hc : Continuous f := continuous_subtype_val.subtype_mk _
  have hi : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    exact congrArg (fun x : abelianMovingRealLattice G => (x : AbelianRealHyperplane G)) h
  exact DiscreteTopology.of_continuous_injective hc hi

instance : IsZLattice ℝ (abelianAugmentationRealLattice G) where
  span_top := by
    apply top_unique
    rw [← (EuclideanZeroSum.basis G 1).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    -- Group order annihilates each root moment, so every basis direction is spanned.
    have hm : (Fintype.card G : ℝ) • EuclideanZeroSum.basis G 1 i ∈
        abelianAugmentationRealLattice G := by
      refine ⟨Fintype.card G • cyclicMovingBasis G i, card_smul_mem_abelianAugmentation G _, ?_⟩
      rw [map_nsmul, abelianMovingRealMap_basis, Nat.cast_smul_eq_nsmul]
    have hspan := (Submodule.span ℝ (abelianAugmentationRealLattice G : Set (AbelianRealHyperplane G))).smul_mem
      (Fintype.card G : ℝ)⁻¹ (Submodule.subset_span hm)
    have hn : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [smul_smul, inv_mul_cancel₀ hn, one_smul] at hspan
    exact hspan

omit [DecidableEq G] in
theorem abelianAugmentationRealLattice_relIndex :
    (abelianAugmentationRealLattice G).toAddSubgroup.relIndex
      (abelianMovingRealLattice G).toAddSubgroup = Fintype.card G := by
  have htop : (abelianMovingRealLattice G).toAddSubgroup =
      (⊤ : AddSubgroup (CyclicIntegralMoving G)).map (abelianMovingRealMap G).toAddMonoidHom := by
    ext v
    change (∃ x, abelianMovingRealMap G x = v) ↔
      ∃ x, x ∈ (⊤ : AddSubgroup (CyclicIntegralMoving G)) ∧ abelianMovingRealMap G x = v
    simp only [AddSubgroup.mem_top, true_and]
  change ((AbelianAugmentationLattice G).toAddSubgroup.map
    (abelianMovingRealMap G).toAddMonoidHom).relIndex _ = _
  rw [htop, AddSubgroup.relIndex_map_map_of_injective _ _ (abelianMovingRealMap_injective G),
    AddSubgroup.relIndex_top_right]
  exact abelianAugmentation_index G

theorem abelianAugmentationRealLattice_covolume :
    ZLattice.covolume (abelianAugmentationRealLattice G) =
      (Fintype.card G : ℝ) * Real.sqrt (Fintype.card G : ℝ) := by
  have h := ZLattice.covolume_div_covolume_eq_relIndex'
    (abelianAugmentationRealLattice G) (abelianMovingRealLattice G) (abelianAugmentationRealLattice_le G)
  rw [abelianAugmentationRealLattice_relIndex, abelianMovingRealLattice_covolume] at h
  exact (div_eq_iff (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)).ne').mp h

/-- The square of the arithmetic covolume is the cube of the group order. -/
theorem abelianAugmentationRealLattice_covolume_sq :
    ZLattice.covolume (abelianAugmentationRealLattice G)^2 = (Fintype.card G : ℝ)^3 := by
  rw [abelianAugmentationRealLattice_covolume, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  ring

theorem abelianAugmentationRealLattice_covolume_sqrt :
    ZLattice.covolume (abelianAugmentationRealLattice G) = Real.sqrt ((Fintype.card G : ℝ)^3) := by
  rw [← abelianAugmentationRealLattice_covolume_sq, Real.sqrt_sq
    (ZLattice.covolume_pos (abelianAugmentationRealLattice G) MeasureTheory.volume).le]

#print axioms abelianAugmentationRealLattice_covolume
#print axioms abelianAugmentationRealLattice_relIndex
end GaloisForLFunctions.RepresentationLifting

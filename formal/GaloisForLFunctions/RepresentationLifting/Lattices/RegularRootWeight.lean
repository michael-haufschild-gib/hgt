import GaloisForLFunctions.RepresentationLifting.Lattices.RootWeightCokernel
import GaloisForLFunctions.RepresentationLifting.Lattices.CyclicDifferenceEnergy

/-!
# Root-to-weight comparison for regular representations

The integral norm kernel of the regular representation is the type-A root
lattice. Its map into the diagonal quotient is injective and has cyclic
cokernel of order the group cardinality. This applies the root-to-weight
isogeny to the corpus's moving and augmentation lattices.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.RepresentationLifting
variable (G : Type) [CommGroup G] [Fintype G]

/-- Regular coefficients identify the norm kernel with zero-sum integral vectors. -/
def regularRootCoordinates : CyclicIntegralMoving G →ₗ[ℤ] coordinateRootLattice G :=
  (cyclicMovingProfile G).codRestrict _ (cyclicMovingProfile_sum G)

theorem regularRootCoordinates_bijective : Function.Bijective (regularRootCoordinates G) := by
  classical
  constructor
  · intro v w h
    exact cyclicMovingProfile_injective G (congrArg Subtype.val h)
  · intro w
    let v : CyclicRegular ℤ G := ∑ g, MonoidAlgebra.single g (w.val g)
    have hv : cyclicAugmentation ℤ G v = 0 := by
      rw [map_sum]
      have hw : ∑ g, w.val g = 0 := w.property
      simpa only [cyclicAugmentation_single] using hw
    refine ⟨⟨v, (cyclicRegularNorm_eq_zero_iff G v).mpr hv⟩, ?_⟩
    apply Subtype.ext
    funext g
    change v.coeff g = w.val g
    simp [v, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single]

/-- The regular norm kernel is the type-A root lattice, integrally. -/
def regularRootEquiv : CyclicIntegralMoving G ≃ₗ[ℤ] coordinateRootLattice G :=
  LinearEquiv.ofBijective (regularRootCoordinates G) (regularRootCoordinates_bijective G)

/-- The root-to-weight map in regular coefficients. -/
def regularRootToWeight (p : G) : CyclicIntegralMoving G →ₗ[ℤ] coordinateWeightLattice G p :=
  (rootToWeight G p).comp (regularRootCoordinates G)

theorem regularRootToWeight_injective (p : G) : Function.Injective (regularRootToWeight G p) :=
  (rootToWeight_injective G p).comp (regularRootCoordinates_bijective G).1

/-- No integral root weights are lost when the root lattice is presented by the norm kernel. -/
theorem regularRootToWeight_range (p : G) :
    LinearMap.range (regularRootToWeight G p) = LinearMap.range (rootToWeight G p) := by
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨regularRootCoordinates G v, rfl⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨u, rfl⟩ := (regularRootCoordinates_bijective G).2 v
    exact ⟨u, rfl⟩

/-- Exact congruence criterion for a weight to come from an integral moving vector. -/
theorem mem_range_regularRootToWeight_iff (p : G) (w : coordinateWeightLattice G p) :
    w ∈ LinearMap.range (regularRootToWeight G p) ↔
      (Fintype.card G : ℤ) ∣ ∑ g, w.val g := by
  rw [regularRootToWeight_range, mem_range_rootToWeight_iff]

variable [Nontrivial G]

/-- The cyclic defect is independent of the multiplication law on the label group. -/
def regularRootWeightCokernelEquiv (p : G) :
    (coordinateWeightLattice G p ⧸ LinearMap.range (regularRootToWeight G p)) ≃ₗ[ℤ]
      ZMod (Fintype.card G) :=
  (Submodule.quotEquivOfEq _ _ (regularRootToWeight_range G p)).trans
    (rootWeightCokernelEquiv G p)

theorem regularRootWeight_index (p : G) :
    Nat.card (coordinateWeightLattice G p ⧸ LinearMap.range (regularRootToWeight G p)) =
      Fintype.card G := by
  rw [regularRootToWeight_range, rootWeight_index]

/-- The root-to-weight defect is the existing invariant-plus-moving gluing obstruction. -/
def regularRootWeightGluingEquiv [IsCyclic G] (p : G) :
    (coordinateWeightLattice G p ⧸ LinearMap.range (regularRootToWeight G p)) ≃ₗ[ℤ]
      (CyclicRegular ℤ G ⧸ cyclicIntegralGluingSubmodule G) :=
  (regularRootWeightCokernelEquiv G p).trans (cyclicIntegralGluingEquiv G).symm

#print axioms regularRootEquiv
#print axioms mem_range_regularRootToWeight_iff
#print axioms regularRootWeightCokernelEquiv
#print axioms regularRootWeightGluingEquiv
end GaloisForLFunctions.RepresentationLifting

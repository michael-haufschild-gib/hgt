import GaloisForLFunctions.HTGeometry.GroupAlgebras.FirstJet
import GaloisForLFunctions.RepresentationLifting.Lattices.CyclicDifferenceEnergy

/-!
# Augmentation-square lattices for finite abelian groups

The integral universal first jet identifies the augmentation square with the
simultaneous kernel of coefficient sum and group-valued first moment. Hence its
zero-sum lattice excludes every nonzero coordinate root, is even, and has squared
norm at least four on nonzero vectors. No cyclicity assumption is needed.

For cyclic groups this is exactly the previously constructed restricted difference
lattice. This extends the integral first-moment mechanism behind the rootless
lattices in Auel–Shaikh (https://arxiv.org/abs/2611.13468).
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open HTGeometry.GroupAlgebraFirstJet HTGeometry.IntegralZeroSum
variable (G : Type) [CommGroup G]

/-- Over the integers, scalar extension recovers the native group-valued moment. -/
theorem integralJet_moment (v : MonoidAlgebra ℤ G) :
    TensorProduct.lid ℤ (Additive G) (jet ℤ G v).snd = cyclicFirstMoment G v := by
  have h : (TensorProduct.lid ℤ (Additive G)).toLinearMap.comp
      ((TrivSqZeroExt.sndHom ℤ (MomentSpace ℤ G)).comp (jet ℤ G).toLinearMap) =
      cyclicFirstMoment G := by
    apply (MonoidAlgebra.basis G ℤ).ext
    intro g
    change TensorProduct.lid ℤ (Additive G) (jet ℤ G (MonoidAlgebra.of ℤ G g)).snd = _
    rw [jet_of]
    simpa using (cyclicFirstMoment_single G g).symm
  exact LinearMap.congr_fun h v

/-- The augmentation square is detected by coefficient sum and first moment. -/
theorem integral_mem_augmentation_square_iff (v : MonoidAlgebra ℤ G) :
    v ∈ (augmentationIdeal ℤ G)^2 ↔
      augmentation ℤ G v = 0 ∧ cyclicFirstMoment G v = 0 := by
  rw [← jet_ker_eq_square]
  change jet ℤ G v = 0 ↔ _
  constructor
  · intro h
    constructor
    · rw [← jet_fst, h]; rfl
    · rw [← integralJet_moment, h]; exact map_zero _
  · rintro ⟨ha, hm⟩
    apply TrivSqZeroExt.ext
    · exact (jet_fst ℤ G v).trans ha
    · apply (TensorProduct.lid ℤ (Additive G)).injective
      exact (integralJet_moment G v).trans hm

variable [Fintype G]

theorem augmentation_eq_cyclic (v : MonoidAlgebra ℤ G) :
    augmentation ℤ G v = cyclicAugmentation ℤ G v := by
  have h : (augmentation ℤ G).toLinearMap = cyclicAugmentation ℤ G := by
    apply (MonoidAlgebra.basis G ℤ).ext
    intro g
    change augmentation ℤ G (MonoidAlgebra.of ℤ G g) = _
    rw [augmentation_of]
    exact (cyclicAugmentation_single ℤ G g 1).symm
  exact LinearMap.congr_fun h v

/-- The augmentation-square lattice for any finite abelian group. -/
def AbelianAugmentationLattice := (cyclicMovingFirstMoment G).ker

/-- The moment-kernel lattice is precisely the integral augmentation square. -/
theorem abelianAugmentation_mem_iff (v : CyclicIntegralMoving G) :
    v ∈ AbelianAugmentationLattice G ↔
      (v : MonoidAlgebra ℤ G) ∈ (augmentationIdeal ℤ G)^2 := by
  rw [integral_mem_augmentation_square_iff, augmentation_eq_cyclic]
  have hv := (cyclicRegularNorm_eq_zero_iff G v).mp v.property
  simp only [hv, true_and]
  rfl

/-- A coordinate root lies in the square exactly when it is zero. -/
theorem abelianAugmentation_root_iff (a b : G) :
    cyclicRootVector G a b ∈ AbelianAugmentationLattice G ↔ a = b := by
  change cyclicMovingFirstMoment G (cyclicRootVector G a b) = 0 ↔ _
  rw [cyclicMovingFirstMoment_root, sub_eq_zero]
  exact ⟨fun h => congrArg Additive.toMul h, fun h => congrArg Additive.ofMul h⟩

theorem abelianAugmentation_energy_even (v : AbelianAugmentationLattice G) :
    Even (cyclicMovingEnergy G v) := cyclicMovingEnergy_even G v

/-- Every nonzero vector has squared Euclidean norm at least four. -/
theorem abelianAugmentation_energy_ge_four (v : AbelianAugmentationLattice G) (hv : v ≠ 0) :
    4 ≤ cyclicMovingEnergy G v := by
  apply four_le_energy_of_no_root (cyclicMovingProfile_sum G v)
  · intro h
    exact hv (Subtype.ext (cyclicMovingProfile_injective G (h.trans (map_zero _).symm)))
  · intro a b hab he
    have he' : v.val = cyclicRootVector G a b :=
      cyclicMovingProfile_injective G (he.trans (cyclicMovingProfile_root G a b).symm)
    exact hab ((abelianAugmentation_root_iff G a b).mp (he' ▸ v.property))

/-- The augmentation-square lattice has quotient exactly the label group. -/
def abelianAugmentationQuotientEquiv :
    (CyclicIntegralMoving G ⧸ AbelianAugmentationLattice G) ≃ₗ[ℤ] Additive G :=
  (cyclicMovingFirstMoment G).quotKerEquivOfSurjective (cyclicMovingFirstMoment_surjective G)

/-- Its index in the zero-sum lattice is the group order. -/
theorem abelianAugmentation_index :
    Nat.card (CyclicIntegralMoving G ⧸ AbelianAugmentationLattice G) = Fintype.card G := by
  calc
    _ = Nat.card (Additive G) := Nat.card_congr (abelianAugmentationQuotientEquiv G).toEquiv
    _ = Nat.card G := Nat.card_congr (Equiv.refl G)
    _ = Fintype.card G := Nat.card_eq_fintype_card

variable [IsCyclic G]

/-- The cyclic difference construction is the cyclic augmentation-square lattice. -/
theorem cyclicDifference_eq_abelianAugmentation :
    CyclicDifferenceLattice G = AbelianAugmentationLattice G :=
  cyclicMovingDelta_range_eq_firstMoment_ker G

#print axioms integral_mem_augmentation_square_iff
#print axioms abelianAugmentationQuotientEquiv
#print axioms abelianAugmentation_index
#print axioms abelianAugmentation_energy_ge_four
#print axioms cyclicDifference_eq_abelianAugmentation
end GaloisForLFunctions.RepresentationLifting

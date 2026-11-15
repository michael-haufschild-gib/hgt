import GaloisForLFunctions.RepresentationLifting.Lattices.CyclicMovingGram
import GaloisForLFunctions.HTGeometry.Lattices.EuclideanZeroSumBasis
import GaloisForLFunctions.HTGeometry.Lattices.GramCovolume
import GaloisForLFunctions.HTGeometry.Lattices.IntegralEnergyGeometry

/-!
# Euclidean realization of the integral augmentation lattice

Integral zero-sum coefficients embed in the Euclidean zero-sum hyperplane.
The shared-base root basis realizes the integral moving basis as a real basis;
its Gram determinant is the number of group labels. Consequently the embedded
lattice is discrete, spans the hyperplane, and has covolume `sqrt(|G|)`.
No cyclicity assumption is needed.
-/

open scoped BigOperators Matrix
noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open HTGeometry HTGeometry.IntegerLatticePoisson
variable (G : Type) [CommGroup G] [Fintype G]

/-- The real zero-sum hyperplane of regular group coordinates. -/
abbrev AbelianRealHyperplane := EuclideanZeroSum.space G

/-- The integral regular coefficients embedded as Euclidean coordinates. -/
def abelianMovingRealMap : CyclicIntegralMoving G →ₗ[ℤ] AbelianRealHyperplane G where
  toFun v := ⟨euclideanIntegerPoint (cyclicMovingProfile G v), by
    change ∑ g, (cyclicMovingProfile G v g : ℝ) = 0
    exact_mod_cast cyclicMovingProfile_sum G v⟩
  map_add' v w := by
    apply Subtype.ext
    ext g
    change (cyclicMovingProfile G (v + w) g : ℝ) =
      (cyclicMovingProfile G v g : ℝ) + (cyclicMovingProfile G w g : ℝ)
    rw [map_add, Pi.add_apply, Int.cast_add]
  map_smul' c v := by
    apply Subtype.ext
    ext g
    change (cyclicMovingProfile G (c • v) g : ℝ) = c • (cyclicMovingProfile G v g : ℝ)
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, Int.cast_mul, zsmul_eq_mul]

theorem abelianMovingRealMap_injective : Function.Injective (abelianMovingRealMap G) := by
  intro v w h
  apply cyclicMovingProfile_injective G
  ext g
  have he := congrArg (fun z : AbelianRealHyperplane G => z.val g) h
  change (cyclicMovingProfile G v g : ℝ) = (cyclicMovingProfile G w g : ℝ) at he
  exact_mod_cast he

theorem abelianMovingRealMap_root (a b : G) :
    abelianMovingRealMap G (cyclicRootVector G a b) = EuclideanZeroSum.root G a b := by
  classical
  apply Subtype.ext
  ext g
  change (cyclicMovingProfile G (cyclicRootVector G a b) g : ℝ) = _
  rw [cyclicMovingProfile_root]
  simp [IntegralZeroSum.root, EuclideanZeroSum.root, Pi.single_apply, PiLp.single_apply]

theorem abelianMovingRealMap_inner (v w : CyclicIntegralMoving G) :
    inner ℝ (abelianMovingRealMap G v) (abelianMovingRealMap G w) =
      (cyclicMovingForm G v w : ℝ) := by
  change inner ℝ (euclideanIntegerPoint (cyclicMovingProfile G v))
    (euclideanIntegerPoint (cyclicMovingProfile G w)) =
    (IntegralZeroSum.pairing (cyclicMovingProfile G v) (cyclicMovingProfile G w) : ℝ)
  simp [PiLp.inner_apply, euclideanIntegerPoint, integerPoint, IntegralZeroSum.pairing, mul_comm]

/-- Squared Euclidean distance is the integral zero-sum energy of the difference. -/
theorem abelianMovingRealMap_dist_sq (v w : CyclicIntegralMoving G) :
    dist (abelianMovingRealMap G v) (abelianMovingRealMap G w)^2 =
      (cyclicMovingEnergy G (v - w) : ℝ) := by
  change dist (euclideanIntegerPoint (cyclicMovingProfile G v))
    (euclideanIntegerPoint (cyclicMovingProfile G w))^2 = _
  rw [euclideanIntegerPoint_dist_sq, ← map_sub]
  rfl

/-- The image of the full integral augmentation lattice. -/
def abelianMovingRealLattice : Submodule ℤ (AbelianRealHyperplane G) :=
  LinearMap.range (abelianMovingRealMap G)

variable [DecidableEq G]

theorem abelianMovingRealMap_basis (i : CyclicMovingIndex G) :
    abelianMovingRealMap G (cyclicMovingBasis G i) = EuclideanZeroSum.basis G 1 i := by
  rw [cyclicMovingBasis_apply, EuclideanZeroSum.basis_apply, abelianMovingRealMap_root]

theorem abelianMovingRealLattice_eq_span :
    abelianMovingRealLattice G = Submodule.span ℤ (Set.range (EuclideanZeroSum.basis G 1)) := by
  have h := Submodule.map_span (abelianMovingRealMap G) (Set.range (cyclicMovingBasis G))
  rw [(cyclicMovingBasis G).span_eq, Submodule.map_top] at h
  rw [abelianMovingRealLattice, h]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, abelianMovingRealMap_basis]

instance : DiscreteTopology (abelianMovingRealLattice G) := by
  rw [abelianMovingRealLattice_eq_span]
  infer_instance

instance : IsZLattice ℝ (abelianMovingRealLattice G) := by
  simpa only [abelianMovingRealLattice_eq_span] using
    (inferInstance : IsZLattice ℝ (Submodule.span ℤ (Set.range (EuclideanZeroSum.basis G 1))))

theorem abelianMovingRealBasis_gram :
    Matrix.gram ℝ (EuclideanZeroSum.basis G 1) =
      ((cyclicMovingForm G).toMatrix (cyclicMovingBasis G)).map (Int.castRingHom ℝ) := by
  ext i j
  simp only [Matrix.gram_apply, Matrix.map_apply, LinearMap.BilinForm.toMatrix_apply]
  rw [← abelianMovingRealMap_basis G i, ← abelianMovingRealMap_basis G j]
  exact abelianMovingRealMap_inner G _ _

/-- The augmentation lattice has covolume equal to the square root of its number of coordinates. -/
theorem abelianMovingRealLattice_covolume :
    ZLattice.covolume (abelianMovingRealLattice G) = Real.sqrt (Fintype.card G : ℝ) := by
  rw [abelianMovingRealLattice_eq_span, EuclideanLattice.covolume_span_eq_sqrt_gram,
    abelianMovingRealBasis_gram]
  congr 1
  calc
    _ = (((cyclicMovingForm G).toMatrix (cyclicMovingBasis G)).det : ℝ) :=
      ((Int.castRingHom ℝ).map_det _).symm
    _ = _ := by rw [cyclicMovingGram_det]; simp

#print axioms abelianMovingRealLattice_covolume
#print axioms abelianMovingRealMap_dist_sq
end GaloisForLFunctions.RepresentationLifting

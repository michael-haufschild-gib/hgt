import GaloisForLFunctions.RepresentationLifting.Lattices.CyclicUnitBallPacking
import GaloisForLFunctions.HTGeometry.Lattices.EuclideanZeroSumBasis
import GaloisForLFunctions.HTGeometry.Lattices.GramCovolume

/-!
# The real cyclic difference lattice

Integral regular coordinates embed the cyclic difference module into the
Euclidean zero-sum hyperplane. Its image basis has Gram determinant `|G|^3`,
so it is a real basis. Its integer span is exactly the embedded module;
discreteness, full rank, and covolume follow without extra lattice assumptions.
-/

open scoped BigOperators Matrix
open Module
noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open HTGeometry HTGeometry.IntegerLatticePoisson
variable (G : Type) [CommGroup G] [Fintype G] [IsCyclic G]

/-- The Euclidean augmentation hyperplane, with its real linear structure. -/
abbrev CyclicRealHyperplane := EuclideanZeroSum.space G

/-- The existing packing centers, regarded as an integral linear map. -/
def cyclicDifferenceRealMap : CyclicDifferenceLattice G →ₗ[ℤ] CyclicRealHyperplane G where
  toFun := cyclicDifferencePoint G
  map_add' v w := by
    apply Subtype.ext
    ext g
    change (cyclicMovingProfile G (v + w) g : ℝ) =
      (cyclicMovingProfile G v g : ℝ) + (cyclicMovingProfile G w g : ℝ)
    rw [map_add, Pi.add_apply, Int.cast_add]
  map_smul' c v := by
    apply Subtype.ext
    ext g
    change (cyclicMovingProfile G (c • v) g : ℝ) =
      c • (cyclicMovingProfile G v g : ℝ)
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, Int.cast_mul, zsmul_eq_mul]

theorem cyclicDifferenceRealMap_inner (v w : CyclicDifferenceLattice G) :
    inner ℝ (cyclicDifferenceRealMap G v) (cyclicDifferenceRealMap G w) =
      (cyclicDifferenceForm G v w : ℝ) := by
  change inner ℝ (euclideanIntegerPoint (cyclicMovingProfile G v))
    (euclideanIntegerPoint (cyclicMovingProfile G w)) =
    (IntegralZeroSum.pairing (cyclicMovingProfile G v) (cyclicMovingProfile G w) : ℝ)
  simp [PiLp.inner_apply, euclideanIntegerPoint, integerPoint, IntegralZeroSum.pairing, mul_comm]

variable [DecidableEq G]

/-- The integral difference basis embedded in the real hyperplane. -/
def cyclicDifferenceRealFamily : CyclicMovingIndex G → CyclicRealHyperplane G :=
  fun i => cyclicDifferenceRealMap G (cyclicDifferenceBasis G i)

theorem cyclicDifferenceRealFamily_gram :
    Matrix.gram ℝ (cyclicDifferenceRealFamily G) =
      ((cyclicDifferenceForm G).toMatrix (cyclicDifferenceBasis G)).map (Int.castRingHom ℝ) := by
  ext i j
  simp only [Matrix.gram_apply, cyclicDifferenceRealFamily, Matrix.map_apply,
    LinearMap.BilinForm.toMatrix_apply]
  exact cyclicDifferenceRealMap_inner G _ _

theorem cyclicDifferenceRealFamily_gram_det :
    (Matrix.gram ℝ (cyclicDifferenceRealFamily G)).det = (Fintype.card G : ℝ)^3 := by
  rw [cyclicDifferenceRealFamily_gram]
  calc
    _ = (((cyclicDifferenceForm G).toMatrix (cyclicDifferenceBasis G)).det : ℝ) :=
      ((Int.castRingHom ℝ).map_det _).symm
    _ = _ := by rw [cyclicDifferenceGram_det]; simp

theorem cyclicDifferenceRealFamily_independent : LinearIndependent ℝ (cyclicDifferenceRealFamily G) := by
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  rw [cyclicDifferenceRealFamily_gram_det]
  exact pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- The embedded difference basis spans the entire real hyperplane. -/
def cyclicDifferenceRealBasis : Basis (CyclicMovingIndex G) ℝ (CyclicRealHyperplane G) :=
  basisOfLinearIndependentOfCardEqFinrank' (cyclicDifferenceRealFamily G)
    (cyclicDifferenceRealFamily_independent G)
    (EuclideanZeroSum.finrank_space G (1 : G)).symm

theorem cyclicDifferenceRealBasis_apply (i : CyclicMovingIndex G) :
    cyclicDifferenceRealBasis G i = cyclicDifferenceRealFamily G i := by
  simp [cyclicDifferenceRealBasis]

/-- The actual image of the integral cyclic difference module. -/
def cyclicDifferenceRealLattice : Submodule ℤ (CyclicRealHyperplane G) :=
  LinearMap.range (cyclicDifferenceRealMap G)

theorem cyclicDifferenceRealLattice_eq_span :
    cyclicDifferenceRealLattice G = Submodule.span ℤ (Set.range (cyclicDifferenceRealBasis G)) := by
  have h := Submodule.map_span (cyclicDifferenceRealMap G) (Set.range (cyclicDifferenceBasis G))
  rw [(cyclicDifferenceBasis G).span_eq, Submodule.map_top] at h
  rw [cyclicDifferenceRealLattice, h]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and]
  simp only [cyclicDifferenceRealBasis_apply, cyclicDifferenceRealFamily]

instance : DiscreteTopology (cyclicDifferenceRealLattice G) := by
  rw [cyclicDifferenceRealLattice_eq_span]
  infer_instance

instance : IsZLattice ℝ (cyclicDifferenceRealLattice G) := by
  simpa only [cyclicDifferenceRealLattice_eq_span] using
    (inferInstance : IsZLattice ℝ (Submodule.span ℤ (Set.range (cyclicDifferenceRealBasis G))))

/-- The geometric fundamental cell has volume `sqrt(|G|^3)`. -/
theorem cyclicDifferenceRealLattice_covolume :
    ZLattice.covolume (cyclicDifferenceRealLattice G) = Real.sqrt ((Fintype.card G : ℝ)^3) := by
  rw [cyclicDifferenceRealLattice_eq_span, EuclideanLattice.covolume_span_eq_sqrt_gram]
  have hb : (cyclicDifferenceRealBasis G : CyclicMovingIndex G → CyclicRealHyperplane G) =
      cyclicDifferenceRealFamily G := funext (cyclicDifferenceRealBasis_apply G)
  rw [hb, cyclicDifferenceRealFamily_gram_det]

omit [IsCyclic G] in
theorem cyclicRealHyperplane_rank :
    finrank ℝ (CyclicRealHyperplane G) + 1 = Fintype.card G := by
  rw [EuclideanZeroSum.finrank_space G (1 : G)]
  exact card_subtype_ne_succ (1 : G)

/-- The rank `n + 3` unit-ball packing has covolume `sqrt((n + 4)^3)`. -/
theorem cyclicPacking_covolume (n : ℕ) :
    ZLattice.covolume (cyclicDifferenceRealLattice (CyclicPackingGroup n)) =
      Real.sqrt ((n + 4 : ℝ)^3) := by
  rw [cyclicDifferenceRealLattice_covolume, cyclicPackingGroup_card]
  norm_cast

#print axioms cyclicDifferenceRealLattice_covolume
#print axioms cyclicPacking_covolume
end GaloisForLFunctions.RepresentationLifting

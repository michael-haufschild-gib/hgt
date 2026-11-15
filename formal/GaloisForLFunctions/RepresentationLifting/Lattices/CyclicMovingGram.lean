import GaloisForLFunctions.RepresentationLifting.Lattices.CyclicDifferenceEnergy
import GaloisForLFunctions.HTGeometry.BarnesSliceReindex
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Gram determinants of cyclic difference lattices

The augmentation lattice has basis `e_g - e_1`, indexed by nonidentity group
labels. Its Gram matrix is identity plus the all-ones matrix, with determinant
`|G|`. Cyclic difference is injective and has absolute determinant `|G|`, so
its image basis has Gram determinant `|G|^3` and rank `|G| - 1`.
-/

open scoped BigOperators Matrix
noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open HTGeometry.IntegralZeroSum
variable (G : Type) [CommGroup G] [Fintype G]

/-- The nonidentity labels indexing the augmentation basis. -/
abbrev CyclicMovingIndex := {g : G // g ≠ 1}

variable [DecidableEq G]

/-- Delete the identity coefficient; zero augmentation recovers it uniquely. -/
def cyclicMovingCoordinates : CyclicIntegralMoving G →ₗ[ℤ] (CyclicMovingIndex G → ℤ) where
  toFun v i := cyclicMovingProfile G v i.val
  map_add' v w := by ext i; exact congrFun (map_add (cyclicMovingProfile G) v w) i.val
  map_smul' c v := by ext i; exact congrFun (map_smul (cyclicMovingProfile G) c v) i.val

theorem cyclicMovingCoordinates_eq_zero {v : CyclicIntegralMoving G}
    (hv : cyclicMovingCoordinates G v = 0) : v = 0 := by
  classical
  have haway (g : G) (hg : g ≠ 1) : cyclicMovingProfile G v g = 0 := congrFun hv ⟨g, hg⟩
  have hsum : ∑ g, cyclicMovingProfile G v g = cyclicMovingProfile G v 1 := by
    apply Finset.sum_eq_single 1
    · intro g _ hg
      exact haway g hg
    · simp
  have hone : cyclicMovingProfile G v 1 = 0 := hsum.symm.trans (cyclicMovingProfile_sum G v)
  apply cyclicMovingProfile_injective G
  rw [map_zero]
  ext g
  by_cases hg : g = 1
  · subst g; exact hone
  · exact haway g hg

theorem cyclicMovingCoordinates_injective : Function.Injective (cyclicMovingCoordinates G) := by
  intro v w h
  apply sub_eq_zero.mp
  apply cyclicMovingCoordinates_eq_zero G
  rw [map_sub, h, sub_self]

theorem cyclicMovingCoordinates_root (i : CyclicMovingIndex G) :
    cyclicMovingCoordinates G (cyclicRootVector G i.val 1) = Pi.single i 1 := by
  ext j
  change cyclicMovingProfile G (cyclicRootVector G i.val 1) j.val = _
  rw [cyclicMovingProfile_root]
  simp [root, Pi.single_apply, j.property, Subtype.ext_iff]

theorem cyclicMovingCoordinates_surjective : Function.Surjective (cyclicMovingCoordinates G) := by
  classical
  intro f
  refine ⟨∑ i, f i • cyclicRootVector G i.val 1, ?_⟩
  simp only [map_sum, map_smul, cyclicMovingCoordinates_root]
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

/-- Independent integral coordinates on the augmentation lattice. -/
def cyclicMovingCoordinateEquiv : CyclicIntegralMoving G ≃ₗ[ℤ] (CyclicMovingIndex G → ℤ) :=
  LinearEquiv.ofBijective (cyclicMovingCoordinates G)
    ⟨cyclicMovingCoordinates_injective G, cyclicMovingCoordinates_surjective G⟩

/-- The basis of roots sharing the identity as base coordinate. -/
def cyclicMovingBasis : Module.Basis (CyclicMovingIndex G) ℤ (CyclicIntegralMoving G) :=
  (Pi.basisFun ℤ (CyclicMovingIndex G)).map (cyclicMovingCoordinateEquiv G).symm

theorem cyclicMovingBasis_apply (i : CyclicMovingIndex G) :
    cyclicMovingBasis G i = cyclicRootVector G i.val 1 := by
  classical
  apply (cyclicMovingCoordinateEquiv G).injective
  simp only [cyclicMovingBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply]
  change Pi.basisFun ℤ (CyclicMovingIndex G) i = cyclicMovingCoordinates G (cyclicRootVector G i.val 1)
  rw [cyclicMovingCoordinates_root]
  simp only [Pi.basisFun_apply]

/-- The integral Euclidean pairing on regular coordinates. -/
def cyclicMovingForm : LinearMap.BilinForm ℤ (CyclicIntegralMoving G) :=
  LinearMap.BilinForm.comp (dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (G → ℤ))
    (cyclicMovingProfile G) (cyclicMovingProfile G)

omit [DecidableEq G] in
theorem cyclicMovingForm_apply (v w : CyclicIntegralMoving G) :
    cyclicMovingForm G v w = pairing (cyclicMovingProfile G v) (cyclicMovingProfile G w) := rfl

/-- The augmentation basis has Gram matrix identity plus all-ones. -/
theorem cyclicMovingBasis_gram :
    (cyclicMovingForm G).toMatrix (cyclicMovingBasis G) =
      (1 : Matrix (CyclicMovingIndex G) (CyclicMovingIndex G) ℤ) + Matrix.of (fun _ _ => 1) := by
  classical
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply, cyclicMovingBasis_apply, cyclicMovingBasis_apply,
    cyclicMovingForm_apply, cyclicMovingProfile_root, cyclicMovingProfile_root,
    pairing_roots_common_base _ _ _ i.property j.property]
  simp only [Matrix.add_apply, Matrix.one_apply]
  congr 1
  simp only [Subtype.ext_iff]

/-- The augmentation lattice has codimension one. -/
theorem cyclicMoving_rank : Module.finrank ℤ (CyclicIntegralMoving G) + 1 = Fintype.card G := by
  classical
  rw [Module.finrank_eq_card_basis (cyclicMovingBasis G)]
  exact card_subtype_ne_succ (1 : G)

/-- The augmentation Gram determinant equals the number of group labels. -/
theorem cyclicMovingGram_det :
    ((cyclicMovingForm G).toMatrix (cyclicMovingBasis G)).det = (Fintype.card G : ℤ) := by
  classical
  rw [cyclicMovingBasis_gram]
  let A : Matrix (CyclicMovingIndex G) Unit ℤ := fun _ _ => 1
  let B : Matrix Unit (CyclicMovingIndex G) ℤ := fun _ _ => 1
  have hAB : A * B = Matrix.of (fun _ _ => (1 : ℤ)) := by ext i j; simp [Matrix.mul_apply, A, B]
  rw [← hAB, Matrix.det_one_add_mul_comm, Matrix.det_unique]
  have hc : Fintype.card (CyclicMovingIndex G) + 1 = Fintype.card G :=
    card_subtype_ne_succ (1 : G)
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, A, B,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact_mod_cast (by omega : 1 + Fintype.card (CyclicMovingIndex G) = Fintype.card G)

variable [IsCyclic G]

omit [DecidableEq G] in
/-- Cyclic difference is injective on the augmentation lattice. -/
theorem cyclicMovingDelta_injective : Function.Injective (cyclicMovingDelta G) := by
  apply LinearMap.injective_of_det_ne_zero
  intro h
  have hd := cyclicMovingDelta_det_natAbs G
  rw [h, Int.natAbs_zero] at hd
  exact (Fintype.card_pos_iff.mpr (inferInstance : Nonempty G)).ne' hd.symm

/-- Difference identifies the augmentation lattice with its image. -/
def cyclicDifferenceEquiv : CyclicIntegralMoving G ≃ₗ[ℤ] CyclicDifferenceLattice G :=
  LinearEquiv.ofInjective (cyclicMovingDelta G) (cyclicMovingDelta_injective G)

/-- The image under cyclic difference of the augmentation basis. -/
def cyclicDifferenceBasis : Module.Basis (CyclicMovingIndex G) ℤ (CyclicDifferenceLattice G) :=
  (cyclicMovingBasis G).map (cyclicDifferenceEquiv G)

/-- The coordinate pairing restricted to the cyclic difference lattice. -/
def cyclicDifferenceForm : LinearMap.BilinForm ℤ (CyclicDifferenceLattice G) :=
  (cyclicMovingForm G).comp (CyclicDifferenceLattice G).subtype (CyclicDifferenceLattice G).subtype

/-- The image Gram matrix is the pullback Gram matrix of cyclic difference. -/
theorem cyclicDifferenceGram_eq :
    (cyclicDifferenceForm G).toMatrix (cyclicDifferenceBasis G) =
      ((cyclicMovingForm G).comp (cyclicMovingDelta G) (cyclicMovingDelta G)).toMatrix
        (cyclicMovingBasis G) := by
  ext i j
  simp only [LinearMap.BilinForm.toMatrix_apply, cyclicDifferenceBasis, Module.Basis.map_apply]
  rfl

/-- The cyclic difference lattice has discriminant equal to the cube of the group order. -/
theorem cyclicDifferenceGram_det :
    ((cyclicDifferenceForm G).toMatrix (cyclicDifferenceBasis G)).det = (Fintype.card G : ℤ)^3 := by
  rw [cyclicDifferenceGram_eq,
    LinearMap.BilinForm.toMatrix_comp (cyclicMovingBasis G) (cyclicMovingBasis G),
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  simp only [LinearMap.det_toMatrix, cyclicMovingGram_det]
  have hd : |LinearMap.det (cyclicMovingDelta G)| = (Fintype.card G : ℤ) := by
    rw [← Int.natCast_natAbs, cyclicMovingDelta_det_natAbs]
  have hs : (LinearMap.det (cyclicMovingDelta G))^2 = (Fintype.card G : ℤ)^2 := by
    rw [← hd, sq_abs]
  calc
    _ = (LinearMap.det (cyclicMovingDelta G))^2 * (Fintype.card G : ℤ) := by ring
    _ = _ := by rw [hs]; ring

/-- Cyclic difference preserves the rank of the augmentation lattice. -/
theorem cyclicDifference_rank :
    Module.finrank ℤ (CyclicDifferenceLattice G) + 1 = Fintype.card G := by
  rw [(cyclicDifferenceEquiv G).finrank_eq.symm]
  exact cyclicMoving_rank G

omit [DecidableEq G] in
/-- The diagonal pairing is the integral coordinate energy. -/
theorem cyclicDifferenceForm_diag (v : CyclicDifferenceLattice G) :
    cyclicDifferenceForm G v v = cyclicMovingEnergy G v := by
  change pairing (cyclicMovingProfile G v) (cyclicMovingProfile G v) =
    energy (cyclicMovingProfile G v)
  simp only [pairing, energy, pow_two]

omit [DecidableEq G] in
/-- The cyclic difference lattice is even. -/
theorem cyclicDifferenceForm_even (v : CyclicDifferenceLattice G) :
    Even (cyclicDifferenceForm G v v) := by
  rw [cyclicDifferenceForm_diag]
  exact cyclicMovingEnergy_even G v

omit [DecidableEq G] in
/-- The cyclic difference pairing is positive on every nonzero vector. -/
theorem cyclicDifferenceForm_positive (v : CyclicDifferenceLattice G) (hv : v ≠ 0) :
    0 < cyclicDifferenceForm G v v := by
  rw [cyclicDifferenceForm_diag]
  exact lt_of_lt_of_le (by norm_num) (cyclicDifference_energy_ge_four G v hv)

#print axioms cyclicDifference_rank
#print axioms cyclicDifferenceForm_positive
#print axioms cyclicMovingGram_det
#print axioms cyclicDifferenceGram_det

end GaloisForLFunctions.RepresentationLifting

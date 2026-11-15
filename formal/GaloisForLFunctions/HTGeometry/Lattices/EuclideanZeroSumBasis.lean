import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# A basis of the Euclidean zero-sum hyperplane

Deleting one coordinate identifies the hyperplane with the remaining real
coordinates. The inverse sends coordinate vectors to roots sharing the
deleted coordinate as base.
-/

open scoped BigOperators
open Module
noncomputable section
namespace GaloisForLFunctions.HTGeometry.EuclideanZeroSum
variable (ι : Type*) [Fintype ι]

/-- Sum of the Euclidean coordinates. -/
def coordinateSum : EuclideanSpace ℝ ι →ₗ[ℝ] ℝ where
  toFun v := ∑ i, v i
  map_add' v w := by simp [Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.mul_sum]

/-- The real zero-sum hyperplane. -/
abbrev space := LinearMap.ker (coordinateSum ι)

/-- A difference of coordinate unit vectors. -/
def root (a b : ι) : space ι := by
  classical
  exact ⟨EuclideanSpace.single a 1 - EuclideanSpace.single b 1, by
    change ∑ i, ((EuclideanSpace.single a (1 : ℝ) - EuclideanSpace.single b 1) : EuclideanSpace ℝ ι).ofLp i = 0
    simp [PiLp.single_apply, Finset.sum_sub_distrib]⟩

variable [DecidableEq ι] (e : ι)
abbrev index := {i : ι // i ≠ e}

/-- Delete the base coordinate; the zero-sum equation recovers it. -/
def coordinates : space ι →ₗ[ℝ] (index ι e → ℝ) where
  toFun v i := v.val i.val
  map_add' v w := by ext i; rfl
  map_smul' c v := by ext i; rfl

theorem coordinates_eq_zero {v : space ι} (hv : coordinates ι e v = 0) : v = 0 := by
  have haway (i : ι) (hi : i ≠ e) : v.val i = 0 := congrFun hv ⟨i, hi⟩
  -- The omitted coordinate is the negative sum of the others.
  have hsum : ∑ i, v.val i = v.val e := by
    apply Finset.sum_eq_single e
    · intro i _ hi
      exact haway i hi
    · simp
  have he : v.val e = 0 := hsum.symm.trans v.property
  apply Subtype.ext
  ext i
  by_cases hi : i = e
  · subst i; exact he
  · exact haway i hi

theorem coordinates_injective : Function.Injective (coordinates ι e) := by
  intro v w h
  apply sub_eq_zero.mp
  apply coordinates_eq_zero ι e
  rw [map_sub, h, sub_self]

theorem coordinates_root (i : index ι e) :
    coordinates ι e (root ι i.val e) = Pi.single i 1 := by
  ext j
  simp [coordinates, root, PiLp.single_apply, Pi.single_apply, j.property, Subtype.ext_iff]

theorem coordinates_surjective : Function.Surjective (coordinates ι e) := by
  intro f
  refine ⟨∑ i, f i • root ι i.val e, ?_⟩
  simp only [map_sum, map_smul, coordinates_root]
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

/-- Independent real coordinates on the hyperplane. -/
def coordinateEquiv : space ι ≃ₗ[ℝ] (index ι e → ℝ) :=
  LinearEquiv.ofBijective (coordinates ι e) ⟨coordinates_injective ι e, coordinates_surjective ι e⟩

/-- The root basis with a common base coordinate. -/
def basis : Basis (index ι e) ℝ (space ι) :=
  (Pi.basisFun ℝ (index ι e)).map (coordinateEquiv ι e).symm

theorem basis_apply (i : index ι e) : basis ι e i = root ι i.val e := by
  apply (coordinateEquiv ι e).injective
  simp only [basis, Basis.map_apply, LinearEquiv.apply_symm_apply]
  change Pi.basisFun ℝ (index ι e) i = coordinates ι e (root ι i.val e)
  rw [coordinates_root, Pi.basisFun_apply]

theorem finrank_space : finrank ℝ (space ι) = Fintype.card (index ι e) :=
  finrank_eq_card_basis (basis ι e)

omit [DecidableEq ι] in
theorem inner_root (a b : ι) (v : space ι) :
    inner ℝ (root ι a b) v = v.val a - v.val b := by
  classical
  change inner ℝ (EuclideanSpace.single a (1 : ℝ) - EuclideanSpace.single b 1) v.val = _
  simp [PiLp.inner_apply, mul_sub,
    Finset.sum_sub_distrib]

#print axioms basis_apply
#print axioms finrank_space
end GaloisForLFunctions.HTGeometry.EuclideanZeroSum

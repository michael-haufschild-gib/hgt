import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Algebra.BigOperators.Pi

/-!
# Circle characters of arbitrary products

A continuous circle character on a product of groups depends on finitely
many coordinates. A product neighborhood constrains only finitely many
coordinates; all powers of a tail element remain in it, so the absence of
small circle subgroups kills the tail. For abelian factors this gives an
exact finite product of the coordinate characters.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical
namespace GaloisForLFunctions.HTGeometry.ProductCircleCharacters

variable {ι : Type*} {G : ι → Type*}

section Group
variable [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]

/-- Inclusion of one coordinate, with identity in every other coordinate. -/
def coordinateInclusion (i : ι) : G i →ₜ* (∀ j, G j) where
  toMonoidHom := MonoidHom.mulSingle G i
  continuous_toFun := continuous_mulSingle i

/-- Restriction of a continuous character to one coordinate group. -/
def coordinateCharacter (χ : (∀ i, G i) →ₜ* Circle) (i : ι) : G i →ₜ* Circle :=
  χ.comp (coordinateInclusion i)

/-- The character kills every element supported outside one finite set. -/
theorem exists_finite_tail_kernel (χ : (∀ i, G i) →ₜ* Circle) :
    ∃ S : Finset ι, ∀ x : ∀ i, G i, (∀ i ∈ S, x i = 1) → χ x = 1 := by
  have hopen := (Circle.isOpen_centeredArc (π / 2)).preimage χ.continuous
  have hone : (1 : ∀ i, G i) ∈ χ ⁻¹' Circle.centeredArc (π / 2) := by
    change χ 1 ∈ Circle.centeredArc (π / 2)
    rw [map_one, Circle.mem_centeredArc (by linarith [pi_pos])]
    simpa using half_pos pi_pos
  have hnhds := hopen.mem_nhds hone
  rw [nhds_pi] at hnhds
  obtain ⟨I, hI, t, ht, hsub⟩ := Filter.mem_pi.mp hnhds
  refine ⟨hI.toFinset, fun x hx => ?_⟩
  apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
  intro n _
  have hpowers : x ^ n ∈ I.pi t := by
    intro i hi
    change x i ^ n ∈ t i
    rw [hx i (hI.mem_toFinset.mpr hi), one_pow]
    exact mem_of_mem_nhds (ht i)
  have h : χ (x ^ n) ∈ Circle.centeredArc (π / 2) := hsub hpowers
  simpa only [map_pow] using h

/-- Equality in finitely many coordinates determines the character value. -/
theorem exists_finite_dependence (χ : (∀ i, G i) →ₜ* Circle) :
    ∃ S : Finset ι, ∀ x y : ∀ i, G i, (∀ i ∈ S, x i = y i) → χ x = χ y := by
  obtain ⟨S, hS⟩ := exists_finite_tail_kernel χ
  refine ⟨S, fun x y hxy => ?_⟩
  have htail : χ (x * y⁻¹) = 1 := hS _ (fun i hi => by
    change x i * (y i)⁻¹ = 1
    rw [hxy i hi, mul_inv_cancel])
  rw [map_mul, map_inv] at htail
  exact mul_inv_eq_one.mp htail

/-- Only finitely many coordinate restrictions can be nontrivial. -/
theorem finite_nontrivial_coordinates (χ : (∀ i, G i) →ₜ* Circle) :
    {i | coordinateCharacter χ i ≠ 1}.Finite := by
  obtain ⟨S, hS⟩ := exists_finite_tail_kernel χ
  apply S.finite_toSet.subset
  intro i hi
  by_contra hiS
  apply hi
  apply ContinuousMonoidHom.ext
  intro u
  change χ (Pi.mulSingle i u) = 1
  apply hS
  intro j hj
  have hji : j ≠ i := by
    intro h
    subst j
    exact hiS hj
  exact Pi.mulSingle_eq_of_ne hji u

end Group

section CommGroup
variable [∀ i, CommGroup (G i)] [∀ i, TopologicalSpace (G i)]

/-- Every character is the finite product of its actual coordinate restrictions. -/
theorem exists_finite_coordinate_product (χ : (∀ i, G i) →ₜ* Circle) :
    ∃ S : Finset ι, ∀ x : ∀ i, G i,
      χ x = ∏ i ∈ S, coordinateCharacter χ i (x i) := by
  obtain ⟨S, hS⟩ := exists_finite_dependence χ
  refine ⟨S, fun x => ?_⟩
  have htrunc (j : ι) (hj : j ∈ S) :
      (∏ i ∈ S, Pi.mulSingle i (x i)) j = x j := by
    rw [Finset.prod_apply, Finset.prod_eq_single_of_mem j hj]
    · exact Pi.mulSingle_eq_same j (x j)
    · intro i _ hij
      exact Pi.mulSingle_eq_of_ne hij.symm (x i)
  calc
    χ x = χ (∏ i ∈ S, Pi.mulSingle i (x i)) :=
      hS x _ (fun j hj => (htrunc j hj).symm)
    _ = ∏ i ∈ S, coordinateCharacter χ i (x i) := by
      rw [map_prod]
      rfl

#print axioms exists_finite_tail_kernel
#print axioms finite_nontrivial_coordinates
#print axioms exists_finite_coordinate_product

end CommGroup
end GaloisForLFunctions.HTGeometry.ProductCircleCharacters

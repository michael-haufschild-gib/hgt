import GaloisForLFunctions.HTGeometry.CubicFamilySplittingGroup
import GaloisForLFunctions.RHTower.XiCubicDiscriminantPackets

/-!
# The full finite joint cubic Galois group of the actual Xi source

Every finite set of distinct integer marks contributes an independent S3
factor. The common splitting field has degree six to the number of marks,
with all discriminant independence supplied by actual Xi square-class proofs.
-/

noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry

local instance : CharZero MeromorphicPlane :=
  charZero_of_injective_ringHom constPlane_injective

/-- The actual cubic channel labelled by the integer n+2. -/
def integerMarkedXiCubic (n : ℕ) : Cubic MeromorphicPlane :=
  ⟨1, 0, -3, -(2 + 4 * xiCubicParameterElement (Real.log (n + 2)))⟩

theorem integerMarkedXiCubic_toPoly (n : ℕ) :
    (integerMarkedXiCubic n).toPoly = xiCubicPolynomial (Real.log (n + 2)) := rfl

theorem integerMarkedXiCubic_discr (n : ℕ) :
    (integerMarkedXiCubic n).discr = xiCubicDiscriminant (Real.log (n + 2)) := rfl

theorem integerMarkedXiCubic_irreducible (n : ℕ) :
    Irreducible (integerMarkedXiCubic n).toPoly :=
  xiCubicPolynomial_irreducible _ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n + 2)))

/-- Actual discriminant independence on any finite collection of distinct channel labels. -/
theorem integerMarkedXiCubic_subtype_independent (S : Finset ℕ)
    (T : Finset S) (hT : T.Nonempty) : ¬ IsSquare (∏ i ∈ T, (integerMarkedXiCubic i).discr) := by
  classical
  have hns := xiCubicDiscriminant_packet_not_isSquare (T.image Subtype.val) (hT.image _)
  rw [Finset.prod_image] at hns
  · exact hns
  · intro i _ j _ h
    exact Subtype.ext h

/-- A polynomial presenting the common splitting field of the selected actual cubics. -/
def xiJointCubicPolynomial (S : Finset ℕ) : Polynomial MeromorphicPlane :=
  cubicFamilyPolynomial (fun n : S => integerMarkedXiCubic n)

theorem xiJointCubicPolynomial_eq_prod (S : Finset ℕ) :
    xiJointCubicPolynomial S = ∏ n ∈ S, xiCubicPolynomial (Real.log (n + 2)) := by
  exact Finset.prod_coe_sort S (fun n => xiCubicPolynomial (Real.log (n + 2)))

/-- Every finite collection of actual marked Xi cubics has the full joint product Galois group. -/
def xiJointCubicGaloisEquiv (S : Finset ℕ) :
    (xiJointCubicPolynomial S).Gal ≃* (S → Equiv.Perm (Fin 3)) :=
  cubicFamilyGaloisEquiv (fun n : S => integerMarkedXiCubic n)
    (fun _ => one_ne_zero) (fun n => integerMarkedXiCubic_irreducible n)
    (integerMarkedXiCubic_subtype_independent S)

/-- The finite joint cubic splitting degree is exactly six to the number of selected channels. -/
theorem xiJointCubic_splittingField_finrank (S : Finset ℕ) :
    Module.finrank MeromorphicPlane (xiJointCubicPolynomial S).SplittingField = 6 ^ S.card := by
  unfold xiJointCubicPolynomial
  simpa using cubicFamily_splittingField_finrank (fun n : S => integerMarkedXiCubic n)
    (fun _ => one_ne_zero) (fun n => integerMarkedXiCubic_irreducible n)
    (integerMarkedXiCubic_subtype_independent S)

end RHTower

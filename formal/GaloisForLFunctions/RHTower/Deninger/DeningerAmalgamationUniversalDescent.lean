import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Universal descent through the unit amalgamation

The amalgamation of two algebras over a common base is their tensor product, and its universal
property is exactly the statement the descent theorem needs: a pair of maps out of the two factors,
agreeing on the base, extends to the amalgamation, and the extension is unique.  No further
relation has to be imposed — every relation already satisfied by both factors is satisfied by the
extension, because the extension exists.

Applied to a split square-zero target, the first component of the extension is the specialization
and the second is a derivation over it: it is additive, and its Leibniz rule is the multiplication
rule of the split square-zero extension.  So a compatible pair of boundary squares determines a
unique specialization together with a unique derivation extending the two given ones.

* `deningerAmalgamationLift`, `_left`, `_right`, `_unique` : the universal property.
* `deningerAmalgamSpecialization`, `deningerAmalgamResidue` : the two components on a split
  square-zero target.
* `deningerAmalgamResidue_leibniz` : the residue component is a derivation over the
  specialization.
-/

namespace RHTower

open scoped TensorProduct

section UniversalProperty

variable {P T K S : Type*} [CommRing P] [CommRing T] [CommRing K] [CommRing S]
variable [Algebra P T] [Algebra P K] [Algebra P S]

/-- **The amalgamation lift.**  A pair of algebra maps out of the two factors extends to the
amalgamation. -/
def deningerAmalgamationLift (sT : T →ₐ[P] S) (sK : K →ₐ[P] S) : (T ⊗[P] K) →ₐ[P] S :=
  Algebra.TensorProduct.productMap sT sK

@[simp]
theorem deningerAmalgamationLift_tmul (sT : T →ₐ[P] S) (sK : K →ₐ[P] S) (t : T) (k : K) :
    deningerAmalgamationLift sT sK (t ⊗ₜ[P] k) = sT t * sK k := rfl

/-- The lift restricts to the given map on the first factor. -/
theorem deningerAmalgamationLift_left (sT : T →ₐ[P] S) (sK : K →ₐ[P] S) (t : T) :
    deningerAmalgamationLift sT sK (t ⊗ₜ[P] (1 : K)) = sT t := by
  rw [deningerAmalgamationLift_tmul, map_one, mul_one]

/-- The lift restricts to the given map on the second factor. -/
theorem deningerAmalgamationLift_right (sT : T →ₐ[P] S) (sK : K →ₐ[P] S) (k : K) :
    deningerAmalgamationLift sT sK ((1 : T) ⊗ₜ[P] k) = sK k := by
  rw [deningerAmalgamationLift_tmul, map_one, one_mul]

/-- **Uniqueness.**  Two maps out of the amalgamation agreeing on both factors are equal, so the
space of extensions of a compatible pair is a point: all further relations descend automatically. -/
theorem deningerAmalgamationLift_unique {phi psi : (T ⊗[P] K) →ₐ[P] S}
    (hleft : ∀ t : T, phi (t ⊗ₜ[P] (1 : K)) = psi (t ⊗ₜ[P] (1 : K)))
    (hright : ∀ k : K, phi ((1 : T) ⊗ₜ[P] k) = psi ((1 : T) ⊗ₜ[P] k)) : phi = psi := by
  refine Algebra.TensorProduct.ext ?_ ?_
  · exact AlgHom.ext fun t => hleft t
  · exact AlgHom.ext fun k => hright k

end UniversalProperty

section SquareZeroTarget

variable {P A B M : Type*} [CommRing P] [CommRing A] [CommRing B] [AddCommGroup M]
variable [Algebra P A] [Algebra P B] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
variable [Module P M] [IsScalarTower P B M] [IsScalarTower P Bᵐᵒᵖ M]

/-- **The specialization component.**  Projecting a map into a split square-zero extension along
its augmentation gives the specialization. -/
def deningerAmalgamSpecialization (phi : A →ₐ[P] TrivSqZeroExt B M) : A →ₐ[P] B :=
  (TrivSqZeroExt.fstHom P B M).comp phi

@[simp]
theorem deningerAmalgamSpecialization_apply (phi : A →ₐ[P] TrivSqZeroExt B M) (a : A) :
    deningerAmalgamSpecialization phi a = (phi a).fst := rfl

/-- **The residue component.**  The square-zero part of a map into a split square-zero
extension. -/
def deningerAmalgamResidue (phi : A →ₐ[P] TrivSqZeroExt B M) (a : A) : M := (phi a).snd

@[simp]
theorem deningerAmalgamResidue_apply (phi : A →ₐ[P] TrivSqZeroExt B M) (a : A) :
    deningerAmalgamResidue phi a = (phi a).snd := rfl

theorem deningerAmalgamResidue_add (phi : A →ₐ[P] TrivSqZeroExt B M) (a b : A) :
    deningerAmalgamResidue phi (a + b)
      = deningerAmalgamResidue phi a + deningerAmalgamResidue phi b := by
  show (phi (a + b)).snd = (phi a).snd + (phi b).snd
  rw [map_add]
  rfl

theorem deningerAmalgamResidue_one (phi : A →ₐ[P] TrivSqZeroExt B M) :
    deningerAmalgamResidue phi 1 = 0 := by
  show (phi 1).snd = 0
  rw [map_one]
  rfl

/-- **The residue component is a derivation over the specialization.**  Its Leibniz rule is the
multiplication rule of the split square-zero extension, so a compatible pair of boundary squares
determines a unique specialization together with a unique derivation extending them. -/
theorem deningerAmalgamResidue_leibniz (phi : A →ₐ[P] TrivSqZeroExt B M) (a b : A) :
    deningerAmalgamResidue phi (a * b)
      = deningerAmalgamSpecialization phi a • deningerAmalgamResidue phi b
        + MulOpposite.op (deningerAmalgamSpecialization phi b) • deningerAmalgamResidue phi a := by
  show (phi (a * b)).snd
      = (phi a).fst • (phi b).snd + MulOpposite.op ((phi b).fst) • (phi a).snd
  rw [map_mul, TrivSqZeroExt.snd_mul]

end SquareZeroTarget

section AmalgamatedResidue

variable {P T K B M : Type*} [CommRing P] [CommRing T] [CommRing K] [CommRing B] [AddCommGroup M]
variable [Algebra P T] [Algebra P K] [Algebra P B]
variable [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
variable [Module P M] [IsScalarTower P B M] [IsScalarTower P Bᵐᵒᵖ M]

/-- **The descended boundary square.**  Two compatible square-zero boundary maps extend uniquely to
the amalgamation, and the extension has the two given specializations and residues on the two
factors. -/
theorem deningerAmalgamResidue_left (sT : T →ₐ[P] TrivSqZeroExt B M)
    (sK : K →ₐ[P] TrivSqZeroExt B M) (t : T) :
    deningerAmalgamResidue (deningerAmalgamationLift sT sK) (t ⊗ₜ[P] (1 : K))
      = deningerAmalgamResidue sT t := by
  show ((deningerAmalgamationLift sT sK) (t ⊗ₜ[P] (1 : K))).snd = (sT t).snd
  rw [deningerAmalgamationLift_left]

theorem deningerAmalgamResidue_right (sT : T →ₐ[P] TrivSqZeroExt B M)
    (sK : K →ₐ[P] TrivSqZeroExt B M) (k : K) :
    deningerAmalgamResidue (deningerAmalgamationLift sT sK) ((1 : T) ⊗ₜ[P] k)
      = deningerAmalgamResidue sK k := by
  show ((deningerAmalgamationLift sT sK) ((1 : T) ⊗ₜ[P] k)).snd = (sK k).snd
  rw [deningerAmalgamationLift_right]

theorem deningerAmalgamSpecialization_left (sT : T →ₐ[P] TrivSqZeroExt B M)
    (sK : K →ₐ[P] TrivSqZeroExt B M) (t : T) :
    deningerAmalgamSpecialization (deningerAmalgamationLift sT sK) (t ⊗ₜ[P] (1 : K))
      = deningerAmalgamSpecialization sT t := by
  show ((deningerAmalgamationLift sT sK) (t ⊗ₜ[P] (1 : K))).fst = (sT t).fst
  rw [deningerAmalgamationLift_left]

theorem deningerAmalgamSpecialization_right (sT : T →ₐ[P] TrivSqZeroExt B M)
    (sK : K →ₐ[P] TrivSqZeroExt B M) (k : K) :
    deningerAmalgamSpecialization (deningerAmalgamationLift sT sK) ((1 : T) ⊗ₜ[P] k)
      = deningerAmalgamSpecialization sK k := by
  show ((deningerAmalgamationLift sT sK) ((1 : T) ⊗ₜ[P] k)).fst = (sK k).fst
  rw [deningerAmalgamationLift_right]

end AmalgamatedResidue

section RealifiedResidue

/-- **The quadratic correction dies after realification.**  The class `{-1}` is `2`-torsion, and a
`2`-torsion element of a vector space over a field in which `2` is invertible is zero, so Milnor's
relation `Π² = {-1}Π` becomes `Π² = 0`: after realification the specialization--residue target is a
genuinely split square-zero extension. -/
theorem deningerQuadraticCorrection_eq_zero {k M : Type*} [DivisionRing k] [AddCommGroup M]
    [Module k M] (hk : (2 : k) ≠ 0) {c : M} (h : (2 : ℤ) • c = 0) : c = 0 := by
  have h2 : (2 : k) • c = 0 := by
    rw [two_smul]
    rw [two_zsmul] at h
    exact h
  rcases smul_eq_zero.mp h2 with hc | hc
  · exact absurd hc hk
  · exact hc

/-- In the split square-zero extension the residue direction squares to zero. -/
theorem deningerResidueDirection_sq_eq_zero {B M : Type*} [CommRing B] [AddCommGroup M]
    [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (m n : M) :
    (TrivSqZeroExt.inr m : TrivSqZeroExt B M) * TrivSqZeroExt.inr n = 0 :=
  TrivSqZeroExt.inr_mul_inr B m n

end RealifiedResidue

end RHTower

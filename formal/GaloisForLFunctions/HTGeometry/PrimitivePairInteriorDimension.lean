import GaloisForLFunctions.HTGeometry.ColorGramNullFusion
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.StdBasis

/-!
# Primitive-pair interior fusion forces two complex components

For a complex root `u`, its rank-one Gram record is `uᴴu`.  This file proves an exact dimension
classification: when `q ≥ 2`, every linearly independent pair of roots in `ℂ^q` has
positive-definite Gram sum if and only if `q = 2`.

The positive direction reuses the genuine `2 × 2` colour-Gram null-fusion theorem.  The negative
direction works for every `q = n + 3`: the first two coordinate roots are independent, but their
Gram sum annihilates the third coordinate root.

This is the root-level mathematical content of elementary future fusion.  It does not derive that
physical events satisfy the property, identify the resulting cone with spacetime, or establish
gravity.
-/

open Matrix
open scoped ComplexOrder Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Rank-one positive Gram record of one primitive complex root. -/
def primitiveRootGram {n : Type*} (u : n → ℂ) : Matrix n n ℂ :=
  Matrix.vecMulVec (star u) u

/-- Ordered pair of roots, indexed by `Fin 2`. -/
def primitiveRootPair {n : Type*} (u v : n → ℂ) : Fin 2 → (n → ℂ) :=
  fun i => if i = 0 then u else v

/-- Every independent primitive pair creates an interior Gram record. -/
def PrimitivePairInterior (n : Type*) [Fintype n] : Prop :=
  ∀ u v : n → ℂ, LinearIndependent ℂ (primitiveRootPair u v) →
    (primitiveRootGram u + primitiveRootGram v).PosDef

/-- On two components, a primitive root Gram record is a one-row colour-event Gram record. -/
theorem primitiveRootGram_finTwo_eq_colorGram
    (u : Fin 2 → ℂ) :
    primitiveRootGram u = colorGramMatrix (singleColorEvent u) := by
  ext i j
  simp [primitiveRootGram, Matrix.vecMulVec_apply, Pi.star_apply,
    colorGramMatrix, singleColorEvent, Matrix.mul_apply]

/-- Every independent primitive pair in two complex components fuses to the interior. -/
theorem primitivePairInterior_finTwo :
    PrimitivePairInterior (Fin 2) := by
  intro u v hindependent
  let B : Matrix (Fin 2) (Fin 2) ℂ := fun i => primitiveRootPair u v i
  have hunit : IsUnit B :=
    Matrix.linearIndependent_rows_iff_isUnit.mp hindependent
  have hdet : B.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det B).mp hunit).ne_zero
  have hminor : u 0 * v 1 - v 0 * u 1 ≠ 0 := by
    simpa [B, primitiveRootPair, Matrix.det_fin_two, mul_comm] using hdet
  rw [primitiveRootGram_finTwo_eq_colorGram,
    primitiveRootGram_finTwo_eq_colorGram]
  exact independent_nullRoot_gram_add_posDef u v hminor

/-- The first two coordinate roots remain independent in every dimension at least three. -/
theorem primitiveCoordinatePair_linearIndependent (n : ℕ) :
    LinearIndependent ℂ
      (primitiveRootPair
        (Pi.single (0 : Fin (n + 3)) (1 : ℂ))
        (Pi.single (1 : Fin (n + 3)) (1 : ℂ))) := by
  rw [linearIndependent_fin2]
  constructor
  · intro hzero
    have h := congrFun hzero (1 : Fin (n + 3))
    simp [primitiveRootPair] at h
  · intro a heq
    have h := congrFun heq (0 : Fin (n + 3))
    simp [primitiveRootPair] at h

/-- A rank-one Gram record acts through the scalar overlap with its root. -/
theorem primitiveRootGram_mulVec
    {n : Type*} [Fintype n] (u x : n → ℂ) :
    primitiveRootGram u *ᵥ x =
      fun i => star (u i) * (u ⬝ᵥ x) := by
  ext i
  simp only [primitiveRootGram, Matrix.mulVec, Matrix.vecMulVec_apply,
    Pi.star_apply, dotProduct, Finset.mul_sum, mul_assoc]

/-- A coordinate-root Gram record kills every distinct coordinate root. -/
theorem primitiveCoordinateRootGram_mulVec_of_ne
    {n : Type*} [Fintype n] [DecidableEq n]
    (i k : n) (hik : i ≠ k) :
    primitiveRootGram (Pi.single i (1 : ℂ)) *ᵥ
      Pi.single k (1 : ℂ) = 0 := by
  rw [primitiveRootGram_mulVec]
  have hdot :
      Pi.single i (1 : ℂ) ⬝ᵥ Pi.single k (1 : ℂ) = 0 := by
    rw [single_one_dotProduct, Pi.single_eq_of_ne hik]
  simp only [hdot, mul_zero]
  rfl

/-- In every dimension at least three, two independent primitive roots can fail to reach interior. -/
theorem not_primitivePairInterior_finAddThree (n : ℕ) :
    ¬ PrimitivePairInterior (Fin (n + 3)) := by
  intro hinterior
  let u : Fin (n + 3) → ℂ := Pi.single 0 1
  let v : Fin (n + 3) → ℂ := Pi.single 1 1
  let x : Fin (n + 3) → ℂ := Pi.single 2 1
  have hpos := hinterior u v (primitiveCoordinatePair_linearIndependent n)
  have hx : x ≠ 0 := by
    intro hzero
    have h := congrFun hzero (2 : Fin (n + 3))
    simp [x] at h
  have hzero_two : (0 : Fin (n + 3)) ≠ 2 := by
    intro h
    have hval := congrArg Fin.val h
    change 0 = 2 % (n + 3) at hval
    rw [Nat.mod_eq_of_lt (by omega : 2 < n + 3)] at hval
    omega
  have hone_two : (1 : Fin (n + 3)) ≠ 2 := by
    intro h
    have hval := congrArg Fin.val h
    change 1 = 2 % (n + 3) at hval
    rw [Nat.mod_eq_of_lt (by omega : 2 < n + 3)] at hval
    omega
  have hmul : (primitiveRootGram u + primitiveRootGram v) *ᵥ x = 0 := by
    rw [add_mulVec]
    simp only [u, v, x]
    rw [primitiveCoordinateRootGram_mulVec_of_ne 0 2 hzero_two,
      primitiveCoordinateRootGram_mulVec_of_ne 1 2 hone_two]
    exact add_zero 0
  have hstrict := hpos.dotProduct_mulVec_pos hx
  rw [hmul, dotProduct_zero] at hstrict
  exact (lt_irrefl 0) hstrict

/--
For every nonclassical complex component count `q ≥ 2`, universal primitive-pair interior fusion
holds exactly in two components.
-/
theorem primitivePairInterior_fin_iff (q : ℕ) (hq : 2 ≤ q) :
    PrimitivePairInterior (Fin q) ↔ q = 2 := by
  constructor
  · intro hinterior
    by_contra hne
    have hthree : 3 ≤ q := by omega
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hthree
    exact (not_primitivePairInterior_finAddThree n) hinterior
  · rintro rfl
    exact primitivePairInterior_finTwo

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.PrimitivePairInteriorDimension
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Primitive Gram interior arity

For a family of complex roots, sum their rank-one Gram records. This file proves that the sum is
positive definite exactly when the associated row-evaluation map is injective. Consequently fewer
than `q` roots can never reach the interior of `H_q(ℂ)₊`, while the `q` coordinate roots sum to
the identity.

Thus the least number of primitive Gram records that can create an interior record is exactly the
complex rank `q`. This is standard finite-dimensional Gram/rank mathematics. It does not prove
that physical actualization has arity two, that causalization preserves arity, or that the cone is
spacetime.
-/

open Matrix
open scoped ComplexOrder Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Matrix whose rows are a finite family of primitive complex roots. -/
def primitiveRootFamilyMatrix {q k : ℕ}
    (u : Fin k → (Fin q → ℂ)) : Matrix (Fin k) (Fin q) ℂ :=
  fun a i => u a i

/-- Sum of the rank-one positive Gram records of a finite root family. -/
def primitiveRootGramSum {q k : ℕ}
    (u : Fin k → (Fin q → ℂ)) : Matrix (Fin q) (Fin q) ℂ :=
  ∑ a, primitiveRootGram (u a)

/-- A root-family Gram sum is the ordinary rectangular Gram matrix of its row matrix. -/
theorem primitiveRootGramSum_eq_conjTranspose_mul_self {q k : ℕ}
    (u : Fin k → (Fin q → ℂ)) :
    primitiveRootGramSum u =
      (primitiveRootFamilyMatrix u)ᴴ * primitiveRootFamilyMatrix u := by
  ext i j
  simp only [primitiveRootGramSum, Matrix.sum_apply,
    primitiveRootGram, Matrix.vecMulVec_apply, Pi.star_apply,
    primitiveRootFamilyMatrix, Matrix.mul_apply,
    Matrix.conjTranspose_apply]

/--
A finite sum of primitive Gram records is interior exactly when the corresponding root-evaluation
map has no nonzero common annihilator.
-/
theorem primitiveRootGramSum_posDef_iff_mulVec_injective {q k : ℕ}
    (u : Fin k → (Fin q → ℂ)) :
    (primitiveRootGramSum u).PosDef ↔
      Function.Injective (primitiveRootFamilyMatrix u).mulVec := by
  rw [primitiveRootGramSum_eq_conjTranspose_mul_self]
  constructor
  · intro hpos x y hxy
    apply sub_eq_zero.mp
    by_contra hne
    have hzero :
        primitiveRootFamilyMatrix u *ᵥ (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    have hstrict := hpos.dotProduct_mulVec_pos hne
    rw [← Matrix.mulVec_mulVec, hzero, Matrix.mulVec_zero,
      dotProduct_zero] at hstrict
    exact (lt_irrefl 0) hstrict
  · exact Matrix.PosDef.conjTranspose_mul_self _

/-- Fewer than `q` primitive roots cannot create an interior record in `H_q(ℂ)₊`. -/
theorem primitiveRootGramSum_not_posDef_of_lt {q k : ℕ}
    (h : k < q) (u : Fin k → (Fin q → ℂ)) :
    ¬ (primitiveRootGramSum u).PosDef := by
  intro hpos
  have hinj :
      Function.Injective (primitiveRootFamilyMatrix u).mulVec :=
    (primitiveRootGramSum_posDef_iff_mulVec_injective u).mp hpos
  have hdim :
      Module.finrank ℂ (Fin k → ℂ) <
        Module.finrank ℂ (Fin q → ℂ) := by
    simpa only [Module.finrank_fin_fun] using h
  have hker :
      LinearMap.ker (primitiveRootFamilyMatrix u).mulVecLin ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  apply hker
  apply LinearMap.ker_eq_bot.mpr
  intro x y hxy
  apply hinj
  exact hxy

/-- The canonical family of all coordinate roots in complex rank `q`. -/
def primitiveCoordinateRootFamily (q : ℕ) :
    Fin q → (Fin q → ℂ) :=
  fun i => Pi.single i 1

/-- The row matrix of the coordinate-root family is the identity. -/
theorem primitiveCoordinateRootFamily_matrix (q : ℕ) :
    primitiveRootFamilyMatrix (primitiveCoordinateRootFamily q) = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [primitiveRootFamilyMatrix, primitiveCoordinateRootFamily]
  · simp [primitiveRootFamilyMatrix, primitiveCoordinateRootFamily,
      h, Ne.symm h]

/-- The `q` coordinate-root Gram records sum exactly to the identity. -/
theorem primitiveCoordinateRootGramSum_eq_one (q : ℕ) :
    primitiveRootGramSum (primitiveCoordinateRootFamily q) = 1 := by
  rw [primitiveRootGramSum_eq_conjTranspose_mul_self,
    primitiveCoordinateRootFamily_matrix, Matrix.conjTranspose_one,
    Matrix.one_mul]

/-- The full coordinate-root family creates an interior record. -/
theorem primitiveCoordinateRootGramSum_posDef (q : ℕ) :
    (primitiveRootGramSum (primitiveCoordinateRootFamily q)).PosDef := by
  rw [primitiveCoordinateRootGramSum_eq_one]
  exact Matrix.PosDef.one

/--
Primitive interior arity is exactly `q`: an interior sum exists with `q` roots, and none exists
with fewer roots.
-/
theorem primitiveInteriorArity_exact (q : ℕ) :
    (∃ u : Fin q → (Fin q → ℂ), (primitiveRootGramSum u).PosDef) ∧
      ∀ k < q, ¬ ∃ u : Fin k → (Fin q → ℂ),
        (primitiveRootGramSum u).PosDef := by
  constructor
  · exact ⟨primitiveCoordinateRootFamily q,
      primitiveCoordinateRootGramSum_posDef q⟩
  · intro k hk
    rintro ⟨u, hu⟩
    exact primitiveRootGramSum_not_posDef_of_lt hk u hu

end GaloisForLFunctions.HTGeometry

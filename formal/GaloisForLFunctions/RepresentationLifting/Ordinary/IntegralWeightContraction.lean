import GaloisForLFunctions.HTGeometry.SymmetricSquareMatrix
import Mathlib.Data.ZMod.Basic

/-!+# Integral contraction onto the highest-weight space

The normalized cocharacter in Loeffler–Rockwood–Zerbes, arXiv:2106.16082,
Lemma 2.3.4 and Corollary 3.3.2, acts by powers of the prime indexed by
the deficit from the highest weight. For an arbitrary integral weight
decomposition, its error from the zero-weight projection is divisible
by the full level. This includes the existing symmetric-square matrix.
-/

namespace GaloisForLFunctions.RepresentationLifting.IntegralOrdinary

noncomputable section

variable {ι : Type*}

/-- Integral action whose nonnegative weights measure the deficit from the highest weight. -/
def contraction (w : ι → ℕ) (a : ℤ) (r : ℕ) : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) where
  toFun v i := a ^ (r * w i) * v i
  map_add' v u := by ext i; exact mul_add _ _ _
  map_smul' c v := by ext i; simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- Projection onto the summands of weight zero. -/
def highestProjection (w : ι → ℕ) : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) where
  toFun v i := if w i = 0 then v i else 0
  map_add' v u := by ext i; by_cases h : w i = 0 <;> simp [h]
  map_smul' c v := by ext i; by_cases h : w i = 0 <;> simp [h]

/-- Increasing the level composes the normalized cocharacter actions. -/
theorem contraction_add (w : ι → ℕ) (a : ℤ) (r s : ℕ) :
    contraction w a (r + s) = (contraction w a r).comp (contraction w a s) := by
  ext v i
  simp only [contraction, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    add_mul, pow_add, mul_assoc]

theorem highestProjection_idempotent (w : ι → ℕ) :
    (highestProjection w).comp (highestProjection w) = highestProjection w := by
  ext v i
  by_cases h : w i = 0 <;> simp [highestProjection, h]

theorem contraction_highestProjection (w : ι → ℕ) (a : ℤ) (r : ℕ) :
    (contraction w a r).comp (highestProjection w) = highestProjection w := by
  ext v i
  by_cases h : w i = 0 <;> simp [contraction, highestProjection, h]

/-- The quotient of the non-highest-weight contribution by the level factor. -/
def contractionError (w : ι → ℕ) (a : ℤ) (r : ℕ) (v : ι → ℤ) : ι → ℤ :=
  fun i => if w i = 0 then 0 else a ^ (r * (w i - 1)) * v i

/-- Exact integral form of the highest-weight congruence; no prime is inverted. -/
theorem contraction_eq_projection_add (w : ι → ℕ) (a : ℤ) (r : ℕ) (v : ι → ℤ) :
    contraction w a r v = highestProjection w v + a ^ r • contractionError w a r v := by
  ext i
  by_cases h : w i = 0
  · simp [contraction, highestProjection, contractionError, h]
  · have hw : r * w i = r + r * (w i - 1) := by
      have hi : w i = 1 + (w i - 1) := by omega
      calc
        r * w i = r * (1 + (w i - 1)) := congrArg (r * ·) hi
        _ = r + r * (w i - 1) := by ring
    simp only [contraction, LinearMap.coe_mk, AddHom.coe_mk, highestProjection,
      contractionError, if_neg h, Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_add]
    rw [hw, pow_add, mul_assoc]

/-- The contraction modulo the level is exactly the highest-weight projector. -/
theorem contraction_mod_level (w : ι → ℕ) (p r : ℕ) (v : ι → ℤ) (i : ι) :
    (contraction w p r v i : ZMod (p ^ r)) = (highestProjection w v i : ZMod (p ^ r)) := by
  have h := congrFun (contraction_eq_projection_add w p r v) i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [h]
  simp

/-- Differences with their highest-weight component removed acquire the full level factor. -/
theorem contraction_difference_divisible (w : ι → ℕ) (a : ℤ) (r : ℕ)
    (v u : ι → ℤ) :
    ∃ e : ι → ℤ,
      contraction w a r (v - u) - highestProjection w (v - u) = a ^ r • e := by
  refine ⟨contractionError w a r (v - u), ?_⟩
  rw [contraction_eq_projection_add]
  abel

open GaloisForLFunctions.HTGeometry in
/-- The corpus's symmetric-square action has deficits `0,1,2`. -/
theorem symmetricSquare_contraction (p : ℤ) (r : ℕ) (v : Fin 3 → ℤ) :
    (symmetricSquareMatrix (!![1, 0; 0, p ^ r] : Matrix (Fin 2) (Fin 2) ℤ)).mulVec v =
      contraction Fin.val p r v := by
  funext i
  fin_cases i <;>
    simp [symmetricSquareMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      contraction, pow_mul]

open GaloisForLFunctions.HTGeometry in
/-- Modulo `p^r`, the integral symmetric-square action remembers only the highest coordinate. -/
theorem symmetricSquare_mod_level (p r : ℕ) (v : Fin 3 → ℤ) (i : Fin 3) :
    (((symmetricSquareMatrix (!![1, 0; 0, (p : ℤ) ^ r] :
      Matrix (Fin 2) (Fin 2) ℤ)).mulVec v) i : ZMod (p ^ r)) =
        if i = 0 then (v 0 : ZMod (p ^ r)) else 0 := by
  rw [symmetricSquare_contraction, contraction_mod_level]
  fin_cases i <;> simp [highestProjection]

end

end GaloisForLFunctions.RepresentationLifting.IntegralOrdinary

#print axioms GaloisForLFunctions.RepresentationLifting.IntegralOrdinary.contraction_eq_projection_add
#print axioms GaloisForLFunctions.RepresentationLifting.IntegralOrdinary.symmetricSquare_mod_level

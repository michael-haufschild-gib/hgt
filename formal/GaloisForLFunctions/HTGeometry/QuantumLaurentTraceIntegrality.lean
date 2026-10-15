import GaloisForLFunctions.HTGeometry.SkewLaurentCoefficientTrace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Algebraic quantum Laurent trace integrality

An idempotent over a division ring factors as `E = A * B`, `B * A = 1`
through a finite free module. Every normalized cyclic scalar trace therefore
takes a natural-number value on the matrix idempotent.

Apply this to the explicitly constructed quantum Laurent division ring and
its explicit iterated coefficient trace. The resulting theorem has no
division-ring-existence or trace-existence premise. Finite quantum Laurent
expressions are included in this concrete formal series algebra.

This algebraic integrality theorem does not construct Xi's relative index,
identify a C*-completed canonical trace, or prove the Riemann hypothesis.
-/

open scoped Classical

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Splitting

variable {D : Type*} [DivisionRing D] {n : ℕ}

/-- An idempotent over a division ring factors through a finite free module,
with the reverse product equal to its identity. -/
theorem divisionRing_idempotent_rectangular_factorization
    (E : Matrix (Fin n) (Fin n) D) (hE : E * E = E) :
    ∃ (r : ℕ) (A : Matrix (Fin n) (Fin r) D) (B : Matrix (Fin r) (Fin n) D),
      A * B = E ∧ B * A = 1 := by
  let T : (Fin n → D) →ₗ[D] (Fin n → D) := E.toLinearMapRight'
  have hT : T.comp T = T := by
    change E.toLinearMapRight'.comp E.toLinearMapRight' = E.toLinearMapRight'
    rw [← Matrix.toLinearMapRight'_mul, hE]
  let W := LinearMap.range T
  let r := Module.finrank D W
  let e : W ≃ₗ[D] (Fin r → D) := (Module.finBasis D W).equivFun
  let L : (Fin r → D) →ₗ[D] (Fin n → D) := W.subtype.comp e.symm.toLinearMap
  let R : (Fin n → D) →ₗ[D] (Fin r → D) := e.toLinearMap.comp T.rangeRestrict
  have hfix (w : W) : T w = (w : Fin n → D) := by
    obtain ⟨x, hx⟩ := w.property
    rw [← hx]
    exact DFunLike.congr_fun hT x
  have hLR : L.comp R = T := by
    apply LinearMap.ext
    intro x
    change (e.symm (e (T.rangeRestrict x)) : Fin n → D) = T x
    rw [e.symm_apply_apply]
    rfl
  have hRL : R.comp L = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change e (T.rangeRestrict (e.symm x)) = x
    calc
      e (T.rangeRestrict (e.symm x)) = e (e.symm x) := by
        apply congrArg e
        exact Subtype.ext (hfix (e.symm x))
      _ = x := e.apply_symm_apply x
  refine ⟨r, R.toMatrixRight', L.toMatrixRight', ?_, ?_⟩
  · rw [← LinearMap.toMatrixRight'_comp, hLR]
    exact Matrix.toLinearMapRight'.symm_apply_apply E
  · rw [← LinearMap.toMatrixRight'_comp, hRL, LinearMap.toMatrixRight'_id]

end Splitting

section Trace

variable {D F : Type*} [DivisionRing D] [Field F]

/-- Matrix extension of an additive scalar trace. -/
def divisionRingMatrixTrace {n : ℕ} (τ : D →+ F) (E : Matrix (Fin n) (Fin n) D) : F :=
  ∑ i, τ (E i i)

/-- Cyclicity also holds for the two rectangular products. -/
theorem divisionRingMatrixTrace_mul_comm
    (τ : D →+ F) (hτ : ∀ a b, τ (a * b) = τ (b * a))
    {n r : ℕ} (A : Matrix (Fin n) (Fin r) D) (B : Matrix (Fin r) (Fin n) D) :
    divisionRingMatrixTrace τ (A * B) = divisionRingMatrixTrace τ (B * A) := by
  simp only [divisionRingMatrixTrace, Matrix.mul_apply, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact hτ _ _

/-- A normalized cyclic trace is integer-valued on every division-ring idempotent. -/
theorem divisionRingMatrixTrace_idempotent_eq_nat
    (τ : D →+ F) (hτ : ∀ a b, τ (a * b) = τ (b * a)) (hτ1 : τ 1 = 1)
    {n : ℕ} (E : Matrix (Fin n) (Fin n) D) (hE : E * E = E) :
    ∃ r : ℕ, divisionRingMatrixTrace τ E = r := by
  obtain ⟨r, A, B, hAB, hBA⟩ := divisionRing_idempotent_rectangular_factorization E hE
  refine ⟨r, ?_⟩
  rw [← hAB, divisionRingMatrixTrace_mul_comm τ hτ A B, hBA]
  simp [divisionRingMatrixTrace, hτ1]

end Trace

/-- The explicit quantum Laurent trace is integral on matrix idempotents.
All division-ring and normalized-trace structure is constructed upstream. -/
theorem quantumLaurentTrace_idempotent_eq_nat {F : Type*} [Field F]
    (c : Fˣ) {n : ℕ} (E : Matrix (Fin n) (Fin n) (QuantumLaurentDivisionRing c))
    (hE : E * E = E) :
    ∃ r : ℕ, (∑ i, quantumLaurentTrace c (E i i)) = r :=
  divisionRingMatrixTrace_idempotent_eq_nat (quantumLaurentTrace c)
    (quantumLaurentTrace_cyclic c) (quantumLaurentTrace_one c) E hE

end
end GaloisForLFunctions.HTGeometry

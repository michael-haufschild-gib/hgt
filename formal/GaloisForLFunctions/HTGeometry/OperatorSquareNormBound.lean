import GaloisForLFunctions.HTGeometry.UnitMassWordLeakage

/-!
# Norm bounds give Loewner bounds on squares

A self-adjoint operator of norm at most `M` has `A² ≤ M²`, and a finite family of such operators
has `∑ A_q² ≤ (card) M²`.  This is the upper half of every Casimir window: it needs only the
operator-norm bound on each generator and the number of generators, and no spectral decomposition.
-/

open Finset Matrix
open scoped MatrixOrder ComplexOrder

namespace GaloisForLFunctions.HTGeometry

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The quadratic form of the identity is the squared length. -/
private theorem quadForm_one (v : d → ℂ) : star v ⬝ᵥ ((1 : Matrix d d ℂ) *ᵥ v)
    = ((∑ l, ‖v l‖ ^ 2 : ℝ) : ℂ) := by
  have h := quadForm_conjTranspose_mul_self (1 : Matrix d d ℂ) v
  rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.one_mulVec] at h
  rw [Matrix.one_mulVec]
  exact h

/-- **A norm bound bounds the square in Loewner order.** -/
theorem posSemidef_sq_le_of_bound {A : Matrix d d ℂ} (hA : Aᴴ = A) {M : ℝ}
    (hbound : ∀ v : d → ℂ, ∑ l, ‖(A *ᵥ v) l‖ ^ 2 ≤ M ^ 2 * ∑ l, ‖v l‖ ^ 2) :
    (((M ^ 2 : ℝ) : ℂ) • (1 : Matrix d d ℂ) - A * A).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
  · show (_ : Matrix d d ℂ)ᴴ = _
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Matrix.conjTranspose_mul, hA]
    simp [Complex.conj_ofReal]
  · have hAA : A * A = Aᴴ * A := by rw [hA]
    have hquad : star v ⬝ᵥ ((((M ^ 2 : ℝ) : ℂ) • (1 : Matrix d d ℂ) - A * A) *ᵥ v)
        = ((M ^ 2 * ∑ l, ‖v l‖ ^ 2 - ∑ l, ‖(A *ᵥ v) l‖ ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul,
        quadForm_one, hAA, quadForm_conjTranspose_mul_self]
      push_cast
      ring
    rw [hquad]
    exact Complex.zero_le_real.mpr (by linarith [hbound v])

/-- **A uniformly bounded family has a bounded Casimir.** -/
theorem posSemidef_sum_sq_le_of_bound {ι : Type*} [Fintype ι] {A : ι → Matrix d d ℂ}
    (hA : ∀ q, (A q)ᴴ = A q) {M : ℝ}
    (hbound : ∀ q, ∀ v : d → ℂ, ∑ l, ‖(A q *ᵥ v) l‖ ^ 2 ≤ M ^ 2 * ∑ l, ‖v l‖ ^ 2) :
    (((((Fintype.card ι : ℕ) : ℝ) * M ^ 2 : ℝ) : ℂ) • (1 : Matrix d d ℂ)
      - ∑ q, A q * A q).PosSemidef := by
  classical
  have hc : ((((Fintype.card ι : ℕ) : ℝ) * M ^ 2 : ℝ) : ℂ)
      = ((Fintype.card ι : ℕ) : ℂ) * ((M ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have hsplit : (((((Fintype.card ι : ℕ) : ℝ) * M ^ 2 : ℝ) : ℂ) • (1 : Matrix d d ℂ)
        - ∑ q, A q * A q)
      = ∑ q : ι, (((M ^ 2 : ℝ) : ℂ) • (1 : Matrix d d ℂ) - A q * A q) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hc]
  rw [hsplit]
  refine Finset.sum_induction _ Matrix.PosSemidef (fun x y hx hy => hx.add hy)
    Matrix.PosSemidef.zero fun q _ => ?_
  exact posSemidef_sq_le_of_bound (hA q) (hbound q)

end GaloisForLFunctions.HTGeometry

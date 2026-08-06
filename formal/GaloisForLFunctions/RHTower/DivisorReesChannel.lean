import GaloisForLFunctions.RHTower.DivisorReesBoundaryContraction
import GaloisForLFunctions.RHTower.DivisorReesDehomogenization

/-!
# The graded symbol as a channel

The graded symbol is a symmetric idempotent, so conjugation by it is a map on matrices, not only a
Gram.  That map is the graded radical channel.

Because the symbol is a rank-one projection, the channel has a single effect: it measures the
quadratic form of its Kraus vector and prepares the symbol itself.  So it is completely positive
with one Kraus operator, idempotent, and it sends the whole matrix algebra onto the line spanned by
the symbol.  Conjugating by the divisor twist turns it into the ungraded channel at the divisor
point, which is the map form of the dehomogenization identity.
-/

open scoped BigOperators Matrix Kronecker

open GaloisForLFunctions

namespace RHTower

noncomputable section

/-! ### Conjugation by an outer square -/

variable {n : Type*} [Fintype n]

/-- **Conjugation by an outer square is measure-and-prepare.**  Sandwiching a matrix between two
copies of `v vᵀ` measures the quadratic form of `v` and prepares `v vᵀ`. -/
theorem vecMulVec_mul_mul_vecMulVec (v : n → ℝ) (X : Matrix n n ℝ) :
    Matrix.vecMulVec v v * X * Matrix.vecMulVec v v
      = (v ⬝ᵥ (X *ᵥ v)) • Matrix.vecMulVec v v := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul,
    dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- Conjugation by an idempotent is idempotent as a map. -/
theorem mul_mul_mul_mul_of_idempotent {M : Matrix n n ℝ} (h : M * M = M)
    (X : Matrix n n ℝ) : M * (M * X * M) * M = M * X * M := by
  calc M * (M * X * M) * M = M * M * X * (M * M) := by simp only [mul_assoc]
    _ = M * X * M := by rw [h]

/-! ### The graded channel -/

/-- The graded radical channel at a divisor point of multiplicity `d`: conjugation by the graded
symbol. -/
def gradedDivisorChannel (d : ℕ) (X : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  gradedDivisorProjection d * X * gradedDivisorProjection d

/-- **The graded channel is measure-and-prepare.**  It reads off the quadratic form of the Kraus
vector `(1, d)` and prepares the symbol.  This is the single-effect Stinespring form of the
channel. -/
theorem gradedDivisorChannel_eq_smul (d : ℕ) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    gradedDivisorChannel d X
      = ((gradedDivisorEnergy d)⁻¹ * (![1, (d : ℝ)] ⬝ᵥ (X *ᵥ ![1, (d : ℝ)]))) •
          gradedDivisorProjection d := by
  simp only [gradedDivisorChannel, gradedDivisorProjection, Matrix.smul_mul, Matrix.mul_smul,
    vecMulVec_mul_mul_vecMulVec, smul_smul]
  congr 1
  ring

/-- The graded channel preserves positivity. -/
theorem gradedDivisorChannel_posSemidef (d : ℕ) {X : Matrix (Fin 2) (Fin 2) ℝ}
    (hX : X.PosSemidef) : (gradedDivisorChannel d X).PosSemidef := by
  have h := hX.conjTranspose_mul_mul_same (gradedDivisorProjection d)
  rwa [show (gradedDivisorProjection d)ᴴ = gradedDivisorProjection d from
    gradedDivisorProjection_isSymm d] at h

/-- **The graded channel is completely positive.**  Every ancilla amplification of the symbol is
again a symmetric idempotent, so conjugation by it again preserves positivity. -/
theorem gradedDivisorChannel_completely_positive (d : ℕ) {k : Type*} [Fintype k] [DecidableEq k]
    {X : Matrix (Fin 2 × k) (Fin 2 × k) ℝ} (hX : X.PosSemidef) :
    ((gradedDivisorProjection d ⊗ₖ (1 : Matrix k k ℝ)) * X *
      (gradedDivisorProjection d ⊗ₖ (1 : Matrix k k ℝ))).PosSemidef := by
  have hsymm := isSymm_kronecker_one (k := k) (gradedDivisorProjection_isSymm d)
  have h := hX.conjTranspose_mul_mul_same (gradedDivisorProjection d ⊗ₖ (1 : Matrix k k ℝ))
  rwa [show (gradedDivisorProjection d ⊗ₖ (1 : Matrix k k ℝ))ᴴ
      = gradedDivisorProjection d ⊗ₖ (1 : Matrix k k ℝ) from hsymm] at h

/-- The graded channel is idempotent: it is a conditional expectation onto the line of the
symbol. -/
theorem gradedDivisorChannel_idempotent (d : ℕ) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    gradedDivisorChannel d (gradedDivisorChannel d X) = gradedDivisorChannel d X :=
  mul_mul_mul_mul_of_idempotent (gradedDivisorProjection_idempotent d) X

/-- The graded channel fixes the symbol. -/
theorem gradedDivisorChannel_projection (d : ℕ) :
    gradedDivisorChannel d (gradedDivisorProjection d) = gradedDivisorProjection d := by
  have hP := gradedDivisorProjection_idempotent d
  rw [gradedDivisorChannel, hP, hP]

end

end RHTower

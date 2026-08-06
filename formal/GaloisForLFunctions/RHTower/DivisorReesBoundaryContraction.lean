import GaloisForLFunctions.RHTower.DivisorReesEulerContinuation

/-!
# The boundary symbol is a complete contraction

The assembled boundary symbol is a symmetric idempotent, so it splits every vector orthogonally
into the part it keeps and the part it discards.  The discarded part has nonnegative square, so
the symbol never increases length: it is a contraction.

Amplifying by an ancilla replaces the symbol by its Kronecker product with an identity matrix,
which is again a symmetric idempotent.  So every amplification is a contraction too, and the
boundary symbol is a *complete* contraction — with no bound assumed anywhere, in contrast with the
ordinary ungraded pair, which admits no uniformly bounded positive completion at all.
-/

open scoped BigOperators Matrix Kronecker

open GaloisForLFunctions

namespace RHTower

noncomputable section

/-! ### Symmetric idempotents are contractions -/

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The dot product of a real vector with itself is nonnegative. -/
theorem dotProduct_self_nonneg (x : n → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

omit [DecidableEq n] in
/-- A symmetric idempotent reproduces its own quadratic form: the length it keeps is exactly the
quadratic form it defines. -/
theorem dotProduct_mulVec_self_of_isSymm_idempotent {M : Matrix n n ℝ} (hS : M.IsSymm)
    (hI : M * M = M) (x : n → ℝ) :
    (M *ᵥ x) ⬝ᵥ (M *ᵥ x) = x ⬝ᵥ (M *ᵥ x) := by
  have hMM : M *ᵥ (M *ᵥ x) = M *ᵥ x := by rw [Matrix.mulVec_mulVec, hI]
  calc (M *ᵥ x) ⬝ᵥ (M *ᵥ x)
      = (M *ᵥ (M *ᵥ x)) ⬝ᵥ x := by
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS.eq]
    _ = (M *ᵥ x) ⬝ᵥ x := by rw [hMM]
    _ = x ⬝ᵥ (M *ᵥ x) := dotProduct_comm _ _

omit [DecidableEq n] in
/-- **Orthogonal splitting.**  A symmetric idempotent decomposes the square length of every vector
into the part it keeps and the part it discards. -/
theorem dotProduct_self_eq_add_of_isSymm_idempotent {M : Matrix n n ℝ} (hS : M.IsSymm)
    (hI : M * M = M) (x : n → ℝ) :
    x ⬝ᵥ x = (M *ᵥ x) ⬝ᵥ (M *ᵥ x) + (x - M *ᵥ x) ⬝ᵥ (x - M *ᵥ x) := by
  have hq := dotProduct_mulVec_self_of_isSymm_idempotent hS hI x
  have hc : (M *ᵥ x) ⬝ᵥ x = x ⬝ᵥ (M *ᵥ x) := dotProduct_comm _ _
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hq, hc]
  ring

omit [DecidableEq n] in
/-- **A symmetric idempotent is a contraction.** -/
theorem dotProduct_mulVec_le_of_isSymm_idempotent {M : Matrix n n ℝ} (hS : M.IsSymm)
    (hI : M * M = M) (x : n → ℝ) :
    (M *ᵥ x) ⬝ᵥ (M *ᵥ x) ≤ x ⬝ᵥ x := by
  rw [dotProduct_self_eq_add_of_isSymm_idempotent hS hI x]
  exact le_add_of_nonneg_right (dotProduct_self_nonneg _)

/-! ### Amplifications -/

variable {k : Type*} [Fintype k] [DecidableEq k]

omit [Fintype n] [DecidableEq n] [Fintype k] in
/-- The ancilla amplification of a symmetric idempotent is again a symmetric idempotent. -/
theorem isSymm_kronecker_one {M : Matrix n n ℝ} (hS : M.IsSymm) :
    (M ⊗ₖ (1 : Matrix k k ℝ)).IsSymm := by
  show (M ⊗ₖ (1 : Matrix k k ℝ))ᵀ = _
  rw [show (M ⊗ₖ (1 : Matrix k k ℝ))ᵀ = Mᵀ ⊗ₖ (1 : Matrix k k ℝ)ᵀ from rfl, hS.eq,
    Matrix.transpose_one]

omit [DecidableEq n] in
theorem idempotent_kronecker_one {M : Matrix n n ℝ} (hI : M * M = M) :
    (M ⊗ₖ (1 : Matrix k k ℝ)) * (M ⊗ₖ (1 : Matrix k k ℝ)) = M ⊗ₖ (1 : Matrix k k ℝ) := by
  rw [← Matrix.mul_kronecker_mul, hI, one_mul]

omit [DecidableEq n] in
/-- **A symmetric idempotent is a complete contraction.**  Every ancilla amplification is again a
symmetric idempotent, hence again length-decreasing. -/
theorem dotProduct_mulVec_kronecker_le_of_isSymm_idempotent {M : Matrix n n ℝ} (hS : M.IsSymm)
    (hI : M * M = M) (x : n × k → ℝ) :
    ((M ⊗ₖ (1 : Matrix k k ℝ)) *ᵥ x) ⬝ᵥ ((M ⊗ₖ (1 : Matrix k k ℝ)) *ᵥ x) ≤ x ⬝ᵥ x :=
  dotProduct_mulVec_le_of_isSymm_idempotent (isSymm_kronecker_one hS)
    (idempotent_kronecker_one hI) x

/-! ### The boundary symbol -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graded symbol at one divisor point is positive: it is a nonnegative multiple of the
positive graded Gram. -/
theorem gradedDivisorProjection_posSemidef (d : ℕ) : (gradedDivisorProjection d).PosSemidef := by
  rw [gradedDivisorProjection_eq d one_ne_zero]
  exact posSemidef_smul (gradedDivisorReesGram_posSemidef _ one_ne_zero)
    (inv_nonneg.mpr (gradedDivisorEnergy_pos _).le)

/-- The graded symbol at one divisor point is symmetric. -/
theorem gradedDivisorProjection_isSymm (d : ℕ) : (gradedDivisorProjection d).IsSymm :=
  (gradedDivisorProjection_posSemidef d).1

/-- The assembled boundary symbol is symmetric. -/
theorem xiGradedBoundarySymbol_isSymm (rho : V → ℂ) :
    (xiGradedBoundarySymbol rho).IsSymm :=
  (xiGradedBoundarySymbol_posSemidef rho).1

/-- **The boundary symbol is a contraction.**  No vector grows under it. -/
theorem xiGradedBoundarySymbol_contraction (rho : V → ℂ) (x : Fin 2 × V → ℝ) :
    (xiGradedBoundarySymbol rho *ᵥ x) ⬝ᵥ (xiGradedBoundarySymbol rho *ᵥ x) ≤ x ⬝ᵥ x :=
  dotProduct_mulVec_le_of_isSymm_idempotent (xiGradedBoundarySymbol_isSymm rho)
    (xiGradedBoundarySymbol_idempotent rho) x

/-- **The boundary symbol is a complete contraction.**  Amplifying by any finite ancilla leaves it
length-decreasing, so the graded symbol is completely contractive on the whole Xi boundary graph.
Nothing here is assumed: the ungraded pair admits no uniformly bounded positive completion, and the
grading removes exactly that obstruction. -/
theorem xiGradedBoundarySymbol_completely_contractive (rho : V → ℂ)
    (x : (Fin 2 × V) × k → ℝ) :
    ((xiGradedBoundarySymbol rho ⊗ₖ (1 : Matrix k k ℝ)) *ᵥ x)
        ⬝ᵥ ((xiGradedBoundarySymbol rho ⊗ₖ (1 : Matrix k k ℝ)) *ᵥ x)
      ≤ x ⬝ᵥ x :=
  dotProduct_mulVec_kronecker_le_of_isSymm_idempotent (xiGradedBoundarySymbol_isSymm rho)
    (xiGradedBoundarySymbol_idempotent rho) x

/-- The single graded symbol at one divisor point is a complete contraction as well: it is the
one-vertex case of the boundary graph. -/
theorem gradedDivisorProjection_completely_contractive (d : ℕ) (x : Fin 2 × k → ℝ) :
    ((gradedDivisorProjection d ⊗ₖ (1 : Matrix k k ℝ)) *ᵥ x)
        ⬝ᵥ ((gradedDivisorProjection d ⊗ₖ (1 : Matrix k k ℝ)) *ᵥ x)
      ≤ x ⬝ᵥ x :=
  dotProduct_mulVec_kronecker_le_of_isSymm_idempotent (gradedDivisorProjection_isSymm d)
    (gradedDivisorProjection_idempotent d) x

end

end RHTower

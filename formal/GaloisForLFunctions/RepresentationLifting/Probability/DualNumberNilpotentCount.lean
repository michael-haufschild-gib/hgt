import GaloisForLFunctions.RepresentationLifting.ModularTrace
import GaloisForLFunctions.RepresentationLifting.Probability.NilpotentMatrixCardinality

/-!
# Nilpotence in the square-zero centralizer

An endomorphism commuting with the free square-zero shift has repeated
triangular blocks `[A B; 0 A]`. It is nilpotent exactly when `A` is
nilpotent, with no restriction on `B`. Over a finite field this gives
the same nilpotent proportion as for ordinary square matrices.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting

open OperatorKernels

section Blocks
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Powers preserve the repeated diagonal blocks; the extension block may change. -/
theorem dualNumberBlock_pow (A B : Matrix ι ι R) (m : ℕ) :
    ∃ D : Matrix ι ι R,
      (Matrix.fromBlocks A B 0 A) ^ m = Matrix.fromBlocks (A ^ m) D 0 (A ^ m) := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨D, hD⟩ := ih
    refine ⟨A ^ m * B + D * A, ?_⟩
    rw [pow_succ, hD, Matrix.fromBlocks_multiply]
    simp only [zero_mul, mul_zero, add_zero, zero_add, ← pow_succ]

/-- Nilpotence depends only on the residue block, even when the two blocks do not commute. -/
theorem dualNumberBlock_isNilpotent_iff (A B : Matrix ι ι R) :
    IsNilpotent (Matrix.fromBlocks A B 0 A) ↔ IsNilpotent A := by
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨D, hD⟩ := dualNumberBlock_pow A B m
    refine ⟨m, ?_⟩
    have h := congrArg Matrix.toBlocks₁₁ (hD.symm.trans hm)
    ext i j
    exact congrFun (congrFun h i) j
  · rintro ⟨m, hm⟩
    obtain ⟨D, hD⟩ := dualNumberBlock_pow A B m
    refine ⟨m * 2, ?_⟩
    rw [pow_mul, hD, hm, pow_two, Matrix.fromBlocks_multiply]
    simp only [zero_mul, mul_zero, add_zero, Matrix.fromBlocks_zero]

/-- Matrices commuting with multiplication by the square-zero parameter. -/
abbrev DualNumberCentralizer (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι] :=
  {T : Matrix (ι ⊕ ι) (ι ⊕ ι) R // T * dualNumberShift = dualNumberShift * T}

/-- Nilpotent matrices in the square-zero centralizer. -/
abbrev NilpotentDualNumberCentralizer
    (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι] :=
  {T : Matrix (ι ⊕ ι) (ι ⊕ ι) R //
    T * dualNumberShift = dualNumberShift * T ∧ IsNilpotent T}

/-- The two free matrix blocks parameterize the complete centralizer. -/
def dualNumberCentralizerEquiv :
    (Matrix ι ι R × Matrix ι ι R) ≃ DualNumberCentralizer R ι where
  toFun P := ⟨Matrix.fromBlocks P.1 P.2 0 P.1,
    (commute_dualNumberShift_iff _).mpr ⟨P.1, P.2, rfl⟩⟩
  invFun T := (T.1.toBlocks₁₁, T.1.toBlocks₁₂)
  left_inv P := rfl
  right_inv T := by
    apply Subtype.ext
    change Matrix.fromBlocks T.1.toBlocks₁₁ T.1.toBlocks₁₂ 0 T.1.toBlocks₁₁ = T.1
    obtain ⟨A, B, hT⟩ := (commute_dualNumberShift_iff T.1).mp T.2
    rw [hT]
    rfl

/-- The nilpotent centralizer is one nilpotent residue block and one arbitrary extension block. -/
def nilpotentDualNumberCentralizerEquiv :
    ({A : Matrix ι ι R // IsNilpotent A} × Matrix ι ι R) ≃
      NilpotentDualNumberCentralizer R ι where
  toFun P := ⟨Matrix.fromBlocks P.1.1 P.2 0 P.1.1,
    (commute_dualNumberShift_iff _).mpr ⟨P.1.1, P.2, rfl⟩,
    (dualNumberBlock_isNilpotent_iff _ _).mpr P.1.2⟩
  invFun T := (⟨T.1.toBlocks₁₁, by
    obtain ⟨A, B, hT⟩ := (commute_dualNumberShift_iff T.1).mp T.2.1
    have hnil := T.2.2
    rw [hT, dualNumberBlock_isNilpotent_iff] at hnil
    simpa only [hT, Matrix.toBlocks_fromBlocks₁₁] using hnil⟩, T.1.toBlocks₁₂)
  left_inv P := rfl
  right_inv T := by
    apply Subtype.ext
    change Matrix.fromBlocks T.1.toBlocks₁₁ T.1.toBlocks₁₂ 0 T.1.toBlocks₁₁ = T.1
    obtain ⟨A, B, hT⟩ := (commute_dualNumberShift_iff T.1).mp T.2.1
    rw [hT]
    rfl

end Blocks

variable (K : Type*) [Field K] [Finite K]

omit [Finite K] in
/-- A free dual-number module of rank `n` has `q^(2*n*n)` endomorphisms. -/
theorem card_dualNumberCentralizer (n : ℕ) :
    Nat.card (DualNumberCentralizer K (Fin n)) = Nat.card K ^ (2 * (n * n)) := by
  rw [← Nat.card_congr (dualNumberCentralizerEquiv (R := K) (ι := Fin n)), Nat.card_prod]
  simp only [Matrix, Nat.card_fun, Nat.card_fin, ← pow_mul, ← pow_add]
  congr 1
  ring

/-- The extension block is free, so the nilpotent count acquires exactly `q^(n*n)`. -/
theorem card_nilpotentDualNumberCentralizer (n : ℕ) :
    Nat.card (NilpotentDualNumberCentralizer K (Fin n)) =
      Nat.card K ^ (n * (n - 1) + n * n) := by
  rw [← Nat.card_congr (nilpotentDualNumberCentralizerEquiv (R := K) (ι := Fin n)),
    Nat.card_prod, card_nilpotent_matrices]
  simp only [Matrix, Nat.card_fun, Nat.card_fin, ← pow_mul, ← pow_add]

/-- The nilpotent proportion is `q^(-n)`, unchanged by the square-zero extension. -/
theorem nilpotentDualNumberCentralizer_density (n : ℕ) :
    (Nat.card (NilpotentDualNumberCentralizer K (Fin n)) : ℚ) /
      Nat.card (DualNumberCentralizer K (Fin n)) = 1 / (Nat.card K : ℚ) ^ n := by
  have hq : (Nat.card K : ℚ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := K)).ne'
  have he : 2 * (n * n) = (n * (n - 1) + n * n) + n := by
    cases n with
    | zero => rfl
    | succ n => simp only [Nat.add_sub_cancel]; ring
  rw [card_nilpotentDualNumberCentralizer, card_dualNumberCentralizer,
    Nat.cast_pow, Nat.cast_pow, he]
  simp only [pow_add]
  field_simp

/-- In characteristic two the entire centralizer is traceless, while its nilpotent
fraction remains `q^(-n)`. Scalar trace therefore does not measure nilpotence. -/
theorem dualNumber_modular_trace_nilpotent_density [CharP K 2] (n : ℕ) :
    (∀ T : DualNumberCentralizer K (Fin n), Matrix.trace T.1 = 0) ∧
    (Nat.card (NilpotentDualNumberCentralizer K (Fin n)) : ℚ) /
      Nat.card (DualNumberCentralizer K (Fin n)) = 1 / (Nat.card K : ℚ) ^ n := by
  exact ⟨fun T => dualNumberShift_trace_zero T.1 T.2,
    nilpotentDualNumberCentralizer_density K n⟩

#print axioms dualNumberBlock_isNilpotent_iff
#print axioms nilpotentDualNumberCentralizerEquiv
#print axioms nilpotentDualNumberCentralizer_density
#print axioms dualNumber_modular_trace_nilpotent_density

end GaloisForLFunctions.RepresentationLifting

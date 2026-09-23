import Mathlib
import GaloisForLFunctions.HTGeometry.StokesResistance.MirrorSymmetricResponse

/-!
# Algebraic core of piecewise symmetric tensor splittings

This file formalizes the involutive projection mechanism underlying arXiv:2607.04712,
*Piecewise Symmetric Tensors*.  For any linear involution `σ`, every vector splits uniquely into
its `+1` and `-1` components.  Coordinate tensors inherit the split from any involutive permutation
of their tensor slots.

The final section applies the generic mechanism to the tensor-swap operator already present in the
Stokes-resistance corpus.  It supplies the alternating projection complementary to the existing
`symmetricTensorProjection` and proves the two projectors are mutually annihilating idempotents.
-/

noncomputable section

open scoped BigOperators Kronecker

namespace GaloisForLFunctions.HTGeometry

section Involution

variable {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

/-- Projection onto the fixed part of a linear involution. -/
def involutionSymPart (σ : V →ₗ[𝕜] V) (x : V) : V :=
  (2 : 𝕜)⁻¹ • (x + σ x)

/-- Projection onto the anti-fixed part of a linear involution. -/
def involutionAltPart (σ : V →ₗ[𝕜] V) (x : V) : V :=
  (2 : 𝕜)⁻¹ • (x - σ x)

/-- Symmetric and alternating projections reconstruct the original vector. -/
theorem involution_sym_add_alt (σ : V →ₗ[𝕜] V) (x : V) :
    involutionSymPart σ x + involutionAltPart σ x = x := by
  simp [involutionSymPart, involutionAltPart]
  module

/-- The symmetric projection is fixed by an involution. -/
theorem involutionSymPart_fixed (σ : V →ₗ[𝕜] V)
    (hσ : ∀ x, σ (σ x) = x) (x : V) :
    σ (involutionSymPart σ x) = involutionSymPart σ x := by
  simp [involutionSymPart, hσ]
  module

/-- The alternating projection is negated by an involution. -/
theorem involutionAltPart_antiFixed (σ : V →ₗ[𝕜] V)
    (hσ : ∀ x, σ (σ x) = x) (x : V) :
    σ (involutionAltPart σ x) = -involutionAltPart σ x := by
  simp [involutionAltPart, hσ]
  module

/-- The fixed/anti-fixed decomposition of an involution is unique. -/
theorem involution_split_unique (σ : V →ₗ[𝕜] V)
    {x s a : V} (hx : x = s + a) (hs : σ s = s) (ha : σ a = -a) :
    involutionSymPart σ x = s ∧ involutionAltPart σ x = a := by
  subst x
  constructor <;> simp [involutionSymPart, involutionAltPart, hs, ha] <;> module

/-- Fixed subspace of a linear endomorphism. -/
def involutionFixedSubmodule (σ : V →ₗ[𝕜] V) : Submodule 𝕜 V :=
  LinearMap.ker (σ - LinearMap.id)

/-- Anti-fixed subspace of a linear endomorphism. -/
def involutionAntiFixedSubmodule (σ : V →ₗ[𝕜] V) : Submodule 𝕜 V :=
  LinearMap.ker (σ + LinearMap.id)

omit [CharZero 𝕜] in
/-- Membership in the fixed subspace is the equation `σ x = x`. -/
theorem mem_involutionFixedSubmodule_iff (σ : V →ₗ[𝕜] V) (x : V) :
    x ∈ involutionFixedSubmodule σ ↔ σ x = x := by
  simp [involutionFixedSubmodule, sub_eq_zero]

omit [CharZero 𝕜] in
/-- Membership in the anti-fixed subspace is the equation `σ x = -x`. -/
theorem mem_involutionAntiFixedSubmodule_iff (σ : V →ₗ[𝕜] V) (x : V) :
    x ∈ involutionAntiFixedSubmodule σ ↔ σ x = -x := by
  simp [involutionAntiFixedSubmodule, add_eq_zero_iff_eq_neg]

/-- The fixed and anti-fixed subspaces of an involution are complementary.  This is the abstract
direct-sum content of the piecewise symmetric/piecewise alternating decomposition. -/
theorem involution_fixed_isCompl_antiFixed (σ : V →ₗ[𝕜] V)
    (hσ : ∀ x, σ (σ x) = x) :
    IsCompl (involutionFixedSubmodule σ) (involutionAntiFixedSubmodule σ) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hy
    rw [mem_involutionFixedSubmodule_iff] at hx
    rw [mem_involutionAntiFixedSubmodule_iff] at hy
    have hneg : x = -x := hx.symm.trans hy
    have htwo : x + x = 0 := (eq_neg_iff_add_eq_zero).mp hneg
    have hsmul : (2 : 𝕜) • x = 0 := by simpa [two_smul] using htwo
    exact (smul_eq_zero.mp hsmul).resolve_left (by norm_num)
  · apply codisjoint_iff.mpr
    apply top_unique
    intro x _
    rw [← involution_sym_add_alt σ x]
    exact Submodule.add_mem_sup
      ((mem_involutionFixedSubmodule_iff σ _).mpr (involutionSymPart_fixed σ hσ x))
      ((mem_involutionAntiFixedSubmodule_iff σ _).mpr (involutionAltPart_antiFixed σ hσ x))

end Involution

section Matrices

variable {𝕜 ι : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Symmetric part of a square matrix. -/
def matrixSymPart (A : Matrix ι ι 𝕜) : Matrix ι ι 𝕜 :=
  (2 : 𝕜)⁻¹ • (A + A.transpose)

/-- Skew-symmetric part of a square matrix. -/
def matrixSkewPart (A : Matrix ι ι 𝕜) : Matrix ι ι 𝕜 :=
  (2 : 𝕜)⁻¹ • (A - A.transpose)

/-- Every square matrix is the sum of its symmetric and skew-symmetric parts. -/
theorem matrix_sym_add_skew (A : Matrix ι ι 𝕜) :
    matrixSymPart A + matrixSkewPart A = A := by
  ext i j
  simp [matrixSymPart, matrixSkewPart]
  ring

/-- The symmetric part is fixed by transpose. -/
theorem matrixSymPart_transpose (A : Matrix ι ι 𝕜) :
    (matrixSymPart A).transpose = matrixSymPart A := by
  ext i j
  simp [matrixSymPart, add_comm]
  ring

/-- The skew-symmetric part is negated by transpose. -/
theorem matrixSkewPart_transpose (A : Matrix ι ι 𝕜) :
    (matrixSkewPart A).transpose = -matrixSkewPart A := by
  ext i j
  simp [matrixSkewPart]
  ring

end Matrices

section CoordinateTensors

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- A rank-`k` coordinate tensor with entries in `𝕜` and coordinate type `d`. -/
abbrev CoordinateTensor (𝕜 d : Type*) (k : ℕ) := (Fin k → d) → 𝕜

/-- Permute the slots of a coordinate tensor. -/
def tensorPermute {d : Type*} {k : ℕ} (e : Equiv.Perm (Fin k))
    (t : CoordinateTensor 𝕜 d k) : CoordinateTensor 𝕜 d k :=
  fun w => t (w ∘ e)

/-- Symmetric projection associated to a permutation of tensor slots. -/
def tensorPermutationSymPart {d : Type*} {k : ℕ} (e : Equiv.Perm (Fin k))
    (t : CoordinateTensor 𝕜 d k) : CoordinateTensor 𝕜 d k :=
  fun w => (2 : 𝕜)⁻¹ * (t w + tensorPermute e t w)

/-- Alternating projection associated to a permutation of tensor slots. -/
def tensorPermutationAltPart {d : Type*} {k : ℕ} (e : Equiv.Perm (Fin k))
    (t : CoordinateTensor 𝕜 d k) : CoordinateTensor 𝕜 d k :=
  fun w => (2 : 𝕜)⁻¹ * (t w - tensorPermute e t w)

/-- Permutation-symmetric and permutation-alternating pieces reconstruct a tensor. -/
theorem tensorPermutation_sym_add_alt {d : Type*} {k : ℕ}
    (e : Equiv.Perm (Fin k)) (t : CoordinateTensor 𝕜 d k) :
    tensorPermutationSymPart e t + tensorPermutationAltPart e t = t := by
  funext w
  simp [tensorPermutationSymPart, tensorPermutationAltPart]
  ring

/-- An involutive slot permutation fixes its symmetric tensor component. -/
theorem tensorPermute_symPart_fixed {d : Type*} {k : ℕ}
    (e : Equiv.Perm (Fin k)) (he : ∀ i, e (e i) = i)
    (t : CoordinateTensor 𝕜 d k) :
    tensorPermute e (tensorPermutationSymPart e t) = tensorPermutationSymPart e t := by
  funext w
  simp only [tensorPermute, tensorPermutationSymPart]
  have hw : (w ∘ e) ∘ e = w := by
    funext i
    exact congrArg w (he i)
  rw [hw]
  ring

/-- An involutive slot permutation negates its alternating tensor component. -/
theorem tensorPermute_altPart_antiFixed {d : Type*} {k : ℕ}
    (e : Equiv.Perm (Fin k)) (he : ∀ i, e (e i) = i)
    (t : CoordinateTensor 𝕜 d k) :
    tensorPermute e (tensorPermutationAltPart e t) = -tensorPermutationAltPart e t := by
  funext w
  simp only [tensorPermute, tensorPermutationAltPart, Pi.neg_apply]
  have hw : (w ∘ e) ∘ e = w := by
    funext i
    exact congrArg w (he i)
  rw [hw]
  ring

/-! ### Descent-indexed basis partition from Corollary 2.5 -/

/-- Number of strict descents in a finite list. -/
def listDescentCount {α : Type*} [LT α] [DecidableRel ((· < ·) : α → α → Prop)] :
    List α → ℕ
  | a :: b :: rest => (if b < a then 1 else 0) + listDescentCount (b :: rest)
  | _ => 0

/-- Number of descents in a tensor basis word. -/
def tensorWordDescentCount {d k : ℕ} (w : Fin k → Fin d) : ℕ :=
  listDescentCount (List.ofFn w)

/-- Basis words contributing to the paper's piecewise symmetric summand: fewer than `m`
descents. -/
def piecewiseSymmetricWordIndices (d k m : ℕ) : Finset (Fin k → Fin d) :=
  Finset.univ.filter fun w => tensorWordDescentCount w < m

/-- Complementary basis words contributing to the piecewise alternating summand. -/
def piecewiseAlternatingWordIndices (d k m : ℕ) : Finset (Fin k → Fin d) :=
  Finset.univ.filter fun w => m ≤ tensorWordDescentCount w

/-- The descent-indexed symmetric and alternating basis sets partition all `d ^ k` tensor words.
This is the cardinality backbone of Corollary 2.5. -/
theorem piecewise_wordIndex_card_add (d k m : ℕ) :
    (piecewiseSymmetricWordIndices d k m).card +
        (piecewiseAlternatingWordIndices d k m).card = d ^ k := by
  classical
  rw [piecewiseSymmetricWordIndices, piecewiseAlternatingWordIndices]
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin k → Fin d)))
    (fun w => tensorWordDescentCount w < m)
  rw [show (Finset.univ.filter fun w : Fin k → Fin d => m ≤ tensorWordDescentCount w) =
      Finset.univ.filter fun w => ¬tensorWordDescentCount w < m by
    apply Finset.filter_congr
    intro w _
    exact (not_lt).symm]
  simpa using h

end CoordinateTensors

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry.StokesResistance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Left multiplication by the tensor-swap matrix, as a linear involution. -/
def tensorSwapAction :
    Matrix (ι × ι) (ι × ι) ℂ →ₗ[ℂ] Matrix (ι × ι) (ι × ι) ℂ where
  toFun A := tensorSwap * A
  map_add' A B := by ext p q; simp
  map_smul' c A := by ext p q; simp

/-- Left multiplication by tensor swap is involutive. -/
theorem tensorSwapAction_involutive
    (A : Matrix (ι × ι) (ι × ι) ℂ) :
    tensorSwapAction (ι := ι) (tensorSwapAction (ι := ι) A) = A := by
  change tensorSwap * (tensorSwap * A) = A
  rw [← Matrix.mul_assoc, tensorSwap_mul_self, Matrix.one_mul]

/-- Tensor-swap fixed and anti-fixed matrix spaces are complementary. -/
theorem tensorSwap_fixed_isCompl_antiFixed :
    IsCompl
      (involutionFixedSubmodule (tensorSwapAction (ι := ι)))
      (involutionAntiFixedSubmodule (tensorSwapAction (ι := ι))) :=
  involution_fixed_isCompl_antiFixed tensorSwapAction tensorSwapAction_involutive

/-- Alternating projector complementary to `symmetricTensorProjection`. -/
def alternatingTensorProjection : Matrix (ι × ι) (ι × ι) ℂ :=
  (1 / 2 : ℂ) • (1 - tensorSwap)

/-- Alternating-square dimension formula, expressed as projector trace. -/
theorem trace_alternatingTensorProjection :
    Matrix.trace (alternatingTensorProjection (ι := ι)) =
      ((Fintype.card ι : ℂ) ^ (2 : ℕ) - Fintype.card ι) / 2 := by
  rw [alternatingTensorProjection, Matrix.trace_smul, Matrix.trace_sub,
    Matrix.trace_one, trace_tensorSwap]
  simp [Fintype.card_prod]
  ring

/-- Alternating projection commutes with every doubled action. -/
theorem alternatingTensorProjection_commutes_kronecker_self (M : Matrix ι ι ℂ) :
    alternatingTensorProjection * (M ⊗ₖ M) =
      (M ⊗ₖ M) * alternatingTensorProjection := by
  rw [alternatingTensorProjection, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    tensorSwap_commutes_kronecker_self]

/-- Alternating-square character formula complementary to the corpus symmetric-square formula. -/
theorem trace_alternatingTensorProjection_mul_kronecker_self (M : Matrix ι ι ℂ) :
    Matrix.trace (alternatingTensorProjection * (M ⊗ₖ M)) =
      (Matrix.trace M ^ (2 : ℕ) - Matrix.trace (M * M)) / 2 := by
  rw [alternatingTensorProjection, Matrix.smul_mul, Matrix.sub_mul,
    Matrix.one_mul, Matrix.trace_smul, Matrix.trace_sub,
    Matrix.trace_kronecker, trace_tensorSwap_mul_kronecker_self]
  ring

/-- Generic involution symmetric projection agrees with the corpus matrix projector. -/
theorem involutionSymPart_tensorSwapAction_eq
    (A : Matrix (ι × ι) (ι × ι) ℂ) :
    involutionSymPart (tensorSwapAction (ι := ι)) A = symmetricTensorProjection * A := by
  rw [involutionSymPart, symmetricTensorProjection, Matrix.smul_mul, Matrix.add_mul,
    Matrix.one_mul]
  simp [tensorSwapAction]

/-- Generic involution alternating projection agrees with the complementary corpus projector. -/
theorem involutionAltPart_tensorSwapAction_eq
    (A : Matrix (ι × ι) (ι × ι) ℂ) :
    involutionAltPart (tensorSwapAction (ι := ι)) A = alternatingTensorProjection * A := by
  rw [involutionAltPart, alternatingTensorProjection, Matrix.smul_mul, Matrix.sub_mul,
    Matrix.one_mul]
  simp [tensorSwapAction]

omit [Fintype ι] in
/-- Symmetric and alternating tensor projectors sum to the identity. -/
theorem symmetric_add_alternatingTensorProjection :
    symmetricTensorProjection (ι := ι) + alternatingTensorProjection (ι := ι) = 1 := by
  rw [symmetricTensorProjection, alternatingTensorProjection]
  module

/-- The alternating tensor projector is idempotent. -/
@[simp] theorem alternatingTensorProjection_mul_self :
    (alternatingTensorProjection : Matrix (ι × ι) (ι × ι) ℂ) *
        alternatingTensorProjection = alternatingTensorProjection := by
  rw [alternatingTensorProjection, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, tensorSwap_mul_self]
  module

/-- Symmetric projection followed by alternating projection vanishes. -/
@[simp] theorem symmetric_mul_alternatingTensorProjection :
    (symmetricTensorProjection : Matrix (ι × ι) (ι × ι) ℂ) *
        alternatingTensorProjection = 0 := by
  rw [symmetricTensorProjection, alternatingTensorProjection,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [add_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, tensorSwap_mul_self]
  module

/-- Alternating projection followed by symmetric projection vanishes. -/
@[simp] theorem alternatingTensorProjection_mul_symmetric :
    (alternatingTensorProjection : Matrix (ι × ι) (ι × ι) ℂ) *
        symmetricTensorProjection = 0 := by
  rw [symmetricTensorProjection, alternatingTensorProjection,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [sub_mul, mul_add, Matrix.one_mul, Matrix.mul_one, tensorSwap_mul_self]
  module

/-- Every tensor square splits into its symmetric and alternating components. -/
theorem tensorSquare_symmetric_alternating_decomposition
    (A : Matrix (ι × ι) (ι × ι) ℂ) :
    symmetricTensorProjection * A + alternatingTensorProjection * A = A := by
  rw [← Matrix.add_mul, symmetric_add_alternatingTensorProjection, Matrix.one_mul]

/-- Tensor swap fixes the symmetric component. -/
theorem tensorSwap_symmetric_component
    (A : Matrix (ι × ι) (ι × ι) ℂ) :
    tensorSwap * (symmetricTensorProjection * A) = symmetricTensorProjection * A := by
  rw [← Matrix.mul_assoc]
  congr 1
  rw [symmetricTensorProjection, Matrix.mul_smul]
  simp only [Matrix.mul_add, Matrix.mul_one, tensorSwap_mul_self]
  module

/-- Tensor swap negates the alternating component. -/
theorem tensorSwap_alternating_component
    (A : Matrix (ι × ι) (ι × ι) ℂ) :
    tensorSwap * (alternatingTensorProjection * A) = -(alternatingTensorProjection * A) := by
  calc
    tensorSwap * (alternatingTensorProjection * A) =
        (tensorSwap * alternatingTensorProjection) * A := by rw [Matrix.mul_assoc]
    _ = (-alternatingTensorProjection) * A := by
      congr 1
      rw [alternatingTensorProjection, Matrix.mul_smul]
      simp only [Matrix.mul_sub, Matrix.mul_one, tensorSwap_mul_self]
      module
    _ = -(alternatingTensorProjection * A) := by simp

/-! ### Alternating mirror responses -/

/-- Projection onto alternating response tensors fixed by the mirror `A`. -/
def mirrorAlternatingResponseProjection (A : Matrix ι ι ℂ) :
    Matrix (ι × ι) (ι × ι) ℂ :=
  alternatingTensorProjection *
    ((2 : ℂ)⁻¹ • (1 + (A ⊗ₖ A)))

/-- Alternating and mirror projections combine to an idempotent response projector. -/
theorem mirrorAlternatingResponseProjection_isIdempotent
    (A : Matrix ι ι ℂ) (hA : A * A = 1) :
    IsIdempotentElem (mirrorAlternatingResponseProjection A) := by
  let P : Matrix (ι × ι) (ι × ι) ℂ := alternatingTensorProjection
  let Q : Matrix (ι × ι) (ι × ι) ℂ :=
    (2 : ℂ)⁻¹ • (1 + (A ⊗ₖ A))
  have hP : P * P = P := alternatingTensorProjection_mul_self
  have hQ : Q * Q = Q := (mirrorTensorProjection_isIdempotent A hA).eq
  have hcomm : Q * P = P * Q := by
    dsimp [Q, P]
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one,
      alternatingTensorProjection_commutes_kronecker_self]
  rw [IsIdempotentElem]
  change P * Q * (P * Q) = P * Q
  calc
    P * Q * (P * Q) = P * (Q * P) * Q := by noncomm_ring
    _ = P * (P * Q) * Q := by rw [hcomm]
    _ = (P * P) * (Q * Q) := by noncomm_ring
    _ = P * Q := by rw [hP, hQ]

/-- Symmetric and alternating mirror sectors reconstruct the full mirror-fixed sector. -/
theorem mirrorResponse_symmetric_add_alternating (A : Matrix ι ι ℂ) :
    mirrorSymmetricResponseProjection A + mirrorAlternatingResponseProjection A =
      (2 : ℂ)⁻¹ • (1 + (A ⊗ₖ A)) := by
  rw [mirrorSymmetricResponseProjection, mirrorAlternatingResponseProjection,
    ← Matrix.add_mul, symmetric_add_alternatingTensorProjection, Matrix.one_mul]

/-- Character formula for the alternating mirror-response sector. -/
theorem trace_mirrorAlternatingResponseProjection
    (A : Matrix ι ι ℂ) (hA : A * A = 1) :
    Matrix.trace (mirrorAlternatingResponseProjection A) =
      ((Fintype.card ι : ℂ) ^ (2 : ℕ) - 2 * Fintype.card ι +
        Matrix.trace A ^ (2 : ℕ)) / 4 := by
  rw [mirrorAlternatingResponseProjection, Matrix.mul_smul, Matrix.mul_add,
    Matrix.mul_one, Matrix.trace_smul, Matrix.trace_add,
    trace_alternatingTensorProjection,
    trace_alternatingTensorProjection_mul_kronecker_self, hA,
    Matrix.trace_one]
  ring

end GaloisForLFunctions.HTGeometry.StokesResistance

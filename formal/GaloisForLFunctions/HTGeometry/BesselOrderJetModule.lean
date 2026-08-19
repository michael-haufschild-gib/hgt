import GaloisForLFunctions.HTGeometry.BesselOrderIsomonodromyObstruction
import Mathlib.Data.Matrix.Basic

/-!
# The Bessel order module carries no connection: matrix form

A difference system `σY = A Y` prolongs to its first jet system `σ Ỹ = Ã Ỹ` with
`Ã = [[A, δA], [0, A]]`, because `σ(δY) = (δA) Y + A (δY)`.  The jet system is gauge equivalent to
the split system `[[A,0],[0,A]]` by a block-unipotent gauge exactly when
`σ(B) A - A B = -δA` has a solution `B` over the base — the isomonodromy datum.

For the Bessel order companion `A = [[0,1],[1,c(ν+1)]]` no such `B` exists: the four entrywise
identities reduce to the two scalar compatibility identities that the degree count at infinity
refutes.  So the first jet module of the Bessel order module is a non-split self-extension.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-! ### The jet prolongation and its splitting -/

/-- The first jet system of a difference system. -/
def jetMatrix {K : Type*} [CommRing K] {n : Type*} [Fintype n] [DecidableEq n]
    (A dA : Matrix n n K) : Matrix (n ⊕ n) (n ⊕ n) K :=
  Matrix.fromBlocks A dA 0 A

/-- A block-unipotent gauge transformation. -/
def blockUnipotent {K : Type*} [CommRing K] {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n K) : Matrix (n ⊕ n) (n ⊕ n) K :=
  Matrix.fromBlocks 1 B 0 1

/-- **The jet system splits under a block-unipotent gauge exactly when the connection equation is
solvable.** -/
theorem jetMatrix_gauge_split_iff {K : Type*} [CommRing K] {n : Type*} [Fintype n] [DecidableEq n]
    (σ : K →+* K) (A dA B : Matrix n n K) :
    (blockUnipotent B).map σ * jetMatrix A dA = jetMatrix A 0 * blockUnipotent B
      ↔ B.map σ * A - A * B = -dA := by
  have hmapT : (blockUnipotent B).map σ = Matrix.fromBlocks 1 (B.map σ) 0 1 := by
    rw [blockUnipotent, Matrix.fromBlocks_map]
    simp
  have hblock : ((blockUnipotent B).map σ * jetMatrix A dA = jetMatrix A 0 * blockUnipotent B)
      ↔ (dA + B.map σ * A = A * B) := by
    rw [hmapT, jetMatrix, jetMatrix, blockUnipotent, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.fromBlocks_inj, and_true, true_and, and_self]
  rw [hblock]
  constructor
  · intro h
    rw [sub_eq_iff_eq_add, ← h]
    abel
  · intro h
    rw [sub_eq_iff_eq_add.mp h]
    abel

/-! ### The Bessel order companion -/

/-- The companion matrix of the Bessel order recurrence. -/
def besselOrderCompanion (c : ℂ) : Matrix (Fin 2) (Fin 2) (RatFunc ℂ) :=
  !![0, 1; 1, orderShiftCoeff c]

/-- Its entrywise derivative. -/
def besselOrderCompanionDeriv (c : ℂ) : Matrix (Fin 2) (Fin 2) (RatFunc ℂ) :=
  !![0, 0; 0, algebraMap ℂ (RatFunc ℂ) c]

/-- **The Bessel order module carries no rational connection.** -/
theorem besselOrder_no_matrix_delta_structure {c : ℂ} (hc : c ≠ 0)
    (B : Matrix (Fin 2) (Fin 2) (RatFunc ℂ))
    (hB : B.map ratShift * besselOrderCompanion c - besselOrderCompanion c * B
      = besselOrderCompanionDeriv c) : False := by
  have hentry : ∀ i j : Fin 2,
      (B.map ratShift * besselOrderCompanion c - besselOrderCompanion c * B) i j
        = besselOrderCompanionDeriv c i j := fun i j => by rw [hB]
  have h00 := hentry 0 0
  have h01 := hentry 0 1
  have h10 := hentry 1 0
  have h11 := hentry 1 1
  simp [besselOrderCompanion, besselOrderCompanionDeriv, Matrix.sub_apply,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.vecMul, dotProduct]
    at h00 h01 h10 h11
  have hr : ratShift (B 0 1) = B 1 0 := by linear_combination h00
  have ht : ratShift (B 0 0) + orderShiftCoeff c * ratShift (B 0 1) = B 1 1 := by
    linear_combination h01
  have h3 : ratShift (B 1 1) = B 0 0 + orderShiftCoeff c * B 1 0 := by linear_combination h10
  have hCeq : algebraMap ℂ (RatFunc ℂ) c = RatFunc.C c := rfl
  have h4 : ratShift (B 1 0) + orderShiftCoeff c * ratShift (B 1 1) - B 0 1
      - orderShiftCoeff c * B 1 1 = algebraMap ℂ (RatFunc ℂ) c := by
    rw [hCeq]; linear_combination h11
  rw [← hr, ← ht] at h3 h4
  simp only [map_add, map_mul] at h3 h4
  exact besselOrder_no_rational_delta_structure hc (B 0 0) (B 0 1)
    (by linear_combination h3) (by linear_combination h4)

end

end GaloisForLFunctions.HTGeometry

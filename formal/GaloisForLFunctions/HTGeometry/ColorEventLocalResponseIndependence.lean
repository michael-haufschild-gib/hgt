import GaloisForLFunctions.HTGeometry.ColorGramMinkowskiCone

/-!
# Local causal and internal responses of a colour event are independent

For an isometric complex event matrix `X`, every square matrix is the cross-comparison
`Xᴴ * Y` of `X` with the column-aligned variation `Y = X * A`. Splitting that comparison into
its Hermitian and skew-Hermitian parts therefore imposes no relation between the two parts.

This file proves the exact finite-dimensional no-go:

* Hermitian and skew-Hermitian parts reconstruct the full comparison;
* equality of both parts is equivalent to equality of comparisons;
* any prescribed Hermitian matrix `H` and skew-Hermitian matrix `K` occur simultaneously;
* in particular, this holds for the `3 × 2` colour-event carrier.

The result is standard matrix algebra. Its physical use is negative: a common local carrier
cannot by itself derive a gravity--gauge coupling law. Nothing here identifies the Hermitian
response with spacetime, the skew-Hermitian response with gauge force, or event succession with
dynamics.
-/

open Matrix
open scoped Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Hermitian half of a complex square-matrix comparison. -/
def localHermitianResponse {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 : ℂ)⁻¹ • (A + Aᴴ)

/-- Skew-Hermitian half of a complex square-matrix comparison. -/
def localSkewHermitianResponse {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 : ℂ)⁻¹ • (A - Aᴴ)

/-- Hermitian and skew-Hermitian local responses reconstruct the full comparison. -/
theorem localHermitianResponse_add_localSkewHermitianResponse
    {n : Type*} [Fintype n] (A : Matrix n n ℂ) :
    localHermitianResponse A + localSkewHermitianResponse A = A := by
  ext i j
  simp [localHermitianResponse, localSkewHermitianResponse]
  ring

/-- Two comparisons are equal exactly when both of their local responses are equal. -/
theorem localResponses_eq_iff
    {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    localHermitianResponse A = localHermitianResponse B ∧
        localSkewHermitianResponse A = localSkewHermitianResponse B ↔
      A = B := by
  constructor
  · rintro ⟨hHermitian, hSkew⟩
    calc
      A = localHermitianResponse A + localSkewHermitianResponse A := by
        symm
        exact localHermitianResponse_add_localSkewHermitianResponse A
      _ = localHermitianResponse B + localSkewHermitianResponse B := by
        rw [hHermitian, hSkew]
      _ = B := localHermitianResponse_add_localSkewHermitianResponse B
  · rintro rfl
    exact ⟨rfl, rfl⟩

/-- An isometric event realizes any prescribed Hermitian and skew-Hermitian response pair.

The explicit variation is `X * (H + K)`. Thus the local response reporter is surjective, with no
compatibility condition between `H` and `K` beyond their separate adjoint symmetries.
-/
theorem isometricEvent_prescribes_local_responses
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℂ) (hX : Xᴴ * X = 1)
    (H K : Matrix n n ℂ) (hH : Hᴴ = H) (hK : Kᴴ = -K) :
    localHermitianResponse (Xᴴ * (X * (H + K))) = H ∧
      localSkewHermitianResponse (Xᴴ * (X * (H + K))) = K := by
  have hcross : Xᴴ * (X * (H + K)) = H + K := by
    rw [← Matrix.mul_assoc, hX, one_mul]
  rw [hcross]
  constructor
  · rw [localHermitianResponse, Matrix.conjTranspose_add, hH, hK]
    ext i j
    simp
    ring
  · rw [localSkewHermitianResponse, Matrix.conjTranspose_add, hH, hK]
    ext i j
    simp
    ring

/-- Every Hermitian/skew response pair occurs at an isometric `3 × 2` colour event. -/
theorem colorEvent_prescribes_local_responses
    (X : ColorEventMatrix) (hX : Xᴴ * X = 1)
    (H K : Matrix (Fin 2) (Fin 2) ℂ) (hH : Hᴴ = H) (hK : Kᴴ = -K) :
    ∃ Y : ColorEventMatrix,
      localHermitianResponse (Xᴴ * Y) = H ∧
        localSkewHermitianResponse (Xᴴ * Y) = K := by
  refine ⟨X * (H + K), ?_⟩
  exact isometricEvent_prescribes_local_responses X hX H K hH hK

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.RHTower.SourceHorizontalHolomorphicPrimeLogZeroCondensation

/-!
# Finite matrix equivalence cannot repair the SC determinant

The coefficient-faithful holomorphic SC packet admits a literal matrix realization.  Its universal
reservoir factor is `I - 𝟙𝟙ᵀ`, while its prime-labelled columns carry the entire signed
Gamma-Bocksteins.  Sylvester's identity computes the reservoir determinant as `1 - n`, so this
matrix has exactly the previously constructed SC packet determinant.

This exposes a sharp operator-level obstruction.  Arbitrary packet-dependent left and right
matrix factors may mix every prime coordinate and may themselves be singular, but determinant
multiplicativity only multiplies the SC determinant by their two determinants.  Consequently the
noncentral prime-log zeros still condense at the origin, and local uniform convergence to
normalized centered Xi remains impossible.

The surviving coupling is therefore genuinely additive or otherwise non-equivalent before
determinant formation, or meromorphically singular at the moving noncentral prime-log points.
No RH assumption or spectral-location input is used.
-/

open Complex Filter Topology Set
open scoped BigOperators Matrix

namespace RHTower

noncomputable section

/-- Universal all-one reservoir column over `ℂ`. -/
def holomorphicReservoirColumn (n : ℕ) : Matrix (Fin n) (Fin 1) ℂ :=
  fun _ _ => 1

/-- Universal all-one reservoir row over `ℂ`. -/
def holomorphicReservoirRow (n : ℕ) : Matrix (Fin 1) (Fin n) ℂ :=
  fun _ _ => 1

/-- Universal complex reservoir matrix `I - 𝟙𝟙ᵀ`. -/
def holomorphicReservoirBaseMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  1 - holomorphicReservoirColumn n * holomorphicReservoirRow n

/-- The complex universal reservoir determinant is exactly `1 - n`. -/
theorem holomorphicReservoirBaseMatrix_det (n : ℕ) :
    (holomorphicReservoirBaseMatrix n).det = (1 : ℂ) - (n : ℂ) := by
  rw [holomorphicReservoirBaseMatrix, Matrix.det_one_sub_mul_comm]
  have hmatrix :
      (1 - holomorphicReservoirRow n * holomorphicReservoirColumn n :
          Matrix (Fin 1) (Fin 1) ℂ) =
        !![(1 - n : ℂ)] := by
    ext i j
    fin_cases i
    fin_cases j
    simp [holomorphicReservoirRow, holomorphicReservoirColumn, Matrix.mul_apply]
  rw [hmatrix]
  simp

/-- Literal coefficient-faithful holomorphic SC reservoir matrix.  Column `i` carries the entire
signed Bockstein of the `i`th ordinary prime. -/
def preDivisorRiggedPrimeHolomorphicReservoirMatrix
    (m : ℕ) (z : ℂ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ :=
  holomorphicReservoirBaseMatrix (m + 2) * Matrix.diagonal
    (fun i : Fin (m + 2) =>
      preDivisorHolomorphicPrimeBockstein z (nthPrimePoint i))

/-- Exact matrix realization: its determinant is the coefficient-faithful holomorphic SC packet. -/
theorem preDivisorRiggedPrimeHolomorphicReservoirMatrix_det
    (m : ℕ) (z : ℂ) :
    (preDivisorRiggedPrimeHolomorphicReservoirMatrix m z).det =
      preDivisorRiggedPrimeHolomorphicPacket m z := by
  rw [preDivisorRiggedPrimeHolomorphicReservoirMatrix, Matrix.det_mul,
    holomorphicReservoirBaseMatrix_det, Matrix.det_diagonal]
  unfold preDivisorRiggedPrimeHolomorphicPacket
  push_cast
  rfl

/-- Determinant after arbitrary finite left/right packet-dependent cross-prime matrix mixing. -/
def preDivisorRiggedPrimeHolomorphicMatrixCoupledDeterminant
    (A B : (m : ℕ) → ℂ → Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)
    (m : ℕ) (z : ℂ) : ℂ :=
  (A m z * preDivisorRiggedPrimeHolomorphicReservoirMatrix m z * B m z).det

/-- Every finite left/right matrix coupling remains a scalar determinant factorization of the
original holomorphic SC packet.  Dense cross-prime entries and singular factors are allowed. -/
theorem preDivisorRiggedPrimeHolomorphicMatrixCoupledDeterminant_eq
    (A B : (m : ℕ) → ℂ → Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)
    (m : ℕ) (z : ℂ) :
    preDivisorRiggedPrimeHolomorphicMatrixCoupledDeterminant A B m z =
      (A m z).det * (B m z).det *
        preDivisorRiggedPrimeHolomorphicPacket m z := by
  rw [preDivisorRiggedPrimeHolomorphicMatrixCoupledDeterminant,
    Matrix.det_mul, Matrix.det_mul,
    preDivisorRiggedPrimeHolomorphicReservoirMatrix_det]
  ring

/-- **Finite cross-prime matrix-equivalence no-go.**  No packet-dependent finite-valued left/right
matrix coupling of the exact holomorphic SC reservoir can have determinants converging locally
uniformly to normalized centered Xi.  This rules out every finite basis change, preconditioner,
and multiplicative cross-prime mixing, without invertibility or regularity hypotheses on the
coupling matrices.

The missing Xi landing must change the matrix pencil additively/non-equivalently before taking its
determinant, or introduce meromorphic singularities at the condensing noncentral prime-log zeros. -/
theorem not_tendstoLocallyUniformly_normalizedXiC_of_holomorphicMatrixCoupling
    (A B : (m : ℕ) → ℂ → Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) :
    ¬ TendstoLocallyUniformly
      (preDivisorRiggedPrimeHolomorphicMatrixCoupledDeterminant A B)
      (fun z => XiC z / XiC 0) atTop := by
  apply not_tendstoLocallyUniformly_normalizedXiC_of_holomorphicPacket_scalarFactor
    (preDivisorRiggedPrimeHolomorphicMatrixCoupledDeterminant A B)
    (fun m z => (A m z).det * (B m z).det)
  intro m z _
  exact preDivisorRiggedPrimeHolomorphicMatrixCoupledDeterminant_eq A B m z

end
end RHTower

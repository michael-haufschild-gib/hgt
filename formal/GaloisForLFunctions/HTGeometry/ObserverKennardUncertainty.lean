import GaloisForLFunctions.HTGeometry.MatrixMechanicsKennard
import GaloisForLFunctions.HTGeometry.ObserverTriangleInequality

/-!
# Kennard uncertainty for observer-frame spectral matrices

Real spectra transported into complex frames are Hermitian observables. Their existing observer
matrix representation therefore inherits finite matrix Kennard uncertainty without extra premises.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Matrix

/-- A real diagonal spectrum transported by a complex frame, packaged as an observable. -/
def observerFrameObservable {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℝ) : HermitianObservable (Fin n) where
  matrix := Uᴴ * rdiag w * U
  hermitian := isHermitian_conj_rdiag U w

/-- Kennard uncertainty between two observer-frame spectral matrices. -/
theorem observerFrame_kennard {n : ℕ} (ψ : MatrixMechanicsState (Fin n))
    (U V : Matrix (Fin n) (Fin n) ℂ) (w v : Fin n → ℝ) :
    (QuantumAlg.expval ψ.vector
      ((Uᴴ * rdiag w * U) * (Vᴴ * rdiag v * V) -
        (Vᴴ * rdiag v * V) * (Uᴴ * rdiag w * U))).im ^ 2 ≤
      4 * QuantumAlg.qCov ψ.vector (Uᴴ * rdiag w * U) (Uᴴ * rdiag w * U) *
        QuantumAlg.qCov ψ.vector (Vᴴ * rdiag v * V) (Vᴴ * rdiag v * V) :=
  matrixMechanics_kennard ψ (observerFrameObservable U w) (observerFrameObservable V v)

end

end GaloisForLFunctions.HTGeometry

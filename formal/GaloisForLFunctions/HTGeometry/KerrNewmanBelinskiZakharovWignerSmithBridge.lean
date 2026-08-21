import GaloisForLFunctions.HTGeometry.KerrNewmanBelinskiZakharovBridge
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances
import GaloisForLFunctions.HTGeometry.WignerSmithTraceDeterminant

/-!
# Belinski--Zakharov spectral dressing and the Wigner--Smith central clock

The finite real model of `KerrNewmanBelinskiZakharovBridge` records a one-pole unipotent BZ
dressing.  This file places that same nilpotent one-pole shape over the rational spectral field
`ℂ(λ)`.  Its determinant is identically one, hence Jacobi's formula makes the trace of every
algebraic Wigner--Smith observable exactly zero.

This is an algebraic spectral-coordinate statement only.  It does not assert a physical
frequency-domain scattering construction or asymptotic boundary conditions for Kerr--Newman.
-/

open scoped Differential UnivMeroFieldInstances
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Complexified one-pole BZ dressing over the rational spectral coordinate `λ`.  It is identity
plus the canonical rank-one nilpotent residue times `(λ - pole)⁻¹`. -/
def belinskiZakharovOnePoleSpectralDressing
    (pole residue : ℂ) : Matrix (Fin 2) (Fin 2) (RatFunc ℂ) :=
  !![1, algebraMap ℂ (RatFunc ℂ) residue /
      (RatFunc.X - algebraMap ℂ (RatFunc ℂ) pole); 0, 1]

/-- The complex spectral BZ one-pole dressing is unimodular identically in the spectral
coordinate. -/
theorem belinskiZakharovOnePoleSpectralDressing_det
    (pole residue : ℂ) :
    (belinskiZakharovOnePoleSpectralDressing pole residue).det = 1 := by
  simp [belinskiZakharovOnePoleSpectralDressing, Matrix.det_fin_two]

/-- **Central-clock decoupling.**  Every algebraic Wigner--Smith coupling sees zero trace on the
unipotent BZ one-pole dressing.  Thus its spectral dynamics are entirely relative-channel data. -/
theorem trace_matrixWignerSmith_belinskiZakharovOnePoleSpectralDressing
    (ι pole residue : ℂ) :
    Matrix.trace (matrixWignerSmith ι
      (belinskiZakharovOnePoleSpectralDressing pole residue)) = 0 := by
  have hdet : IsUnit (belinskiZakharovOnePoleSpectralDressing pole residue).det := by
    rw [belinskiZakharovOnePoleSpectralDressing_det]
    exact isUnit_one
  rw [trace_matrixWignerSmith ι
    (belinskiZakharovOnePoleSpectralDressing pole residue) hdet]
  rw [belinskiZakharovOnePoleSpectralDressing_det]
  simp

end

end GaloisForLFunctions.HTGeometry

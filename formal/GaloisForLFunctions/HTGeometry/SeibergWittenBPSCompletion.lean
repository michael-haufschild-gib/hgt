import GaloisForLFunctions.HTGeometry.SeibergWittenAbelianSpinor
import GaloisForLFunctions.HTGeometry.BogomolnyPrasadSommerfieldBounds

/-!
# BPS completion of the finite Seiberg--Witten curvature equation

The existing BPS corpus packages an energy as a charge plus a non-negative defect.  This module
applies that pattern to the finite Abelian spinor--curvature equation: the energy is the squared
Hilbert-coordinate residual of `F = q(ψ)`, its charge is zero, and saturation is exactly that
equation.  The coordinate Hilbert norm is used because the existing matrix carrier has no norm
instance.

This is a finite pointwise completion of the square, not a Bogomolny monopole or a continuum
Seiberg--Witten functional.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Squared Hilbert-coordinate residual of the finite curvature equation. -/
def seibergWittenBPSEnergy
    (F : SeibergWittenCurvature) (psi : SeibergWittenSpinor) : ℝ :=
  ‖(EuclideanSpace.equiv (Fin 2 × Fin 2) ℂ).symm
    (fun ij => (F - seibergWittenQuadraticMap psi) ij.1 ij.2)‖ ^ (2 : ℕ)

/-- Topological-charge term of this residual completion; it is zero in the finite pointwise model. -/
def seibergWittenBPSCharge
    (_F : SeibergWittenCurvature) (_psi : SeibergWittenSpinor) : ℝ := 0

/-- Non-negative residual defect in the finite BPS decomposition. -/
def seibergWittenBPSDefect
    (F : SeibergWittenCurvature) (psi : SeibergWittenSpinor) : ℝ :=
  seibergWittenBPSEnergy F psi

/-- Exact energy--charge--defect decomposition for the finite curvature equation. -/
theorem seibergWittenBPSEnergy_eq_charge_add_defect
    (F : SeibergWittenCurvature) (psi : SeibergWittenSpinor) :
    seibergWittenBPSEnergy F psi =
      seibergWittenBPSCharge F psi + seibergWittenBPSDefect F psi := by
  simp [seibergWittenBPSCharge, seibergWittenBPSDefect]

/-- The finite residual defect is non-negative. -/
theorem seibergWittenBPSDefect_nonneg
    (F : SeibergWittenCurvature) (psi : SeibergWittenSpinor) :
    0 ≤ seibergWittenBPSDefect F psi :=
  sq_nonneg _

/-- The zero charge is a lower bound for the finite residual energy. -/
theorem seibergWittenBPSCharge_le_energy
    (F : SeibergWittenCurvature) (psi : SeibergWittenSpinor) :
    seibergWittenBPSCharge F psi ≤ seibergWittenBPSEnergy F psi := by
  simpa [seibergWittenBPSCharge, seibergWittenBPSDefect] using
    seibergWittenBPSDefect_nonneg F psi

/-- BPS saturation is exactly the finite Seiberg--Witten curvature equation. -/
theorem seibergWittenBPSSaturation_iff
    (F : SeibergWittenCurvature) (psi : SeibergWittenSpinor) :
    seibergWittenBPSEnergy F psi = seibergWittenBPSCharge F psi ↔
      seibergWittenEquation F psi := by
  change ‖(EuclideanSpace.equiv (Fin 2 × Fin 2) ℂ).symm
      (fun ij => (F - seibergWittenQuadraticMap psi) ij.1 ij.2)‖ ^ (2 : ℕ) = 0 ↔
    F = seibergWittenQuadraticMap psi
  constructor
  · intro h
    have hnorm : (EuclideanSpace.equiv (Fin 2 × Fin 2) ℂ).symm
        (fun ij => (F - seibergWittenQuadraticMap psi) ij.1 ij.2) = 0 :=
      norm_eq_zero.mp (sq_eq_zero_iff.mp h)
    have hentries : (fun ij : Fin 2 × Fin 2 =>
        (F - seibergWittenQuadraticMap psi) ij.1 ij.2) = 0 := by
      simpa using congrArg (EuclideanSpace.equiv (Fin 2 × Fin 2) ℂ) hnorm
    ext i j
    exact sub_eq_zero.mp (by simpa using congrFun hentries (i, j))
  · intro h
    rw [h, sub_self]
    change ‖(EuclideanSpace.equiv (Fin 2 × Fin 2) ℂ).symm
      (0 : Fin 2 × Fin 2 → ℂ)‖ ^ (2 : ℕ) = 0
    simp

/-- The finite BPS energy is invariant under the existing common `U(1)` phase action. -/
theorem seibergWittenBPSEnergy_gaugeInvariant
    (u : Circle) (F : SeibergWittenCurvature) (psi : SeibergWittenSpinor) :
    seibergWittenBPSEnergy F (u • psi) = seibergWittenBPSEnergy F psi := by
  unfold seibergWittenBPSEnergy
  rw [seibergWittenQuadraticMap_gaugeInvariant u psi]

/-- The pointwise BPS energy is constant along every finite Seiberg--Witten gauge flow. -/
theorem seibergWittenGaugeFlow_bpsEnergyInvariant
    (phase : ℝ → Circle) (t : ℝ) (F : SeibergWittenCurvature) (psi : SeibergWittenSpinor) :
    seibergWittenBPSEnergy F (seibergWittenGaugeFlow phase psi t) =
      seibergWittenBPSEnergy F psi := by
  simpa [seibergWittenGaugeFlow] using
    seibergWittenBPSEnergy_gaugeInvariant (phase t) F psi

/-- The induced finite curvature always BPS-saturates. -/
theorem seibergWittenInducedCurvature_bpsSaturates (psi : SeibergWittenSpinor) :
    seibergWittenBPSEnergy (seibergWittenQuadraticMap psi) psi =
      seibergWittenBPSCharge (seibergWittenQuadraticMap psi) psi :=
  (seibergWittenBPSSaturation_iff (seibergWittenQuadraticMap psi) psi).mpr
    (seibergWittenEquation_inducedCurvature psi)

end GaloisForLFunctions.HTGeometry

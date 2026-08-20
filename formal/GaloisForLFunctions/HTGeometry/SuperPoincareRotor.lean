import GaloisForLFunctions.HTGeometry.SuperPoincareAlgebra
import GaloisForLFunctions.HTGeometry.MarkedHalfCharacterCompactActionLaw

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Winding parity is an involution on the algebraic rotor core. -/
theorem rotorParityCore_sq :
    rotorParityCore * rotorParityCore = 1 := by
  apply Finsupp.lhom_ext
  intro k z
  have hsingle : Finsupp.single k z = z • rotorKet k := by
    ext j
    simp [rotorKet]
  rw [hsingle]
  simp only [map_smul, rotorParityCore_ket, smul_smul,
    Module.End.mul_apply]
  change
    (z * (((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k))) • rotorKet k =
      z • rotorKet k
  have hsq : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    exact (show Even (k + k) from ⟨k, rfl⟩).neg_one_zpow
  rw [hsq, mul_one]

/-- Winding parity anticommutes with bilateral winding shift. -/
theorem rotorParityCore_mul_shift_eq_neg :
    rotorParityCore * rotorShiftCore = -(rotorShiftCore * rotorParityCore) := by
  have h := congrArg
    (fun T : Module.End ℂ RotorCore => T * rotorParityCore)
    rotorParity_shift_anticommutation
  change
    (rotorParityCore * (rotorShiftCore * rotorParityCore)) * rotorParityCore =
      (-rotorShiftCore) * rotorParityCore at h
  calc
    rotorParityCore * rotorShiftCore =
        rotorParityCore * rotorShiftCore *
          (rotorParityCore * rotorParityCore) := by
            rw [rotorParityCore_sq, mul_one]
    _ = (rotorParityCore * (rotorShiftCore * rotorParityCore)) *
        rotorParityCore := by simp only [mul_assoc]
    _ = (-rotorShiftCore) * rotorParityCore := h
    _ = -(rotorShiftCore * rotorParityCore) := by rfl

/-- Rotor winding parity and bilateral shift form a split supertranslation sector. -/
def rotorParityShiftD1N2Split :
    SuperPoincare.D1N2Split (Module.End ℂ RotorCore) :=
  SuperPoincare.D1N2Split.ofEqNeg
    rotorParityCore rotorShiftCore rotorParityCore_mul_shift_eq_neg

/-- Rotor parity generates identity momentum. -/
theorem rotorParityShift_momentum0_eq_one :
    rotorParityShiftD1N2Split.momentum0 = 1 :=
  rotorParityCore_sq

end GaloisForLFunctions.HTGeometry

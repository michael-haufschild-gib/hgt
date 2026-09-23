import GaloisForLFunctions.HTGeometry.KerrNewmanBelinskiZakharovBridge
import GaloisForLFunctions.HTGeometry.ConfocalEnvelopeHull

/-!
# Belinski--Zakharov dressing and the confocal Lorentz cone

At the designated flat Kerr--Newman point, the stationary two-Killing block is the two-dimensional
Minkowski form.  Its nonpositive quadratic cone is exactly the existing confocal Lorentz cone after
recording the absolute time coordinate.  A BZ congruence transports this cone through the
transpose of its dressing matrix.  This is a causal-cone transport identity, not a claim that every
dressing preserves a fixed causal cone or that it solves the reduced Einstein--Maxwell system.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Matrix

/-- Record a two-Killing vector as a confocal Lorentz coordinate: axial direction and absolute
stationary-time coordinate. -/
def belinskiZakharovConfocalLift (v : Fin 2 → ℝ) : ℝ × ℝ := (v 1, |v 0|)

/-- The flat Kerr--Newman Killing block is the two-dimensional Minkowski matrix. -/
theorem belinskiZakharov_flatKillingBlock :
    kerrNewmanKillingBlock 0 0 0 1 (Real.pi / 2) = !![-1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [kerrNewmanKillingBlock, kerrNewmanSigma, kerrNewmanDelta]

/-- The flat Killing quadratic form is space squared minus time squared. -/
theorem belinskiZakharovKillingQuadratic_flat (v : Fin 2 → ℝ) :
    belinskiZakharovKillingQuadratic !![-1, 0; 0, 1] v = v 1 ^ (2 : ℕ) - v 0 ^ (2 : ℕ) := by
  simp [belinskiZakharovKillingQuadratic, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- The flat Kerr--Newman nonpositive Killing cone is exactly the confocal Lorentz cone. -/
theorem belinskiZakharovFlatKillingCone_iff (v : Fin 2 → ℝ) :
    belinskiZakharovConfocalLift v ∈ _root_.HTGeometry.confocalLorentzCone ↔
      belinskiZakharovKillingQuadratic
        (kerrNewmanKillingBlock 0 0 0 1 (Real.pi / 2)) v ≤ 0 := by
  rw [belinskiZakharov_flatKillingBlock, belinskiZakharovKillingQuadratic_flat]
  change |v 1| ≤ |v 0| ↔ v 1 ^ (2 : ℕ) - v 0 ^ (2 : ℕ) ≤ 0
  constructor
  · intro h
    have htime : 0 ≤ |v 0| := abs_nonneg _
    have hsq : v 1 ^ (2 : ℕ) ≤ v 0 ^ (2 : ℕ) := by
      rw [sq_le_sq]
      simpa only [abs_of_nonneg htime] using h
    linarith
  · intro h
    have hsq : v 1 ^ (2 : ℕ) ≤ v 0 ^ (2 : ℕ) := by linarith
    rwa [sq_le_sq] at hsq

/-- A BZ congruence transports the flat Killing causal cone by its transposed dressing map. -/
theorem belinskiZakharovDressedFlatKillingCone_iff
    (dressing : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) :
    belinskiZakharovKillingQuadratic
        (belinskiZakharovDressing dressing
          (kerrNewmanKillingBlock 0 0 0 1 (Real.pi / 2))) v ≤ 0 ↔
      belinskiZakharovConfocalLift (Matrix.transpose dressing *ᵥ v) ∈
        _root_.HTGeometry.confocalLorentzCone := by
  rw [belinskiZakharovDressing_killingQuadratic]
  exact (belinskiZakharovFlatKillingCone_iff (Matrix.transpose dressing *ᵥ v)).symm

/-- The transported-cone law specializes to every one-pole BZ dressing. -/
theorem belinskiZakharovOnePoleDressedFlatKillingCone_iff
    (spectral pole residue : ℝ) (v : Fin 2 → ℝ) :
    belinskiZakharovKillingQuadratic
        (belinskiZakharovDressing (belinskiZakharovOnePoleDressing spectral pole residue)
          (kerrNewmanKillingBlock 0 0 0 1 (Real.pi / 2))) v ≤ 0 ↔
      belinskiZakharovConfocalLift
        (Matrix.transpose (belinskiZakharovOnePoleDressing spectral pole residue) *ᵥ v) ∈
          _root_.HTGeometry.confocalLorentzCone :=
  belinskiZakharovDressedFlatKillingCone_iff
    (belinskiZakharovOnePoleDressing spectral pole residue) v

/-- A unipotent BZ dressing fixes the flat Killing block exactly at its trivial parameter.
Thus determinant preservation alone is strictly weaker than background-metric preservation. -/
theorem belinskiZakharovUnipotentDressing_flatKillingBlock_iff
    (parameter : ℝ) :
    belinskiZakharovDressing (belinskiZakharovUnipotentDressing parameter) !![-1, 0; 0, 1] =
      !![-1, 0; 0, 1] ↔ parameter = 0 := by
  constructor
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    simpa [belinskiZakharovDressing, belinskiZakharovUnipotentDressing,
      Matrix.mul_apply, Fin.sum_univ_two] using h01
  · rintro rfl
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [belinskiZakharovDressing, belinskiZakharovUnipotentDressing,
        Matrix.mul_apply, Fin.sum_univ_two]

/-- A one-pole BZ dressing fixes the flat Killing block exactly when its effective residue at the
chosen spectral value vanishes. -/
theorem belinskiZakharovOnePoleDressing_flatKillingBlock_iff
    (spectral pole residue : ℝ) :
    belinskiZakharovDressing (belinskiZakharovOnePoleDressing spectral pole residue) !![-1, 0; 0, 1] =
      !![-1, 0; 0, 1] ↔ residue / (spectral - pole) = 0 := by
  change belinskiZakharovDressing
    (belinskiZakharovUnipotentDressing (residue / (spectral - pole))) !![-1, 0; 0, 1] =
      !![-1, 0; 0, 1] ↔ residue / (spectral - pole) = 0
  constructor
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    simpa [belinskiZakharovDressing, belinskiZakharovUnipotentDressing,
      Matrix.mul_apply, Fin.sum_univ_two] using h01
  · intro h
    rw [h]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [belinskiZakharovDressing, belinskiZakharovUnipotentDressing,
        Matrix.mul_apply, Fin.sum_univ_two]

end GaloisForLFunctions.HTGeometry

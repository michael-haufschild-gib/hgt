import GaloisForLFunctions.HTGeometry.HiggsSpinorNullCone
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Two-channel causal-ray polarity nonselection

A complex doublet and its antilinear spin flip have positive null outer squares with the same
time/Born-weight coordinate.  The two outer squares are adjugate, mutually annihilating, and can be
distinct.  Positivity, nullness, scalar weight, and phase blindness therefore do not select an
elementary causal-ray orientation.

These are unconditional finite matrix identities.  They do not identify either outer square with
physical spacetime or supply a physical source polarity.
-/

open Matrix
open scoped ComplexOrder Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Antilinear two-channel spin flip. -/
def causalSpinFlip (H : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![-star (H 1), star (H 0)]

/-- Applying the two-channel spin flip twice gives the negative original doublet. -/
theorem causalSpinFlip_twice (H : Fin 2 → ℂ) :
    causalSpinFlip (causalSpinFlip H) = -H := by
  funext i
  fin_cases i <;> simp [causalSpinFlip]

/-- The outer square of the spin-flipped doublet is the adjugate outer square. -/
theorem higgsSpinorEventMatrix_causalSpinFlip_eq_adjugate (H : Fin 2 → ℂ) :
    higgsSpinorEventMatrix (causalSpinFlip H) =
      (higgsSpinorEventMatrix H).adjugate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [causalSpinFlip, higgsSpinorEventMatrix, Matrix.vecMulVec_apply,
      Matrix.adjugate_fin_two] <;> ring

/-- Direct and spin-flipped null outer squares mutually annihilate. -/
theorem higgsSpinorEventMatrix_mul_causalSpinFlip_eq_zero (H : Fin 2 → ℂ) :
    higgsSpinorEventMatrix H *
      higgsSpinorEventMatrix (causalSpinFlip H) = 0 := by
  rw [higgsSpinorEventMatrix_causalSpinFlip_eq_adjugate,
    Matrix.mul_adjugate, higgsSpinorEventMatrix_det]
  simp

/-- The complementary spin-flipped record is positive semidefinite. -/
theorem higgsSpinorEventMatrix_causalSpinFlip_posSemidef (H : Fin 2 → ℂ) :
    (higgsSpinorEventMatrix (causalSpinFlip H)).PosSemidef :=
  higgsSpinorEventMatrix_posSemidef (causalSpinFlip H)

/-- The complementary spin-flipped record is Lorentz-null. -/
theorem higgsSpinorEventMatrix_causalSpinFlip_det (H : Fin 2 → ℂ) :
    (higgsSpinorEventMatrix (causalSpinFlip H)).det = 0 :=
  higgsSpinorEventMatrix_det (causalSpinFlip H)

/-- Spin flip preserves the time/Born-weight coordinate. -/
theorem higgsSpinorTime_causalSpinFlip (H : Fin 2 → ℂ) :
    higgsSpinorTime (causalSpinFlip H) = higgsSpinorTime H := by
  simp [higgsSpinorTime, causalSpinFlip, Complex.normSq]
  ring

/-- Standard north-pole spinor used to witness distinct direct and complementary rays. -/
def causalPolarityNorthSpinor : Fin 2 → ℂ :=
  ![1, 0]

/-- Positive null outer-square data and scalar weight do not select a unique causal ray. -/
theorem higgsSpinorEventMatrix_causalSpinFlip_ne_at_north :
    higgsSpinorEventMatrix causalPolarityNorthSpinor ≠
      higgsSpinorEventMatrix (causalSpinFlip causalPolarityNorthSpinor) := by
  intro h
  have h00 := congrFun₂ h 0 0
  norm_num [causalPolarityNorthSpinor, causalSpinFlip, higgsSpinorEventMatrix,
    Matrix.vecMulVec_apply] at h00

end GaloisForLFunctions.HTGeometry

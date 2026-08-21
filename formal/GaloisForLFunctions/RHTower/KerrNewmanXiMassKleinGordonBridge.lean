import GaloisForLFunctions.RHTower.XiMassKleinGordonConnection
import GaloisForLFunctions.HTGeometry.BelinskiZakharovConfocalLorentzBridge

/-!
# Flat Kerr--Newman Killing wave operator for the Xi mass profile

The zero mass--spin--charge Kerr--Newman stationary block is the flat Lorentz plane. At closed
unit mass and damping parameters, the existing Xi mass Klein--Gordon equation becomes a wave
operator eigen-equation after contraction with that block. This is only a sign and operator
correspondence: it does not identify RHTower and Boyer--Lindquist coordinates, calculate a curved
wave operator, or imply RH.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Unit mass/damping member of the existing Xi spectral-cross profile family. -/
noncomputable def xiMassUnitProfile (u h : ℝ) : ℂ :=
  xiMassSpectralCrossMoment 1 1 u 0 h

/-- Scalar wave operator contracted with the flat Kerr--Newman stationary Killing block. -/
noncomputable def kerrNewmanFlatKillingWaveOperator (f : ℝ → ℝ → ℂ) (u h : ℝ) : ℂ :=
  (kerrNewmanKillingBlock 0 0 0 1 (Real.pi / 2) 0 0 : ℂ) *
      deriv (deriv (fun v : ℝ => f v h)) u +
    (kerrNewmanKillingBlock 0 0 0 1 (Real.pi / 2) 1 1 : ℂ) *
      deriv (deriv (fun v : ℝ => f u v)) h

/-- The flat Kerr--Newman block supplies the Lorentzian principal signs `(-,+)`. -/
theorem kerrNewmanFlatKillingWaveOperator_eq
    (f : ℝ → ℝ → ℂ) (u h : ℝ) :
    kerrNewmanFlatKillingWaveOperator f u h =
      -deriv (deriv (fun v : ℝ => f v h)) u +
        deriv (deriv (fun v : ℝ => f u v)) h := by
  unfold kerrNewmanFlatKillingWaveOperator
  rw [belinskiZakharov_flatKillingBlock]
  norm_num

/-- The unit Xi mass profile is an eigenfunction of the flat Kerr--Newman Killing wave operator. -/
theorem xiMassUnitProfile_kerrNewmanFlatKillingWave
    (u h : ℝ) :
    kerrNewmanFlatKillingWaveOperator xiMassUnitProfile u h =
      xiMassUnitProfile u h := by
  change kerrNewmanFlatKillingWaveOperator
      (fun u h => xiMassSpectralCrossMoment 1 1 u 0 h) u h =
        xiMassSpectralCrossMoment 1 1 u 0 h
  rw [kerrNewmanFlatKillingWaveOperator_eq]
  have hkg := xiMassProfile_kleinGordon (a := 1) (σ := 1) (by norm_num) (by norm_num) u h
  simp_rw [xiMassSpectralCrossMoment_zero] at hkg ⊢
  have hspace : xiMassSpectralCrossMoment 1 1 u 0 =
      fun v => xiMassSpectralCrossProfile 1 1 u v := by
    funext v
    exact xiMassSpectralCrossMoment_zero 1 1 u v
  rw [hspace] at hkg
  norm_num at hkg
  linear_combination -hkg

/-- The prime-tail position profile in the RH criterion is the coordinate-weighted unit
Kerr--Newman wave profile. -/
theorem xiMassPrimeTailPositionProfile_unit_eq_kerrNewmanFlatWave
    (u : ℝ) :
    xiMassPrimeTailPositionProfile 1 1 u =
      fun h : ℝ => (h : ℂ) * xiMassUnitProfile u h := by
  funext h
  rfl

/-- The prime-tail profile used in the RH current has the stated first coordinate derivative. -/
theorem hasDerivAt_kerrNewmanFlatXiMassWeightedProfile
    (u h : ℝ) :
    HasDerivAt (fun q : ℝ => (q : ℂ) * xiMassUnitProfile u q)
      (xiMassPrimeTailPositionProfileDeriv 1 1 u h) h := by
  change HasDerivAt (xiMassPrimeTailPositionProfile 1 1 u)
    (xiMassPrimeTailPositionProfileDeriv 1 1 u h) h
  exact hasDerivAt_xiMassPrimeTailPositionProfile (a := 1) (sigma := 1)
    (by norm_num) (by norm_num) u h

/-- The derivative from the coordinate-weighted flat Kerr--Newman profile has the exact second
derivative used to define the prime-tail Green current. -/
theorem hasDerivAt_kerrNewmanFlatXiMassWeightedProfileDeriv
    (u h : ℝ) :
    HasDerivAt (xiMassPrimeTailPositionProfileDeriv 1 1 u)
      (xiMassPrimeTailPositionProfileSecond 1 1 u h) h :=
  hasDerivAt_xiMassPrimeTailPositionProfileDeriv (a := 1) (sigma := 1)
    (by norm_num) (by norm_num) u h

/-- The prime-tail Green current used by the Xi-mass criterion, specialized to the same unit
profile that solves the flat Kerr--Newman wave equation. -/
noncomputable def kerrNewmanFlatXiMassPrimeTailGreenCurrent (u : ℝ) : ℂ :=
  xiMassCriticalPrimeTailGreenCurrent 1 1 u

/-- **Exact RH interface.** RH is equivalent to uniform boundedness of the prime-tail
Green--Stokes current driven by the coordinate-weighted unit flat Kerr--Newman wave profile.

The preceding wave equation alone gives no such bound: the prime-tail source is the indispensable
arithmetic input. -/
theorem riemannHypothesis_iff_kerrNewmanFlatXiMassPrimeTailGreenCurrentLineBound :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
        ‖kerrNewmanFlatXiMassPrimeTailGreenCurrent u‖ ≤ C := by
  simpa [kerrNewmanFlatXiMassPrimeTailGreenCurrent] using
    (riemannHypothesis_iff_xiMassCriticalPrimeTailGreenCurrentLineBound
      (a := 1) (sigma := 1) (by norm_num) (by norm_num))

end RHTower

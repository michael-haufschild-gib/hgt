import GaloisForLFunctions.RHTower.HedenmalmGammaSewnSquarefreeFisherPowerRiggingNoGo

/-!
# Threshold-tracked rigging for the singular Möbius--Sonin carrier

Fixed-power Hilbert riggings face an exact dichotomy: a power below the
admission threshold does not carry the physical column, while every fixed
power above it makes the normalized cofinal source collapse to zero.  The
latter forces the regular value `2` into the vertical fibre of every closed
single-valued graph.

The only real power that prevents collapse at safe base `sigma` is
`r(sigma) = sigma - Re(rho)`.  It shifts the physical source coordinate to the
imaginary axis, so its boundary mass parameter is exactly `sigma` and its
literal rigged source has norm square exactly one.  Multiplication by
`n^-r(sigma)` is coefficient-exact.

The source audit closes this apparent escape.  A power rigging translates the
affine spectral target by `r`.  Threshold tracking therefore lands at
`sigma + i Im(rho)`, in the Euler zero-free half-plane, rather than at the
original divisor `rho`.  No real power rigging can simultaneously preserve
the source mass parameter and the divisor target for `Re(rho) < 1`.

The positive survivor is the sharp classification of this trade-off.  A live
MSC completion must consequently be non-power in a stronger sense: it must
retain divisor incidence through a source-derived singular transport, rather
than through any diagonal real power of the physical column.
-/

open Complex Filter Set Topology
open scoped Topology

noncomputable section

namespace RHTower.HedenmalmThetaSource

/-- The unique threshold-tracking power which makes the physical source mass
parameter equal to its safe Euler base. -/
def mscThresholdTrackedRigging (rho : ℂ) (sigma : ℝ) : ℝ :=
  sigma - rho.re

/-- Physical zero coordinate after applying the threshold-tracking power. -/
def mscThresholdTrackedCoordinate (rho : ℂ) (sigma : ℝ) : ℂ :=
  mscPowerRiggedPhysicalZeroCoordinate rho
    (mscThresholdTrackedRigging rho sigma) sigma

/-- Threshold tracking moves the rigged physical coordinate exactly onto the
imaginary axis. -/
theorem mscThresholdTrackedCoordinate_re
    (rho : ℂ) {sigma : ℝ} (hsigma : sigma ≠ 1) :
    (mscThresholdTrackedCoordinate rho sigma).re = 0 := by
  rw [mscThresholdTrackedCoordinate,
    mscPowerRiggedPhysicalZeroCoordinate_re rho
      (mscThresholdTrackedRigging rho sigma) hsigma]
  simp only [mscThresholdTrackedRigging]
  ring

/-- The source boundary-mass parameter of the threshold-tracked physical
column is exactly the safe base, not a collapsing exterior parameter. -/
theorem mobiusCriticalBoundaryParameter_mscThresholdTrackedCoordinate
    (rho : ℂ) {sigma : ℝ} (hsigma : sigma ≠ 1) :
    mobiusCriticalBoundaryParameter sigma
      (2 * (mscThresholdTrackedCoordinate rho sigma).re) = sigma := by
  rw [mscThresholdTrackedCoordinate_re rho hsigma]
  simp [mobiusCriticalBoundaryParameter]

/-- The threshold-tracking exponent is forced: among real power riggings, it
is exactly the one for which the source boundary-mass parameter stays equal to
the safe base. -/
theorem mscPowerRigged_boundaryParameter_eq_base_iff
    (rho : ℂ) {r sigma : ℝ} (hsigma : sigma ≠ 1) :
    mobiusCriticalBoundaryParameter sigma
      (2 * (mscPowerRiggedPhysicalZeroCoordinate rho r sigma).re) = sigma ↔
        r = sigma - rho.re := by
  rw [mscPowerRiggedPhysicalZeroCoordinate_re rho r hsigma]
  unfold mobiusCriticalBoundaryParameter
  field_simp [sub_ne_zero.mpr hsigma]
  constructor <;> intro h <;> linarith

/-- Literal Hilbert source column at the threshold-tracked rigged coordinate. -/
def mscThresholdTrackedSourceLp
    (rho : ℂ) (sigma : ℝ) (hsigma : 1 < sigma) :
    lp (fun _ : ℕ => ℂ) 2 :=
  ⟨infiniteMobiusCriticalComplexDampedSignedWeight sigma
      (mscThresholdTrackedCoordinate rho sigma),
    HilbertSchmidt.memℓp_of_sq
      ((summable_norm_sq_infiniteMobiusCriticalComplexDampedSignedWeight_iff
        hsigma).2 (by
          rw [mscThresholdTrackedCoordinate_re rho hsigma.ne']
          norm_num))⟩

/-- **Noncollapse law.**  The threshold-tracked literal source has exact norm
square one at every safe stage. -/
theorem norm_sq_mscThresholdTrackedSourceLp
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖mscThresholdTrackedSourceLp rho sigma hsigma‖ ^ (2 : ℕ) = 1 := by
  rw [mscThresholdTrackedSourceLp, HilbertSchmidt.lp_norm_sq_eq]
  change (∑' n : ℕ,
      ‖infiniteMobiusCriticalComplexDampedSignedWeight sigma
        (mscThresholdTrackedCoordinate rho sigma) n‖ ^ (2 : ℕ)) = 1
  rw [show (fun n : ℕ =>
        ‖infiniteMobiusCriticalComplexDampedSignedWeight sigma
          (mscThresholdTrackedCoordinate rho sigma) n‖ ^ (2 : ℕ)) =
      fun n => squarefreeMobiusBoundaryLayerTerm sigma
        (2 * (mscThresholdTrackedCoordinate rho sigma).re) n by
      funext n
      rw [norm_infiniteMobiusCriticalComplexDampedSignedWeight]
      exact norm_sq_infiniteMobiusCriticalDampedSignedWeight_eq_boundaryLayer
        hsigma n,
    tsum_squarefreeMobiusBoundaryLayerTerm,
    mobiusCriticalBoundaryParameter_mscThresholdTrackedCoordinate rho hsigma.ne']
  exact div_self (squarefreeMobiusTotal_pos hsigma).ne'

/-- Threshold tracking is a coefficient-faithful moving power rigging of the
physical source, rather than an abstract replacement vector. -/
theorem mscThresholdTrackedSourceLp_powerRigging
    (rho : ℂ) {sigma : ℝ} (hsigma : sigma ≠ 1) (n : ℕ) :
    infiniteMobiusCriticalComplexDampedSignedWeight sigma
        (mscThresholdTrackedCoordinate rho sigma) n =
      Complex.exp (-((mscThresholdTrackedRigging rho sigma * Real.log n : ℝ) : ℂ)) *
        infiniteMobiusCriticalComplexDampedSignedWeight sigma
          (mscPhysicalZeroCoordinate rho sigma) n := by
  simpa only [mscThresholdTrackedCoordinate] using
    infiniteMobiusCriticalComplexDampedSignedWeight_powerRigged rho
      (mscThresholdTrackedRigging rho sigma) hsigma n

/-- A real power rigging translates the affine spectral target by its power
exponent. -/
theorem mscPowerRiggedPhysicalZeroCoordinate_affine_landing
    (rho : ℂ) (r : ℝ) {sigma : ℝ} (hsigma : sigma ≠ 1) :
    (sigma : ℂ) + mscPowerRiggedPhysicalZeroCoordinate rho r sigma *
        ((sigma - 1 : ℝ) : ℂ) = rho + (r : ℂ) := by
  unfold mscPowerRiggedPhysicalZeroCoordinate
  have heps : (((sigma - 1 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hsigma
  field_simp [heps]
  ring

/-- A real power preserves the original spectral target exactly when it is
the trivial power. -/
theorem mscPowerRiggedPhysicalZeroCoordinate_affine_landing_eq_rho_iff
    (rho : ℂ) {r sigma : ℝ} (hsigma : sigma ≠ 1) :
    (sigma : ℂ) + mscPowerRiggedPhysicalZeroCoordinate rho r sigma *
        ((sigma - 1 : ℝ) : ℂ) = rho ↔ r = 0 := by
  rw [mscPowerRiggedPhysicalZeroCoordinate_affine_landing rho r hsigma]
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simpa using hre
  · intro hr
    simp [hr]

/-- The threshold-tracked target is the Euler-safe point with the original
height, not the original spectral point. -/
theorem mscThresholdTrackedCoordinate_affine_landing
    (rho : ℂ) {sigma : ℝ} (hsigma : sigma ≠ 1) :
    (sigma : ℂ) + mscThresholdTrackedCoordinate rho sigma *
        ((sigma - 1 : ℝ) : ℂ) =
      (sigma : ℂ) + (rho.im : ℂ) * I := by
  rw [mscThresholdTrackedCoordinate,
    mscPowerRiggedPhysicalZeroCoordinate_affine_landing rho
      (mscThresholdTrackedRigging rho sigma) hsigma]
  apply Complex.ext
  · simp [mscThresholdTrackedRigging]
  · simp [mscThresholdTrackedRigging]

/-- The threshold-tracked affine target is zero-free at every safe base. -/
theorem xi_ne_zero_mscThresholdTrackedAffineTarget
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) :
    xi ((sigma : ℂ) + mscThresholdTrackedCoordinate rho sigma *
      ((sigma - 1 : ℝ) : ℂ)) ≠ 0 := by
  rw [mscThresholdTrackedCoordinate_affine_landing rho hsigma.ne']
  apply xi_ne_zero_of_one_lt_re
  simpa using hsigma

/-- **Sharp power-rigging no-go.**  At a point left of one, no real power can
both retain the physical source mass parameter at its safe base and keep the
affine spectral target at that point. -/
theorem no_mscPowerRigged_massPreserving_divisorFidelity
    (rho : ℂ) (hrho : rho.re < 1) {sigma : ℝ} (hsigma : 1 < sigma) :
    ¬ ∃ r : ℝ,
      mobiusCriticalBoundaryParameter sigma
        (2 * (mscPowerRiggedPhysicalZeroCoordinate rho r sigma).re) = sigma ∧
      (sigma : ℂ) + mscPowerRiggedPhysicalZeroCoordinate rho r sigma *
        ((sigma - 1 : ℝ) : ℂ) = rho := by
  rintro ⟨r, hmass, hlanding⟩
  have hr :=
    (mscPowerRigged_boundaryParameter_eq_base_iff rho hsigma.ne').mp hmass
  have hr0 :=
    (mscPowerRiggedPhysicalZeroCoordinate_affine_landing_eq_rho_iff rho
      hsigma.ne').mp hlanding
  rw [hr0] at hr
  linarith

/-- Premise-free certificate for the complete real-power rigging
classification. -/
structure MSCThresholdTrackedMovingRiggingCertificate : Prop where
  coordinatePurelyImaginary : ∀ (rho : ℂ) {sigma : ℝ}, sigma ≠ 1 →
    (mscThresholdTrackedCoordinate rho sigma).re = 0
  massPreservingExponent : ∀ (rho : ℂ) {r sigma : ℝ}, sigma ≠ 1 →
    (mobiusCriticalBoundaryParameter sigma
      (2 * (mscPowerRiggedPhysicalZeroCoordinate rho r sigma).re) = sigma ↔
        r = sigma - rho.re)
  physicalPowerFidelity : ∀ (rho : ℂ) {sigma : ℝ}, sigma ≠ 1 → ∀ n : ℕ,
    infiniteMobiusCriticalComplexDampedSignedWeight sigma
        (mscThresholdTrackedCoordinate rho sigma) n =
      Complex.exp (-((mscThresholdTrackedRigging rho sigma * Real.log n : ℝ) : ℂ)) *
        infiniteMobiusCriticalComplexDampedSignedWeight sigma
          (mscPhysicalZeroCoordinate rho sigma) n
  sourceNormOne : ∀ (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma),
    ‖mscThresholdTrackedSourceLp rho sigma hsigma‖ ^ (2 : ℕ) = 1
  affineTarget : ∀ (rho : ℂ) (r : ℝ) {sigma : ℝ}, sigma ≠ 1 →
    (sigma : ℂ) + mscPowerRiggedPhysicalZeroCoordinate rho r sigma *
        ((sigma - 1 : ℝ) : ℂ) = rho + (r : ℂ)
  thresholdTargetZeroFree : ∀ (rho : ℂ) {sigma : ℝ}, 1 < sigma →
    xi ((sigma : ℂ) + mscThresholdTrackedCoordinate rho sigma *
      ((sigma - 1 : ℝ) : ℂ)) ≠ 0
  noMassPreservingDivisorFidelity : ∀ (rho : ℂ), rho.re < 1 →
    ∀ {sigma : ℝ}, 1 < sigma →
      ¬ ∃ r : ℝ,
        mobiusCriticalBoundaryParameter sigma
          (2 * (mscPowerRiggedPhysicalZeroCoordinate rho r sigma).re) = sigma ∧
        (sigma : ℂ) + mscPowerRiggedPhysicalZeroCoordinate rho r sigma *
          ((sigma - 1 : ℝ) : ℂ) = rho

/-- **Threshold-tracked singular source law.** -/
theorem mscThresholdTrackedMovingRigging_law :
    MSCThresholdTrackedMovingRiggingCertificate where
  coordinatePurelyImaginary := mscThresholdTrackedCoordinate_re
  massPreservingExponent := mscPowerRigged_boundaryParameter_eq_base_iff
  physicalPowerFidelity := mscThresholdTrackedSourceLp_powerRigging
  sourceNormOne := norm_sq_mscThresholdTrackedSourceLp
  affineTarget := mscPowerRiggedPhysicalZeroCoordinate_affine_landing
  thresholdTargetZeroFree := xi_ne_zero_mscThresholdTrackedAffineTarget
  noMassPreservingDivisorFidelity :=
    no_mscPowerRigged_massPreserving_divisorFidelity

end RHTower.HedenmalmThetaSource

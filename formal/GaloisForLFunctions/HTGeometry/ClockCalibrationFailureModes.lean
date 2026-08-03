import GaloisForLFunctions.HTGeometry.ClockPropagatorSelfCalibration

/-!
# The two hypotheses of two-mass self-calibration are exact failure modes

Two-mass self-calibration cancels the entire geometric operator and leaves the endpoint-calibration
product. Two hypotheses carry that cancellation, and this file proves both sharp rather than
technical.

* **Species-independent endpoint gain.** If each species carries its own gains, the geometric
  operator survives in the residual. The residual is free of the geometry exactly when the two
  species share their endpoint dressing, and there are gains for which it is not.
* **A pure mass difference.** The residual is a pure calibration term exactly when the two species'
  zeroth-order couplings differ by a constant. A non-scalar coupling difference — a differing
  principal part or a nonminimal curvature coupling — leaves a residual that is not a calibration
  at all, for any constant.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

/-! ## Species-dependent endpoint gain -/

section SpeciesGain

variable {K : Type u} {A : Type v} [Field K] [Ring A] [Algebra K A]

/-- Measured inverse operator when a species carries its own endpoint gains. -/
def speciesMeasuredInverse (geometricOperator sourceGainInv receiverGainInv : A) (massSq : K) :
    A :=
  sourceGainInv * (geometricOperator + algebraMap K A massSq) * receiverGainInv

/-- Residual of two clock species whose endpoint gains are allowed to differ. -/
def speciesResidual (geometricOperator sourceGainInv₁ receiverGainInv₁ sourceGainInv₂
    receiverGainInv₂ : A) (massSq₁ massSq₂ : K) : A :=
  speciesMeasuredInverse geometricOperator sourceGainInv₁ receiverGainInv₁ massSq₁ -
    speciesMeasuredInverse geometricOperator sourceGainInv₂ receiverGainInv₂ massSq₂

theorem speciesResidual_eq (geometricOperator b₁ a₁ b₂ a₂ : A) (massSq₁ massSq₂ : K) :
    speciesResidual geometricOperator b₁ a₁ b₂ a₂ massSq₁ massSq₂ =
      (b₁ * geometricOperator * a₁ - b₂ * geometricOperator * a₂) +
        (b₁ * algebraMap K A massSq₁ * a₁ - b₂ * algebraMap K A massSq₂ * a₂) := by
  simp only [speciesResidual, speciesMeasuredInverse]
  noncomm_ring

theorem speciesResidual_zero (b₁ a₁ b₂ a₂ : A) (massSq₁ massSq₂ : K) :
    speciesResidual (0 : A) b₁ a₁ b₂ a₂ massSq₁ massSq₂ =
      b₁ * algebraMap K A massSq₁ * a₁ - b₂ * algebraMap K A massSq₂ * a₂ := by
  rw [speciesResidual_eq]
  simp

/-- **Species-independent endpoint dressing is exactly what cancels the geometry.**

The two-mass residual is independent of the geometric operator precisely when the two species
dress it identically. -/
theorem speciesResidual_geometryFree_iff (b₁ a₁ b₂ a₂ : A) (massSq₁ massSq₂ : K) :
    (∀ geometricOperator : A,
        speciesResidual geometricOperator b₁ a₁ b₂ a₂ massSq₁ massSq₂ =
          speciesResidual (0 : A) b₁ a₁ b₂ a₂ massSq₁ massSq₂) ↔
      ∀ geometricOperator : A,
        b₁ * geometricOperator * a₁ = b₂ * geometricOperator * a₂ := by
  constructor
  · intro hfree P
    have h := hfree P
    rw [speciesResidual_eq, speciesResidual_zero] at h
    have hsub : b₁ * P * a₁ - b₂ * P * a₂ = 0 := by
      have := sub_eq_zero.mpr h
      simpa using this
    exact sub_eq_zero.mp hsub
  · intro hdress P
    rw [speciesResidual_eq, speciesResidual_zero, hdress P]
    simp

/-- **Species-dependent gain really does defeat calibration.** For explicit unequal gains the
residual depends on the geometric operator, so it is not a calibration datum. -/
theorem exists_speciesResidual_depends_on_geometry :
    ∃ (b₁ a₁ b₂ a₂ massSq₁ massSq₂ : ℝ),
      massSq₁ ≠ massSq₂ ∧
        ∃ geometricOperator : ℝ,
          speciesResidual geometricOperator b₁ a₁ b₂ a₂ massSq₁ massSq₂ ≠
            speciesResidual (0 : ℝ) b₁ a₁ b₂ a₂ massSq₁ massSq₂ := by
  refine ⟨1, 1, 1, 2, 1, 0, by norm_num, 1, ?_⟩
  simp only [speciesResidual, speciesMeasuredInverse]
  norm_num

end SpeciesGain

/-! ## Non-scalar coupling difference -/

section Coupling

variable {K : Type u} {A : Type v} [Field K] [Ring A] [Algebra K A]

/-- **A pure calibration residual is exactly a constant coupling difference.**

With invertible endpoint gains, the dressed difference of the two species' operators is the
calibration product scaled by a constant precisely when the undressed difference is that
constant. -/
theorem dressedCouplingDifference_eq_calibration_iff
    {sourceGainInv sourceGain receiverGainInv receiverGain : A}
    (_hs : sourceGainInv * sourceGain = 1) (hs' : sourceGain * sourceGainInv = 1)
    (hr : receiverGainInv * receiverGain = 1) (_hr' : receiverGain * receiverGainInv = 1)
    (couplingDiff : A) (c : K) :
    sourceGainInv * couplingDiff * receiverGainInv =
        algebraMap K A c * (sourceGainInv * receiverGainInv) ↔
      couplingDiff = algebraMap K A c := by
  constructor
  · intro hEq
    calc couplingDiff
        = (sourceGain * sourceGainInv) * couplingDiff * (receiverGainInv * receiverGain) := by
          rw [hs', hr]
          noncomm_ring
      _ = sourceGain * (sourceGainInv * couplingDiff * receiverGainInv) * receiverGain := by
          noncomm_ring
      _ = sourceGain * (algebraMap K A c * (sourceGainInv * receiverGainInv)) *
            receiverGain := by rw [hEq]
      _ = algebraMap K A c * ((sourceGain * sourceGainInv) * (receiverGainInv * receiverGain)) := by
          have hcomm : sourceGain * algebraMap K A c = algebraMap K A c * sourceGain :=
            (Algebra.commutes c sourceGain).symm
          calc sourceGain * (algebraMap K A c * (sourceGainInv * receiverGainInv)) * receiverGain
              = (sourceGain * algebraMap K A c) * (sourceGainInv * receiverGainInv) *
                  receiverGain := by noncomm_ring
            _ = (algebraMap K A c * sourceGain) * (sourceGainInv * receiverGainInv) *
                  receiverGain := by rw [hcomm]
            _ = algebraMap K A c *
                  ((sourceGain * sourceGainInv) * (receiverGainInv * receiverGain)) := by
                noncomm_ring
      _ = algebraMap K A c := by rw [hs', hr]; simp
  · intro hEq
    rw [hEq, ← Algebra.commutes c sourceGainInv]
    noncomm_ring

/-- A product algebra carries elements that are not scalars. -/
theorem exists_ne_algebraMap_prod :
    ∃ X : ℝ × ℝ, ∀ c : ℝ, X ≠ algebraMap ℝ (ℝ × ℝ) c := by
  refine ⟨(1, 0), fun c hc => ?_⟩
  have h1 : (1 : ℝ) = c := congrArg Prod.fst hc
  have h2 : (0 : ℝ) = c := congrArg Prod.snd hc
  exact one_ne_zero (h1.trans h2.symm)

/-- **A non-scalar coupling difference really does defeat calibration.** If the two species'
zeroth-order couplings differ by a non-scalar element, the dressed residual is not the calibration
product scaled by any constant. -/
theorem dressedCouplingDifference_ne_calibration_of_ne_algebraMap
    {sourceGainInv sourceGain receiverGainInv receiverGain : A}
    (hs : sourceGainInv * sourceGain = 1) (hs' : sourceGain * sourceGainInv = 1)
    (hr : receiverGainInv * receiverGain = 1) (hr' : receiverGain * receiverGainInv = 1)
    {couplingDiff : A} (hns : ∀ c : K, couplingDiff ≠ algebraMap K A c) (c : K) :
    sourceGainInv * couplingDiff * receiverGainInv ≠
      algebraMap K A c * (sourceGainInv * receiverGainInv) := by
  intro hEq
  exact hns c
    ((dressedCouplingDifference_eq_calibration_iff hs hs' hr hr' couplingDiff c).1 hEq)

/-- The failure mode is inhabited: an explicit non-scalar coupling difference with trivial gains. -/
theorem exists_dressedCouplingDifference_ne_calibration :
    ∃ (couplingDiff : ℝ × ℝ), ∀ c : ℝ,
      (1 : ℝ × ℝ) * couplingDiff * (1 : ℝ × ℝ) ≠
        algebraMap ℝ (ℝ × ℝ) c * ((1 : ℝ × ℝ) * (1 : ℝ × ℝ)) := by
  obtain ⟨X, hX⟩ := exists_ne_algebraMap_prod
  refine ⟨X, fun c => ?_⟩
  exact dressedCouplingDifference_ne_calibration_of_ne_algebraMap
    (one_mul (1 : ℝ × ℝ)) (one_mul (1 : ℝ × ℝ)) (one_mul (1 : ℝ × ℝ)) (one_mul (1 : ℝ × ℝ))
    hX c

end Coupling

end GaloisForLFunctions.HTGeometry

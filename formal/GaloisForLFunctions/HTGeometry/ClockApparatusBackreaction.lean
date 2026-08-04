import GaloisForLFunctions.HTGeometry.ClockPropagatorSelfCalibration

/-!
# The apparatus's own backreaction

A laboratory that probes geometry with clocks perturbs the geometry it probes. The two-mass
construction is insensitive to that perturbation in its calibration channel and honest about it in
its symbol channel.

The calibration channel is the difference of the two measured inverse operators. That difference
does not mention the geometric operator at all, so any change of the geometry — including the
apparatus's own backreaction — leaves it untouched, provided both species see the same changed
geometry. If the two species see *different* operators the residual acquires exactly the dressed
difference of those operators, and calibration fails by that amount; an explicit witness shows this
is not vacuous.

The symbol channel does see the perturbation: what the two-mass reconstruction returns is the
principal symbol of the operator that is actually there, that is, the backreacted geometry, which
differs from the undisturbed one by exactly the symbol of the perturbation.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

/-! ## The calibration channel ignores species-common backreaction -/

section Calibration

variable {K : Type u} {A : Type v} [Field K] [Ring A] [Algebra K A]

/-- **Species-common backreaction is invisible to the calibration channel.** The difference of the
two measured inverse operators is the same for any two geometric operators, so a perturbation of the
geometry — the apparatus's own included — cannot corrupt the reconstructed endpoint calibration. -/
theorem measuredClockInverse_difference_geometry_independent
    (geometricOperator₁ geometricOperator₂ sourceGainInv receiverGainInv : A) (massSq₁ massSq₂ : K) :
    measuredClockInverse geometricOperator₁ sourceGainInv receiverGainInv massSq₁ -
        measuredClockInverse geometricOperator₁ sourceGainInv receiverGainInv massSq₂ =
      measuredClockInverse geometricOperator₂ sourceGainInv receiverGainInv massSq₁ -
        measuredClockInverse geometricOperator₂ sourceGainInv receiverGainInv massSq₂ := by
  rw [measuredClockInverse_difference, measuredClockInverse_difference]

/-- **Species-dependent backreaction is exactly the residual.** If the two species see different
geometric operators the calibration channel acquires their dressed difference. -/
theorem measuredClockInverse_difference_species_geometry
    (geometricOperator₁ geometricOperator₂ sourceGainInv receiverGainInv : A) (massSq₁ massSq₂ : K) :
    measuredClockInverse geometricOperator₁ sourceGainInv receiverGainInv massSq₁ -
        measuredClockInverse geometricOperator₂ sourceGainInv receiverGainInv massSq₂ =
      algebraMap K A (massSq₁ - massSq₂) * (sourceGainInv * receiverGainInv) +
        sourceGainInv * (geometricOperator₁ - geometricOperator₂) * receiverGainInv := by
  have hsplit :
      measuredClockInverse geometricOperator₁ sourceGainInv receiverGainInv massSq₁ -
          measuredClockInverse geometricOperator₂ sourceGainInv receiverGainInv massSq₂ =
        (measuredClockInverse geometricOperator₂ sourceGainInv receiverGainInv massSq₁ -
            measuredClockInverse geometricOperator₂ sourceGainInv receiverGainInv massSq₂) +
          sourceGainInv * (geometricOperator₁ - geometricOperator₂) * receiverGainInv := by
    simp only [measuredClockInverse]
    noncomm_ring
  rw [hsplit, measuredClockInverse_difference]

/-- The species-dependent residual is not vacuous: with equal masses and unit gains, two different
geometric operators leave a nonzero calibration residual where the ideal one vanishes. -/
theorem exists_measuredClockInverse_difference_ne :
    ∃ (geometricOperator₁ geometricOperator₂ : ℝ) (massSq : ℝ),
      measuredClockInverse geometricOperator₁ (1 : ℝ) 1 massSq -
          measuredClockInverse geometricOperator₂ (1 : ℝ) 1 massSq ≠ 0 := by
  refine ⟨1, 0, 0, ?_⟩
  simp [measuredClockInverse]

end Calibration

/-! ## The symbol channel reconstructs the backreacted geometry -/

namespace ScalarSecondOrderOperator

section Perturbation

variable {ι : Type*} {R : Type*} [CommRing R] [Fintype ι]

/-- Sum of local second-order operators, coefficient by coefficient. -/
def add (P Q : ScalarSecondOrderOperator ι R) : ScalarSecondOrderOperator ι R where
  zeroth := P.zeroth + Q.zeroth
  first i := P.first i + Q.first i
  second i j := P.second i j + Q.second i j

/-- The principal symbol is additive in the operator, so a perturbation of the geometry shifts the
symbol by exactly its own symbol. -/
theorem principalSymbol_add (P Q : ScalarSecondOrderOperator ι R) (ξ : ι → R) :
    principalSymbol (add P Q) ξ = principalSymbol P ξ + principalSymbol Q ξ := by
  classical
  simp only [principalSymbol, add]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end Perturbation

section Backreacted

variable {ι : Type*} {R : Type*} [Field R] [Fintype ι]

/-- **The two-mass reconstruction returns the backreacted geometry.** Applied to a perturbed
geometric operator, the calibrated symbol quotient reconstructs the principal symbol of the operator
that is actually present: the undisturbed symbol plus the symbol of the perturbation. The apparatus's
backreaction is measured, not an error. -/
theorem twoMassPrincipalSymbol_reconstruction_perturbed
    (P perturbation : ScalarSecondOrderOperator ι R)
    {sourceGainInv : R} (hsource : sourceGainInv ≠ 0)
    (receiverGainInv : ScalarTwoJet ι R) (hreceiver : receiverGainInv.value ≠ 0)
    {μ₁ μ₂ : R} (hmass : μ₁ ≠ μ₂) (ξ : ι → R) :
    (μ₁ - μ₂) *
          principalSymbol
            (measuredClockInverseOperator (add P perturbation) sourceGainInv receiverGainInv μ₁)
            ξ /
        ((μ₁ - μ₂) * (sourceGainInv * receiverGainInv.value)) =
      principalSymbol P ξ + principalSymbol perturbation ξ := by
  rw [twoMassPrincipalSymbol_reconstruction (add P perturbation) hsource receiverGainInv hreceiver
    hmass ξ, principalSymbol_add]

end Backreacted

end ScalarSecondOrderOperator

end GaloisForLFunctions.HTGeometry

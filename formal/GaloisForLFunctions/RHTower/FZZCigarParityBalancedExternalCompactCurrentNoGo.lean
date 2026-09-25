import GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTOrderedNeutralCrossDepthCurrent
import GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTNeutralPairCrossDepth
import GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTAdaptiveOnShellOccurrenceNoGo

/-!
# Balanced external compact-current obstruction

The physical balanced external-Gamma sector has zero compact momentum. The
neutral-pair and ordered-current constructions that feed this compact momentum
into the radial Fourier characteristic therefore have real, depth-independent
values: respectively `1` and `1/2`. Neither can orient that sector.

Compact charge and radial Fourier momentum are distinct parameters. Keeping
the latter independent preserves the exact cross-depth phase, but does not
identify a full torus source or prove a replica Ward law.
-/

open Complex MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The radial cross-depth characteristic loses its relative phase at zero
Fourier momentum, for every pair of coupling depths. -/
theorem fzzRadialCouplingCrossDepthCoherence_zero
    (u₁ u₂ v : ℝ) :
    fzzRadialCouplingCrossDepthCoherence u₁ u₂ v 0 = 1 := by
  simp [fzzRadialCouplingCrossDepthCoherence,
    fzzRadialCouplingCharacteristic_zero]

/-- The compact-neutral pair carrier as defined with its Fourier momentum
equal to compact charge is constant on the balanced external sector. -/
theorem fzzCigarExternalBRSTNeutralCrossDepthCompactIntegral_balanced
    (k : ℝ) (j : ℂ) (ν : ℤ) (u₁ u₂ v : ℝ) :
    fzzCigarExternalBRSTNeutralCrossDepthCompactIntegral
      k j 0 ν u₁ u₂ v = 1 := by
  rw [fzzCigarExternalBRSTNeutralCrossDepthCompactIntegral_eq]
  simpa using fzzRadialCouplingCrossDepthCoherence_zero u₁ u₂ v

/-- At zero compact charge the cyclic ordered chamber is a triangle of unit
area density; the nonzero-charge inverse-frequency formula does not apply. -/
theorem fzzCigarExternalBRSTOrderedNeutralAngularIntegral_balanced
    (k : ℝ) (j : ℂ) (ν : ℤ) :
    fzzCigarExternalBRSTOrderedNeutralAngularIntegral k j 0 ν = 1 / 2 := by
  unfold fzzCigarExternalBRSTOrderedNeutralAngularIntegral
  simp [fzzCigarExternalBRSTOrderedNeutralAngularKernel_eq]
  rw [intervalIntegral.integral_ofReal, integral_id]
  norm_num

/-- The ordered diagonal compact--radial current is also real and constant in
the balanced external sector. -/
theorem fzzCigarExternalBRSTOrderedNeutralDiagonalCurrent_balanced
    (k : ℝ) (j : ℂ) (ν : ℤ) (u v : ℝ) :
    fzzCigarExternalBRSTOrderedNeutralDiagonalCurrent k j 0 ν u v = 1 / 2 := by
  rw [fzzCigarExternalBRSTOrderedNeutralDiagonalCurrent,
    fzzCigarExternalBRSTOrderedNeutralAngularIntegral_balanced]
  simp only [Int.cast_zero, fzzRadialCouplingCrossDepthCoherence_zero]
  ring

/-- **Balanced compact-current route kill.** Substituting the physical
continuum radial label cannot restore orientation to this compact-charge-fed
ordered current. -/
theorem fzzHJBalancedExternalCompactCurrent_im_eq_zero
    (k P : ℝ) (ν : ℤ) (u v : ℝ) :
    (fzzCigarExternalBRSTOrderedNeutralDiagonalCurrent k
      (RHTower.fzzHJPhysicalRadialLabel k P) 0 ν u v).im = 0 := by
  rw [fzzCigarExternalBRSTOrderedNeutralDiagonalCurrent_balanced]
  norm_num

/-- No source-fixed postprocessing of the two compact-charge-fed carriers can
select the radial-momentum wall: both inputs are the same at every `P`. -/
theorem not_exists_fzzHJBalancedCompactCarriers_radialSelector
    (k : ℝ) (ν : ℤ) (u₁ u₂ u v : ℝ) :
    ¬ ∃ Q : ℂ × ℂ → Prop, ∀ P : ℝ,
      Q (fzzCigarExternalBRSTNeutralCrossDepthCompactIntegral k
            (RHTower.fzzHJPhysicalRadialLabel k P) 0 ν u₁ u₂ v,
          fzzCigarExternalBRSTOrderedNeutralDiagonalCurrent k
            (RHTower.fzzHJPhysicalRadialLabel k P) 0 ν u v) ↔ P = 0 := by
  rintro ⟨Q, hQ⟩
  have hzero : Q (1, 1 / 2) := by
    have h := (hQ 0).mpr rfl
    simpa only [fzzCigarExternalBRSTNeutralCrossDepthCompactIntegral_balanced,
      fzzCigarExternalBRSTOrderedNeutralDiagonalCurrent_balanced] using h
  have hone : (1 : ℝ) = 0 := (hQ 1).mp (by
    simpa only [fzzCigarExternalBRSTNeutralCrossDepthCompactIntegral_balanced,
      fzzCigarExternalBRSTOrderedNeutralDiagonalCurrent_balanced] using hzero)
  norm_num at hone

/-- Exact positive survivor with independent compact and radial momenta. This
integral is a diagnostic carrier, not a derived torus Ward source. -/
def fzzBalancedExternalIndependentRadialCompactIntegral
    (k : ℝ) (j : ℂ) (ν : ℤ) (u₁ u₂ v P : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..1,
    fzzCigarExternalBRSTNeutralAngularPairKernel k j 0 ν s *
      fzzRadialCouplingCrossDepthCoherence u₁ u₂ v P

/-- Compact integration retains an independently supplied radial phase. -/
theorem fzzBalancedExternalIndependentRadialCompactIntegral_eq
    (k : ℝ) (j : ℂ) (ν : ℤ) (u₁ u₂ v P : ℝ) :
    fzzBalancedExternalIndependentRadialCompactIntegral
      k j ν u₁ u₂ v P =
        fzzRadialCouplingCrossDepthCoherence u₁ u₂ v P := by
  unfold fzzBalancedExternalIndependentRadialCompactIntegral
  simp [fzzCigarExternalBRSTNeutralAngularPairKernel_eq_one]

/-- Exact surviving radial phase; physical source selection of this carrier is
still open. -/
theorem fzzBalancedExternalIndependentRadialCompactIntegral_im
    (k : ℝ) (j : ℂ) (ν : ℤ) (u₁ u₂ v P : ℝ) :
    (fzzBalancedExternalIndependentRadialCompactIntegral
      k j ν u₁ u₂ v P).im =
        -(Complex.normSq
          (Complex.Gamma (1 + ((P / Real.exp v : ℝ) : ℂ) * Complex.I)) *
            Real.sin (P * (u₁ - u₂) / Real.exp v)) := by
  rw [fzzBalancedExternalIndependentRadialCompactIntegral_eq]
  exact fzzRadialCouplingCrossDepthCoherence_im u₁ u₂ v P

end

end GaloisForLFunctions.RHTower

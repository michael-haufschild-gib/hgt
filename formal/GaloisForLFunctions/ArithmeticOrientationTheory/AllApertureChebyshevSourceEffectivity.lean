import GaloisForLFunctions.ArithmeticOrientationTheory.SourceSectionBoundaryRigidity

/-!
# Exact arithmetic source effectivity at every aperture

The archimedean gauge minus the Chebyshev box correction represents the exact defect.
Allowing signed fibre degrees therefore gives a source presentation of the closed positive
cone, with unconditional Riemann–Roch at every aperture. Bézout and ampleness remain equivalent
to payment of the source correction. No sign theorem follows from the representation identity.
-/

noncomputable section

open GaloisForLFunctions.ArithmeticCastelnuovoSeveri Zeta23

namespace GaloisForLFunctions.ArithmeticOrientationTheory

/-- Graded effectivity read from the archimedean gauge and the prime-power box defect. -/
def gradedChebyshevSectionCone (r R : ℝ) : Set (ℝ × ℝ × oddRealTestsAt r) :=
  (scalingSubsurface (oddRealTestsAt r)).gradedSourceCone (chebyshevSourceEnergy r R)

/-- The exact arithmetic reserve presents the positive cone without a sign premise. -/
theorem gradedChebyshevSectionCone_eq_positiveCone {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) :
    gradedChebyshevSectionCone r R = (scalingSubsurface (oddRealTestsAt r)).positiveCone := by
  have hrep := (chebyshevSectionCone_eq_sectionEffectivityCone hr hrR).1
  rw [gradedChebyshevSectionCone,
    show chebyshevSourceEnergy r R =
      (fun x => (scalingSubsurface (oddRealTestsAt r)).defect x x) from
      funext fun x => (hrep x).symm,
    PolarSurface.gradedSourceCone_defect_eq_positiveCone]

/-- Exact source Riemann–Roch holds at every aperture on the original odd-source surface. -/
theorem gradedChebyshevSectionCone_riemannRoch {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) :
    (scalingSubsurface (oddRealTestsAt r)).RiemannRochAxiom
      (gradedChebyshevSectionCone r R) := by
  rw [gradedChebyshevSectionCone_eq_positiveCone hr hrR]
  exact (scalingSubsurface (oddRealTestsAt r)).positiveCone_riemannRoch

/-- The exact source cone leaves the entire Hodge-index obligation in Bézout. -/
theorem gradedChebyshevSectionCone_bezout_iff_hodgeIndex {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) :
    (scalingSubsurface (oddRealTestsAt r)).BezoutAxiom (gradedChebyshevSectionCone r R) ↔
      (scalingSubsurface (oddRealTestsAt r)).HodgeIndex := by
  rw [gradedChebyshevSectionCone_eq_positiveCone hr hrR]
  exact (scalingSubsurface (oddRealTestsAt r)).hodgeIndex_iff_positiveCone_bezout.symm

/-- Ampleness of the graded arithmetic cone has the same source-sign obligation. -/
theorem gradedChebyshevSectionCone_ample_iff_hodgeIndex {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) :
    (scalingSubsurface (oddRealTestsAt r)).AmpleAxiom (gradedChebyshevSectionCone r R) ↔
      (scalingSubsurface (oddRealTestsAt r)).HodgeIndex := by
  rw [gradedChebyshevSectionCone_eq_positiveCone hr hrR]
  exact (scalingSubsurface (oddRealTestsAt r)).positiveCone_ample_iff_hodgeIndex

/-- Bézout is precisely the unpaid arithmetic source inequality, at each aperture. -/
theorem gradedChebyshevSectionCone_bezout_iff_source_payment {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) :
    (scalingSubsurface (oddRealTestsAt r)).BezoutAxiom (gradedChebyshevSectionCone r R) ↔
      ∀ f : oddRealTestsAt r,
        apertureH1ChebyshevCorrection r (f.1 : ℝ → ℝ) ≤
          archGaugeBudget r R (f.1 : ℝ → ℝ) := by
  rw [gradedChebyshevSectionCone_bezout_iff_hodgeIndex hr hrR,
    PolarSurface.hodgeIndex_iff_castelnuovoSeveri,
    PolarSurface.castelnuovoSeveri_iff_defect_nonneg]
  have hrep := (chebyshevSectionCone_eq_sectionEffectivityCone hr hrR).1
  constructor
  · intro h f
    have hf := h (0, 0, f)
    rw [hrep, chebyshevSourceEnergy] at hf
    linarith only [hf]
  · intro h x
    rw [hrep, chebyshevSourceEnergy]
    exact sub_nonneg.mpr (h x.2.2)

/-- All-aperture Bézout for this exact source presentation is equivalent to RH. -/
theorem riemannHypothesis_iff_all_aperture_gradedChebyshev_bezout :
    RiemannHypothesis ↔ ∀ r : ℝ, 0 < r →
      (scalingSubsurface (oddRealTestsAt r)).BezoutAxiom (gradedChebyshevSectionCone r (r + 1)) := by
  rw [riemannHypothesis_iff_rightZeros_zeta_eq_empty,
    rightZeros_zeta_eq_empty_iff_forall_odd_scalingSubsurface_hodgeIndex]
  exact forall₂_congr fun r hr =>
    (gradedChebyshevSectionCone_bezout_iff_hodgeIndex hr (by linarith)).symm

/-- All-aperture ampleness carries the same unresolved condition. -/
theorem riemannHypothesis_iff_all_aperture_gradedChebyshev_ample :
    RiemannHypothesis ↔ ∀ r : ℝ, 0 < r →
      (scalingSubsurface (oddRealTestsAt r)).AmpleAxiom (gradedChebyshevSectionCone r (r + 1)) := by
  rw [riemannHypothesis_iff_rightZeros_zeta_eq_empty,
    rightZeros_zeta_eq_empty_iff_forall_odd_scalingSubsurface_hodgeIndex]
  exact forall₂_congr fun r hr =>
    (gradedChebyshevSectionCone_ample_iff_hodgeIndex hr (by linarith)).symm

end GaloisForLFunctions.ArithmeticOrientationTheory

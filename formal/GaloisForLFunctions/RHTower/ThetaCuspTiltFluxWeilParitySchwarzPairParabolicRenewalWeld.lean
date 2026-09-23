import GaloisForLFunctions.RHTower.ThetaCuspTiltFluxWeilParitySchwarzPairNormalRenewalWeld
import GaloisForLFunctions.RHTower.XiShiftedTerminalFrontierParabolicSynchronization

/-!
# Parabolically synchronized Schwarz-pair normal receiver

Fixed-degree far-right positivity is not needed to choose unrelated renewal masses.  The corpus
parabolic Hankel theorem gives one explicit universal square-root-mass schedule

`w_n = sqrt(routeUParabolicDegreeHorizon) * (n + 5)`

whose degree-`n+5` shifted-Xi block is positive definite.  On this same `O(n)` schedule, every
off-line Xi copy has an exact positive nonlinear Weyl receiver value at every degree after its
aperture is fitted to the spectral displacement.  The value is independent of degree and, after
reciprocal-metric and analytic-multiplicity scaling, equals the Schwarz-pair Lorentz normal
coefficient.

Thus the finite-degree receiver theorem upgrades to an explicit cofinal synchronized orbit;
neither arbitrarily delayed witnesses nor Xi-dependent mass choices remain.  This does not produce
arithmetic normal charge: the normalized value is selected by external aperture.  The companion
universality no-go proves that every positive target is realized in exactly the same way.
-/

open Complex Filter Topology Matrix

namespace RHTower

noncomputable section

/-- Universal parabolic square-root-mass schedule for normal-channel degree reception. -/
def xiSchwarzPairParabolicNormalRenewalSchedule (n : ℕ) : ℝ :=
  Real.sqrt routeUParabolicDegreeHorizon * ((n + 5 : ℕ) : ℝ)

/-- Exact physical mass of the parabolic schedule. -/
theorem xiSchwarzPairParabolicNormalRenewalSchedule_sq (n : ℕ) :
    xiSchwarzPairParabolicNormalRenewalSchedule n ^ (2 : ℕ) =
      routeUParabolicDegreeHorizon * (((n + 5 : ℕ) : ℝ) ^ (2 : ℕ)) := by
  rw [xiSchwarzPairParabolicNormalRenewalSchedule, mul_pow,
    Real.sq_sqrt routeUParabolicDegreeHorizon_pos.le]

/-- Every degree-matched shifted-Xi block is positive on the explicit parabolic schedule. -/
theorem xiSchwarzPairParabolicNormalRenewalSchedule_posDef (n : ℕ) :
    (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence (xiSchwarzPairParabolicNormalRenewalSchedule n))
      (n + 5)).PosDef := by
  have hmass : routeUParabolicDegreeHorizon * (((n + 5 : ℕ) : ℝ) ^ (2 : ℕ)) ≤
      xiSchwarzPairParabolicNormalRenewalSchedule n ^ (2 : ℕ) := by
    rw [xiSchwarzPairParabolicNormalRenewalSchedule_sq]
  have hA := xiShiftedMomentHankelMatrix_posDef_of_parabolicDegreeHorizon
    (n + 3) hmass
  have heq : xiShiftedMomentHankelMatrix
      (xiSchwarzPairParabolicNormalRenewalSchedule n ^ (2 : ℕ)) (n + 5) =
      HTGeometry.momentHankelMatrix
        (xiShiftedRealMomentSequence (xiSchwarzPairParabolicNormalRenewalSchedule n))
        (n + 5) := by
    ext i j
    rfl
  rw [← heq]
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hA

/-- On the explicit parabolic schedule, every off-line Xi copy's fitted aperture returns its exact
Lorentz normal coefficient through every positive nonlinear degree renewal. -/
theorem xiSchwarzPair_offLine_parabolic_nonlinearRenewal
    (q : XiZeroCopy) (him : (xiSpectralPoint q).im ≠ 0) (n : ℕ) :
    xiSchwarzPairCompletedSourceWeylNormalizedIncrement q
        (xiSchwarzPairParabolicNormalRenewalSchedule n) (n + 1) =
      |(xiSpectralPoint q).im| ∧
    2 * xiSchwarzPairAnalyticMultiplicity q *
        xiSchwarzPairCompletedSourceWeylNormalizedIncrement q
          (xiSchwarzPairParabolicNormalRenewalSchedule n) (n + 1) =
      Complex.normSq (xiSpectralPoint q) *
        xiSchwarzPairSourceNormalCoefficient q := by
  have hHbig := xiSchwarzPairParabolicNormalRenewalSchedule_posDef n
  have hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence (xiSchwarzPairParabolicNormalRenewalSchedule n))
      (n + 4)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hHbig
  have hinc := xiSchwarzPairCompletedSourceWeylNormalizedIncrement_eq_normalDisplacement
    q (by omega : 0 < n + 1) hH him
  refine ⟨hinc, ?_⟩
  have hD : Complex.normSq (xiSpectralPoint q) ≠ 0 :=
    (Complex.normSq_pos.mpr (xiSpectralPoint_ne_zero q)).ne'
  rw [hinc, xiSchwarzPairSourceNormalCoefficient,
    xiSchwarzPairSourceNormalRate_eq]
  field_simp

/-- Closed synchronized certificate/receiver dichotomy: fixed class-law realization occurs
exactly in neutral normal phase; otherwise the fitted parabolic nonlinear receiver is positive at
every degree. -/
theorem xiSchwarzPair_classLaw_or_parabolic_nonlinearRenewalPhase
    (q : XiZeroCopy) (p : Nat.Primes) {d : ℝ} (hd : 1 < d) :
    Nonempty (SourceHorizontalXiAdaptiveClassLawScaleOrbitCertificate q p d) ∨
      (∀ n : ℕ,
        xiSchwarzPairCompletedSourceWeylNormalizedIncrement q
            (xiSchwarzPairParabolicNormalRenewalSchedule n) (n + 1) =
          |(xiSpectralPoint q).im| ∧
        0 < xiSchwarzPairCompletedSourceWeylNormalizedIncrement q
          (xiSchwarzPairParabolicNormalRenewalSchedule n) (n + 1)) := by
  by_cases hnormal : xiSchwarzPairSourceNormalCoefficient q = 0
  · exact Or.inl
      ((sourceHorizontalXiAdaptiveClassLawScaleOrbitCertificate_nonempty_iff_normalCoefficient_eq_zero
        q p hd).2 hnormal)
  · right
    have him : (xiSpectralPoint q).im ≠ 0 := fun h => hnormal
      ((xiSchwarzPairSourceNormalCoefficient_eq_zero_iff q).2 h)
    intro n
    have hinc := (xiSchwarzPair_offLine_parabolic_nonlinearRenewal q him n).1
    exact ⟨hinc, hinc.symm ▸ abs_pos.mpr him⟩

end

end RHTower

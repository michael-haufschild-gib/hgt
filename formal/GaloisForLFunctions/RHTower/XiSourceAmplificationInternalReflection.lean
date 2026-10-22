import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingStimulatedCubicUnmaskingEndpoint
import GaloisForLFunctions.RHTower.XiExternalInternalReflectionSeparation
import GaloisForLFunctions.RHTower.XiRelativeGammaAnomalyCompactReduction

/-!
# Source amplification forces internal reflection

Functional-equation reflection and a moderate unitary source-phase orbit survive at a hypothetical
off-line Xi divisor.  They are therefore external symmetries, not selectors.  This module tests a
strictly weaker dynamical condition than positivity at every gain: on the single fixed shell triple
`(1, 2, 3)`, nonnegative selectively amplified responses need only recur at arbitrarily large gain.

That cofinal recurrence already forces the divisor onto the critical line.  Consequently the
external reflection upgrades to a nonzero closed source-linear sewing, the unitary phase upgrades
to physical half-density transport, and the matched Gamma boundary system admits compact
reduction.  Conversely, every hypothetical off-line divisor has a finite gain threshold beyond
which all responses on the fixed triple are negative, even though external reflection, moderate
phase coherence, and relative Gamma matching remain intact.

This is a source-stability/internalization bridge, not an RH proof: the arithmetic source theorem
that would supply cofinal selective admissibility remains separate.
-/

open Complex Real

namespace RHTower

noncomputable section

/-- On the fixed shell triple `(1, 2, 3)`, the selectively amplified response returns to the
nonnegative determinant chamber at arbitrarily large gains.  No uniform positivity in the gain or
in the shell variables is assumed. -/
def XiOrbitCofinalSelectiveCubicAdmissible (q : XiZeroCopy) : Prop :=
  ∀ R : ℝ, ∃ r : ℝ, R ≤ r ∧
    0 ≤ symmetricThreePointDet
      (thetaCuspHawkingSelectiveModularGainKernel q r) 1 2 3

/-- Cofinal recurrence in one fixed cubic chamber excludes nonzero transverse displacement. -/
theorem xiOrbitCofinalSelectiveCubicAdmissible_re_eq_half
    (q : XiZeroCopy)
    (hadmissible : XiOrbitCofinalSelectiveCubicAdmissible q) :
    (q.1 : ℂ).re = 1 / 2 := by
  by_contra hoff
  obtain ⟨R, hnegative⟩ :=
    exists_eventually_negative_thetaCuspHawkingSelectiveModularGainKernel_threePointDet
      q hoff (x := 1) (y := 2) (z := 3)
        (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨r, hr, hnonnegative⟩ := hadmissible R
  have hnegative' := hnegative r hr
  linarith

/-- **Internalization law.** Cofinal selective source stability upgrades external reflection to
closed prime-source sewing and physical half-density transport, and makes the uniquely matched
Gamma boundary system compactly reducible. -/
theorem xiOrbitCofinalSelectiveCubicAdmissible_internalReflection
    (p : Nat.Primes) (q : XiZeroCopy)
    (hadmissible : XiOrbitCofinalSelectiveCubicAdmissible q) :
    XiPrimePoissonReflectionSewing q.1 ∧
      XiGammaBoundaryAdmitsCompactReduction q ∧
      ∀ e : ℤ,
        ccmRationalAdelicPrimeXiSourcePhaseOrbit p q.1 (e - 1) =
          bilateralHalfDensityCharacter (p : ℕ) (q.1 : ℂ) *
            ccmRationalAdelicPrimeXiSourcePhaseOrbit p q.1 e := by
  have hline :=
    xiOrbitCofinalSelectiveCubicAdmissible_re_eq_half q hadmissible
  have hsewing : XiPrimePoissonReflectionSewing q.1 := by
    rw [xiPrimePoissonReflectionSewing_iff_internalOnly,
      xiDivisorSyndromeIsInternalOnly_iff_re_eq_half]
    exact hline
  refine ⟨hsewing, ?_,
    (xiPrimePoissonReflectionSewing_iff_sourcePhaseOrbit_physicalSewing p q.1).1
      hsewing⟩
  rw [xiGammaBoundaryAdmitsCompactReduction_iff_parameter_eq_zero,
    sourceHorizontalGammaSixPhysicalCharacterParameter_eq_zero_iff]
  exact hline

/-- **Off-line falsifier.** A hypothetical off-line divisor retains external reflection, a
nonzero moderate unitary source orbit, and relative Gamma matching, but fails cofinal selective
stability, internal sewing, and compact reduction. -/
theorem xiOffLine_externalReflection_cofinalCubicFalsifier
    (p : Nat.Primes) (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    ¬ XiOrbitCofinalSelectiveCubicAdmissible q ∧
      (MeromorphicOn.divisor xi Set.univ) (1 - (q.1 : ℂ)) =
        (MeromorphicOn.divisor xi Set.univ) (q.1 : ℂ) ∧
      ccmRationalAdelicPrimeXiSourcePhaseOrbit p q.1 ≠ 0 ∧
      bilateralModerate (ccmRationalAdelicPrimeXiSourcePhaseOrbit p q.1) ∧
      XiPrimePoissonReflectionDisjoint q.1 ∧
      ¬ XiPrimePoissonReflectionSewing q.1 ∧
      XiGammaBoundaryRelativeAnomalyMatched q
        (sourceHorizontalGammaSixPhysicalHolonomy q) ∧
      ¬ XiGammaBoundaryAdmitsCompactReduction q := by
  have hnotAdmissible : ¬ XiOrbitCofinalSelectiveCubicAdmissible q := by
    intro hadmissible
    exact hoff
      (xiOrbitCofinalSelectiveCubicAdmissible_re_eq_half q hadmissible)
  obtain ⟨hreflection, hphase, hmoderate, _, _, hdisjoint, hnosewing⟩ :=
    xiOffLine_externalPhase_without_internalSewing p q.1 hoff
  obtain ⟨hmatched, hnocompact⟩ :=
    xiGammaBoundary_relativeMatched_but_notCompact_of_offLine q hoff
  exact ⟨hnotAdmissible, hreflection, hphase, hmoderate, hdisjoint,
    hnosewing, hmatched, hnocompact⟩

/-- Global cofinal admissibility on one fixed triple is sufficient for RH.  This is weaker than
positivity for all shell triples and all gains. -/
theorem riemannHypothesis_of_forall_xiOrbitCofinalSelectiveCubicAdmissible
    (hadmissible : ∀ q : XiZeroCopy,
      XiOrbitCofinalSelectiveCubicAdmissible q) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
  intro rho
  simpa using
    xiOrbitCofinalSelectiveCubicAdmissible_re_eq_half
      (xiFirstZeroCopy rho) (hadmissible (xiFirstZeroCopy rho))

end

end RHTower

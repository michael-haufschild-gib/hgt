import GaloisForLFunctions.RHTower.PreDivisorTransverseDualNumberFormalNeighborhood
import GaloisForLFunctions.RHTower.ConstitutiveGammaCoronaTailRoosEmbedding
import GaloisForLFunctions.RHTower.XiTerminalMultiplicityCentralHolonomyTransgression

/-!
# Pre-divisor transverse ramification as a Roos transgression

The whole-plane reflection-normal dual-number arc has a coefficient-faithful realization in the
fixed-tail Roos `lim¹` obstruction space.  This makes formal ramification and derived completion
escape two structures on one transverse carrier, rather than parallel critical-line tests.

On an Xi fibre, this local derived class and the source-marked Fisher escape have the same zero
radical.  They are not identified as carriers: the critical Gamma response connecting them is
non-injective off neutral grade and therefore cannot preserve the source marker.  The protected
terminal multiplicity jet survives throughout.

This is a source-first whole-plane transgression and an exact falsification law.  It does not prove
global vanishing of the class and hence does not prove RH.
-/

open Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

open PreDivisorReflectionDefectStabilization
open GaloisForLFunctions.HTGeometry.BoundaryMigration

/-- Roos `lim¹` realization of the whole-plane transverse infinitesimal. -/
def preDivisorTransverseDerivedCompletionClass (s : ℂ) :
    DerivedLimitOne (fun _ : ℕ => routeRSummableSequenceIdeal)
      routeRTailRoosRestrictedBond :=
  routeRSummableHadamardToTailRoos
    (preDivisorTransverseCompletionDefect s)

/-- The transverse infinitesimal lands coefficient-for-coefficient in the first-wall Roos class. -/
theorem preDivisorTransverseDerivedCompletionClass_eq_criticalWall
    (s : ℂ) :
    preDivisorTransverseDerivedCompletionClass s =
      routeRDiagonalTailRoosClass
        (routeRPrimeGammaCriticalWallSequence (preDivisorCenteredRate s)) := by
  rw [preDivisorTransverseDerivedCompletionClass,
    preDivisorTransverseCompletionDefect,
    routeRSummableHadamardToTailRoos_criticalWall]

/-- The same class is the Roos image of the critically responded all-prime Bockstein. -/
theorem preDivisorTransverseDerivedCompletionClass_eq_criticalResponse
    (s : ℂ) :
    preDivisorTransverseDerivedCompletionClass s =
      constitutiveGammaCoronaToTailRoos
        (constitutiveGammaCoronaResponse
          ⟨|preDivisorCenteredRate s| / 2, by positivity⟩
          (primeGammaCofinalBockstein (preDivisorCenteredRate s))) := by
  rw [preDivisorTransverseDerivedCompletionClass_eq_criticalWall,
    constitutiveGammaCoronaToTailRoos_criticalResponse_bockstein]

/-- Source-marked response value: local critical response and untouched derived history travel in
parallel. -/
def preDivisorTransverseMarkedDerivedResponse (s : ℂ) :
    ConstitutiveGammaCorona ×
      DerivedLimitOne (fun _ : ℕ => routeRSummableSequenceIdeal)
        routeRTailRoosRestrictedBond :=
  constitutiveGammaTailRoosMarkedResponse
    ⟨|preDivisorCenteredRate s| / 2, by positivity⟩
    (primeGammaCofinalBockstein (preDivisorCenteredRate s))

/-- Exact two-coordinate law: the responded coordinate realizes local transverse ramification,
while the parallel Roos coordinate is the coefficient-faithful source-boundary escape. -/
theorem preDivisorTransverseMarkedDerivedResponse_coordinates (s : ℂ) :
    constitutiveGammaCoronaToTailRoos
        (preDivisorTransverseMarkedDerivedResponse s).1 =
        preDivisorTransverseDerivedCompletionClass s ∧
      (preDivisorTransverseMarkedDerivedResponse s).2 =
        routeRPrimeGammaFisherEscapeToTailRoos (preDivisorCenteredRate s)
          (routeRPrimeGammaFisherCompletionEscapeClass
            (preDivisorCenteredRate s)) := by
  constructor
  · rw [preDivisorTransverseMarkedDerivedResponse,
      constitutiveGammaTailRoosMarkedResponse,
      constitutiveGammaMarkedResponse]
    exact
      (preDivisorTransverseDerivedCompletionClass_eq_criticalResponse s).symm
  · rw [preDivisorTransverseMarkedDerivedResponse,
      constitutiveGammaTailRoosMarkedResponse,
      constitutiveGammaMarkedResponse]
    exact constitutiveBockstein_eq_sourceMarkedEscape_in_tailRoos
      (preDivisorCenteredRate s)

/-- The parallel Roos history repairs provenance loss at every response time. -/
theorem preDivisorTransverseMarkedResponse_injective (s : ℂ) :
    Function.Injective
      (constitutiveGammaTailRoosMarkedResponse
        ⟨|preDivisorCenteredRate s| / 2, by positivity⟩) :=
  constitutiveGammaTailRoosMarkedResponse_injective _

/-- Reflection reverses the derived completion class before any divisor is selected. -/
theorem preDivisorTransverseDerivedCompletionClass_lineConj (s : ℂ) :
    preDivisorTransverseDerivedCompletionClass (preDivisorLineConj s) =
      -preDivisorTransverseDerivedCompletionClass s := by
  rw [preDivisorTransverseDerivedCompletionClass,
    preDivisorTransverseCompletionDefect_lineConj, map_neg]
  rfl

/-- Coefficient-faithful transgression: the derived class is nonzero exactly off the wall. -/
theorem preDivisorTransverseDerivedCompletionClass_ne_zero_iff (s : ℂ) :
    preDivisorTransverseDerivedCompletionClass s ≠ 0 ↔ s.re ≠ 1 / 2 := by
  constructor
  · intro h
    apply (preDivisorTransverseCompletionDefect_ne_zero_iff s).1
    intro hzero
    apply h
    simp [preDivisorTransverseDerivedCompletionClass, hzero]
  · intro hoff hzero
    have himage :
        routeRSummableHadamardToTailRoos
            (preDivisorTransverseCompletionDefect s) =
          routeRSummableHadamardToTailRoos 0 := by
      simpa [preDivisorTransverseDerivedCompletionClass] using hzero
    exact (preDivisorTransverseCompletionDefect_ne_zero_iff s).2 hoff
      (routeRSummableHadamardToTailRoos_injective himage)

/-- Vanishing of the derived completion class is exactly the reflection wall. -/
theorem preDivisorTransverseDerivedCompletionClass_eq_zero_iff (s : ℂ) :
    preDivisorTransverseDerivedCompletionClass s = 0 ↔ s.re = 1 / 2 := by
  simpa only [not_ne_iff] using
    not_congr (preDivisorTransverseDerivedCompletionClass_ne_zero_iff s)

/-- Formal unramifiedness is precisely Roos exactness of the transgressed transverse class. -/
theorem preDivisorTransverseArcAlgebra_formallyUnramified_iff_derivedCompletionClass_eq_zero
    (s : ℂ) :
    Algebra.FormallyUnramified ℂ (PreDivisorTransverseArcAlgebra s) ↔
      preDivisorTransverseDerivedCompletionClass s = 0 := by
  rw [preDivisorTransverseArcAlgebra_formallyUnramified_iff,
    preDivisorTransverseDerivedCompletionClass_eq_zero_iff]

/-- On Xi support, local transverse Roos exactness and source-marked Fisher exactness have the
same zero radical.  This does not identify their carriers or erase the source marker. -/
theorem preDivisorTransverseDerivedCompletionClass_at_xiSupport_eq_zero_iff_escapeClass
    (rho : XiDivisorSupport) :
    preDivisorTransverseDerivedCompletionClass (rho : ℂ) = 0 ↔
      routeRPrimeGammaXiCompletionEscapeClass rho = 0 := by
  rw [preDivisorTransverseDerivedCompletionClass_eq_zero_iff,
    routeRPrimeGammaXiCompletionEscapeClass_eq_zero_iff_re_eq_half]

/-- Trivial central arithmetic holonomy is exactly Roos exactness of the transverse class. -/
theorem xiCentralHolonomyDefect_eq_zero_iff_transverseDerivedCompletionClass_eq_zero
    {n : ℕ} (hn : 2 ≤ n) (q : XiZeroCopy) :
    GaloisForLFunctions.IrregularStokes.centralHolonomyDefect n (q.1 : ℂ)
        (thetaInternalJetLeadingSourceCoefficient q.1) = 0 ↔
      preDivisorTransverseDerivedCompletionClass (q.1 : ℂ) = 0 := by
  rw [centralHolonomyDefect_eq_zero_iff_terminalMultiplicityCutLogGain_eq_zero,
    xiThetaTerminalMultiplicityCutLogGain_eq,
    primeDepthBVWoldXiCenteredRate,
    preDivisorTransverseDerivedCompletionClass_eq_zero_iff]
  have hlog : Real.log (n : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hn)))
  constructor
  · intro h
    have hmul :
        (2 * Real.log (n : ℝ)) * (2 * (q.1 : ℂ).re - 1) = 0 := by
      calc
        (2 * Real.log (n : ℝ)) * (2 * (q.1 : ℂ).re - 1) =
            2 * (((2 * Real.log (n : ℝ)) * (2 * (q.1 : ℂ).re - 1)) / 2) := by ring
        _ = 0 := by rw [h]; ring
    have hrate : 2 * (q.1 : ℂ).re - 1 = 0 :=
      (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero (by norm_num) hlog)
    linarith
  · intro hline
    rw [hline]
    ring

/-- Differential-character closure across local geometry and derived completion.  Multiplicity
survives while holonomy, formal ramification, Roos escape, and source-boundary escape share one
zero radical. -/
theorem xiProtectedMultiplicityHolonomyRamificationRoos_transgression
    {n : ℕ} (hn : 2 ≤ n) (q : XiZeroCopy) :
    xiThetaTerminalMultiplicityCutJet q.1 0 ≠ 0 ∧
      (GaloisForLFunctions.IrregularStokes.centralHolonomyDefect n (q.1 : ℂ)
          (thetaInternalJetLeadingSourceCoefficient q.1) = 0 ↔
        Algebra.FormallyUnramified ℂ
          (PreDivisorTransverseArcAlgebra (q.1 : ℂ))) ∧
      (Algebra.FormallyUnramified ℂ
          (PreDivisorTransverseArcAlgebra (q.1 : ℂ)) ↔
        preDivisorTransverseDerivedCompletionClass (q.1 : ℂ) = 0) ∧
      (preDivisorTransverseDerivedCompletionClass (q.1 : ℂ) = 0 ↔
        routeRPrimeGammaXiCompletionEscapeClass q.1 = 0) := by
  have hformal :=
    preDivisorTransverseArcAlgebra_formallyUnramified_iff_derivedCompletionClass_eq_zero
      (q.1 : ℂ)
  exact
    ⟨xiThetaTerminalMultiplicityCutJet_ne_zero q.1 0,
      (xiCentralHolonomyDefect_eq_zero_iff_transverseDerivedCompletionClass_eq_zero
        hn q).trans hformal.symm,
      hformal,
      preDivisorTransverseDerivedCompletionClass_at_xiSupport_eq_zero_iff_escapeClass q.1⟩

/-- Off-line Xi support falsifies every triviality clause while the multiplicity jet survives;
the critical response realizing the local class is additionally not provenance-faithful. -/
theorem xiOffLine_falsifies_holonomyRamificationRoos_exactness
    {n : ℕ} (hn : 2 ≤ n) (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    GaloisForLFunctions.IrregularStokes.centralHolonomyDefect n (q.1 : ℂ)
        (thetaInternalJetLeadingSourceCoefficient q.1) ≠ 0 ∧
      ¬ Algebra.FormallyUnramified ℂ
        (PreDivisorTransverseArcAlgebra (q.1 : ℂ)) ∧
      preDivisorTransverseDerivedCompletionClass (q.1 : ℂ) ≠ 0 ∧
      routeRTailRoosExactnessFlag ∈ ExFlag.survival
        (routeRPrimeGammaFixedGradeTailLanding
          (2 * (q.1 : ℂ).re - 1) routeRPrimeGammaFisherSourceBoundary) ∧
      xiThetaTerminalMultiplicityCutJet q.1 0 ≠ 0 ∧
      ¬ Function.Injective
        (constitutiveGammaCoronaResponse
          ⟨|preDivisorCenteredRate (q.1 : ℂ)| / 2, by positivity⟩) := by
  have hderived : preDivisorTransverseDerivedCompletionClass (q.1 : ℂ) ≠ 0 :=
    (preDivisorTransverseDerivedCompletionClass_ne_zero_iff (q.1 : ℂ)).2 hoff
  have hholonomy :
      GaloisForLFunctions.IrregularStokes.centralHolonomyDefect n (q.1 : ℂ)
          (thetaInternalJetLeadingSourceCoefficient q.1) ≠ 0 := by
    intro hzero
    exact hderived
      ((xiCentralHolonomyDefect_eq_zero_iff_transverseDerivedCompletionClass_eq_zero
        hn q).1 hzero)
  have hrate : preDivisorCenteredRate (q.1 : ℂ) ≠ 0 := by
    rw [preDivisorCenteredRate]
    intro hzero
    apply hoff
    linarith
  have hstrip : |preDivisorCenteredRate (q.1 : ℂ)| < 1 := by
    simpa [preDivisorCenteredRate] using xiCenteredPrimeIdealRate_abs_lt_one q.1
  exact
    ⟨hholonomy,
      preDivisorTransverseArcAlgebra_not_formallyUnramified_of_offWall
        (q.1 : ℂ) hoff,
      hderived,
      (routeRPrimeGammaXiCompletionDefect_survives_iff_re_ne_half q.1).2 hoff,
      xiThetaTerminalMultiplicityCutJet_ne_zero q.1 0,
      constitutiveGammaCoronaResponse_critical_not_injective hstrip hrate⟩

/-- Off-line specialization proves the categorical repair law: local response alone forgets
source provenance, whereas adjoining the parallel derived-history coordinate is faithful and its
two coordinates are exactly local ramification and source-boundary escape. -/
theorem xiOffLine_requires_parallelDerivedHistoryMarker
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    (¬ Function.Injective
      (constitutiveGammaCoronaResponse
        ⟨|preDivisorCenteredRate (q.1 : ℂ)| / 2, by positivity⟩)) ∧
      Function.Injective
        (constitutiveGammaTailRoosMarkedResponse
          ⟨|preDivisorCenteredRate (q.1 : ℂ)| / 2, by positivity⟩) ∧
      constitutiveGammaCoronaToTailRoos
          (preDivisorTransverseMarkedDerivedResponse (q.1 : ℂ)).1 =
        preDivisorTransverseDerivedCompletionClass (q.1 : ℂ) ∧
      (preDivisorTransverseMarkedDerivedResponse (q.1 : ℂ)).2 =
        routeRPrimeGammaFisherEscapeToTailRoos
          (preDivisorCenteredRate (q.1 : ℂ))
          (routeRPrimeGammaFisherCompletionEscapeClass
            (preDivisorCenteredRate (q.1 : ℂ))) := by
  have hrate : preDivisorCenteredRate (q.1 : ℂ) ≠ 0 := by
    rw [preDivisorCenteredRate]
    intro hzero
    apply hoff
    linarith
  have hstrip : |preDivisorCenteredRate (q.1 : ℂ)| < 1 := by
    simpa [preDivisorCenteredRate] using xiCenteredPrimeIdealRate_abs_lt_one q.1
  exact
    ⟨constitutiveGammaCoronaResponse_critical_not_injective hstrip hrate,
      preDivisorTransverseMarkedResponse_injective (q.1 : ℂ),
      (preDivisorTransverseMarkedDerivedResponse_coordinates (q.1 : ℂ)).1,
      (preDivisorTransverseMarkedDerivedResponse_coordinates (q.1 : ℂ)).2⟩

end

end RHTower

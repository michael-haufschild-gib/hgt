import GaloisForLFunctions.RHTower.XiInternalTransverseCompletionSyndrome
import GaloisForLFunctions.RHTower.XiSourceSpinThinningCoherence

/-!
# Transverse completion is exactly source-spin non-descent

Two independently constructed Xi channels detect the same horizontal obstruction.

* Route R produces a stationary square-zero class in the summable Hadamard corona.
* The literal theta half-density tests whether the centered Xi character descends through the
  logarithmic cover without changing its ambient spin sector.

This file proves that the completion class vanishes exactly when theta spin descends.  Hence an
off-line divisor point retains its nonzero internal square-zero divisor channel, but necessarily
carries a nonzero transverse completion class and changes the source spin.  The result does not
assume a new global source-coherence principle; it identifies the exact object that such a
principle would have to annihilate.
-/

open Complex Matrix

namespace RHTower

noncomputable section

/-- Route-R transverse completion triviality is exactly preservation of the literal theta
half-density spin sector by the centered Xi deformation. -/
theorem xiTransverseCompletionDefect_eq_zero_iff_thetaSpinCoherent
    (rho : XiDivisorSupport) :
    xiTransverseCompletionDefect rho = 0 ↔
      XiCenteredThetaSpinCoherent rho := by
  have hdefect : xiTransverseCompletionDefect rho = 0 ↔
      (rho : ℂ).re = 1 / 2 :=
    (xiTransverseCompletionDefect_eq_zero_iff_eulerWickOrientation rho).trans
      (GaloisForLFunctions.RHTower.eulerWickPrimitiveCompletedJetGradedRealAt_iff_re_eq_half
        (rho : ℂ))
  have hspin : XiCenteredThetaSpinCoherent rho ↔
      (rho : ℂ).re = 1 / 2 :=
    (xiCenteredThetaSpinCoherent_iff_thinningCoherent rho).trans
      (xiCenteredThetaSpinThinningCoherent_iff_re_eq_half rho)
  exact hdefect.trans hspin.symm

/-- The same completion class is the exact obstruction to reporter-faithful three-slot thinning
of the actual centered monodromy into the neutral ambient theta spin. -/
theorem xiTransverseCompletionDefect_eq_zero_iff_thetaSpinThinningCoherent
    (rho : XiDivisorSupport) :
    xiTransverseCompletionDefect rho = 0 ↔
      XiCenteredThetaSpinThinningCoherent rho := by
  exact (xiTransverseCompletionDefect_eq_zero_iff_thetaSpinCoherent rho).trans
    (xiCenteredThetaSpinCoherent_iff_thinningCoherent rho)

/-- Transverse completion triviality is exactly descent of the centered Xi character through the
complex logarithmic cover. -/
theorem xiTransverseCompletionDefect_eq_zero_iff_logCharacterDescends
    (rho : XiDivisorSupport) :
    xiTransverseCompletionDefect rho = 0 ↔
      XiCenteredLogCharacterDescends rho := by
  exact
    (xiTransverseCompletionDefect_eq_zero_iff_thetaSpinThinningCoherent rho).trans
      (xiCenteredThetaSpinThinningCoherent_iff_logCharacterDescends rho)

/-- At every prime, the Route-R transverse class vanishes exactly when the noncensoring terminal
multiplicity jet descends. -/
theorem xiTransverseCompletionDefect_eq_zero_iff_terminalMultiplicityJetDescends
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    xiTransverseCompletionDefect rho = 0 ↔
      FrankensteinXiPrimeThetaTerminalMultiplicityJetDescendsAt p rho := by
  exact
    (xiTransverseCompletionDefect_eq_zero_iff_thetaSpinThinningCoherent rho).trans
      (xiCenteredThetaSpinThinningCoherent_iff_terminalMultiplicityJetDescends p rho)

/-- Hostile off-line witness.  Internal divisor nilpotence survives, but the distinct transverse
completion class is nonzero and every equivalent source-spin/log-cover descent condition fails. -/
theorem xiDivisor_offLine_internalChannel_and_transverseSpinNonDescent
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    (∃ n : ℕ,
      GaloisForLFunctions.RHTower.eulerWickCompletedJetExtension (rho : ℂ) n ≠ 0 ∧
      GaloisForLFunctions.RHTower.eulerWickCompletedJetExtension (rho : ℂ) n *
        GaloisForLFunctions.RHTower.eulerWickCompletedJetExtension (rho : ℂ) n = 0) ∧
    xiTransverseCompletionDefect rho ≠ 0 ∧
    xiTransverseCompletionDefect rho ^ 2 = 0 ∧
    routeRSummableHadamardShiftEquiv (xiTransverseCompletionDefect rho) =
      xiTransverseCompletionDefect rho ∧
    ¬ XiCenteredThetaSpinCoherent rho ∧
    ¬ XiCenteredThetaSpinThinningCoherent rho ∧
    ¬ XiCenteredLogCharacterDescends rho ∧
    ¬ FrankensteinXiPrimeThetaTerminalMultiplicityJetDescendsAt p rho := by
  have hinterior :=
    (xiDivisor_internal_nonzero_transverse_stationary_squareZero rho).1
  obtain ⟨htransverse, hsquare, hstationary, -⟩ :=
    xiDivisor_offLine_transverse_completion_defect rho hoff
  have hspin : ¬ XiCenteredThetaSpinCoherent rho :=
    (xiTransverseCompletionDefect_eq_zero_iff_thetaSpinCoherent rho).not.mp
      htransverse
  have hthinning : ¬ XiCenteredThetaSpinThinningCoherent rho :=
    (xiTransverseCompletionDefect_eq_zero_iff_thetaSpinThinningCoherent rho).not.mp
      htransverse
  have hlog : ¬ XiCenteredLogCharacterDescends rho :=
    (xiTransverseCompletionDefect_eq_zero_iff_logCharacterDescends rho).not.mp
      htransverse
  have hterminal :
      ¬ FrankensteinXiPrimeThetaTerminalMultiplicityJetDescendsAt p rho :=
    (xiTransverseCompletionDefect_eq_zero_iff_terminalMultiplicityJetDescends p rho).not.mp
      htransverse
  exact ⟨hinterior, htransverse, hsquare, hstationary,
    hspin, hthinning, hlog, hterminal⟩

end

end RHTower

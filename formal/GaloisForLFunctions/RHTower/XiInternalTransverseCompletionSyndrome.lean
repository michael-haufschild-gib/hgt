import GaloisForLFunctions.RHTower.RouteRSummableHadamardConstitutiveCoronaEmbedding
import GaloisForLFunctions.RHTower.EulerSquarefreeWickCompletedJetOrientationRigidity
import GaloisForLFunctions.RHTower.PrimeDepthBVWoldCurvedSourceDifferential

/-!
# Internal/transverse completion syndrome on the Xi divisor

Two independently constructed nilpotent channels play different roles on the Xi divisor.

* The completed EWQ jet bundle has a nonzero square-zero matrix channel at every Xi zero.
  This is the internal divisor channel and must not be removed by a global reducedness axiom.
* The Route-R critical wall gives a stationary square-zero class in the summable Hadamard corona.
  It is nonzero exactly away from neutral horizontal grade and maps coefficient-for-coefficient to
  the existing physical constitutive Gamma wall class.

The EWQ all-order orientation law holds exactly when the transverse class vanishes.  Consequently
RH is equivalent to every Xi-divisor syndrome being internal-only: internal nilpotence survives,
while transverse completion nilpotence is absent.  This separates divisor existence/multiplicity
from horizontal placement without postulating that all zeros have one internal cause.
-/

open Complex Matrix

namespace RHTower

noncomputable section

/-- Divisor-resolved transverse completion class in the multiplicative summable corona. -/
def xiTransverseCompletionDefect
    (rho : XiDivisorSupport) : RouteRSummableHadamardCorona :=
  routeRPrimeGammaCriticalWallSummableHadamardClass
    (primeDepthBVWoldXiCenteredRate rho)

/-- A lifted critical-wall defect vanishes exactly at neutral grade. -/
theorem routeRPrimeGammaCriticalWallSummableHadamardClass_eq_zero_iff
    (t : ℝ) :
    routeRPrimeGammaCriticalWallSummableHadamardClass t = 0 ↔ t = 0 := by
  simpa only [not_ne_iff] using
    not_congr (routeRPrimeGammaCriticalWallSummableHadamardClass_ne_zero_iff t)

/-- Exact bridge between Route-R transverse triviality and intrinsic EWQ all-order orientation. -/
theorem xiTransverseCompletionDefect_eq_zero_iff_eulerWickOrientation
    (rho : XiDivisorSupport) :
    xiTransverseCompletionDefect rho = 0 ↔
      GaloisForLFunctions.RHTower.EulerWickPrimitiveCompletedJetGradedRealAt
        (rho : ℂ) := by
  rw [xiTransverseCompletionDefect,
    routeRPrimeGammaCriticalWallSummableHadamardClass_eq_zero_iff,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]
  exact
    (GaloisForLFunctions.RHTower.eulerWickPrimitiveCompletedJetGradedRealAt_iff_re_eq_half
      (rho : ℂ)).symm

/-- Functional-equation reflection reverses the transverse completion orientation. -/
theorem xiTransverseCompletionDefect_lineConj
    (rho : XiDivisorSupport) :
    xiTransverseCompletionDefect (xiZeroLineConjEquiv rho) =
      -xiTransverseCompletionDefect rho := by
  rw [xiTransverseCompletionDefect, primeDepthBVWoldXiCenteredRate_reflection,
    routeRPrimeGammaCriticalWallSummableHadamardClass_neg,
    xiTransverseCompletionDefect]

/-- Every Xi-divisor point has a nonzero square-zero internal EWQ channel, while its transverse
Route-R class is square-zero and stationary.  Only transverse nonvanishing remains variable. -/
theorem xiDivisor_internal_nonzero_transverse_stationary_squareZero
    (rho : XiDivisorSupport) :
    (∃ n : ℕ,
      GaloisForLFunctions.RHTower.eulerWickCompletedJetExtension (rho : ℂ) n ≠ 0 ∧
      GaloisForLFunctions.RHTower.eulerWickCompletedJetExtension (rho : ℂ) n *
        GaloisForLFunctions.RHTower.eulerWickCompletedJetExtension (rho : ℂ) n = 0) ∧
    xiTransverseCompletionDefect rho ^ 2 = 0 ∧
    routeRSummableHadamardShiftEquiv (xiTransverseCompletionDefect rho) =
      xiTransverseCompletionDefect rho := by
  refine
    ⟨(GaloisForLFunctions.RHTower.eulerWickCompletedJetExtension_nonzero_squareZero_iff
      (rho : ℂ)).2 (xi_eq_zero_of_mem_divisor_support rho), ?_, ?_⟩
  · exact routeRPrimeGammaCriticalWallSummableHadamardClass_sq_zero _
  · exact routeRPrimeGammaCriticalWallSummableHadamardClass_shift_fixed _

/-- Off-line divisor points have a literal nonzero stationary square-zero transverse completion
class and fail EWQ orientation, while retaining the internal square-zero divisor channel. -/
theorem xiDivisor_offLine_transverse_completion_defect
    (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    xiTransverseCompletionDefect rho ≠ 0 ∧
    xiTransverseCompletionDefect rho ^ 2 = 0 ∧
    routeRSummableHadamardShiftEquiv (xiTransverseCompletionDefect rho) =
      xiTransverseCompletionDefect rho ∧
    ¬ GaloisForLFunctions.RHTower.EulerWickPrimitiveCompletedJetGradedRealAt
      (rho : ℂ) := by
  have hrate : primeDepthBVWoldXiCenteredRate rho ≠ 0 :=
    (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).not.mpr hoff
  refine
    ⟨(routeRPrimeGammaCriticalWallSummableHadamardClass_ne_zero_iff _).2 hrate,
      routeRPrimeGammaCriticalWallSummableHadamardClass_sq_zero _,
      routeRPrimeGammaCriticalWallSummableHadamardClass_shift_fixed _, ?_⟩
  exact
    (GaloisForLFunctions.RHTower.eulerWickPrimitiveCompletedJetGradedRealAt_iff_re_eq_half
      (rho : ℂ)).not.mpr hoff

/-- A divisor syndrome is internal-only when the unavoidable internal square-zero EWQ channel is
present but the transverse completion class vanishes. -/
def XiDivisorSyndromeIsInternalOnly (rho : XiDivisorSupport) : Prop :=
  (∃ n : ℕ,
      GaloisForLFunctions.RHTower.eulerWickCompletedJetExtension (rho : ℂ) n ≠ 0 ∧
      GaloisForLFunctions.RHTower.eulerWickCompletedJetExtension (rho : ℂ) n *
        GaloisForLFunctions.RHTower.eulerWickCompletedJetExtension (rho : ℂ) n = 0) ∧
    xiTransverseCompletionDefect rho = 0

/-- Internal-only syndrome is exactly intrinsic EWQ completed-jet orientation. -/
theorem xiDivisorSyndromeIsInternalOnly_iff_eulerWickOrientation
    (rho : XiDivisorSupport) :
    XiDivisorSyndromeIsInternalOnly rho ↔
      GaloisForLFunctions.RHTower.EulerWickPrimitiveCompletedJetGradedRealAt
        (rho : ℂ) := by
  constructor
  · rintro ⟨_, htransverse⟩
    exact
      (xiTransverseCompletionDefect_eq_zero_iff_eulerWickOrientation rho).mp
        htransverse
  · intro horientation
    exact
      ⟨(xiDivisor_internal_nonzero_transverse_stationary_squareZero rho).1,
        (xiTransverseCompletionDefect_eq_zero_iff_eulerWickOrientation rho).mpr
          horientation⟩

/-- Internal-only syndrome is exactly critical-line placement. -/
theorem xiDivisorSyndromeIsInternalOnly_iff_re_eq_half
    (rho : XiDivisorSupport) :
    XiDivisorSyndromeIsInternalOnly rho ↔ (rho : ℂ).re = 1 / 2 := by
  rw [xiDivisorSyndromeIsInternalOnly_iff_eulerWickOrientation,
    GaloisForLFunctions.RHTower.eulerWickPrimitiveCompletedJetGradedRealAt_iff_re_eq_half]

/-- **Internal/transverse reformulation of RH.** Every Xi divisor retains a nonzero internal
square-zero EWQ channel, but no Xi divisor has a transverse completion defect. -/
theorem everyXiDivisorSyndromeIsInternalOnly_iff_riemannHypothesis :
    (∀ rho : XiDivisorSupport, XiDivisorSyndromeIsInternalOnly rho) ↔
      RiemannHypothesis := by
  constructor
  · intro hall
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro s hs
    let rho : XiDivisorSupport := ⟨s, mem_xi_divisor_support_of_eq_zero hs⟩
    exact (xiDivisorSyndromeIsInternalOnly_iff_re_eq_half rho).mp (hall rho)
  · intro hRH rho
    apply (xiDivisorSyndromeIsInternalOnly_iff_re_eq_half rho).mpr
    exact (riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH)
      (rho : ℂ) (xi_eq_zero_of_mem_divisor_support rho)

end

end RHTower

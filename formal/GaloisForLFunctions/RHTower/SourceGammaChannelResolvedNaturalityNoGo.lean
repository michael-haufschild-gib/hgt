import GaloisForLFunctions.RHTower.SourceGammaNaturalitySharedGhostProducer
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFECocycleHyperbolicModulusOrientation
import GaloisForLFunctions.RHTower.FZZCigarParityDeningerInformationWardTransmutation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekFZZDeningerWardTransmutation
import GaloisForLFunctions.RHTower.ReflectedBiHeatFZZDeningerInformationWardTransmutation

/-!
# Channel-resolved source/Gamma naturality is nonselective

The common Ward producer shared by HB, FZZ-P, PW-B, and RBH asks one source-derived
archimedean component to repair the inverse-Gamma rotations at primes two and three.  A possible
escape is to retain the two prime labels in separate output channels before scalarization.

This file classifies that escape on the genuine Calderon--Witt prime--archimedean Green
boundaries.  Pair the two canonical scalar reporters, fitting the first archimedean component at
prime two and the second at prime three.  The resulting `C^2`-valued reporter is separately natural
after projecting each boundary to its matching channel at every horizontal grade.  Its cross-channel
leaks are exact opposites:

`(0, 2^(-t) - 3^(-t))` and `(3^(-t) - 2^(-t), 0)`.

Thus channel-projected naturality is unconditional and cannot force Ward extinction.  Requiring
joint naturality of the full two-channel output forces the two fitted ghosts to coincide, hence
`t = 0`.  On actual Xi support, universal joint naturality is equivalent to RH and to the common
HB/FZZ-P/PW-B/RBH Ward endpoint.

This kills direct-sum/channel-resolved source naturality as a producer in

`source/Gamma naturality -> common Ward extinction -> HB = FZZ-P = PW-B = RBH -> RH`.

The exact survivor is irreducible cross-prime coupling before channel projection or scalarization.

`[NEW] [SHARED-WARD ROUTE-CLASS NO-GO] [SOURCE-PURE] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Two retained prime-labelled reporter channels. -/
abbrev PrimeGammaTwoChannel := ℂ × ℂ

/-- Canonical channel-resolved reporter.  Its two archimedean components are fitted independently
to the prime-two and prime-three inverse-Gamma ghosts. -/
def deningerCalderonWittChannelResolvedInverseGammaReporter
    (t : ℝ) :
    (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) →ₗ[ℂ]
      PrimeGammaTwoChannel :=
  (deningerCalderonWittInverseGammaGhostReporter t
      (primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeTwo)).prod
    (deningerCalderonWittInverseGammaGhostReporter t
      (primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeThree))

/-- On the prime-two boundary, the matching channel vanishes and the other channel retains the
exact two-prime ghost mismatch. -/
theorem deningerCalderonWittChannelResolvedInverseGammaReporter_twoBoundary
    (t : ℝ) :
    deningerCalderonWittChannelResolvedInverseGammaReporter t
        (deningerCalderonWittGlobalOrientedBoundary
          (deningerCalderonWittPrimeArchOrientationGreenBoundaryWitness
            deningerCalderonWittPrimeTwo)) =
      (0,
        (primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeTwo : ℂ) -
          primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeThree) := by
  ext <;>
    simp [deningerCalderonWittChannelResolvedInverseGammaReporter,
      deningerCalderonWittInverseGammaGhostReporter_primeArchBoundary]

/-- On the prime-three boundary, the matching channel vanishes and the other channel retains the
oppositely oriented two-prime ghost mismatch. -/
theorem deningerCalderonWittChannelResolvedInverseGammaReporter_threeBoundary
    (t : ℝ) :
    deningerCalderonWittChannelResolvedInverseGammaReporter t
        (deningerCalderonWittGlobalOrientedBoundary
          (deningerCalderonWittPrimeArchOrientationGreenBoundaryWitness
            deningerCalderonWittPrimeThree)) =
      ((primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeThree : ℂ) -
          primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeTwo,
        0) := by
  ext <;>
    simp [deningerCalderonWittChannelResolvedInverseGammaReporter,
      deningerCalderonWittInverseGammaGhostReporter_primeArchBoundary]

/-- Weak direct-sum naturality: each prime boundary is tested only in its matching channel. -/
def PrimeGammaTwoThreeChannelProjectedNaturality (t : ℝ) : Prop :=
  (deningerCalderonWittChannelResolvedInverseGammaReporter t
      (deningerCalderonWittGlobalOrientedBoundary
        (deningerCalderonWittPrimeArchOrientationGreenBoundaryWitness
          deningerCalderonWittPrimeTwo))).1 = 0 ∧
  (deningerCalderonWittChannelResolvedInverseGammaReporter t
      (deningerCalderonWittGlobalOrientedBoundary
        (deningerCalderonWittPrimeArchOrientationGreenBoundaryWitness
          deningerCalderonWittPrimeThree))).2 = 0

/-- Projected naturality holds at every horizontal grade; it is not a Ward selector. -/
theorem primeGammaTwoThreeChannelProjectedNaturality (t : ℝ) :
    PrimeGammaTwoThreeChannelProjectedNaturality t := by
  rw [PrimeGammaTwoThreeChannelProjectedNaturality,
    deningerCalderonWittChannelResolvedInverseGammaReporter_twoBoundary,
    deningerCalderonWittChannelResolvedInverseGammaReporter_threeBoundary]
  simp

/-- Strong joint naturality: each genuine source boundary must vanish in the full two-channel
output, so cross-prime leakage is visible. -/
def PrimeGammaTwoThreeChannelJointNaturality (t : ℝ) : Prop :=
  deningerCalderonWittChannelResolvedInverseGammaReporter t
      (deningerCalderonWittGlobalOrientedBoundary
        (deningerCalderonWittPrimeArchOrientationGreenBoundaryWitness
          deningerCalderonWittPrimeTwo)) = 0 ∧
  deningerCalderonWittChannelResolvedInverseGammaReporter t
      (deningerCalderonWittGlobalOrientedBoundary
        (deningerCalderonWittPrimeArchOrientationGreenBoundaryWitness
          deningerCalderonWittPrimeThree)) = 0

/-- Joint naturality recovers the shared-ghost wall exactly.  Extra direct-sum output dimension
does not weaken the common Ward condition once cross-channel leakage is retained. -/
theorem primeGammaTwoThreeChannelJointNaturality_iff (t : ℝ) :
    PrimeGammaTwoThreeChannelJointNaturality t ↔ t = 0 := by
  rw [PrimeGammaTwoThreeChannelJointNaturality,
    deningerCalderonWittChannelResolvedInverseGammaReporter_twoBoundary,
    deningerCalderonWittChannelResolvedInverseGammaReporter_threeBoundary]
  constructor
  · rintro ⟨htwo, _⟩
    have h23 :
        primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeTwo =
          primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeThree := by
      have h := congrArg Prod.snd htwo
      have hc :
          (primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeTwo : ℂ) =
            primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeThree := by
        exact sub_eq_zero.mp h
      exact_mod_cast hc
    have hshared : PrimeGammaTwoThreeSharedInverseOrientedGhostWard t := by
      refine ⟨primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeTwo,
        primeGammaLocalInverseOrientedGhost_pos t deningerCalderonWittPrimeTwo,
        primeGammaLocalInverseOrientedGhost_ward t deningerCalderonWittPrimeTwo, ?_⟩
      rw [h23]
      exact primeGammaLocalInverseOrientedGhost_ward t deningerCalderonWittPrimeThree
    exact (primeGammaTwoThreeSharedInverseOrientedGhostWard_iff t).mp hshared
  · rintro rfl
    simp [primeGammaLocalInverseOrientedGhost]

/-- Joint two-channel source/Gamma naturality at one actual Xi divisor. -/
def FrankensteinChannelResolvedGammaJointNaturalityAt
    (rho : XiDivisorSupport) : Prop :=
  PrimeGammaTwoThreeChannelJointNaturality (2 * (rho : ℂ).re - 1)

/-- Universal joint two-channel source/Gamma naturality over actual Xi support. -/
def EveryFrankensteinChannelResolvedGammaJointNaturality : Prop :=
  ∀ rho : XiDivisorSupport, FrankensteinChannelResolvedGammaJointNaturalityAt rho

/-- Pointwise joint channel naturality is exactly critical-line placement. -/
theorem frankensteinChannelResolvedGammaJointNaturalityAt_iff
    (rho : XiDivisorSupport) :
    FrankensteinChannelResolvedGammaJointNaturalityAt rho ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [FrankensteinChannelResolvedGammaJointNaturalityAt,
    primeGammaTwoThreeChannelJointNaturality_iff]
  constructor <;> intro h <;> linarith

/-- Universal joint channel naturality is exactly RH. -/
theorem everyFrankensteinChannelResolvedGammaJointNaturality_iff_riemannHypothesis :
    EveryFrankensteinChannelResolvedGammaJointNaturality ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho =>
      (frankensteinChannelResolvedGammaJointNaturalityAt_iff rho).mp (h rho)
  · intro h rho
    exact (frankensteinChannelResolvedGammaJointNaturalityAt_iff rho).mpr
      (xi_divisor_support_re_eq_half_of_rh h rho)

/-- Universal projected naturality over actual Xi support. -/
def EveryFrankensteinChannelResolvedGammaProjectedNaturality : Prop :=
  ∀ rho : XiDivisorSupport,
    PrimeGammaTwoThreeChannelProjectedNaturality (2 * (rho : ℂ).re - 1)

/-- Universal projected naturality is unconditional, including on every hypothetical off-line
divisor. -/
theorem everyFrankensteinChannelResolvedGammaProjectedNaturality :
    EveryFrankensteinChannelResolvedGammaProjectedNaturality := by
  intro rho
  exact primeGammaTwoThreeChannelProjectedNaturality _

/-- One proposition collecting the already proved common HB/FZZ-P/PW-B/RBH Ward endpoint. -/
def SharedFourRouteWardEndpoint : Prop :=
  (∀ q : XiZeroCopy,
    Complex.normSq (hbXiPeierlsUnitSourceFECocycle q) = 1) ∧
  FZZCigarParityDeningerInformationWardEquilibrium ∧
  SchwarzschildParikhWilczekBorelPartnerBalanced ∧
  (∀ rho : XiDivisorSupport,
    reflectedBiHeatMultiplicityLeadingJetNormImbalance rho = 0)

/-- Joint source/Gamma naturality is precisely the common four-route Ward endpoint. -/
theorem everyFrankensteinChannelResolvedGammaJointNaturality_iff_sharedFourRouteWardEndpoint :
    EveryFrankensteinChannelResolvedGammaJointNaturality ↔ SharedFourRouteWardEndpoint := by
  rw [everyFrankensteinChannelResolvedGammaJointNaturality_iff_riemannHypothesis]
  constructor
  · intro h
    refine ⟨(forall_normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff_rh).2 h,
      (fzzCigarParityDeningerInformationWardEquilibrium_iff_riemannHypothesis).2 h,
      (riemannHypothesis_iff_schwarzschildParikhWilczekBorelPartnerBalanced).1 h, ?_⟩
    exact (riemannHypothesis_iff_reflectedBiHeatMultiplicityLeadingJetNormImbalance_eq_zero).1 h
  · rintro ⟨h, _, _, _⟩
    exact (forall_normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff_rh).1 h

/-- **[SHARED-WARD ROUTE-CLASS KILL].** Channel-projected direct-sum naturality is universally
realized and hence nonselective.  Retaining the cross-channel leaks turns the same construction
into the exact HB/FZZ-P/PW-B/RBH Ward endpoint and therefore into an RH receiver, not an upstream
producer. -/
theorem sharedWardChannelResolvedGammaNaturalityRouteKilled :
    EveryFrankensteinChannelResolvedGammaProjectedNaturality ∧
      (EveryFrankensteinChannelResolvedGammaJointNaturality ↔
        SharedFourRouteWardEndpoint) ∧
      (EveryFrankensteinChannelResolvedGammaJointNaturality ↔ RiemannHypothesis) := by
  exact ⟨everyFrankensteinChannelResolvedGammaProjectedNaturality,
    everyFrankensteinChannelResolvedGammaJointNaturality_iff_sharedFourRouteWardEndpoint,
    everyFrankensteinChannelResolvedGammaJointNaturality_iff_riemannHypothesis⟩

end

end RHTower

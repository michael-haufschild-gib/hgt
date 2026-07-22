import GaloisForLFunctions.RHTower.PrimeSeamDampingAperture
import GaloisForLFunctions.RHTower.XiPrimeSeamCalkinGram
import GaloisForLFunctions.RHTower.XiPrimeSeamCofinalAnchoredEssentialNormDecay
import GaloisForLFunctions.RHTower.XiPrimeSeamHigherGradeCalkinRigidity
import GaloisForLFunctions.RHTower.XiPrimeSeamPairAsymptotics
import GaloisForLFunctions.RHTower.XiPrimeSeamSummableCalkinAggregate
import GaloisForLFunctions.RHTower.XiPrimeTwoThreeSeamRigidity

/-!
# Xi prime-seam Calkin universality

Two scalar seam norms at the fixed primes `2` and `3` carry the same datum as every currently
formalized all-prime energy-growth and Sonin-Calkin realization.  The complementary theorem
packages the operator and energy witnesses forced by failure of RH.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Simultaneous realization of prime-seam rigidity by every positive-aperture pairwise Gram,
all-prime aggregate, cofinal anchored commutator, fixed two--three packet, and fixed-prime
higher-grade Euler tail. -/
def XiPrimeSeamAllScaleCalkinCertificate : Prop :=
  (∀ a : ℝ, 0 < a → XiPrimeSeamCalkinGramCompact a) ∧
  (∀ a : ℝ, 0 < a → XiPrimeSeamSummableCalkinAggregateCompact a) ∧
  (∀ a : ℝ, 0 < a →
    XiCofinalFirstPrimeEulerCompressionEssentiallyCommuting a) ∧
  (∀ a : ℝ, 0 < a →
    XiCofinalFirstPrimeEulerCompressionEssentialNormDecay a) ∧
  (∀ a : ℝ, 0 < a → XiPrimeTwoThreeEulerOrientationGramCompact a) ∧
  (∀ a : ℝ, 0 < a →
    XiPrimeTwoThreeEulerCompressionEssentiallyCommuting a) ∧
  (∀ a : ℝ, 0 < a → ∀ p : Nat.Primes,
    XiPrimeEulerFEHigherGradeCompact a p)

/-- Every positive-aperture prime-seam Calkin chart is simultaneously rigid exactly under RH. -/
theorem xiPrimeSeamAllScaleCalkinCertificate_iff_riemannHypothesis :
    XiPrimeSeamAllScaleCalkinCertificate ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact (xiPrimeSeamCalkinGramCompact_iff_riemannHypothesis
      1 (by norm_num)).1 (h.1 1 (by norm_num))
  · intro hRH
    exact ⟨
      fun a ha =>
        (xiPrimeSeamCalkinGramCompact_iff_riemannHypothesis a ha).2 hRH,
      fun a ha =>
        (xiPrimeSeamSummableCalkinAggregateCompact_iff_riemannHypothesis
          a ha).2 hRH,
      fun a ha =>
        (xiCofinalFirstPrimeEulerCompressionEssentiallyCommuting_iff_riemannHypothesis
          a ha).2 hRH,
      fun a ha =>
        (xiCofinalFirstPrimeEulerCompressionEssentialNormDecay_iff_riemannHypothesis
          a ha).2 hRH,
      fun a ha =>
        (xiPrimeTwoThreeEulerOrientationGramCompact_iff_riemannHypothesis
          a ha).2 hRH,
      fun a ha =>
        (xiPrimeTwoThreeEulerCompressionEssentiallyCommuting_iff_riemannHypothesis
          a ha).2 hRH,
      fun a ha p =>
        (xiPrimeEulerFEHigherGradeCompact_iff_riemannHypothesis ha p).2 hRH⟩

/-- Simultaneous scalar, growth, damping, and all-scale Calkin realization of prime-seam rigidity. -/
def XiPrimeSeamCalkinUniversalCertificate : Prop :=
  XiPrimeSeamChargesCoherent ∧
  XiPrimeTwoThreeSeamChargesEqual ∧
  XiPrimeTwoThreeSeamNormsEqual ∧
  XiPrimeSeamPairEnergyBounded ∧
  XiPrimeSeamPairEnergySubmass ∧
  XiAllPositivePrimeSeamDamping ∧
  XiPrimeSeamAllScaleCalkinCertificate

/-- The two fixed diagonal seam norms already contain every positive-aperture prime-seam Calkin
chart. -/
theorem xiPrimeTwoThreeSeamNormsEqual_iff_allScaleCalkinCertificate :
    XiPrimeTwoThreeSeamNormsEqual ↔
      XiPrimeSeamAllScaleCalkinCertificate := by
  exact xiPrimeTwoThreeSeamNormsEqual_iff_riemannHypothesis.trans
    xiPrimeSeamAllScaleCalkinCertificate_iff_riemannHypothesis.symm

/-- **Xi prime-seam Calkin universality law.**  Equality of two scalar diagonal seam norms is
equivalent to the complete thirteen-chart prime-seam scalar, growth, damping, and all-scale
operator certificate. -/
theorem xiPrimeTwoThreeSeamNormsEqual_iff_calkinUniversalCertificate :
    XiPrimeTwoThreeSeamNormsEqual ↔
      XiPrimeSeamCalkinUniversalCertificate := by
  constructor
  · intro hnorm
    have hRH : RiemannHypothesis :=
      xiPrimeTwoThreeSeamNormsEqual_iff_riemannHypothesis.1 hnorm
    exact ⟨
      xiPrimeSeamChargesCoherent_iff_riemannHypothesis.2 hRH,
      xiPrimeTwoThreeSeamChargesEqual_iff_riemannHypothesis.2 hRH,
      hnorm,
      xiPrimeSeamPairEnergyBounded_iff_riemannHypothesis.2 hRH,
      xiPrimeSeamPairEnergySubmass_iff_riemannHypothesis.2 hRH,
      xiAllPositivePrimeSeamDamping_iff_riemannHypothesis.2 hRH,
      xiPrimeSeamAllScaleCalkinCertificate_iff_riemannHypothesis.2 hRH⟩
  · intro hcertificate
    exact xiPrimeTwoThreeSeamNormsEqual_iff_riemannHypothesis.2
      (xiPrimeSeamChargesCoherent_iff_riemannHypothesis.1 hcertificate.1)

/-- Simultaneous energy blowup and noncompact operator witnesses at one positive aperture. -/
def XiPrimeSeamCalkinFailureUniversalCertificate (a : ℝ) : Prop :=
  (∃ rho : XiDivisorSupport, ∀ B : ℝ, ∃ s : Finset Nat.Primes,
    B < primePairDifferenceEnergy
      (fun p : Nat.Primes =>
        orbitwiseNatPrimeSeamCharge (p : ℕ) (rho : ℂ)) s) ∧
  (∃ rho : XiDivisorSupport, ∃ p q : ℕ,
    Nat.Prime p ∧ Nat.Prime q ∧
      ¬ IsCompactOperator
        (orbitwisePrimeSeamCalkinGramCorner a p q (rho : ℂ))) ∧
  (∃ rho : XiDivisorSupport,
    ¬ OrbitwisePrimeSeamSummableCalkinAggregateCompact a (rho : ℂ)) ∧
  (∃ rho : XiDivisorSupport,
    ¬ IsCompactOperator
      (finiteArchimedeanEulerOrientationGram a
        (fun i ↦ (primeTwoThreePacket i : ℝ))
        (xiPrimeTwoThreeSeamPacket rho))) ∧
  (∃ rho : XiDivisorSupport,
    ¬ IsCompactOperator
      (finiteArchimedeanEulerCompression a
          (fun i ↦ (primeTwoThreePacket i : ℝ))
          (xiPrimeTwoThreeSeamPacket rho) *
        finiteArchimedeanEulerCompression a
          (fun i ↦ (primeTwoThreePacket i : ℝ)) (fun _ ↦ 1) -
        finiteArchimedeanEulerCompression a
          (fun i ↦ (primeTwoThreePacket i : ℝ)) (fun _ ↦ 1) *
        finiteArchimedeanEulerCompression a
          (fun i ↦ (primeTwoThreePacket i : ℝ))
          (xiPrimeTwoThreeSeamPacket rho))) ∧
  (∃ rho : XiDivisorSupport,
    ¬ IsCompactOperator
      (primeEulerFEHigherGradeArchimedeanCorner a
        (⟨2, by norm_num⟩ : Nat.Primes) (rho : ℂ).re))

/-- **Complementary prime-seam Calkin failure law.**  At every positive aperture, failure of RH
is equivalent to simultaneous pair-energy blowup and noncompactness witnesses in pairwise,
aggregate, fixed two--three Gram, fixed two--three commutator, and higher-grade charts. -/
theorem not_riemannHypothesis_iff_primeSeamCalkinFailureUniversalCertificate
    (a : ℝ) (ha : 0 < a) :
    ¬RiemannHypothesis ↔ XiPrimeSeamCalkinFailureUniversalCertificate a := by
  classical
  constructor
  · intro hnotRH
    have hnotGram : ¬XiPrimeTwoThreeEulerOrientationGramCompact a := by
      intro hcompact
      exact hnotRH
        ((xiPrimeTwoThreeEulerOrientationGramCompact_iff_riemannHypothesis
          a ha).1 hcompact)
    have hnotComm : ¬XiPrimeTwoThreeEulerCompressionEssentiallyCommuting a := by
      intro hcompact
      exact hnotRH
        ((xiPrimeTwoThreeEulerCompressionEssentiallyCommuting_iff_riemannHypothesis
          a ha).1 hcompact)
    have hnotHigher :
        ¬XiPrimeEulerFEHigherGradeCompact a
          (⟨2, by norm_num⟩ : Nat.Primes) := by
      intro hcompact
      exact hnotRH
        ((xiPrimeEulerFEHigherGradeCompact_iff_riemannHypothesis
          ha (⟨2, by norm_num⟩ : Nat.Primes)).1 hcompact)
    simp only [XiPrimeTwoThreeEulerOrientationGramCompact, not_forall] at hnotGram
    simp only [XiPrimeTwoThreeEulerCompressionEssentiallyCommuting,
      not_forall] at hnotComm
    simp only [XiPrimeEulerFEHigherGradeCompact, not_forall] at hnotHigher
    exact ⟨
      exists_xiPrimeSeamPairEnergy_unbounded_of_not_riemannHypothesis hnotRH,
      exists_noncompact_primeSeamCalkinGramCorner_of_not_riemannHypothesis
        a ha hnotRH,
      exists_noncompact_primeSeamSummableCalkinAggregate_of_not_riemannHypothesis
        a ha hnotRH,
      hnotGram,
      hnotComm,
      hnotHigher⟩
  · intro hcertificate hRH
    obtain ⟨rho, p, q, hp, hq, hnoncompact⟩ := hcertificate.2.1
    exact hnoncompact
      ((xiPrimeSeamCalkinGramCompact_iff_riemannHypothesis a ha).2 hRH
        rho p q hp hq)

end

end RHTower

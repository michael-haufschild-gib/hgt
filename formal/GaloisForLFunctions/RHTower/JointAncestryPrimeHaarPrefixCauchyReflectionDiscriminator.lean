import GaloisForLFunctions.RHTower.JointAncestryPrimeSeparatedLocalHaarCreatorCompression
import GaloisForLFunctions.RHTower.RouteRHarmonicQuantumGapCriterion

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

/-- Prefix half-likelihoods are Cauchy exactly when their local Hellinger defects are summable. -/
theorem cauchySeq_circlePoissonPrefixHalfLikelihoodLp_iff
    (a b : ℕ → CirclePoissonParameter) :
    CauchySeq (circlePoissonPrefixHalfLikelihoodLp a b) ↔
      Summable (fun n => 1 - circlePoissonHellingerAffinity (a n) (b n)) := by
  constructor
  · intro hcauchy
    by_contra hsum
    rw [Metric.cauchySeq_iff] at hcauchy
    obtain ⟨K, hK⟩ := hcauchy 1 zero_lt_one
    let aK : ℕ → CirclePoissonParameter := fun n => a (n + K)
    let bK : ℕ → CirclePoissonParameter := fun n => b (n + K)
    have hdivK : ¬ Summable (fun n =>
        1 - circlePoissonHellingerAffinity (aK n) (bK n)) := by
      intro htail
      apply hsum
      rw [← summable_nat_add_iff K]
      simpa [aK, bK] using htail
    have htend :=
      tendsto_circlePoissonPrefixAffinity_zero_of_not_summable aK bK hdivK
    obtain ⟨L, hL⟩ := (Metric.tendsto_atTop.1 htend) (1 / 2 : ℝ) (by norm_num)
    have hsmall := hL L le_rfl
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (circlePoissonPrefixAffinity_nonneg aK bK L)] at hsmall
    have haffinity : circlePoissonIntervalAffinity a b K (K + L) < 1 / 2 := by
      rw [circlePoissonIntervalAffinity, Finset.prod_Ico_eq_prod_range]
      simpa [circlePoissonPrefixAffinity, aK, bK, Nat.add_comm] using hsmall
    have hdist := hK K le_rfl (K + L) (Nat.le_add_right K L)
    rw [dist_eq_norm] at hdist
    have hnormsq := norm_sq_prefixHalfLikelihoodLp_sub a b (Nat.le_add_right K L)
    nlinarith [norm_nonneg
      (circlePoissonPrefixHalfLikelihoodLp a b K -
        circlePoissonPrefixHalfLikelihoodLp a b (K + L))]
  · exact cauchySeq_circlePoissonPrefixHalfLikelihoodLp a b

/-- Canonical finite-prime Haarization sequence inside the natural prime-Poisson product carrier. -/
def primePoissonHaarPrefixHalfLikelihoodLp
    (sigma t : ℝ) (hsigma : 0 < sigma) :
    ℕ → Lp ℝ 2
      (natCirclePoissonProductMeasure
        (primePoissonNaturalParameters sigma t hsigma)) :=
  circlePoissonPrefixHalfLikelihoodLp
    (fun _ => zeroCirclePoissonParameter)
    (primePoissonNaturalParameters sigma t hsigma)

/-- The canonical finite-prime local-Haar vacua are Cauchy exactly to the right of the critical
wall. -/
theorem cauchySeq_primePoissonHaarPrefixHalfLikelihoodLp_iff
    (sigma t : ℝ) (hsigma : 0 < sigma) :
    CauchySeq (primePoissonHaarPrefixHalfLikelihoodLp sigma t hsigma) ↔
      1 / 2 < sigma := by
  rw [primePoissonHaarPrefixHalfLikelihoodLp,
    cauchySeq_circlePoissonPrefixHalfLikelihoodLp_iff]
  constructor
  · intro hsum
    have hnormNat : Summable (fun n =>
        ‖(primePoissonNaturalParameters sigma t hsigma n : ℂ)‖ ^ 2) := by
      have hscaled : Summable (fun n => 8 *
          (1 - circlePoissonHellingerAffinity zeroCirclePoissonParameter
            (primePoissonNaturalParameters sigma t hsigma n))) :=
        hsum.mul_left 8
      refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) ?_ hscaled
      intro n
      have hlower := norm_sq_div_eight_le_one_sub_circlePoissonHellingerAffinity
        zeroCirclePoissonParameter (primePoissonNaturalParameters sigma t hsigma n)
      simp [zeroCirclePoissonParameter] at hlower
      change ‖(primePoissonNaturalParameters sigma t hsigma n : ℂ)‖ ^ 2 / 8 ≤
        1 - circlePoissonHellingerAffinity zeroCirclePoissonParameter
          (primePoissonNaturalParameters sigma t hsigma n) at hlower
      linarith
    have hprime : Summable (fun p : Nat.Primes =>
        ‖(primePoissonParameter sigma t hsigma p : ℂ) - 0‖ ^ 2) := by
      apply (Equiv.summable_iff natEquivPrimes).mp
      simpa [Function.comp_def, primePoissonNaturalParameters, sub_zero] using hnormNat
    exact (summable_normSq_primePoissonParameter_zero_iff sigma t hsigma).mp hprime
  · intro hright
    refine (summable_hellinger_primePoissonNaturalParameters sigma t hright).congr ?_
    intro n
    exact congrArg (fun x : ℝ => 1 - x)
      (circlePoissonHellingerAffinity_comm
        (primePoissonNaturalParameters sigma t hsigma n)
        zeroCirclePoissonParameter)

end

end GaloisForLFunctions.HTGeometry

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Forward and reflected canonical prime-to-Haar prefix half-likelihoods have the same Cauchy
status at one Xi divisor point. -/
def XiPrimePoissonHaarPrefixReflectionCauchyCoherent
    (rho : XiDivisorSupport) : Prop :=
  let hstrip := xi_divisor_support_re_mem_open_unit rho
  CauchySeq
      (primePoissonHaarPrefixHalfLikelihoodLp
        (rho : ℂ).re (rho : ℂ).im hstrip.1) ↔
    CauchySeq
      (primePoissonHaarPrefixHalfLikelihoodLp
        (1 - (rho : ℂ).re) (rho : ℂ).im (sub_pos.mpr hstrip.2))

/-- Reflection preserves the canonical local-Haar exhaustion's Cauchy status exactly on the
critical line. -/
theorem xiPrimePoissonHaarPrefixReflectionCauchyCoherent_iff
    (rho : XiDivisorSupport) :
    XiPrimePoissonHaarPrefixReflectionCauchyCoherent rho ↔
      (rho : ℂ).re = 1 / 2 := by
  let hstrip := xi_divisor_support_re_mem_open_unit rho
  rw [XiPrimePoissonHaarPrefixReflectionCauchyCoherent,
    cauchySeq_primePoissonHaarPrefixHalfLikelihoodLp_iff,
    cauchySeq_primePoissonHaarPrefixHalfLikelihoodLp_iff]
  constructor
  · intro hcoherent
    by_contra hhalf
    rcases lt_or_gt_of_ne hhalf with hleft | hright
    · have hreflected : 1 / 2 < 1 - (rho : ℂ).re := by linarith
      have hnotForward : ¬ 1 / 2 < (rho : ℂ).re := not_lt_of_ge hleft.le
      exact hnotForward (hcoherent.mpr hreflected)
    · have hnotReflected : ¬ 1 / 2 < 1 - (rho : ℂ).re := by linarith
      exact hnotReflected (hcoherent.mp hright)
  · intro hhalf
    rw [hhalf]
    norm_num

/-- Universal reflection-Cauchy coherence over the actual Xi divisor. -/
def EveryXiPrimePoissonHaarPrefixReflectionCauchyCoherent : Prop :=
  ∀ rho : XiDivisorSupport,
    XiPrimePoissonHaarPrefixReflectionCauchyCoherent rho

/-- The new infinite-support reflection discriminator is exactly RH.  This classifies the JAS
producer still required; it does not assert that producer. -/
theorem everyXiPrimePoissonHaarPrefixReflectionCauchyCoherent_iff_riemannHypothesis :
    EveryXiPrimePoissonHaarPrefixReflectionCauchyCoherent ↔ RiemannHypothesis := by
  constructor
  · intro hcoherent
    apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro rho
    exact (xiPrimePoissonHaarPrefixReflectionCauchyCoherent_iff rho).mp
      (hcoherent rho)
  · intro hRH rho
    exact (xiPrimePoissonHaarPrefixReflectionCauchyCoherent_iff rho).mpr
      (xi_divisor_support_re_eq_half_of_rh hRH rho)

end

end RHTower

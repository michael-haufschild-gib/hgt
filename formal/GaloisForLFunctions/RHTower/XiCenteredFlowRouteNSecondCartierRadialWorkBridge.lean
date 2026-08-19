import GaloisForLFunctions.RHTower.RiemannCenteredFlowCapacityIntertwining
import GaloisForLFunctions.RHTower.SourceHorizontalRouteNProjectiveCremonaInvolution
import GaloisForLFunctions.RHTower.HedenmalmPrimeTranslationCompletedRadialWorkEquivalence

/-!
# Bilateral centered-flow capacity is Route-N translation excess

Opposite prime times in the complete Cayley derivative-order packet retain both physical radial
orientations.  Weighting their sum by the critical Route-N channel `p⁻¹` produces one exact
pre-scalar trace.  Its excess above the critical trace is analytic multiplicity times the
reflection-symmetric theta prime-translation excess.

The excess is nonnegative and vanishes exactly on the critical line.  After multiplying by the
completed first-divided Xi response, its prime-two value is uniformly equivalent to literal
completed radial source work.  Thus the Route-P moderation problem, centered-flow conservation,
and Route-N prime translation have the same positive defect.

This module does not assert the missing source upper bound.  Determinant/countercharacter
conservation fixes the product of the two capacities, whereas moderation requires an independent
upper bound on their sum.
-/

open Complex Filter Topology
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Route-N critical weighting of the two opposite prime-time complete Cayley capacities. -/
def xiCenteredFlowBilateralPrimeCapacity
    (q : XiZeroCopy) (p : Nat.Primes) : ℝ :=
  routeNGammaSewnCriticalSquarefreeParityOdds p *
    (xiCenteredFlowRawCapacity q.1 (Real.log (p : ℝ)) +
      xiCenteredFlowRawCapacity q.1 (-Real.log (p : ℝ)))

/-- Excess of bilateral prime-time capacity above its critical trace, with analytic multiplicity
retained before scalarization. -/
def xiCenteredFlowBilateralPrimeCapacityExcess
    (q : XiZeroCopy) (p : Nat.Primes) : ℝ :=
  xiCenteredFlowBilateralPrimeCapacity q p -
    2 * xiCenteredFlowMultiplicityMass q.1 *
      routeNGammaSewnCriticalSquarefreeParityOdds p

/-- Exact coefficient- and multiplicity-faithful identification with the two theta translation
orientations. -/
theorem xiCenteredFlowBilateralPrimeCapacity_eq_translationPair
    (q : XiZeroCopy) (p : Nat.Primes) :
    xiCenteredFlowBilateralPrimeCapacity q p =
      xiCenteredFlowMultiplicityMass q.1 *
        routeNGammaSewnCriticalSquarefreeParityOdds p *
        (HedenmalmThetaSource.frankensteinThetaPrimeTranslationEnergy q p +
          HedenmalmThetaSource.frankensteinThetaPrimeTranslationEnergy
            (xiZeroCopyLineConjEquiv q) p) := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [xiCenteredFlowBilateralPrimeCapacity,
    xiCenteredFlowRawCapacity_eq, xiCenteredFlowRawCapacity_eq,
    HedenmalmThetaSource.frankensteinThetaPrimeTranslationEnergy_eq,
    HedenmalmThetaSource.frankensteinThetaPrimeTranslationEnergy_lineConj_eq]
  rw [sourceCayleyTransverseRate, primeDepthBVWoldXiCenteredRate]
  simp only [Complex.sub_re, Complex.one_re]
  rw [Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hp]
  ring_nf

/-- The centered-flow trace excess is exactly multiplicity times the Route-N critical channel
times theta translation-pair excess. -/
theorem xiCenteredFlowBilateralPrimeCapacityExcess_eq_translationPairExcess
    (q : XiZeroCopy) (p : Nat.Primes) :
    xiCenteredFlowBilateralPrimeCapacityExcess q p =
      xiCenteredFlowMultiplicityMass q.1 *
        routeNGammaSewnCriticalSquarefreeParityOdds p *
        HedenmalmThetaSource.frankensteinThetaPrimeTranslationPairExcess q p := by
  rw [xiCenteredFlowBilateralPrimeCapacityExcess,
    xiCenteredFlowBilateralPrimeCapacity_eq_translationPair,
    HedenmalmThetaSource.frankensteinThetaPrimeTranslationPairExcess]
  ring

/-- Bilateral centered-flow trace has the critical trace as its unconditional lower bound. -/
theorem xiCenteredFlowBilateralPrimeCapacityExcess_nonneg
    (q : XiZeroCopy) (p : Nat.Primes) :
    0 ≤ xiCenteredFlowBilateralPrimeCapacityExcess q p := by
  rw [xiCenteredFlowBilateralPrimeCapacityExcess_eq_translationPairExcess]
  exact mul_nonneg
    (mul_nonneg (xiCenteredFlowMultiplicityMass_pos q.1).le
      (by
        rw [routeNGammaSewnCriticalSquarefreeParityOdds_eq,
          routeNGammaSewnUniversalCriticalChannelMass]
        exact (Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _).le))
    (by
      rw [HedenmalmThetaSource.frankensteinThetaPrimeTranslationPairExcess_eq_cosh]
      nlinarith [Real.one_le_cosh
        (primeDepthBVWoldXiCenteredRate q.1 * Real.log (p : ℝ))])

/-- Sharp rigidity: bilateral trace reaches its critical lower bound exactly on the critical
line. -/
theorem xiCenteredFlowBilateralPrimeCapacityExcess_eq_zero_iff_line
    (q : XiZeroCopy) (p : Nat.Primes) :
    xiCenteredFlowBilateralPrimeCapacityExcess q p = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  have hmass : xiCenteredFlowMultiplicityMass q.1 ≠ 0 :=
    (xiCenteredFlowMultiplicityMass_pos q.1).ne'
  have hcritPos : 0 < routeNGammaSewnCriticalSquarefreeParityOdds p := by
    rw [routeNGammaSewnCriticalSquarefreeParityOdds_eq,
      routeNGammaSewnUniversalCriticalChannelMass]
    exact Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _
  have hcrit : routeNGammaSewnCriticalSquarefreeParityOdds p ≠ 0 :=
    hcritPos.ne'
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos hp1).ne'
  constructor
  · intro hzero
    rw [xiCenteredFlowBilateralPrimeCapacityExcess_eq_translationPairExcess] at hzero
    have hexcess :
        HedenmalmThetaSource.frankensteinThetaPrimeTranslationPairExcess q p = 0 := by
      rcases mul_eq_zero.mp hzero with hfirst | hexcess
      · rcases mul_eq_zero.mp hfirst with hm | hc
        · exact (hmass hm).elim
        · exact (hcrit hc).elim
      · exact hexcess
    let x := primeDepthBVWoldXiCenteredRate q.1 * Real.log (p : ℝ)
    have hgap := two_mul_sq_le_cosh_two_mul_sub_one (x / 2)
    have harg : 2 * (x / 2) = x := by ring
    rw [harg] at hgap
    have hcosh : 2 * (Real.cosh x - 1) = 0 := by
      simpa [x,
        HedenmalmThetaSource.frankensteinThetaPrimeTranslationPairExcess_eq_cosh]
        using hexcess
    have hx : x = 0 := by nlinarith [sq_nonneg x]
    have hrate : primeDepthBVWoldXiCenteredRate q.1 = 0 :=
      (mul_eq_zero.mp hx).resolve_right hlog
    exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).mp hrate
  · intro hline
    have hrate : primeDepthBVWoldXiCenteredRate q.1 = 0 :=
      (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).mpr hline
    rw [xiCenteredFlowBilateralPrimeCapacityExcess_eq_translationPairExcess,
      HedenmalmThetaSource.frankensteinThetaPrimeTranslationPairExcess_eq_cosh,
      hrate]
    simp

/-- Completed bilateral excess observed on the exact first-divided Xi response. -/
def xiCenteredFlowBilateralPrimeCapacityExcessEnergy
    (q : XiZeroCopy) (p : Nat.Primes) : ℝ :=
  xiCenteredFlowBilateralPrimeCapacityExcess q p *
    ‖completedXiFirstDividedL2 q.1‖ ^ 2

/-- Exact landing on completed theta translation-pair excess energy. -/
theorem xiCenteredFlowBilateralPrimeCapacityExcessEnergy_eq_radialTranslation
    (q : XiZeroCopy) (p : Nat.Primes) :
    xiCenteredFlowBilateralPrimeCapacityExcessEnergy q p =
      xiCenteredFlowMultiplicityMass q.1 *
        routeNGammaSewnCriticalSquarefreeParityOdds p *
        HedenmalmThetaSource.frankensteinThetaPrimeTranslationPairExcessEnergy q p := by
  rw [xiCenteredFlowBilateralPrimeCapacityExcessEnergy,
    xiCenteredFlowBilateralPrimeCapacityExcess_eq_translationPairExcess,
    HedenmalmThetaSource.frankensteinThetaPrimeTranslationPairExcessEnergy]
  ring

/-- At prime two, completed bilateral capacity excess and literal completed radial source work are
uniformly equivalent, with exact multiplicity retained. -/
theorem xiCenteredFlowBilateralPrimeCapacityExcessEnergy_two_mem_Icc
    (q : XiZeroCopy) :
    xiCenteredFlowBilateralPrimeCapacityExcessEnergy q
        (⟨2, Nat.prime_two⟩ : Nat.Primes) ∈
      Set.Icc
        (2 * xiCenteredFlowMultiplicityMass q.1 * Real.log 2 ^ 2 *
          burnolCompletedRadialSourceWork q.1)
        (4 * xiCenteredFlowMultiplicityMass q.1 * Real.log 2 ^ 2 *
          burnolCompletedRadialSourceWork q.1) := by
  rw [xiCenteredFlowBilateralPrimeCapacityExcessEnergy_eq_radialTranslation,
    routeNGammaSewnCriticalSquarefreeParityOdds_eq,
    routeNGammaSewnUniversalCriticalChannelMass]
  norm_num [Real.rpow_neg_one]
  have hbounds :=
    HedenmalmThetaSource.primeTranslationPairExcessEnergy_prime_two_mem_Icc q
  have hmass : 0 ≤ xiCenteredFlowMultiplicityMass q.1 :=
    (xiCenteredFlowMultiplicityMass_pos q.1).le
  have hl := mul_le_mul_of_nonneg_left hbounds.1 hmass
  have hu := mul_le_mul_of_nonneg_left hbounds.2 hmass
  constructor <;> nlinarith

/-- Positive prime-two completed excess vanishes exactly with completed radial source work. -/
theorem xiCenteredFlowBilateralPrimeCapacityExcessEnergy_two_eq_zero_iff_radialWork_eq_zero
    (q : XiZeroCopy) :
    xiCenteredFlowBilateralPrimeCapacityExcessEnergy q
        (⟨2, Nat.prime_two⟩ : Nat.Primes) = 0 ↔
      burnolCompletedRadialSourceWork q.1 = 0 := by
  have hbounds :=
    xiCenteredFlowBilateralPrimeCapacityExcessEnergy_two_mem_Icc q
  have hE : 0 ≤ xiCenteredFlowBilateralPrimeCapacityExcessEnergy q
      (⟨2, Nat.prime_two⟩ : Nat.Primes) := by
    rw [xiCenteredFlowBilateralPrimeCapacityExcessEnergy]
    exact mul_nonneg
      (xiCenteredFlowBilateralPrimeCapacityExcess_nonneg q
        (⟨2, Nat.prime_two⟩ : Nat.Primes))
      (sq_nonneg _)
  have hW : 0 ≤ burnolCompletedRadialSourceWork q.1 := by
    rw [burnolCompletedRadialSourceWork_eq_width_sq_mul_norm_sq]
    positivity
  have hcoeff : 0 <
      2 * xiCenteredFlowMultiplicityMass q.1 * Real.log 2 ^ 2 := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact mul_pos
      (mul_pos (by norm_num) (xiCenteredFlowMultiplicityMass_pos q.1))
      (sq_pos_of_pos hlog)
  constructor
  · intro hzero
    apply le_antisymm ?_ hW
    by_contra hnot
    have hWpos : 0 < burnolCompletedRadialSourceWork q.1 :=
      lt_of_not_ge hnot
    have hprod : 0 <
        2 * xiCenteredFlowMultiplicityMass q.1 * Real.log 2 ^ 2 *
          burnolCompletedRadialSourceWork q.1 :=
      mul_pos hcoeff hWpos
    rw [hzero] at hbounds
    exact (not_le_of_gt hprod) hbounds.1
  · intro hzero
    apply le_antisymm ?_ hE
    simpa [hzero] using hbounds.2

/-- Positive prime-time centered-flow transport is the inverse-square literal prime-two endpoint
character, with analytic multiplicity unchanged. -/
theorem xiCenteredFlowRawCapacity_log_two_eq_multiplicity_mul_inv_shell_norm_sq
    (rho : XiDivisorSupport) :
    xiCenteredFlowRawCapacity rho (Real.log 2) =
      xiCenteredFlowMultiplicityMass rho *
        ‖shellTransferCharacter (rho : ℂ)‖⁻¹ ^ 2 := by
  rw [xiCenteredFlowRawCapacity_eq]
  congr 1
  rw [sourceCayleyTransverseRate, norm_shellTransferCharacter]
  simp only [Complex.sub_re, Complex.one_re]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [inv_pow, ← Real.exp_nat_mul, ← Real.exp_neg]
  congr 1
  ring

/-- Negative prime-time centered-flow transport is the square literal prime-two endpoint
character, with analytic multiplicity unchanged. -/
theorem xiCenteredFlowRawCapacity_neg_log_two_eq_multiplicity_mul_shell_norm_sq
    (rho : XiDivisorSupport) :
    xiCenteredFlowRawCapacity rho (-Real.log 2) =
      xiCenteredFlowMultiplicityMass rho *
        ‖shellTransferCharacter (rho : ℂ)‖ ^ 2 := by
  rw [xiCenteredFlowRawCapacity_eq]
  congr 1
  rw [sourceCayleyTransverseRate, norm_shellTransferCharacter]
  simp only [Complex.sub_re, Complex.one_re]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [← Real.exp_nat_mul]
  congr 1
  ring

end

end RHTower

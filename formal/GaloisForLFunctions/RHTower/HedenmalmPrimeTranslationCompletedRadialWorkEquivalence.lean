import GaloisForLFunctions.RHTower.HedenmalmThetaAnomalyWardRadialSourceWorkBridge
import GaloisForLFunctions.RHTower.FrankensteinThetaPrimeTranslationPluckerLanding
import GaloisForLFunctions.RHTower.XiWardSourceWindowMultiplicity
import GaloisForLFunctions.RHTower.SourceHorizontalAbelianClassLawApertureEvacuation

/-!
# Fixed-prime translation excess is completed radial source work

The remaining Route-P fixed-prime detector and the completed Dirac source-work detector are
quantitatively the same horizontal mode.  If `t = 2 Re(q)-1`, reflected prime translation has
exact excess

`D_p(q) = p⁻ᵗ + pᵗ - 2 = 2(cosh(t log p)-1)`.

The completed line-pair resolvent has radial work

`W(q) = (t²/4) ‖f_q‖²`.

Hyperbolic convexity therefore gives a global lower comparison.  In the submicroscopic window
`|t log p| ≤ 1` it also gives a matching upper comparison.  Every actual Xi divisor lies in this
window at prime two, producing an unconditional two-sided equivalence

`4(log 2)² W(q) ≤ D₂(q) ‖f_q‖² ≤ 8(log 2)² W(q)`.

This is not RH.  It proves that fixed-prime translation imbalance cannot be an independent
neutralizing pressure: it is a finite-scale positive transform of the same completed radial work
already exposed by the Ward/Krein layer.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Reflection-symmetric excess of normalized fixed-prime translation energy. -/
def frankensteinThetaPrimeTranslationPairExcess
    (q : RHTower.XiZeroCopy) (p : Nat.Primes) : ℝ :=
  frankensteinThetaPrimeTranslationEnergy q p +
    frankensteinThetaPrimeTranslationEnergy
      (RHTower.xiZeroCopyLineConjEquiv q) p - 2

/-- Exact hyperbolic normal form of fixed-prime reflected translation excess. -/
theorem frankensteinThetaPrimeTranslationPairExcess_eq_cosh
    (q : RHTower.XiZeroCopy) (p : Nat.Primes) :
    frankensteinThetaPrimeTranslationPairExcess q p =
      2 * (Real.cosh
        (RHTower.primeDepthBVWoldXiCenteredRate q.1 * Real.log (p : ℝ)) - 1) := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [frankensteinThetaPrimeTranslationPairExcess,
    frankensteinThetaPrimeTranslationEnergy_eq,
    frankensteinThetaPrimeTranslationEnergy_lineConj_eq,
    Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hp, Real.cosh_eq]
  ring_nf

/-- Translation excess observed with the exact completed first-divided Xi mode energy. -/
def frankensteinThetaPrimeTranslationPairExcessEnergy
    (q : RHTower.XiZeroCopy) (p : Nat.Primes) : ℝ :=
  frankensteinThetaPrimeTranslationPairExcess q p *
    ‖RHTower.completedXiFirstDividedL2 q.1‖ ^ 2

/-- Centered prime rate is minus twice completed spectral width. -/
theorem primeDepthBVWoldXiCenteredRate_eq_neg_two_mul_spectral_im
    (q : RHTower.XiZeroCopy) :
    RHTower.primeDepthBVWoldXiCenteredRate q.1 =
      -2 * (RHTower.xiSpectralPoint q).im := by
  rw [RHTower.primeDepthBVWoldXiCenteredRate, RHTower.xiSpectralPoint_im_eq]
  ring

/-- **Global quadratic comparison.**  Every fixed-prime reflected translation excess dominates
completed radial work with exact prime-log scale. -/
theorem four_log_sq_mul_radialWork_le_primeTranslationPairExcessEnergy
    (q : RHTower.XiZeroCopy) (p : Nat.Primes) :
    4 * Real.log (p : ℝ) ^ 2 * RHTower.burnolCompletedRadialSourceWork q.1 ≤
      frankensteinThetaPrimeTranslationPairExcessEnergy q p := by
  let t := RHTower.primeDepthBVWoldXiCenteredRate q.1
  let L := Real.log (p : ℝ)
  let N := ‖RHTower.completedXiFirstDividedL2 q.1‖ ^ 2
  have hgap0 := RHTower.two_mul_sq_le_cosh_two_mul_sub_one (t * L / 2)
  have harg : 2 * (t * L / 2) = t * L := by ring
  rw [harg] at hgap0
  have hgap : (t * L) ^ 2 ≤
      frankensteinThetaPrimeTranslationPairExcess q p := by
    rw [frankensteinThetaPrimeTranslationPairExcess_eq_cosh]
    exact_mod_cast (show (t * L) ^ 2 ≤
      2 * (Real.cosh (t * L) - 1) by nlinarith [hgap0])
  have hN : 0 ≤ N := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hgap hN
  rw [RHTower.burnolCompletedRadialSourceWork_eq_width_sq_mul_norm_sq]
  rw [← RHTower.xiSpectralPoint_eq_support q]
  rw [frankensteinThetaPrimeTranslationPairExcessEnergy]
  dsimp only [t, L, N] at hmul ⊢
  have him : (RHTower.xiSpectralPoint q).im =
      -RHTower.primeDepthBVWoldXiCenteredRate q.1 / 2 := by
    rw [RHTower.xiSpectralPoint_im_eq,
      RHTower.primeDepthBVWoldXiCenteredRate]
    ring
  rw [him]
  nlinarith

/-- Matching quadratic upper comparison on one bounded hyperbolic frequency window. -/
theorem primeTranslationPairExcessEnergy_le_eight_log_sq_mul_radialWork_of_band
    (q : RHTower.XiZeroCopy) (p : Nat.Primes)
    (hband : |RHTower.primeDepthBVWoldXiCenteredRate q.1 * Real.log (p : ℝ)| ≤ 1) :
    frankensteinThetaPrimeTranslationPairExcessEnergy q p ≤
      8 * Real.log (p : ℝ) ^ 2 * RHTower.burnolCompletedRadialSourceWork q.1 := by
  let t := RHTower.primeDepthBVWoldXiCenteredRate q.1
  let L := Real.log (p : ℝ)
  let N := ‖RHTower.completedXiFirstDividedL2 q.1‖ ^ 2
  have hgap0 := RHTower.cosh_sub_one_le_sq_of_abs_le_one hband
  have hgap : frankensteinThetaPrimeTranslationPairExcess q p ≤
      2 * (t * L) ^ 2 := by
    rw [frankensteinThetaPrimeTranslationPairExcess_eq_cosh]
    dsimp only [t, L] at hgap0 ⊢
    nlinarith
  have hN : 0 ≤ N := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hgap hN
  rw [RHTower.burnolCompletedRadialSourceWork_eq_width_sq_mul_norm_sq]
  rw [← RHTower.xiSpectralPoint_eq_support q]
  rw [frankensteinThetaPrimeTranslationPairExcessEnergy]
  dsimp only [t, L, N] at hmul ⊢
  have him : (RHTower.xiSpectralPoint q).im =
      -RHTower.primeDepthBVWoldXiCenteredRate q.1 / 2 := by
    rw [RHTower.xiSpectralPoint_im_eq,
      RHTower.primeDepthBVWoldXiCenteredRate]
    ring
  rw [him]
  nlinarith

/-- Every actual Xi copy lies in the submicroscopic comparison window at prime two. -/
theorem primeTranslationPairExcess_prime_two_band
    (q : RHTower.XiZeroCopy) :
    |RHTower.primeDepthBVWoldXiCenteredRate q.1 * Real.log 2| ≤ 1 := by
  have ht := RHTower.sourceHorizontalXiCenteredRate_abs_lt_one q
  have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hlog1 : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  rw [abs_mul, abs_of_nonneg hlog0]
  exact (mul_lt_one_of_nonneg_of_lt_one_left (abs_nonneg _) ht hlog1.le).le

/-- **Prime-two equivalence.**  On every actual Xi fibre, fixed-prime translation excess and
completed radial work are uniformly comparable with source-independent constants. -/
theorem primeTranslationPairExcessEnergy_prime_two_mem_Icc
    (q : RHTower.XiZeroCopy) :
    frankensteinThetaPrimeTranslationPairExcessEnergy q
        (⟨2, Nat.prime_two⟩ : Nat.Primes) ∈
      Set.Icc
        (4 * Real.log 2 ^ 2 * RHTower.burnolCompletedRadialSourceWork q.1)
        (8 * Real.log 2 ^ 2 * RHTower.burnolCompletedRadialSourceWork q.1) := by
  exact ⟨
    four_log_sq_mul_radialWork_le_primeTranslationPairExcessEnergy q
      (⟨2, Nat.prime_two⟩ : Nat.Primes),
    primeTranslationPairExcessEnergy_le_eight_log_sq_mul_radialWork_of_band q
      (⟨2, Nat.prime_two⟩ : Nat.Primes)
      (primeTranslationPairExcess_prime_two_band q)⟩

/-- Reflected translation excess energy is nonnegative before any Xi specialization. -/
theorem frankensteinThetaPrimeTranslationPairExcessEnergy_nonneg
    (q : RHTower.XiZeroCopy) (p : Nat.Primes) :
    0 ≤ frankensteinThetaPrimeTranslationPairExcessEnergy q p := by
  rw [frankensteinThetaPrimeTranslationPairExcessEnergy,
    frankensteinThetaPrimeTranslationPairExcess_eq_cosh]
  have hcosh : 1 ≤ Real.cosh
      (RHTower.primeDepthBVWoldXiCenteredRate q.1 * Real.log (p : ℝ)) :=
    Real.one_le_cosh _
  exact mul_nonneg (by nlinarith) (sq_nonneg _)

/-- Prime-two translation excess vanishes exactly when completed radial source work vanishes. -/
theorem primeTranslationPairExcessEnergy_prime_two_eq_zero_iff_radialWork_eq_zero
    (q : RHTower.XiZeroCopy) :
    frankensteinThetaPrimeTranslationPairExcessEnergy q
        (⟨2, Nat.prime_two⟩ : Nat.Primes) = 0 ↔
      RHTower.burnolCompletedRadialSourceWork q.1 = 0 := by
  have hbounds := primeTranslationPairExcessEnergy_prime_two_mem_Icc q
  have hE : 0 ≤ frankensteinThetaPrimeTranslationPairExcessEnergy q
      (⟨2, Nat.prime_two⟩ : Nat.Primes) :=
    frankensteinThetaPrimeTranslationPairExcessEnergy_nonneg q
      (⟨2, Nat.prime_two⟩ : Nat.Primes)
  have hW : 0 ≤ RHTower.burnolCompletedRadialSourceWork q.1 := by
    rw [RHTower.burnolCompletedRadialSourceWork_eq_width_sq_mul_norm_sq]
    positivity
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · intro hzero
    apply le_antisymm ?_ hW
    by_contra hnot
    have hWpos : 0 < RHTower.burnolCompletedRadialSourceWork q.1 :=
      lt_of_not_ge hnot
    have hprod : 0 < 4 * Real.log 2 ^ 2 *
        RHTower.burnolCompletedRadialSourceWork q.1 := by positivity
    rw [hzero] at hbounds
    exact (not_le_of_gt hprod) hbounds.1
  · intro hzero
    apply le_antisymm ?_ hE
    simpa [hzero] using hbounds.2

end

end RHTower.HedenmalmThetaSource

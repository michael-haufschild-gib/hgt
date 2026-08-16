import GaloisForLFunctions.RHTower.FrankensteinParacyclicPrimeClockBigWittGhost
import GaloisForLFunctions.RHTower.PrimeGammaCofinalBocksteinDeterminantTransgression

/-!
# Source-selected Gamma Ward descent and the shared-ghost obstruction

An inverse-oriented Faddeev--Popov correction can repair the physical Gamma
rotation at any one prime and any centered rate.  Positivity makes that local
ghost unique: at prime `p` it is exactly `p⁻ᵗ`.  Thus prime-local ghost
existence is fitted cancellation, not a producer.

Coefficient faithfulness changes the conclusion.  One source-selected Gamma
ghost must be independent of the retained ordinary-prime label.  The same
positive ghost repairs the physical rotations at primes two and three if and
only if the centered rate is zero.  On an actual Xi divisor this shared-ghost
Ward law is therefore equivalent both to the critical line and to the
existing Big-Witt prime-clock selected Ward descent.

This is an unconditional classification of the proposed Gamma Ward producer.
It does not assert the remaining arithmetic existence of a shared ghost.
-/

open Complex

namespace RHTower

noncomputable section

/-- Inverse-oriented Ward equation for a positive scalar ghost.  Reflection
inverts the ghost while reversing the physical horizontal grade. -/
def primeGammaInverseOrientedGhostWardEquation
    (c t : ℝ) (p : Nat.Primes) : Prop :=
  c * primeGammaPhysicalRotationDeterminant t p =
    c⁻¹ * primeGammaPhysicalRotationDeterminant (-t) p

/-- **Local ghost classification.**  A positive inverse-oriented correction
at one retained prime is uniquely the inverse physical radial character. -/
theorem primeGammaInverseOrientedGhostWardEquation_iff
    {c : ℝ} (hc : 0 < c) (t : ℝ) (p : Nat.Primes) :
    primeGammaInverseOrientedGhostWardEquation c t p ↔
      c = (p : ℝ) ^ (-t) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  let x : ℝ := (p : ℝ) ^ t
  have hx : 0 < x := Real.rpow_pos_of_pos hp t
  have hx0 : x ≠ 0 := hx.ne'
  constructor
  · intro h
    rw [primeGammaInverseOrientedGhostWardEquation,
      primeGammaPhysicalRotationDeterminant,
      primeGammaPhysicalRotationDeterminant,
      Real.rpow_neg hp.le] at h
    change c * (-x) = c⁻¹ * (-x⁻¹) at h
    have hpos : c * x = c⁻¹ * x⁻¹ := by linarith
    have hinv : c⁻¹ * x⁻¹ = (c * x)⁻¹ := by
      rw [mul_inv]
    have hy : c * x = (c * x)⁻¹ := hpos.trans hinv
    have hcx0 : c * x ≠ 0 := mul_ne_zero hc.ne' hx0
    have hsq : (c * x) * (c * x) = 1 := by
      calc
        (c * x) * (c * x) = (c * x)⁻¹ * (c * x) :=
          congrArg (fun z : ℝ => z * (c * x)) hy
        _ = 1 := inv_mul_cancel₀ hcx0
    have hcx : c * x = 1 := by
      nlinarith [mul_pos hc hx]
    rw [Real.rpow_neg hp.le]
    exact eq_inv_of_mul_eq_one_left hcx
  · intro hcEq
    rw [Real.rpow_neg hp.le] at hcEq
    rw [primeGammaInverseOrientedGhostWardEquation,
      primeGammaPhysicalRotationDeterminant,
      primeGammaPhysicalRotationDeterminant,
      Real.rpow_neg hp.le, hcEq]
    have hpow0 : (p : ℝ) ^ t ≠ 0 :=
      (Real.rpow_pos_of_pos hp t).ne'
    field_simp

/-- Unique fitted positive ghost at one prime label. -/
def primeGammaLocalInverseOrientedGhost
    (t : ℝ) (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ (-t)

theorem primeGammaLocalInverseOrientedGhost_pos
    (t : ℝ) (p : Nat.Primes) :
    0 < primeGammaLocalInverseOrientedGhost t p := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _

/-- Prime-local fitted ghosts solve the Ward equation unconditionally. -/
theorem primeGammaLocalInverseOrientedGhost_ward
    (t : ℝ) (p : Nat.Primes) :
    primeGammaInverseOrientedGhostWardEquation
      (primeGammaLocalInverseOrientedGhost t p) t p := by
  exact (primeGammaInverseOrientedGhostWardEquation_iff
    (primeGammaLocalInverseOrientedGhost_pos t p) t p).2 rfl

theorem primeGammaLocalInverseOrientedGhost_unique
    {c : ℝ} (hc : 0 < c) (t : ℝ) (p : Nat.Primes)
    (hward : primeGammaInverseOrientedGhostWardEquation c t p) :
    c = primeGammaLocalInverseOrientedGhost t p := by
  exact (primeGammaInverseOrientedGhostWardEquation_iff hc t p).1 hward

/-- Source-selected coefficient-faithful Ward target: one positive Gamma
ghost, independent of prime label, repairs both prime two and prime three. -/
def PrimeGammaTwoThreeSharedInverseOrientedGhostWard (t : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    primeGammaInverseOrientedGhostWardEquation c t
      deningerCalderonWittPrimeTwo ∧
    primeGammaInverseOrientedGhostWardEquation c t
      deningerCalderonWittPrimeThree

/-- **Shared-ghost rigidity.**  Two retained prime labels turn an otherwise
fitted local correction into an exact detector of neutral horizontal grade. -/
theorem primeGammaTwoThreeSharedInverseOrientedGhostWard_iff
    (t : ℝ) :
    PrimeGammaTwoThreeSharedInverseOrientedGhostWard t ↔ t = 0 := by
  constructor
  · rintro ⟨c, hc, htwo, hthree⟩
    have hcTwo := (primeGammaInverseOrientedGhostWardEquation_iff
      hc t deningerCalderonWittPrimeTwo).1 htwo
    have hcThree := (primeGammaInverseOrientedGhostWardEquation_iff
      hc t deningerCalderonWittPrimeThree).1 hthree
    have hpowers : (2 : ℝ) ^ (-t) = (3 : ℝ) ^ (-t) := by
      simpa [deningerCalderonWittPrimeTwo,
        deningerCalderonWittPrimeThree] using hcTwo.symm.trans hcThree
    have hlogs := congrArg Real.log hpowers
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2),
      Real.log_rpow (by norm_num : (0 : ℝ) < 3)] at hlogs
    have hlogne : Real.log (2 : ℝ) ≠ Real.log (3 : ℝ) := by
      intro h
      have hexp := congrArg Real.exp h
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 2),
        Real.exp_log (by norm_num : (0 : ℝ) < 3)] at hexp
      norm_num at hexp
    have hdiff : Real.log (2 : ℝ) - Real.log (3 : ℝ) ≠ 0 :=
      sub_ne_zero.mpr hlogne
    have hmul : (-t) *
        (Real.log (2 : ℝ) - Real.log (3 : ℝ)) = 0 := by
      linear_combination hlogs
    have ht : -t = 0 := (mul_eq_zero.mp hmul).resolve_right hdiff
    linarith
  · rintro rfl
    refine ⟨1, zero_lt_one, ?_, ?_⟩
    · exact (primeGammaInverseOrientedGhostWardEquation_iff
        zero_lt_one 0 deningerCalderonWittPrimeTwo).2 (by norm_num)
    · exact (primeGammaInverseOrientedGhostWardEquation_iff
        zero_lt_one 0 deningerCalderonWittPrimeThree).2 (by norm_num)

/-- Pointwise source-selected Gamma Ward producer target on an actual Xi
divisor class. -/
def FrankensteinSourceSelectedGammaWardSharedGhostDescendsAt
    (rho : XiDivisorSupport) : Prop :=
  PrimeGammaTwoThreeSharedInverseOrientedGhostWard
    (2 * (rho : ℂ).re - 1)

theorem frankensteinSourceSelectedGammaWardSharedGhostDescendsAt_iff
    (rho : XiDivisorSupport) :
    FrankensteinSourceSelectedGammaWardSharedGhostDescendsAt rho ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [FrankensteinSourceSelectedGammaWardSharedGhostDescendsAt,
    primeGammaTwoThreeSharedInverseOrientedGhostWard_iff]
  constructor <;> intro h <;> linarith

/-- The shared-ghost producer is exactly the earlier coefficient-faithful
Big-Witt/Gamma selected Ward descent, not a weaker auxiliary condition. -/
theorem frankensteinSourceSelectedGammaWardSharedGhostDescendsAt_iff_primeClockWard
    (rho : XiDivisorSupport) :
    FrankensteinSourceSelectedGammaWardSharedGhostDescendsAt rho ↔
      FrankensteinPrimeClockParacyclicSelectedWardDescendsAt rho := by
  rw [frankensteinSourceSelectedGammaWardSharedGhostDescendsAt_iff,
    frankensteinPrimeClockParacyclicSelectedWardDescendsAt_iff]

/-- Equivalent coefficient form on the literal `(2,3)` Big-Witt seam. -/
theorem frankensteinSourceSelectedGammaWardSharedGhostDescendsAt_iff_bigWittSeam_zero
    (rho : XiDivisorSupport) :
    FrankensteinSourceSelectedGammaWardSharedGhostDescendsAt rho ↔
      deningerBigWittFrobeniusPrimeSeamPairCoefficient
        (frankensteinPrimeClockParacyclicAnomaly rho)
        deningerCalderonWittPrimeTwo deningerCalderonWittPrimeThree = 0 := by
  rw [frankensteinSourceSelectedGammaWardSharedGhostDescendsAt_iff,
    deningerBigWittFrobeniusPrimeSeamPairCoefficient_primeClockParacyclic_two_three_eq_zero_iff]

def EveryFrankensteinSourceSelectedGammaWardSharedGhostDescends : Prop :=
  ∀ rho : XiDivisorSupport,
    FrankensteinSourceSelectedGammaWardSharedGhostDescendsAt rho

/-- Global classification.  Constructing the shared ghost from genuine
source/Gamma naturality is exactly the remaining RH-strength producer. -/
theorem everyFrankensteinSourceSelectedGammaWardSharedGhostDescends_iff_riemannHypothesis :
    EveryFrankensteinSourceSelectedGammaWardSharedGhostDescends ↔
      RiemannHypothesis := by
  rw [← everyFrankensteinPrimeClockParacyclicSelectedWardDescends_iff_riemannHypothesis]
  unfold EveryFrankensteinSourceSelectedGammaWardSharedGhostDescends
    EveryFrankensteinPrimeClockParacyclicSelectedWardDescends
  apply forall_congr'
  exact frankensteinSourceSelectedGammaWardSharedGhostDescendsAt_iff_primeClockWard

end

end RHTower

import GaloisForLFunctions.RHTower.DeningerBigWittRing
import GaloisForLFunctions.RHTower.FrankensteinMeyerPrimeKoszulGammaReporter

/-!
# Integral bidirectional Big-Witt Gamma descent

This module supplies a new discrete Frankenstein alternative to cross-prime shared-ghost descent.
At one retained prime, lift forward and reflected Gamma ghosts to ghost components of literal
integral Big-Witt classes. Positivity makes both components positive integers; reflection makes
their real product one. Hence each is one and centered grade is zero.

This is exact integral-lattice embedding previously missing from corpus. It preserves both
reflection orientations and needs no transcendence, logarithmic-prime independence, continuity,
or RH premise. For Xi divisors, existence of these two integral lifts is exactly critical-line
placement, and existence for every retained divisor is exactly RH. Remaining producer question is
whether genuine source/Gamma naturality supplies these integral lifts.
-/

open Complex

namespace RHTower

noncomputable section

structure PrimeGammaIntegralBidirectionalBigWittLift (t : ℝ) where
  forward : DeningerBigWittRing ℤ
  inverse : DeningerBigWittRing ℤ
  forward_ghost_two :
    ((deningerBigWittGhostComponent 2 (by omega) forward : ℤ) : ℝ) =
      primeGammaLocalInverseOrientedGhost (-t) deningerCalderonWittPrimeTwo
  inverse_ghost_two :
    ((deningerBigWittGhostComponent 2 (by omega) inverse : ℤ) : ℝ) =
      primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeTwo

theorem primeGammaIntegralBidirectionalBigWittLift_eq_zero
    {t : ℝ} (h : PrimeGammaIntegralBidirectionalBigWittLift t) :
    t = 0 := by
  let a : ℤ := deningerBigWittGhostComponent 2 (by omega) h.forward
  let b : ℤ := deningerBigWittGhostComponent 2 (by omega) h.inverse
  have hp : (0 : ℝ) < (deningerCalderonWittPrimeTwo : ℝ) := by
    exact_mod_cast deningerCalderonWittPrimeTwo.2.pos
  have hprodGhost :
      primeGammaLocalInverseOrientedGhost (-t) deningerCalderonWittPrimeTwo *
        primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeTwo = 1 := by
    rw [primeGammaLocalInverseOrientedGhost,
      primeGammaLocalInverseOrientedGhost]
    rw [show - -t = t by ring, ← Real.rpow_add hp]
    simp
  have ha : (a : ℝ) =
      primeGammaLocalInverseOrientedGhost (-t) deningerCalderonWittPrimeTwo := by
    exact h.forward_ghost_two
  have hb : (b : ℝ) =
      primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeTwo := by
    exact h.inverse_ghost_two
  have haPos : (0 : ℝ) < (a : ℝ) := by
    rw [ha]
    exact primeGammaLocalInverseOrientedGhost_pos _ _
  have hbPos : (0 : ℝ) < (b : ℝ) := by
    rw [hb]
    exact primeGammaLocalInverseOrientedGhost_pos _ _
  have haInt : (1 : ℤ) ≤ a := by
    exact_mod_cast haPos
  have hbInt : (1 : ℤ) ≤ b := by
    exact_mod_cast hbPos
  have hprod : (a : ℝ) * (b : ℝ) = 1 := by
    rw [ha, hb]
    exact hprodGhost
  have haOne : (a : ℝ) = 1 := by
    have haOneLe : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast haInt
    have hbOneLe : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hbInt
    nlinarith
  have hbOne : (b : ℝ) = 1 := by
    have haOneLe : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast haInt
    have hbOneLe : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hbInt
    nlinarith
  have hpow :
      primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeTwo = 1 := by
    rw [← hb, hbOne]
  change (deningerCalderonWittPrimeTwo : ℝ) ^ (-t) = 1 at hpow
  have hlog := congrArg Real.log hpow
  rw [Real.log_rpow hp, Real.log_one] at hlog
  have hlogp : Real.log (deningerCalderonWittPrimeTwo : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    exact_mod_cast deningerCalderonWittPrimeTwo.2.one_lt
  have htneg : -t = 0 := (mul_eq_zero.mp hlog).resolve_right hlogp
  linarith

def primeGammaIntegralBidirectionalBigWittLiftOfEqZero
    {t : ℝ} (ht : t = 0) :
    PrimeGammaIntegralBidirectionalBigWittLift t := by
  subst t
  refine
    { forward := deningerBigWittRingTeichmuller (1 : ℤ)
      inverse := deningerBigWittRingTeichmuller (1 : ℤ)
      forward_ghost_two := ?_
      inverse_ghost_two := ?_ }
  · simp [primeGammaLocalInverseOrientedGhost]
  · simp [primeGammaLocalInverseOrientedGhost]

theorem primeGammaIntegralBidirectionalBigWittLift_nonempty_iff (t : ℝ) :
    Nonempty (PrimeGammaIntegralBidirectionalBigWittLift t) ↔ t = 0 := by
  constructor
  · rintro ⟨h⟩
    exact primeGammaIntegralBidirectionalBigWittLift_eq_zero h
  · intro ht
    exact ⟨primeGammaIntegralBidirectionalBigWittLiftOfEqZero ht⟩

def XiIntegralBidirectionalBigWittGammaDescentAt
    (rho : XiDivisorSupport) : Prop :=
  Nonempty (PrimeGammaIntegralBidirectionalBigWittLift
    (primeDepthBVWoldXiCenteredRate rho))

theorem xiIntegralBidirectionalBigWittGammaDescentAt_iff
    (rho : XiDivisorSupport) :
    XiIntegralBidirectionalBigWittGammaDescentAt rho ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [XiIntegralBidirectionalBigWittGammaDescentAt,
    primeGammaIntegralBidirectionalBigWittLift_nonempty_iff,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

def EveryXiIntegralBidirectionalBigWittGammaDescends : Prop :=
  ∀ rho : XiDivisorSupport,
    XiIntegralBidirectionalBigWittGammaDescentAt rho

theorem everyXiIntegralBidirectionalBigWittGammaDescends_iff_riemannHypothesis :
    EveryXiIntegralBidirectionalBigWittGammaDescends ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro rho
    exact (xiIntegralBidirectionalBigWittGammaDescentAt_iff rho).1 (h rho)
  · intro h rho
    exact (xiIntegralBidirectionalBigWittGammaDescentAt_iff rho).2
      (xi_divisor_support_re_eq_half_of_rh h rho)

end

end RHTower


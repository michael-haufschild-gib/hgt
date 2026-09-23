import GaloisForLFunctions.RHTower.DeningerCalderonWittAllCrossPrimeArithmeticSourceCompletion
import GaloisForLFunctions.RHTower.RiemannGaussianProjectiveDescentLaw
import GaloisForLFunctions.RHTower.XiSourceBoundaryOrientationConservation

/-!
# Gaussian horizontal normalization on the all-cross-prime source

The completed Calderón--Witt packet admits a unit full-support horizon, so
every scalar residual ray is a genuine Hilbert vector.  This file inserts
the two fixed reflected-Gaussian source jets into that actual arithmetic
completion and forms their division-free horizontal Wronskian.

Three exact facts isolate the remaining topology change.

* The Wronskian packet is a fibrewise Koszul cycle with norm exactly the
  scalar Gaussian Wronskian.  It is nonzero at every off-line divisor copy.
* Dividing every packet coordinate by the source horizon produces a
  constant family.  Because the ordered cross-prime index is infinite, this
  unweighted family is square-summable exactly when the residual scalar is
  zero.  Thus unweighted arithmetic normalization of the Gaussian packet is
  equivalent to the critical-line equation.
* The old oriented boundary vanishes on the dense actual-witness span, so
  every continuous extension kills the horizontal packet, including when
  the packet itself is nonzero.

Consequently the weighted source completion and old oriented boundary
cannot supply the missing horizontal anchor.  A successful construction
must introduce a genuinely relative horizontal transgression or prove
source admission into the inverse-horizon domain.  The latter global
admission statement is equivalent to RH and is not assumed here.
-/

open Complex Function Set Topology
open GaloisForLFunctions.HTGeometry
open scoped ENNReal Real

namespace RHTower

noncomputable section

namespace DeningerMeyerGaussianGreen

private def crossPrimeIndexOfPrime (p : Nat.Primes) :
    DeningerCalderonWittCrossPrimePacketIndex :=
  if hp : p = ⟨2, Nat.prime_two⟩ then
    ⟨(p, ⟨3, Nat.prime_three⟩), by
      intro h
      have hval := congrArg (fun r : Nat.Primes => r.1) h
      simp [hp] at hval⟩
  else
    ⟨(p, ⟨2, Nat.prime_two⟩), hp⟩

private theorem crossPrimeIndexOfPrime_first (p : Nat.Primes) :
    (crossPrimeIndexOfPrime p).1.1 = p := by
  rw [crossPrimeIndexOfPrime]
  split <;> rfl

private theorem crossPrimeIndexOfPrime_injective :
    Function.Injective crossPrimeIndexOfPrime := by
  intro p q h
  have hval := congrArg
    (fun i : DeningerCalderonWittCrossPrimePacketIndex => i.1.1) h
  simpa [crossPrimeIndexOfPrime_first] using hval

noncomputable local instance deningerCalderonWittGaussianHorizontalNormalizationInst1 : Infinite DeningerCalderonWittCrossPrimePacketIndex :=
  Infinite.of_injective crossPrimeIndexOfPrime
    crossPrimeIndexOfPrime_injective

/-- A packet is unweighted-normalizable when coefficientwise division by
the nowhere-zero arithmetic horizon is square-summable. -/
def deningerCalderonWittPacketUnweightedNormalizable
    (z : DeningerCalderonWittCrossPrimePacketHilbert) : Prop :=
  Summable fun i : DeningerCalderonWittCrossPrimePacketIndex =>
    ‖z i / deningerCalderonWittCrossPrimePacketHorizon i‖ ^ 2

/-- **Inverse-horizon domain classification.**  The inverse-horizon domain
meets the one-dimensional residual Koszul ray only at zero.  Weighted
completion admits `c • horizon` for every scalar, while arithmetic
normalization exposes the nonsummable constant family `c`. -/
theorem deningerCalderonWittPacketUnweightedNormalizable_horizonRay_iff
    (c : ℂ) :
    deningerCalderonWittPacketUnweightedNormalizable
        (c • deningerCalderonWittCrossPrimePacketHorizon) ↔
      c = 0 := by
  rw [deningerCalderonWittPacketUnweightedNormalizable]
  have hfun :
      (fun i : DeningerCalderonWittCrossPrimePacketIndex =>
        ‖(c • deningerCalderonWittCrossPrimePacketHorizon) i /
            deningerCalderonWittCrossPrimePacketHorizon i‖ ^ 2) =
      (fun _ : DeningerCalderonWittCrossPrimePacketIndex => ‖c‖ ^ 2) := by
    funext i
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      mul_div_cancel_right₀ c
        (deningerCalderonWittCrossPrimePacketHorizon_apply_ne_zero i)]
  rw [hfun, summable_const_iff]
  simp

/-- Weighted coefficientwise inverse-horizon normalization.  The weight is
kept general; physical weighted norms specialize to nonnegative `w`. -/
def deningerCalderonWittPacketWeightedNormalizable
    (w : DeningerCalderonWittCrossPrimePacketIndex → ℝ)
    (z : DeningerCalderonWittCrossPrimePacketHilbert) : Prop :=
  Summable fun i : DeningerCalderonWittCrossPrimePacketIndex =>
    w i * ‖z i / deningerCalderonWittCrossPrimePacketHorizon i‖ ^ 2

/-- **Complete diagonal-weight dichotomy.**  A weighted inverse-horizon
domain admits a nonzero residual ray exactly when its diagonal weight is
summable.  Hence a summable weight admits every residual scalar and selects
nothing, while a nonsummable weight admits only the zero residual. -/
theorem deningerCalderonWittPacketWeightedNormalizable_horizonRay_iff
    (w : DeningerCalderonWittCrossPrimePacketIndex → ℝ) (c : ℂ) :
    deningerCalderonWittPacketWeightedNormalizable w
        (c • deningerCalderonWittCrossPrimePacketHorizon) ↔
      c = 0 ∨ Summable w := by
  rw [deningerCalderonWittPacketWeightedNormalizable]
  have hfun :
      (fun i : DeningerCalderonWittCrossPrimePacketIndex =>
        w i * ‖(c • deningerCalderonWittCrossPrimePacketHorizon) i /
            deningerCalderonWittCrossPrimePacketHorizon i‖ ^ 2) =
      (fun i => w i * ‖c‖ ^ 2) := by
    funext i
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      mul_div_cancel_right₀ c
        (deningerCalderonWittCrossPrimePacketHorizon_apply_ne_zero i)]
  rw [hfun]
  constructor
  · intro h
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      have hnorm : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
      have hdiv := h.div_const (‖c‖ ^ 2)
      simpa [mul_div_cancel_right₀ _ hnorm] using hdiv
  · rintro (rfl | hw)
    · simp
    · exact hw.mul_right _

/-- Every summable diagonal weight admits the whole residual ray. -/
theorem deningerCalderonWittPacketWeightedNormalizable_horizonRay_of_summable
    {w : DeningerCalderonWittCrossPrimePacketIndex → ℝ}
    (hw : Summable w) (c : ℂ) :
    deningerCalderonWittPacketWeightedNormalizable w
      (c • deningerCalderonWittCrossPrimePacketHorizon) := by
  exact
    (deningerCalderonWittPacketWeightedNormalizable_horizonRay_iff w c).2
      (Or.inr hw)

/-- Every nonsummable diagonal weight meets the residual ray only at zero. -/
theorem
    deningerCalderonWittPacketWeightedNormalizable_horizonRay_iff_zero_of_not_summable
    {w : DeningerCalderonWittCrossPrimePacketIndex → ℝ}
    (hw : ¬ Summable w) (c : ℂ) :
    deningerCalderonWittPacketWeightedNormalizable w
        (c • deningerCalderonWittCrossPrimePacketHorizon) ↔
      c = 0 := by
  rw [deningerCalderonWittPacketWeightedNormalizable_horizonRay_iff,
    or_iff_left hw]

/-- Zeroth Gaussian source jet carried by the actual all-cross-prime
arithmetic horizon. -/
def deningerCalderonWittGaussianZeroJetPacket (q : XiZeroCopy) :
    DeningerCalderonWittCrossPrimePacketHilbert :=
  deningerMeyerReflectedGaussianMellinZeroJet q •
    deningerCalderonWittCrossPrimePacketHorizon

/-- First Gaussian source jet carried by the actual all-cross-prime
arithmetic horizon. -/
def deningerCalderonWittGaussianFirstJetPacket (q : XiZeroCopy) :
    DeningerCalderonWittCrossPrimePacketHilbert :=
  deningerMeyerReflectedGaussianMellinFirstJet q •
    deningerCalderonWittCrossPrimePacketHorizon

/-- Division-free horizontal wedge of the two fixed Gaussian source rays. -/
def deningerCalderonWittGaussianHorizontalWronskianPacket (q : XiZeroCopy) :
    DeningerCalderonWittCrossPrimePacketHilbert :=
  deningerMeyerReflectedGaussianMellinFirstJet q •
      deningerCalderonWittGaussianZeroJetPacket
        (xiZeroCopyLineConjEquiv q) -
    deningerMeyerReflectedGaussianMellinZeroJet q •
      deningerCalderonWittGaussianFirstJetPacket
        (xiZeroCopyLineConjEquiv q)

/-- The packet-valued exterior source is exactly the Gaussian Wronskian on
the unique residual Koszul ray. -/
theorem deningerCalderonWittGaussianHorizontalWronskianPacket_eq
    (q : XiZeroCopy) :
    deningerCalderonWittGaussianHorizontalWronskianPacket q =
      deningerMeyerReflectedGaussianLineWronskian q •
        deningerCalderonWittCrossPrimePacketHorizon := by
  rw [deningerCalderonWittGaussianHorizontalWronskianPacket,
    deningerCalderonWittGaussianZeroJetPacket,
    deningerCalderonWittGaussianFirstJetPacket,
    deningerMeyerReflectedGaussianLineWronskian]
  module

/-- Vertical all-cross-prime compatibility kills the packet for every
divisor position; it leaves the horizontal residual scalar untouched. -/
theorem deningerCalderonWittGaussianHorizontalWronskianPacket_koszul
    (q : XiZeroCopy) :
    deningerCalderonWittPacketKoszulDifferential
        (deningerCalderonWittGaussianHorizontalWronskianPacket q) = 0 := by
  rw [deningerCalderonWittGaussianHorizontalWronskianPacket_eq,
    map_smul, deningerCalderonWittPacketKoszulDifferential_horizon, smul_zero]

/-- Weighted source completion preserves the full horizontal magnitude. -/
theorem norm_deningerCalderonWittGaussianHorizontalWronskianPacket
    (q : XiZeroCopy) :
    ‖deningerCalderonWittGaussianHorizontalWronskianPacket q‖ =
      ‖deningerMeyerReflectedGaussianLineWronskian q‖ := by
  rw [deningerCalderonWittGaussianHorizontalWronskianPacket_eq,
    norm_smul, deningerCalderonWittCrossPrimePacketHorizon_norm, mul_one]

/-- **Local normalization selector.**  The actual Gaussian Wronskian packet
enters the unweighted arithmetic normalization domain exactly on the
critical line. -/
theorem deningerCalderonWittGaussianHorizontalWronskianPacket_normalizable_iff
    (q : XiZeroCopy) :
    deningerCalderonWittPacketUnweightedNormalizable
        (deningerCalderonWittGaussianHorizontalWronskianPacket q) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [deningerCalderonWittGaussianHorizontalWronskianPacket_eq,
    deningerCalderonWittPacketUnweightedNormalizable_horizonRay_iff,
    deningerMeyerReflectedGaussianLineWronskian_eq_zero_iff]

/-- Weighted admission of the Gaussian horizontal packet has only two
causes: the horizontal scalar vanishes, or the diagonal weight is summable. -/
theorem
    deningerCalderonWittGaussianHorizontalWronskianPacket_weightedNormalizable_iff
    (w : DeningerCalderonWittCrossPrimePacketIndex → ℝ) (q : XiZeroCopy) :
    deningerCalderonWittPacketWeightedNormalizable w
        (deningerCalderonWittGaussianHorizontalWronskianPacket q) ↔
      deningerMeyerReflectedGaussianLineWronskian q = 0 ∨ Summable w := by
  rw [deningerCalderonWittGaussianHorizontalWronskianPacket_eq,
    deningerCalderonWittPacketWeightedNormalizable_horizonRay_iff]

/-- Every summable diagonal weight admits the Gaussian packet at every
divisor copy, so such a weight contains no horizontal selection. -/
theorem
    deningerCalderonWittGaussianHorizontalWronskianPacket_weightedNormalizable_of_summable
    {w : DeningerCalderonWittCrossPrimePacketIndex → ℝ}
    (hw : Summable w) (q : XiZeroCopy) :
    deningerCalderonWittPacketWeightedNormalizable w
      (deningerCalderonWittGaussianHorizontalWronskianPacket q) := by
  exact
    (deningerCalderonWittGaussianHorizontalWronskianPacket_weightedNormalizable_iff
      w q).2 (Or.inr hw)

/-- A nonsummable diagonal weight recovers the same critical-line selector
as the unweighted inverse-horizon domain; it does not derive admission. -/
theorem
    deningerCalderonWittGaussianHorizontalWronskianPacket_weightedNormalizable_iff_of_not_summable
    {w : DeningerCalderonWittCrossPrimePacketIndex → ℝ}
    (hw : ¬ Summable w) (q : XiZeroCopy) :
    deningerCalderonWittPacketWeightedNormalizable w
        (deningerCalderonWittGaussianHorizontalWronskianPacket q) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [
    deningerCalderonWittGaussianHorizontalWronskianPacket_weightedNormalizable_iff,
    or_iff_left hw,
    deningerMeyerReflectedGaussianLineWronskian_eq_zero_iff]

/-- On the residual Koszul ray, unweighted normalizability is equivalent to
literal vanishing of the packet. -/
theorem deningerCalderonWittGaussianHorizontalWronskianPacket_normalizable_iff_zero
    (q : XiZeroCopy) :
    deningerCalderonWittPacketUnweightedNormalizable
        (deningerCalderonWittGaussianHorizontalWronskianPacket q) ↔
      deningerCalderonWittGaussianHorizontalWronskianPacket q = 0 := by
  rw [deningerCalderonWittGaussianHorizontalWronskianPacket_eq,
    deningerCalderonWittPacketUnweightedNormalizable_horizonRay_iff]
  have hhorizon : deningerCalderonWittCrossPrimePacketHorizon ≠ 0 := by
    intro h
    have hn := congrArg norm h
    rw [deningerCalderonWittCrossPrimePacketHorizon_norm, norm_zero] at hn
    norm_num at hn
  exact (smul_eq_zero.trans (or_iff_left hhorizon)).symm

/-- The packet vanishes exactly at a critical-line divisor copy. -/
theorem deningerCalderonWittGaussianHorizontalWronskianPacket_eq_zero_iff
    (q : XiZeroCopy) :
    deningerCalderonWittGaussianHorizontalWronskianPacket q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  exact
    (deningerCalderonWittGaussianHorizontalWronskianPacket_normalizable_iff_zero q).symm.trans
      (deningerCalderonWittGaussianHorizontalWronskianPacket_normalizable_iff q)

/-- Every off-line divisor copy gives a concrete nonzero packet-valued
horizontal Koszul cycle. -/
theorem deningerCalderonWittGaussianHorizontalWronskianPacket_ne_zero_iff
    (q : XiZeroCopy) :
    deningerCalderonWittGaussianHorizontalWronskianPacket q ≠ 0 ↔
      (q.1 : ℂ).re ≠ 1 / 2 := by
  exact not_congr
    (deningerCalderonWittGaussianHorizontalWronskianPacket_eq_zero_iff q)

/-- **Old-boundary no-go.**  The old oriented boundary loses the horizontal
Gaussian packet under every continuous extension from the dense actual
arithmetic witness span, even when that packet is nonzero. -/
theorem
    deningerCalderonWittContinuousOrientedBoundaryExtension_kills_gaussianHorizontalWronskian
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (F : (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) →ₗ[ℂ] W)
    (B : DeningerCalderonWittCrossPrimePacketHilbert →L[ℂ] W)
    (hB : ∀ x : deningerCalderonWittCrossPrimeAlgebraicSourceSpan,
      B (deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert x) =
        F (deningerCalderonWittGlobalOrientedBoundary x.1.1))
    (q : XiZeroCopy) :
    B (deningerCalderonWittGaussianHorizontalWronskianPacket q) = 0 := by
  rw [deningerCalderonWittCrossPrimeContinuousOrientedBoundaryExtension_eq_zero
    F B hB]
  rfl

/-- Global inverse-horizon admission of the actual Gaussian horizontal
packet is exactly RH.  This theorem classifies the remaining source-domain
obligation; it does not assert that admission. -/
theorem forall_deningerCalderonWittGaussianHorizontalWronskianPacket_normalizable_iff_rh :
    (∀ q : XiZeroCopy,
      deningerCalderonWittPacketUnweightedNormalizable
        (deningerCalderonWittGaussianHorizontalWronskianPacket q)) ↔
      RiemannHypothesis := by
  rw [← deningerMeyerReflectedGaussianLineWronskian_vanishes_iff_riemannHypothesis]
  apply forall_congr'
  intro q
  exact
    (deningerCalderonWittGaussianHorizontalWronskianPacket_normalizable_iff q).trans
      (deningerMeyerReflectedGaussianLineWronskian_eq_zero_iff q).symm

/-- The universal Gaussian descent defect is exactly minus the normalized
prime-shell source entropy.  This identifies the abstract horizontal class
with a concrete arithmetic source coordinate before squaring. -/
theorem deningerMeyerReflectedGaussianLogJet_descentDefect_eq_sourceEntropy
    (q : XiZeroCopy) :
    involutiveDescentDefect xiZeroCopyLineConjEquiv
        deningerMeyerReflectedGaussianLogJet q =
      -((riemannReflectedSourceEntropy (q.1 : ℂ) : ℝ) : ℂ) /
        (2 * Real.pi) := by
  rw [deningerMeyerReflectedGaussianLogJet_descentDefect_eq,
    riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate]
  simp only [sourceCayleyTransverseRate, sub_re, one_re]
  push_cast
  ring

end DeningerMeyerGaussianGreen

end

end RHTower

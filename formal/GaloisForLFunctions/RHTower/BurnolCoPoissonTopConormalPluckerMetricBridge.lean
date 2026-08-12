import GaloisForLFunctions.RHTower.BVPrimeWindowCoPoissonNormalConnection
import GaloisForLFunctions.RHTower.BurnolCoPoissonConormalReflectionCover
import GaloisForLFunctions.RHTower.SourceZeroHorizontalCarrier

/-!
# Burnol top-conormal metric origin of the Route-P horizontal carrier

Argument expansion and dilation act on a compact-BV co-Poisson normal class by reciprocal Mellin
characters.  Their Fisher-weighted Hermitian mass imbalance is the Route-P Gamma Bockstein times
the squared normal amplitude.  This first conjecture has two exact darkness modes: a Mellin-dark
seed or a multiple zero whose first completed-zeta derivative vanishes.

The literal nested Burnol windows supply the required repair.  Differentiating at the exact
analytic order of each Xi divisor makes the common top conormal nonzero; the doubled-window
projective ratio cancels it and recovers the centered character.  At logarithmic length `log p`,
the reflected-minus-forward squared mass is exactly `sourceZeroHorizontalPrimeCarrier q p`, with
no seed-dark or multiplicity-dark alternative.  Hence every prime coefficient admitted into the
physical Pluecker detector has a multiplicity-complete, pre-Hilbert co-Poisson source origin.
-/

open Complex

noncomputable section
namespace RHTower

def xiCenteredCoPoissonCoordinate (q : XiZeroCopy) : ℂ :=
  (q.1 : ℂ) + 1 / 2

theorem norm_cpow_xiCenteredCoPoissonCoordinate_sub_one_sq
    (q : XiZeroCopy) (p : Nat.Primes) :
    ‖((p : ℝ) : ℂ) ^ (xiCenteredCoPoissonCoordinate q - 1)‖ ^ 2 =
      (p : ℝ) ^ primeDepthBVWoldXiCenteredRate q.1 := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hp, ← Real.rpow_natCast,
    ← Real.rpow_mul hp.le]
  congr 1
  simp [xiCenteredCoPoissonCoordinate, primeDepthBVWoldXiCenteredRate]
  ring

theorem norm_cpow_one_sub_xiCenteredCoPoissonCoordinate_sq
    (q : XiZeroCopy) (p : Nat.Primes) :
    ‖((p : ℝ) : ℂ) ^ (1 - xiCenteredCoPoissonCoordinate q)‖ ^ 2 =
      (p : ℝ) ^ (-primeDepthBVWoldXiCenteredRate q.1) := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hp, ← Real.rpow_natCast,
    ← Real.rpow_mul hp.le]
  congr 1
  simp [xiCenteredCoPoissonCoordinate, primeDepthBVWoldXiCenteredRate]
  ring

/-- Fisher-weighted Hermitian imbalance between expansion and dilation of the co-Poisson normal
class. -/
def coPoissonNormalMetricImbalance
    (W : CompactBVPrimeWindow) (q : XiZeroCopy) (p : Nat.Primes) : ℝ :=
  primeActivationOccupancyFisherDensity p *
    (‖(W.argumentExpansion (p : ℝ) (by exact_mod_cast p.prop.pos)).coPoissonNormalClass
          (xiCenteredCoPoissonCoordinate q)‖ ^ 2 -
      ‖(W.argumentDilation (p : ℝ) (by exact_mod_cast p.prop.pos)).coPoissonNormalClass
          (xiCenteredCoPoissonCoordinate q)‖ ^ 2)

/-- The horizontal Gamma Bockstein is exactly the relative Hermitian dilation imbalance of the
co-Poisson conormal class.  The normal amplitude remains as a common square factor, so no
division or simple-zero assumption is used. -/
theorem coPoissonNormalMetricImbalance_eq_bockstein_mul_norm_sq
    (W : CompactBVPrimeWindow) (q : XiZeroCopy) (p : Nat.Primes) :
    coPoissonNormalMetricImbalance W q p =
      sourceZeroHorizontalPrimeCarrier q p *
        ‖W.coPoissonNormalClass (xiCenteredCoPoissonCoordinate q)‖ ^ 2 := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  rw [coPoissonNormalMetricImbalance,
    CompactBVPrimeWindow.coPoissonNormalClass_argumentExpansion,
    CompactBVPrimeWindow.coPoissonNormalClass_argumentDilation,
    norm_mul, norm_mul, mul_pow, mul_pow,
    norm_cpow_one_sub_xiCenteredCoPoissonCoordinate_sq,
    norm_cpow_xiCenteredCoPoissonCoordinate_sub_one_sq]
  rw [sourceZeroHorizontalPrimeCarrier,
    primeGammaCofinalBocksteinCoefficient,
    primeActivationOccupancyFisherTwist,
    primeActivationOccupancyFisherTwist]
  ring

/-- Exact radical classification: normal-class metric imbalance loses horizontal information only
on the critical line or when the chosen conormal class itself is dark. -/
theorem coPoissonNormalMetricImbalance_eq_zero_iff
    (W : CompactBVPrimeWindow) (q : XiZeroCopy) (p : Nat.Primes) :
    coPoissonNormalMetricImbalance W q p = 0 ↔
      (q.1 : ℂ).re = 1 / 2 ∨
        W.coPoissonNormalClass (xiCenteredCoPoissonCoordinate q) = 0 := by
  rw [coPoissonNormalMetricImbalance_eq_bockstein_mul_norm_sq,
    mul_eq_zero, sourceZeroHorizontalPrimeCarrier_eq_zero_iff,
    sq_eq_zero_iff, norm_eq_zero]

theorem coPoissonNormalClass_xiCentered_eq_zero_iff
    (W : CompactBVPrimeWindow) (q : XiZeroCopy) :
    W.coPoissonNormalClass (xiCenteredCoPoissonCoordinate q) = 0 ↔
      W.mellinTransform (xiCenteredCoPoissonCoordinate q) = 0 ∨
        deriv regularizedRiemannZeta (q.1 : ℂ) = 0 := by
  simp [CompactBVPrimeWindow.coPoissonNormalClass,
    xiCenteredCoPoissonCoordinate, mul_eq_zero]

/-- Full obstruction classification.  First conormal metric sees the Route-P Bockstein unless the
copy lies on line, seed Mellin value is dark, or completed-zeta first derivative vanishes. -/
theorem coPoissonNormalMetricImbalance_eq_zero_iff_line_or_seedDark_or_derivDark
    (W : CompactBVPrimeWindow) (q : XiZeroCopy) (p : Nat.Primes) :
    coPoissonNormalMetricImbalance W q p = 0 ↔
      (q.1 : ℂ).re = 1 / 2 ∨
        W.mellinTransform (xiCenteredCoPoissonCoordinate q) = 0 ∨
          deriv regularizedRiemannZeta (q.1 : ℂ) = 0 := by
  rw [coPoissonNormalMetricImbalance_eq_zero_iff,
    coPoissonNormalClass_xiCentered_eq_zero_iff]

/-! ## Multiplicity-complete repair by literal nested Burnol windows -/

/-- Centered projective top-conormal coordinate of two literal nested Burnol windows.  Its
derivative order is the exact analytic multiplicity of the Xi divisor support point. -/
def burnolActualCenteredConormalCoordinate
    (q : XiZeroCopy) (p : Nat.Primes) : ℂ :=
  Complex.exp (-(Real.log (p : ℝ) : ℂ) / 2) *
    burnolCoPoissonActualDoubledWindowConormalRatio (Real.log (p : ℝ)) q.1

/-- The projective top jet cancels every common zeta-conormal factor and recovers the canonical
half-density character. -/
theorem burnolActualCenteredConormalCoordinate_eq_character
    (q : XiZeroCopy) (p : Nat.Primes) :
    burnolActualCenteredConormalCoordinate q p =
      burnolCoPoissonCenteredConormalCharacter (Real.log (p : ℝ)) (q.1 : ℂ) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  rw [burnolActualCenteredConormalCoordinate,
    burnolCoPoissonActualDoubledWindowConormalRatio_eq_exp (Real.log_pos hp1),
    burnolCoPoissonCenteredConormalCharacter, ← Complex.exp_add]
  congr 1
  ring

/-- Squared radial mass of the literal top conormal is the forward modular character. -/
theorem norm_burnolActualCenteredConormalCoordinate_sq
    (q : XiZeroCopy) (p : Nat.Primes) :
    ‖burnolActualCenteredConormalCoordinate q p‖ ^ 2 =
      (p : ℝ) ^ primeDepthBVWoldXiCenteredRate q.1 := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  rw [burnolActualCenteredConormalCoordinate_eq_character,
    norm_burnolCoPoissonCenteredConormalCharacter,
    Real.rpow_def_of_pos hp, pow_two, ← Real.exp_add]
  congr 1
  rw [primeDepthBVWoldXiCenteredRate]
  ring

/-- Reflection turns the literal top-conormal mass into the inverse modular character. -/
theorem norm_burnolActualCenteredConormalCoordinate_reflection_sq
    (q : XiZeroCopy) (p : Nat.Primes) :
    ‖burnolActualCenteredConormalCoordinate (xiZeroCopyLineConjEquiv q) p‖ ^ 2 =
      (p : ℝ) ^ (-primeDepthBVWoldXiCenteredRate q.1) := by
  rw [norm_burnolActualCenteredConormalCoordinate_sq]
  change (p : ℝ) ^
      primeDepthBVWoldXiCenteredRate (xiZeroLineConjEquiv q.1) = _
  rw [primeDepthBVWoldXiCenteredRate_reflection]

/-- Fisher-weighted reflected-minus-forward Hermitian mass of the actual multiplicity-complete
Burnol top conormal. -/
def burnolActualConormalMetricImbalance
    (q : XiZeroCopy) (p : Nat.Primes) : ℝ :=
  primeActivationOccupancyFisherDensity p *
    (‖burnolActualCenteredConormalCoordinate (xiZeroCopyLineConjEquiv q) p‖ ^ 2 -
      ‖burnolActualCenteredConormalCoordinate q p‖ ^ 2)

/-- **Multiplicity-complete source identity.**  The Route-P horizontal carrier is exactly the
relative Hermitian mass imbalance of literal nested Burnol top-conormal jets.  Unlike a fixed
first normal, this coordinate has no seed-dark or multiple-zero-dark alternative. -/
theorem burnolActualConormalMetricImbalance_eq_sourceZeroHorizontalPrimeCarrier
    (q : XiZeroCopy) (p : Nat.Primes) :
    burnolActualConormalMetricImbalance q p =
      sourceZeroHorizontalPrimeCarrier q p := by
  rw [burnolActualConormalMetricImbalance,
    norm_burnolActualCenteredConormalCoordinate_reflection_sq,
    norm_burnolActualCenteredConormalCoordinate_sq,
    sourceZeroHorizontalPrimeCarrier,
    primeGammaCofinalBocksteinCoefficient,
    primeActivationOccupancyFisherTwist,
    primeActivationOccupancyFisherTwist]
  ring

/-- The actual top-conormal metric has no darkness: its radical is exactly the critical line. -/
theorem burnolActualConormalMetricImbalance_eq_zero_iff
    (q : XiZeroCopy) (p : Nat.Primes) :
    burnolActualConormalMetricImbalance q p = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [burnolActualConormalMetricImbalance_eq_sourceZeroHorizontalPrimeCarrier,
    sourceZeroHorizontalPrimeCarrier_eq_zero_iff]

end RHTower

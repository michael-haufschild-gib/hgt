import GaloisForLFunctions.RHTower.EulerSquarefreeWickOppositeResidueCrossing
import GaloisForLFunctions.RHTower.HedenmalmStokesOrientedFirstTraceQuantizedJump

/-!
# EWQ--Hedenmalm reflected crossing

The EWQ opposite-residue form and Hedenmalm's moving-horizon Xi carrier meet coefficientwise.
Polarizing the EWQ crossing in two real amplitudes gives

`4 log(p) z w`.

For the literal signed moving-horizon connection, the self-crossing is exactly one half of the
source-native covariant Stokes first trace.  Functional-equation reflection negates this amplitude,
so the mixed reflected crossing is the negative of that positive self-energy.

Consequently reflection positivity of this combined channel at one actual prime and one residue
cell is equivalent to RH.  This is not an assumed positivity theorem: it precisely locates the
remaining producer.  Standard squaring keeps the Hedenmalm energy positive but erases orientation;
the EWQ polarization retains orientation and is strictly reflection-negative off the critical
line.  Any successful QFT/Wick completion must therefore prove positivity for this exact mixed
incidence, not for its scalar square.
-/

open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Bilinear polarization of the EWQ opposite-residue prime crossing. -/
def eulerPrimeQuadraticResidueOppositeBilinearCrossing
    (p : Nat.Primes) (z w : ℝ) (x y : Fin 2) : ℝ :=
  (GaloisForLFunctions.residuePairing
      (MonoidAlgebra.single
        (GaloisForLFunctions.EulerCharGroup.ofNat p.1 p.2.pos) (1 : ℂ))
      (MonoidAlgebra.single
        (GaloisForLFunctions.EulerCharGroup.ofNat p.1 p.2.pos)⁻¹ (1 : ℂ))).re *
    quadraticResidueKreinForm (quadraticResiduePureRealDepthCoordinates z x y)
      (quadraticResidueDoubleNegativeTranslation
        (quadraticResiduePureRealDepthCoordinates w x y))

/-- Exact polarized prime law. -/
theorem eulerPrimeQuadraticResidueOppositeBilinearCrossing_eq
    (p : Nat.Primes) (z w : ℝ) (x y : Fin 2) :
    eulerPrimeQuadraticResidueOppositeBilinearCrossing p z w x y =
      4 * Real.log (p.1 : ℝ) * z * w := by
  rw [eulerPrimeQuadraticResidueOppositeBilinearCrossing,
    GaloisForLFunctions.residuePairing_opposite,
    quadraticResidueDoubleNegativeTranslation_pureDepth,
    quadraticResidueKreinForm_pureDepth_opposite,
    GaloisForLFunctions.EulerCharGroup.logVal_eq_natLog p.2.pos]
  simp only [Complex.ofReal_re]
  ring

/-- Diagonal polarization recovers the previously constructed EWQ crossing. -/
theorem eulerPrimeQuadraticResidueOppositeBilinearCrossing_self
    (p : Nat.Primes) (z : ℝ) (x y : Fin 2) :
    eulerPrimeQuadraticResidueOppositeBilinearCrossing p z z x y =
      eulerPrimeQuadraticResidueOppositeCrossing p z x y := by
  rfl

/-- The literal signed Hedenmalm moving-horizon connection sampled at one prime. -/
def ewqHedenmalmCovariantAmplitude
    (p : Nat.Primes) (q : _root_.RHTower.XiZeroCopy) : ℝ :=
  _root_.RHTower.HedenmalmThetaSource.thetaMovingHorizonConnection
    (_root_.RHTower.HedenmalmThetaSource.thetaWardContinuousHalfDensityProfile q)
    (Real.log (p : ℝ))

/-- Xi reflection negates the complete covariant amplitude labelwise. -/
theorem ewqHedenmalmCovariantAmplitude_copyReflect
    (p : Nat.Primes) (q : _root_.RHTower.XiZeroCopy) :
    ewqHedenmalmCovariantAmplitude p (_root_.RHTower.xiZeroCopyReflectEquiv q) =
      -ewqHedenmalmCovariantAmplitude p q := by
  rw [ewqHedenmalmCovariantAmplitude, ewqHedenmalmCovariantAmplitude,
    _root_.RHTower.HedenmalmThetaSource.thetaMovingHorizonConnection_eq_centeredRate_mul,
    _root_.RHTower.HedenmalmThetaSource.thetaMovingHorizonConnection_eq_centeredRate_mul,
    _root_.RHTower.HedenmalmThetaSource.primeDepthBVWoldXiCenteredRate_copyReflect,
    abs_neg]
  ring

/-- **Coefficient-exact EWQ--Hedenmalm weld.** Twice the EWQ self-crossing is the literal
covariantly renormalized Stokes first-trace moment. -/
theorem two_mul_ewqHedenmalm_selfCrossing_eq_covariantFirstTrace
    (p : Nat.Primes) (q : _root_.RHTower.XiZeroCopy) (x y : Fin 2) :
    2 * eulerPrimeQuadraticResidueOppositeBilinearCrossing p
        (ewqHedenmalmCovariantAmplitude p q)
        (ewqHedenmalmCovariantAmplitude p q) x y =
      _root_.RHTower.gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment
        |_root_.RHTower.primeDepthBVWoldXiCenteredRate q.1| p := by
  rw [eulerPrimeQuadraticResidueOppositeBilinearCrossing_eq,
    ← _root_.RHTower.thetaWardMovingHorizonCovariantPrimeTerm_eq_stokesCovariantFirstTrace p q]
  simp only [ewqHedenmalmCovariantAmplitude]
  ring

/-- The mixed Xi-reflected crossing is the negative EWQ self-energy. -/
theorem ewqHedenmalm_reflectedCrossing_eq_neg_self
    (p : Nat.Primes) (q : _root_.RHTower.XiZeroCopy) (x y : Fin 2) :
    eulerPrimeQuadraticResidueOppositeBilinearCrossing p
        (ewqHedenmalmCovariantAmplitude p q)
        (ewqHedenmalmCovariantAmplitude p (_root_.RHTower.xiZeroCopyReflectEquiv q)) x y =
      -eulerPrimeQuadraticResidueOppositeCrossing p
        (ewqHedenmalmCovariantAmplitude p q) x y := by
  rw [ewqHedenmalmCovariantAmplitude_copyReflect,
    eulerPrimeQuadraticResidueOppositeBilinearCrossing_eq,
    eulerPrimeQuadraticResidueOppositeCrossing_eq]
  ring

/-- The covariant amplitude is nonzero exactly off the critical line grade. -/
theorem ewqHedenmalmCovariantAmplitude_ne_zero_iff
    (p : Nat.Primes) (q : _root_.RHTower.XiZeroCopy) :
    ewqHedenmalmCovariantAmplitude p q ≠ 0 ↔
      _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1 ≠ 0 := by
  rw [ewqHedenmalmCovariantAmplitude,
    _root_.RHTower.HedenmalmThetaSource.thetaMovingHorizonConnection_eq_centeredRate_mul]
  constructor
  · intro hne hrate
    apply hne
    rw [hrate, zero_mul]
  · intro hrate
    exact mul_ne_zero hrate (Real.exp_ne_zero _)

/-- **Pointwise reflection-positivity wall.** The mixed EWQ--Hedenmalm crossing is nonnegative
exactly on the critical line. -/
theorem ewqHedenmalm_reflectedCrossing_nonneg_iff_re_eq_half
    (p : Nat.Primes) (q : _root_.RHTower.XiZeroCopy) (x y : Fin 2) :
    0 ≤ eulerPrimeQuadraticResidueOppositeBilinearCrossing p
        (ewqHedenmalmCovariantAmplitude p q)
        (ewqHedenmalmCovariantAmplitude p (_root_.RHTower.xiZeroCopyReflectEquiv q)) x y ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [ewqHedenmalm_reflectedCrossing_eq_neg_self, neg_nonneg]
  constructor
  · intro hnonpos
    have hzero : eulerPrimeQuadraticResidueOppositeCrossing p
        (ewqHedenmalmCovariantAmplitude p q) x y = 0 :=
      le_antisymm hnonpos
        (eulerPrimeQuadraticResidueOppositeCrossing_nonneg p
          (ewqHedenmalmCovariantAmplitude p q) x y)
    have hamp : ewqHedenmalmCovariantAmplitude p q = 0 := by
      by_contra hne
      have hpos := eulerPrimeQuadraticResidueOppositeCrossing_pos p hne x y
      rw [hzero] at hpos
      exact (lt_irrefl 0 hpos)
    have hrate : _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1 = 0 := by
      by_contra hrate
      exact ((ewqHedenmalmCovariantAmplitude_ne_zero_iff p q).2 hrate) hamp
    exact (_root_.RHTower.primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).1 hrate
  · intro hline
    have hrate :=
      (_root_.RHTower.primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2 hline
    have hamp : ewqHedenmalmCovariantAmplitude p q = 0 := by
      rw [ewqHedenmalmCovariantAmplitude,
        _root_.RHTower.HedenmalmThetaSource.thetaMovingHorizonConnection_eq_centeredRate_mul,
        hrate, zero_mul]
    rw [eulerPrimeQuadraticResidueOppositeCrossing_eq, hamp]
    norm_num

/-- Global reflection-positive producer target at one fixed prime and residue cell. -/
def EveryXiEWQHedenmalmReflectedCrossingNonnegativeAt
    (p : Nat.Primes) (x y : Fin 2) : Prop :=
  ∀ q : _root_.RHTower.XiZeroCopy,
    0 ≤ eulerPrimeQuadraticResidueOppositeBilinearCrossing p
      (ewqHedenmalmCovariantAmplitude p q)
      (ewqHedenmalmCovariantAmplitude p (_root_.RHTower.xiZeroCopyReflectEquiv q)) x y

/-- Reflection positivity of one coefficient-exact EWQ--Hedenmalm channel is exactly RH. -/
theorem everyXiEWQHedenmalmReflectedCrossingNonnegativeAt_iff_rh
    (p : Nat.Primes) (x y : Fin 2) :
    EveryXiEWQHedenmalmReflectedCrossingNonnegativeAt p x y ↔
      _root_.RiemannHypothesis := by
  constructor
  · intro h
    apply _root_.RHTower.riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro rho
    let q := _root_.RHTower.xiFirstZeroCopy rho
    have hq := (ewqHedenmalm_reflectedCrossing_nonneg_iff_re_eq_half p q x y).1 (h q)
    simpa [q] using hq
  · intro hRH q
    exact (ewqHedenmalm_reflectedCrossing_nonneg_iff_re_eq_half p q x y).2
      (_root_.RHTower.xi_divisor_support_re_eq_half_of_rh hRH q.1)

end GaloisForLFunctions.RHTower

import GaloisForLFunctions.RHTower.GammaSewnEulerCalibratedExterior
import GaloisForLFunctions.RHTower.PrimitiveFibreModularRenormalizationLaw
import GaloisForLFunctions.RHTower.CCMFirstClockJuliaPrincipalRelativeNoGo
import GaloisForLFunctions.RHTower.CCMFirstClockExteriorCapacitySingularity

/-!
# Primitive-promoted Euler exterior source

The literal Euler boundary amplitude is a half-density.  Route J's first-clock capacity
singularity forces any exterior carrier capable of seeing the hard prime block to create a
square-root-logarithmic multiplier.  This module constructs that multiplier from the arithmetic
source itself:

`P(p,e) = sqrt (log p)`.

Before scalar fusion, `P` sends the Euler boundary half-density exactly to the critical
von-Mangoldt/Mellin prime-power current.  The resulting exterior current keeps both prime and
valuation-depth labels.  Its modular deformation has exact reflected geometric mean and an
intrinsic reflection-odd center jet.

At depth zero on the certified first-clock block, the promoted current sandwiches every literal
bad coefficient within a factor two.  Moreover its squared multiplier is trapped between the
two endpoint logarithms of the block.  Thus this is a source construction realizing, rather than
postulating, the minimum singularity previously proved necessary for Route J.

No uniform cofinal budget is asserted here.  That is the remaining global Gamma/co-Poisson
shorting problem.
-/

open Set Finset Filter Topology
open scoped BigOperators

noncomputable section
namespace RHTower

/-- Source-forced half-density promotion on a prime-valuation cell. -/
def xiGammaEulerPrimitivePromotion (pe : Nat.Primes × ℕ) : ℝ :=
  Real.sqrt (Real.log (pe.1 : ℝ))

/-- Euler boundary amplitude after primitive promotion and before scalar fusion. -/
def xiGammaEulerPrimitiveBoundaryAmplitude
    (u : ℝ) (pe : Nat.Primes × ℕ) : ℝ :=
  xiGammaEulerPrimitivePromotion pe *
    xiGammaEulerBoundaryRealAmplitude u pe

theorem xiGammaEulerPrimitiveBoundaryAmplitude_pos
    (u : ℝ) (pe : Nat.Primes × ℕ) :
    0 < xiGammaEulerPrimitiveBoundaryAmplitude u pe := by
  exact mul_pos
    (Real.sqrt_pos.2
      (Real.log_pos (by exact_mod_cast pe.1.property.one_lt)))
    (xiGammaEulerBoundaryRealAmplitude_pos u pe)

/-- Exact promoted density.  Promotion contributes the second copy of the primitive logarithm. -/
theorem xiGammaEulerPrimitiveBoundaryAmplitude_sq
    (u : ℝ) (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveBoundaryAmplitude u pe ^ 2 =
      Real.log (pe.1 : ℝ) ^ 2 /
          (xiGammaEulerValuationNat pe : ℝ) *
        Real.exp (-u * Real.log (xiGammaEulerValuationNat pe)) := by
  have hpLog : 0 ≤ Real.log (pe.1 : ℝ) :=
    (Real.log_pos (by exact_mod_cast pe.1.property.one_lt)).le
  have hnNat : 0 < xiGammaEulerValuationNat pe := by
    unfold xiGammaEulerValuationNat
    exact Nat.pow_pos (Nat.Prime.pos pe.1.property)
  have hn : (0 : ℝ) < xiGammaEulerValuationNat pe := by
    exact_mod_cast hnNat
  rw [xiGammaEulerPrimitiveBoundaryAmplitude,
    xiGammaEulerPrimitivePromotion, mul_pow, Real.sq_sqrt hpLog]
  unfold xiGammaEulerBoundaryRealAmplitude
  rw [Real.sq_sqrt]
  · ring
  · exact mul_nonneg (div_nonneg hpLog hn.le) (Real.exp_pos _).le

/-- At the critical source section, primitive promotion lands exactly on the local primitive
fibre current. -/
theorem xiGammaEulerPrimitiveBoundaryAmplitude_zero_eq_primitiveFibreCriticalCurrent
    (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveBoundaryAmplitude 0 pe =
      primitiveFibreCriticalCurrent (Real.log (pe.1 : ℝ))
        (criticalPrimeTowerRadius pe.1) pe.2 := by
  have hleft := xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 pe
  have hpLog : 0 < Real.log (pe.1 : ℝ) :=
    Real.log_pos (by exact_mod_cast pe.1.property.one_lt)
  have hr := criticalPrimeTowerRadius_pos pe.1.property.pos
  have hright :
      0 < primitiveFibreCriticalCurrent (Real.log (pe.1 : ℝ))
          (criticalPrimeTowerRadius pe.1) pe.2 := by
    unfold primitiveFibreCriticalCurrent
    positivity
  have hsqLeft := xiGammaEulerPrimitiveBoundaryAmplitude_sq 0 pe
  have hval :
      (xiGammaEulerValuationNat pe : ℝ) =
        (pe.1 : ℝ) ^ (pe.2 + 1) := by
    simp [xiGammaEulerValuationNat]
  have hsqRight :
      primitiveFibreCriticalCurrent (Real.log (pe.1 : ℝ))
          (criticalPrimeTowerRadius pe.1) pe.2 ^ 2 =
        Real.log (pe.1 : ℝ) ^ 2 /
          (xiGammaEulerValuationNat pe : ℝ) := by
    rw [primitiveFibreCriticalCurrent, mul_pow, ← pow_mul,
      show (pe.2 + 1) * 2 = 2 * (pe.2 + 1) by omega,
      pow_mul, criticalPrimeTowerRadius_sq (pe.1 : ℕ)]
    rw [hval, inv_pow]
    ring
  norm_num at hsqLeft
  nlinarith

/-- The promoted Euler source is literally the critical von-Mangoldt/Mellin atom at every
prime-power depth. -/
theorem xiGammaEulerPrimitiveBoundaryAmplitude_zero_eq_criticalMellinAtomWeight
    (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveBoundaryAmplitude 0 pe =
      criticalMellinAtomWeight (xiGammaEulerValuationNat pe) := by
  rw [
    xiGammaEulerPrimitiveBoundaryAmplitude_zero_eq_primitiveFibreCriticalCurrent,
    primitiveFibreCriticalCurrent_prime]
  rfl

/-- Prime/depth-labelled promoted exterior source, before Hermitian scalarization. -/
def xiGammaEulerPrimitiveExteriorCell
    (u : ℝ) (i j : Nat.Primes × ℕ) : ℝ :=
  xiGammaEulerPrimitiveBoundaryAmplitude u i *
    xiGammaEulerPrimitiveBoundaryAmplitude u j *
      (xiGammaEulerBoundaryHalfHeight i.1 i.2 -
        xiGammaEulerBoundaryHalfHeight j.1 j.2)

/-- Promotion is applied independently on both source legs before exterior fusion. -/
theorem xiGammaEulerPrimitiveExteriorCell_eq_promotion_mul
    (u : ℝ) (i j : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveExteriorCell u i j =
      xiGammaEulerPrimitivePromotion i *
        xiGammaEulerPrimitivePromotion j *
          xiGammaEulerBoundaryExteriorCell u i j := by
  unfold xiGammaEulerPrimitiveExteriorCell
    xiGammaEulerPrimitiveBoundaryAmplitude
    xiGammaEulerBoundaryExteriorCell
  ring

/-- At the critical source section, both exterior legs are literal critical Mellin atoms. -/
theorem xiGammaEulerPrimitiveExteriorCell_zero_eq_critical
    (i j : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveExteriorCell 0 i j =
      criticalMellinAtomWeight (xiGammaEulerValuationNat i) *
        criticalMellinAtomWeight (xiGammaEulerValuationNat j) *
          (xiGammaEulerBoundaryHalfHeight i.1 i.2 -
            xiGammaEulerBoundaryHalfHeight j.1 j.2) := by
  rw [xiGammaEulerPrimitiveExteriorCell,
    xiGammaEulerPrimitiveBoundaryAmplitude_zero_eq_criticalMellinAtomWeight,
    xiGammaEulerPrimitiveBoundaryAmplitude_zero_eq_criticalMellinAtomWeight]

@[simp] theorem xiGammaEulerPrimitiveExteriorCell_self
    (u : ℝ) (i : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveExteriorCell u i i = 0 := by
  simp [xiGammaEulerPrimitiveExteriorCell]

theorem xiGammaEulerPrimitiveExteriorCell_swap
    (u : ℝ) (i j : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveExteriorCell u j i =
      -xiGammaEulerPrimitiveExteriorCell u i j := by
  unfold xiGammaEulerPrimitiveExteriorCell
  ring

/-- Infinitesimal modular rate of one prime/depth cell. -/
def xiGammaEulerPrimitiveModularRate
    (pe : Nat.Primes × ℕ) : ℝ :=
  2 * (pe.2 + 1) * Real.log (criticalPrimeTowerRadius pe.1)

/-- Source-pointed modular deformation of the promoted critical current. -/
def xiGammaEulerPrimitiveModularCurrent
    (a : ℝ) (pe : Nat.Primes × ℕ) : ℝ :=
  xiGammaEulerPrimitiveBoundaryAmplitude 0 pe *
    Real.exp (a * xiGammaEulerPrimitiveModularRate pe)

/-- Modular exterior source retaining prime, depth, and centered modular parameter. -/
def xiGammaEulerPrimitiveModularExterior
    (a : ℝ) (i j : Nat.Primes × ℕ) : ℝ :=
  xiGammaEulerPrimitiveModularCurrent a i *
    xiGammaEulerPrimitiveModularCurrent a j *
      (xiGammaEulerBoundaryHalfHeight i.1 i.2 -
        xiGammaEulerBoundaryHalfHeight j.1 j.2)

/-- Reflection-odd part is formed before scalar fusion. -/
def xiGammaEulerPrimitiveReflectionOddExterior
    (a : ℝ) (i j : Nat.Primes × ℕ) : ℝ :=
  (xiGammaEulerPrimitiveModularExterior a i j -
    xiGammaEulerPrimitiveModularExterior (-a) i j) / 2

theorem xiGammaEulerPrimitiveReflectionOddExterior_neg
    (a : ℝ) (i j : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveReflectionOddExterior (-a) i j =
      -xiGammaEulerPrimitiveReflectionOddExterior a i j := by
  unfold xiGammaEulerPrimitiveReflectionOddExterior
  rw [neg_neg]
  ring

theorem xiGammaEulerPrimitiveReflectionOddExterior_swap
    (a : ℝ) (i j : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveReflectionOddExterior a j i =
      -xiGammaEulerPrimitiveReflectionOddExterior a i j := by
  unfold xiGammaEulerPrimitiveReflectionOddExterior
    xiGammaEulerPrimitiveModularExterior
  ring

@[simp] theorem xiGammaEulerPrimitiveReflectionOddExterior_zero
    (i j : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveReflectionOddExterior 0 i j = 0 := by
  simp [xiGammaEulerPrimitiveReflectionOddExterior]

/-- The new modular current is exactly the existing primitive-fibre deformation, not a fitted
coefficient family. -/
theorem xiGammaEulerPrimitiveModularCurrent_eq_primitiveFibre
    (a : ℝ) (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveModularCurrent a pe =
      primitiveFibreModularCurrent (Real.log (pe.1 : ℝ))
        (criticalPrimeTowerRadius pe.1) a pe.2 := by
  rw [xiGammaEulerPrimitiveModularCurrent,
    xiGammaEulerPrimitiveBoundaryAmplitude_zero_eq_primitiveFibreCriticalCurrent]
  unfold primitiveFibreModularCurrent primitiveFibreModularTilt
    xiGammaEulerPrimitiveModularRate
  congr 2
  ring

theorem xiGammaEulerPrimitiveModularCurrent_zero
    (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveModularCurrent 0 pe =
      xiGammaEulerPrimitiveBoundaryAmplitude 0 pe := by
  simp [xiGammaEulerPrimitiveModularCurrent]

/-- Reflected deformations have the promoted critical current as exact geometric mean. -/
theorem xiGammaEulerPrimitiveModularCurrent_mul_reflection
    (a : ℝ) (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveModularCurrent a pe *
        xiGammaEulerPrimitiveModularCurrent (-a) pe =
      xiGammaEulerPrimitiveBoundaryAmplitude 0 pe ^ 2 := by
  rw [
    xiGammaEulerPrimitiveBoundaryAmplitude_zero_eq_primitiveFibreCriticalCurrent,
    xiGammaEulerPrimitiveModularCurrent_eq_primitiveFibre,
    xiGammaEulerPrimitiveModularCurrent_eq_primitiveFibre]
  exact primitiveFibreModularCurrent_mul_reflection _ _ _ _

theorem criticalPrimeTowerRadius_log
    (p : Nat.Primes) :
    Real.log (criticalPrimeTowerRadius p) =
      -(1 / 2 : ℝ) * Real.log (p : ℝ) := by
  rw [criticalPrimeTowerRadius,
    Real.log_rpow (by exact_mod_cast p.property.pos)]
  ring

/-- The modular rate is not an independent clock: it is exactly minus twice the physical Euler
half-height.  This locks modular reflection to the source phase. -/
theorem xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight
    (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveModularRate pe =
      -2 * xiGammaEulerBoundaryHalfHeight pe.1 pe.2 := by
  rw [xiGammaEulerPrimitiveModularRate, criticalPrimeTowerRadius_log,
    xiGammaEulerBoundaryHalfHeight]
  ring

/-- The two-leg modular deformation depends on the sum of the two source rates. -/
theorem xiGammaEulerPrimitiveModularExterior_eq
    (a : ℝ) (i j : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveModularExterior a i j =
      xiGammaEulerPrimitiveBoundaryAmplitude 0 i *
        xiGammaEulerPrimitiveBoundaryAmplitude 0 j *
          Real.exp (a * (xiGammaEulerPrimitiveModularRate i +
            xiGammaEulerPrimitiveModularRate j)) *
            (xiGammaEulerBoundaryHalfHeight i.1 i.2 -
              xiGammaEulerBoundaryHalfHeight j.1 j.2) := by
  unfold xiGammaEulerPrimitiveModularExterior
    xiGammaEulerPrimitiveModularCurrent
  calc
    xiGammaEulerPrimitiveBoundaryAmplitude 0 i *
          Real.exp (a * xiGammaEulerPrimitiveModularRate i) *
          (xiGammaEulerPrimitiveBoundaryAmplitude 0 j *
            Real.exp (a * xiGammaEulerPrimitiveModularRate j)) *
          (xiGammaEulerBoundaryHalfHeight i.1 i.2 -
            xiGammaEulerBoundaryHalfHeight j.1 j.2) =
        xiGammaEulerPrimitiveBoundaryAmplitude 0 i *
          xiGammaEulerPrimitiveBoundaryAmplitude 0 j *
          (Real.exp (a * xiGammaEulerPrimitiveModularRate i) *
            Real.exp (a * xiGammaEulerPrimitiveModularRate j)) *
          (xiGammaEulerBoundaryHalfHeight i.1 i.2 -
            xiGammaEulerBoundaryHalfHeight j.1 j.2) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      rw [show
        a * xiGammaEulerPrimitiveModularRate i +
            a * xiGammaEulerPrimitiveModularRate j =
          a * (xiGammaEulerPrimitiveModularRate i +
            xiGammaEulerPrimitiveModularRate j) by ring]

/-- Algebraic center jet of the reflection-odd modular exterior source. -/
def xiGammaEulerPrimitiveOddJetExterior
    (i j : Nat.Primes × ℕ) : ℝ :=
  xiGammaEulerPrimitiveBoundaryAmplitude 0 i *
    xiGammaEulerPrimitiveBoundaryAmplitude 0 j *
      (xiGammaEulerPrimitiveModularRate i +
        xiGammaEulerPrimitiveModularRate j) *
        (xiGammaEulerBoundaryHalfHeight i.1 i.2 -
          xiGammaEulerBoundaryHalfHeight j.1 j.2)

/-- **Squared-height transgression.**  Because the modular rate is locked to Euler height, the
reflection-odd center jet is exactly the exterior current of squared source height.  This is the
extra logarithmic source layer absent from bounded exterior polarizations. -/
theorem xiGammaEulerPrimitiveOddJetExterior_eq_squaredHeight
    (i j : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveOddJetExterior i j =
      -2 * xiGammaEulerPrimitiveBoundaryAmplitude 0 i *
        xiGammaEulerPrimitiveBoundaryAmplitude 0 j *
          (xiGammaEulerBoundaryHalfHeight i.1 i.2 ^ 2 -
            xiGammaEulerBoundaryHalfHeight j.1 j.2 ^ 2) := by
  rw [xiGammaEulerPrimitiveOddJetExterior,
    xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight,
    xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight]
  ring

/-- Division-free longitudinal shorting of the odd modular jet at a source height anchor. -/
def xiGammaEulerPrimitiveAnchoredOddJetExterior
    (H : ℝ) (i j : Nat.Primes × ℕ) : ℝ :=
  xiGammaEulerPrimitiveOddJetExterior i j +
    4 * H * xiGammaEulerPrimitiveExteriorCell 0 i j

/-- **Gamma-anchor shorting identity.**  Adding the source-anchored longitudinal counterterm
centers the squared-height transgression exactly.  No quotient or target coefficient is used. -/
theorem xiGammaEulerPrimitiveAnchoredOddJetExterior_eq_centeredSquare
    (H : ℝ) (i j : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveAnchoredOddJetExterior H i j =
      -2 * xiGammaEulerPrimitiveBoundaryAmplitude 0 i *
        xiGammaEulerPrimitiveBoundaryAmplitude 0 j *
          ((xiGammaEulerBoundaryHalfHeight i.1 i.2 - H) ^ 2 -
            (xiGammaEulerBoundaryHalfHeight j.1 j.2 - H) ^ 2) := by
  rw [xiGammaEulerPrimitiveAnchoredOddJetExterior,
    xiGammaEulerPrimitiveOddJetExterior_eq_squaredHeight]
  unfold xiGammaEulerPrimitiveExteriorCell
  ring

/-- Source-height phased pair carried by the negative half of the anchored odd jet. -/
def xiGammaEulerPrimitiveAnchoredOddJetPhasedPair
    (H τ : ℝ) (i j : Nat.Primes × ℕ) : ℝ :=
  -(1 / 2 : ℝ) *
    xiGammaEulerPrimitiveAnchoredOddJetExterior H i j *
      Real.sin (τ *
        (xiGammaEulerBoundaryHalfHeight i.1 i.2 -
          xiGammaEulerBoundaryHalfHeight j.1 j.2))

/-- Above the anchor and before phase wrap, every anchored odd-jet pair is nonnegative. -/
theorem xiGammaEulerPrimitiveAnchoredOddJetPhasedPair_nonneg
    {H τ : ℝ} {i j : Nat.Primes × ℕ}
    (hτ : 0 ≤ τ)
    (hi : H ≤ xiGammaEulerBoundaryHalfHeight i.1 i.2)
    (hj : H ≤ xiGammaEulerBoundaryHalfHeight j.1 j.2)
    (hphase :
      |τ * (xiGammaEulerBoundaryHalfHeight i.1 i.2 -
        xiGammaEulerBoundaryHalfHeight j.1 j.2)| ≤ Real.pi) :
    0 ≤ xiGammaEulerPrimitiveAnchoredOddJetPhasedPair H τ i j := by
  let ai := xiGammaEulerPrimitiveBoundaryAmplitude 0 i
  let aj := xiGammaEulerPrimitiveBoundaryAmplitude 0 j
  let hi' := xiGammaEulerBoundaryHalfHeight i.1 i.2
  let hj' := xiGammaEulerBoundaryHalfHeight j.1 j.2
  have hai : 0 ≤ ai :=
    (xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 i).le
  have haj : 0 ≤ aj :=
    (xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 j).le
  have hcenter : 0 ≤ hi' + hj' - 2 * H := by
    dsimp only [hi', hj']
    linarith
  have hsin :
      0 ≤ (hi' - hj') * Real.sin (τ * (hi' - hj')) :=
    mul_sin_mul_nonneg_of_phaseBound hτ (by simpa only [hi', hj'] using hphase)
  rw [xiGammaEulerPrimitiveAnchoredOddJetPhasedPair,
    xiGammaEulerPrimitiveAnchoredOddJetExterior_eq_centeredSquare]
  dsimp only [ai, aj, hi', hj'] at hai haj hcenter hsin ⊢
  rw [show
    (xiGammaEulerBoundaryHalfHeight i.1 i.2 - H) ^ 2 -
        (xiGammaEulerBoundaryHalfHeight j.1 j.2 - H) ^ 2 =
      (xiGammaEulerBoundaryHalfHeight i.1 i.2 -
        xiGammaEulerBoundaryHalfHeight j.1 j.2) *
      (xiGammaEulerBoundaryHalfHeight i.1 i.2 +
        xiGammaEulerBoundaryHalfHeight j.1 j.2 - 2 * H) by ring]
  rw [show
    -(1 / 2 : ℝ) *
        (-2 * xiGammaEulerPrimitiveBoundaryAmplitude 0 i *
          xiGammaEulerPrimitiveBoundaryAmplitude 0 j *
          ((xiGammaEulerBoundaryHalfHeight i.1 i.2 -
            xiGammaEulerBoundaryHalfHeight j.1 j.2) *
            (xiGammaEulerBoundaryHalfHeight i.1 i.2 +
              xiGammaEulerBoundaryHalfHeight j.1 j.2 - 2 * H))) *
          Real.sin (τ * (xiGammaEulerBoundaryHalfHeight i.1 i.2 -
            xiGammaEulerBoundaryHalfHeight j.1 j.2)) =
      (xiGammaEulerPrimitiveBoundaryAmplitude 0 i *
        xiGammaEulerPrimitiveBoundaryAmplitude 0 j) *
        (xiGammaEulerBoundaryHalfHeight i.1 i.2 +
          xiGammaEulerBoundaryHalfHeight j.1 j.2 - 2 * H) *
        ((xiGammaEulerBoundaryHalfHeight i.1 i.2 -
          xiGammaEulerBoundaryHalfHeight j.1 j.2) *
          Real.sin (τ * (xiGammaEulerBoundaryHalfHeight i.1 i.2 -
            xiGammaEulerBoundaryHalfHeight j.1 j.2))) by ring]
  exact mul_nonneg (mul_nonneg (mul_nonneg hai haj) hcenter) hsin

/-- Finite scalar current of the anchored reflection-odd source. -/
def xiGammaEulerPrimitiveAnchoredOddJetScalarEnergy
    (packet : Finset (Nat.Primes × ℕ)) (H τ : ℝ) : ℝ :=
  ∑ i ∈ packet, ∑ j ∈ packet,
    xiGammaEulerPrimitiveAnchoredOddJetPhasedPair H τ i j

theorem xiGammaEulerPrimitiveAnchoredOddJetScalarEnergy_nonneg
    (packet : Finset (Nat.Primes × ℕ)) {H τ : ℝ}
    (hτ : 0 ≤ τ)
    (hanchor : ∀ i ∈ packet,
      H ≤ xiGammaEulerBoundaryHalfHeight i.1 i.2)
    (hphase : ∀ i ∈ packet, ∀ j ∈ packet,
      |τ * (xiGammaEulerBoundaryHalfHeight i.1 i.2 -
        xiGammaEulerBoundaryHalfHeight j.1 j.2)| ≤ Real.pi) :
    0 ≤ xiGammaEulerPrimitiveAnchoredOddJetScalarEnergy packet H τ := by
  unfold xiGammaEulerPrimitiveAnchoredOddJetScalarEnergy
  exact Finset.sum_nonneg fun i hi =>
    Finset.sum_nonneg fun j hj =>
      xiGammaEulerPrimitiveAnchoredOddJetPhasedPair_nonneg
        hτ (hanchor i hi) (hanchor j hj) (hphase i hi j hj)

/-- Canonical Gamma anchor of the sixth-power first-clock block. -/
def xiGammaEulerPrimitiveFirstClockAnchor (m : ℕ) : ℝ :=
  ccmFirstClockJuliaSixthPowerAperture m / 3

theorem xiGammaEulerPrimitiveFirstClockAnchor_eq
    (m : ℕ) :
    xiGammaEulerPrimitiveFirstClockAnchor m =
      2 * Real.log (m : ℝ) := by
  rw [xiGammaEulerPrimitiveFirstClockAnchor,
    ccmFirstClockJuliaSixthPowerAperture]
  ring

/-- Every hard-block Euler height lies strictly above the source aperture anchor. -/
theorem xiGammaEulerPrimitive_block_anchor_lt_halfHeight
    {m p : ℕ} (hm : 25 ≤ m)
    (hp : p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4)) :
    xiGammaEulerPrimitiveFirstClockAnchor m <
      xiGammaEulerBoundaryHalfHeight
        ⟨p, (mem_suzukiMangoldtFivePrimeBlock.mp hp).1⟩ 0 := by
  obtain ⟨hpPrime, hpLower, _hpUpper⟩ :=
    mem_suzukiMangoldtFivePrimeBlock.mp hp
  have hmPos : (0 : ℝ) < m := by
    positivity
  have hmPowPos : (0 : ℝ) < ((m ^ 4 : ℕ) : ℝ) := by
    positivity
  have hpPos : (0 : ℝ) < p := by
    exact_mod_cast hpPrime.pos
  have hpLowerR : ((m ^ 4 : ℕ) : ℝ) < (p : ℝ) := by
    have : 2 * ((m ^ 4 : ℕ) : ℝ) < (p : ℝ) := by
      exact_mod_cast hpLower
    nlinarith
  have hlog := Real.log_lt_log hmPowPos hpLowerR
  have hlogPow :
      Real.log (((m ^ 4 : ℕ) : ℝ)) =
        4 * Real.log (m : ℝ) := by
    rw [show (((m ^ 4 : ℕ) : ℝ)) = (m : ℝ) ^ 4 by norm_num,
      Real.log_pow]
    norm_num
  rw [hlogPow] at hlog
  rw [xiGammaEulerPrimitiveFirstClockAnchor_eq,
    xiGammaEulerBoundaryHalfHeight]
  norm_num
  linarith

/-- Exact derivative of the source modular family at every centered rate. -/
theorem hasDerivAt_xiGammaEulerPrimitiveModularCurrent
    (a : ℝ) (pe : Nat.Primes × ℕ) :
    HasDerivAt (fun b => xiGammaEulerPrimitiveModularCurrent b pe)
      (xiGammaEulerPrimitiveModularCurrent a pe *
        xiGammaEulerPrimitiveModularRate pe) a := by
  let c : ℝ := xiGammaEulerPrimitiveModularRate pe
  have hlin : HasDerivAt (fun b : ℝ => b * c) c a := by
    simpa using (hasDerivAt_id a).mul_const c
  have hexp := (Real.hasDerivAt_exp (a * c)).comp a hlin
  have hmul := hexp.const_mul
    (xiGammaEulerPrimitiveBoundaryAmplitude 0 pe)
  simpa only [xiGammaEulerPrimitiveModularCurrent, c,
    Function.comp_apply, mul_assoc] using hmul

/-- The center jet is an intrinsic reflection-odd logarithmic primitive current:

`J'₀(p,e) = -log(p^(e+1)) Λ(p^(e+1))/sqrt(p^(e+1))`.
-/
theorem hasDerivAt_xiGammaEulerPrimitiveModularCurrent_zero
    (pe : Nat.Primes × ℕ) :
    HasDerivAt (fun a => xiGammaEulerPrimitiveModularCurrent a pe)
      (-(Real.log (xiGammaEulerValuationNat pe : ℝ)) *
        criticalMellinAtomWeight (xiGammaEulerValuationNat pe)) 0 := by
  have h := hasDerivAt_xiGammaEulerPrimitiveModularCurrent 0 pe
  have hlogVal :
      Real.log (xiGammaEulerValuationNat pe : ℝ) =
        (pe.2 + 1 : ℕ) * Real.log (pe.1 : ℝ) := by
    rw [xiGammaEulerValuationNat]
    norm_num [Real.log_pow]
  convert h using 1
  rw [xiGammaEulerPrimitiveModularRate, criticalPrimeTowerRadius_log,
    hlogVal, xiGammaEulerPrimitiveModularCurrent_zero,
    xiGammaEulerPrimitiveBoundaryAmplitude_zero_eq_criticalMellinAtomWeight]
  push_cast
  ring

/-- Natural-prime form of the depth-zero promoted source current. -/
def xiGammaEulerPrimitiveDepthZeroAmplitude (p : ℕ) : ℝ :=
  Real.log (p : ℝ) * criticalPrimeTowerRadius p

/-- Natural-prime form of the primitive promotion multiplier. -/
def xiGammaEulerPrimitiveNatPromotion (p : ℕ) : ℝ :=
  Real.sqrt (Real.log (p : ℝ))

theorem xiGammaEulerPrimitiveNatPromotion_sq_of_one_lt
    {p : ℕ} (hp : 1 < p) :
    xiGammaEulerPrimitiveNatPromotion p ^ 2 =
      Real.log (p : ℝ) := by
  rw [xiGammaEulerPrimitiveNatPromotion, Real.sq_sqrt]
  exact Real.log_nonneg (by exact_mod_cast hp.le)

theorem xiGammaEulerPrimitivePromotion_depthZero
    (p : Nat.Primes) :
    xiGammaEulerPrimitivePromotion (p, 0) =
      xiGammaEulerPrimitiveNatPromotion p := rfl

/-- On every hard block cell, the source multiplier has precisely square-root-logarithmic size.
This realizes the rate forced by `ccmFirstClock_exteriorCapacity_forces_log_multiplier_sq`. -/
theorem xiGammaEulerPrimitive_block_promotion_sq_bounds
    {m p : ℕ} (hm : 25 ≤ m)
    (hp : p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4)) :
    Real.log (2 * ((m ^ 4 : ℕ) : ℝ)) <
        xiGammaEulerPrimitiveNatPromotion p ^ 2 ∧
      xiGammaEulerPrimitiveNatPromotion p ^ 2 ≤
        Real.log (5 * ((m ^ 4 : ℕ) : ℝ)) := by
  obtain ⟨hpPrime, hpLower, hpUpper⟩ :=
    mem_suzukiMangoldtFivePrimeBlock.mp hp
  have hmPos : 0 < m := by omega
  have hlowPos : (0 : ℝ) < 2 * ((m ^ 4 : ℕ) : ℝ) := by
    positivity
  have hpPos : (0 : ℝ) < p := by
    exact_mod_cast hpPrime.pos
  have hpLowerR : 2 * ((m ^ 4 : ℕ) : ℝ) < (p : ℝ) := by
    exact_mod_cast hpLower
  have hpUpperR : (p : ℝ) ≤ 5 * ((m ^ 4 : ℕ) : ℝ) := by
    exact_mod_cast hpUpper
  rw [xiGammaEulerPrimitiveNatPromotion_sq_of_one_lt hpPrime.one_lt]
  exact ⟨Real.log_lt_log hlowPos hpLowerR,
    Real.log_le_log hpPos hpUpperR⟩

theorem xiGammaEulerPrimitiveDepthZeroAmplitude_sq
    (p : ℕ) :
    xiGammaEulerPrimitiveDepthZeroAmplitude p ^ 2 =
      Real.log (p : ℝ) ^ 2 / p := by
  rw [xiGammaEulerPrimitiveDepthZeroAmplitude, mul_pow,
    criticalPrimeTowerRadius_sq]
  ring

/-- **Hard-block landing theorem.**  Every literal one-mode bad coefficient is between one half
and one copy of the source-forced promoted current.  Hence primitive promotion reaches the actual
Route J obstruction pointwise, with no target-fitted coefficient. -/
theorem xiGammaEulerPrimitive_block_badTerm_sandwich
    {m p : ℕ} (hm : 25 ≤ m)
    (hp : p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4)) :
    (1 / 2 : ℝ) * xiGammaEulerPrimitiveDepthZeroAmplitude p ≤
        ccmFirstClockReducedBadNatTerm
          (ccmFirstClockJuliaSixthPowerAperture m) p ∧
      ccmFirstClockReducedBadNatTerm
          (ccmFirstClockJuliaSixthPowerAperture m) p ≤
        xiGammaEulerPrimitiveDepthZeroAmplitude p := by
  have hpPrime := (mem_suzukiMangoldtFivePrimeBlock.mp hp).1
  have ha : 0 ≤ xiGammaEulerPrimitiveDepthZeroAmplitude p := by
    exact mul_nonneg
      (Real.log_nonneg (by exact_mod_cast hpPrime.one_le))
      (criticalPrimeTowerRadius_pos hpPrime.pos).le
  have hb :
      0 ≤ ccmFirstClockReducedBadNatTerm
          (ccmFirstClockJuliaSixthPowerAperture m) p := by
    rw [ccmFirstClockReducedBadNatTerm_of_prime _ hpPrime]
    exact (ccmFirstClockJuliaSixthPower_block_badTerm_pos hm hp).le
  have hlower :=
    ccmFirstClockJuliaSixthPower_block_badTerm_sq_lower hm hp
  have hupper :=
    ccmFirstClockJuliaSixthPower_block_badTerm_sq_upper hm hp
  rw [← ccmFirstClockReducedBadNatTerm_of_prime _ hpPrime] at hlower
  have hlower' :
      (1 / 4 : ℝ) *
          xiGammaEulerPrimitiveDepthZeroAmplitude p ^ 2 ≤
        ccmFirstClockReducedBadNatTerm
          (ccmFirstClockJuliaSixthPowerAperture m) p ^ 2 := by
    rw [xiGammaEulerPrimitiveDepthZeroAmplitude_sq]
    convert hlower using 1
    ring
  rw [← xiGammaEulerPrimitiveDepthZeroAmplitude_sq] at hupper
  constructor <;>
    nlinarith [sq_nonneg
      (ccmFirstClockReducedBadNatTerm
        (ccmFirstClockJuliaSixthPowerAperture m) p -
          xiGammaEulerPrimitiveDepthZeroAmplitude p)]

end RHTower

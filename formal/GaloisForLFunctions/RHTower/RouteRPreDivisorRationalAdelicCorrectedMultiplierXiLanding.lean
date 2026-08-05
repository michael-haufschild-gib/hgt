import GaloisForLFunctions.RHTower.RouteRPreDivisorRationalAdelicMultiplierKOneHomology

/-!
# Coefficient-faithful corrected multiplier Xi landing for Route R

The raw Bruhat-decorated prime tensor is not a Hochschild cycle.  This module identifies its
boundary as an explicit prime-dilation coinvariant coboundary.  For retained Bruhat coefficient
`a`, the canonical normalized potential

`b_p = (p⁻¹ • a) * a - 1`

satisfies

`p • b_p - b_p = a * (p • a) - a * (p⁻¹ • a)`.

Subtracting `U_p ⊗ b_p U_{p⁻¹}` from the raw decorated tensor therefore produces a genuine
Hochschild one-cycle.  The normalization term `-1` is essential: its pulled-back Kummer regulator
is exactly `-log p`, so the corrected class is nonzero.  Multiplication by the first nonzero Xi
jet gives an unconditional homological source-to-Xi landing equal to the previously constructed
signed Kummer landing.

This closes the genuine-cycle and coefficient-faithful landing burdens.  It does not assert that
the nonzero landing's physical mate defect vanishes; source-derived annihilation remains separate.
-/

open Complex
open GaloisForLFunctions.RHTower

namespace RHTower
namespace RouteRMultiplierKOne

noncomputable section

def decoratedPrimeCore : MCore :=
  (↑(SCore.mk ccmRationalAdelicPrimeCycleCore) : MCore)

def decoratedPrimeForward (p : Nat.Primes) : Mult :=
  SkewMonoidAlgebra.single (ccmRationalAdelicPrimeScaling p) decoratedPrimeCore

def decoratedPrimeBackward (p : Nat.Primes) : Mult :=
  SkewMonoidAlgebra.single (ccmRationalAdelicPrimeScaling p)⁻¹ decoratedPrimeCore

def decoratedPrimeCoinvariantPotential (p : Nat.Primes) : MCore :=
  ((ccmRationalAdelicPrimeScaling p)⁻¹ • decoratedPrimeCore) *
      decoratedPrimeCore - 1

def decoratedPrimeCoinvariantCorrection (p : Nat.Primes) : MC1 :=
  PiTensorProduct.tprod ℂ (fun i : Fin 2 =>
    Fin.cases (dil (ccmRationalAdelicPrimeScaling p))
      (fun _ => SkewMonoidAlgebra.single
        (ccmRationalAdelicPrimeScaling p)⁻¹
        (decoratedPrimeCoinvariantPotential p)) i)

def decoratedPrimeRawAtom (p : Nat.Primes) : MC1 :=
  PiTensorProduct.tprod ℂ (fun i : Fin 2 =>
    Fin.cases (decoratedPrimeForward p) (fun _ => decoratedPrimeBackward p) i)

def decoratedPrimeCorrectedCycle (p : Nat.Primes) : MC1 :=
  decoratedPrimeRawAtom p - decoratedPrimeCoinvariantCorrection p

theorem decoratedPrimeCoinvariantPotential_coboundary (p : Nat.Primes) :
    ccmRationalAdelicPrimeScaling p • decoratedPrimeCoinvariantPotential p -
        decoratedPrimeCoinvariantPotential p =
      decoratedPrimeCore *
          (ccmRationalAdelicPrimeScaling p • decoratedPrimeCore) -
        decoratedPrimeCore *
          ((ccmRationalAdelicPrimeScaling p)⁻¹ • decoratedPrimeCore) := by
  rw [decoratedPrimeCoinvariantPotential]
  simp only [smul_sub, smul_mul', smul_one, smul_smul, mul_inv_cancel,
    one_smul]
  ring

theorem decoratedPrimeRawAtom_boundary (p : Nat.Primes) :
    mBoundaryOne (decoratedPrimeRawAtom p) =
      SkewMonoidAlgebra.single 1
        (decoratedPrimeCore *
            (ccmRationalAdelicPrimeScaling p • decoratedPrimeCore) -
          decoratedPrimeCore *
            ((ccmRationalAdelicPrimeScaling p)⁻¹ • decoratedPrimeCore)) := by
  rw [decoratedPrimeRawAtom, mBoundaryOne_tprod']
  change decoratedPrimeForward p * decoratedPrimeBackward p -
      decoratedPrimeBackward p * decoratedPrimeForward p = _
  simp [decoratedPrimeForward, decoratedPrimeBackward, sub_eq_add_neg]

theorem decoratedPrimeCoinvariantCorrection_boundary (p : Nat.Primes) :
    mBoundaryOne (decoratedPrimeCoinvariantCorrection p) =
      SkewMonoidAlgebra.single 1
        (ccmRationalAdelicPrimeScaling p • decoratedPrimeCoinvariantPotential p -
          decoratedPrimeCoinvariantPotential p) := by
  rw [decoratedPrimeCoinvariantCorrection, mBoundaryOne_tprod']
  change dil (ccmRationalAdelicPrimeScaling p) *
        SkewMonoidAlgebra.single (ccmRationalAdelicPrimeScaling p)⁻¹
          (decoratedPrimeCoinvariantPotential p) -
      SkewMonoidAlgebra.single (ccmRationalAdelicPrimeScaling p)⁻¹
          (decoratedPrimeCoinvariantPotential p) *
        dil (ccmRationalAdelicPrimeScaling p) = _
  simp [dil, sub_eq_add_neg]

theorem decoratedPrimeCorrectedCycle_boundary (p : Nat.Primes) :
    mBoundaryOne (decoratedPrimeCorrectedCycle p) = 0 := by
  rw [decoratedPrimeCorrectedCycle, map_sub,
    decoratedPrimeRawAtom_boundary,
    decoratedPrimeCoinvariantCorrection_boundary,
    decoratedPrimeCoinvariantPotential_coboundary]
  abel

@[simp] theorem multiplierCoefficientAugmentation_decoratedPrimeCore :
    multiplierCoefficientAugmentation decoratedPrimeCore = 0 := by
  simp [multiplierCoefficientAugmentation, decoratedPrimeCore]

theorem multiplierToKummerGroupRing_single
    (k : CCMRationalAdelicScaling) (x : MCore) :
    multiplierToKummerGroupRing (SkewMonoidAlgebra.single k x) =
      multiplierCoefficientAugmentation x *
        MonoidAlgebra.of ℂ CCMRationalAdelicScaling k := by
  simp [multiplierToKummerGroupRing, SkewMonoidAlgebra.liftNCAlgHom,
    SkewMonoidAlgebra.liftNCRingHom]

@[simp] theorem multiplierToKummerGroupRing_decoratedPrimeForward
    (p : Nat.Primes) :
    multiplierToKummerGroupRing (decoratedPrimeForward p) = 0 := by
  rw [decoratedPrimeForward, multiplierToKummerGroupRing_single,
    multiplierCoefficientAugmentation_decoratedPrimeCore, zero_mul]

@[simp] theorem multiplierToKummerGroupRing_decoratedPrimeBackward
    (p : Nat.Primes) :
    multiplierToKummerGroupRing (decoratedPrimeBackward p) = 0 := by
  rw [decoratedPrimeBackward, multiplierToKummerGroupRing_single,
    multiplierCoefficientAugmentation_decoratedPrimeCore, zero_mul]

@[simp] theorem multiplierCoefficientAugmentation_coinvariantPotential
    (p : Nat.Primes) :
    multiplierCoefficientAugmentation (decoratedPrimeCoinvariantPotential p) = -1 := by
  change MonoidAlgebra.single 1
      (decoratedPrimeCoinvariantPotential p).fst = -1
  have hfst : (decoratedPrimeCoinvariantPotential p).fst = -1 := by
    rw [decoratedPrimeCoinvariantPotential]
    simp only [sub_eq_add_neg, Unitization.fst_add, Unitization.fst_neg,
      Unitization.fst_mul, scalingMCore_fst, Unitization.fst_one]
    change (0 : ℂ) * 0 + -1 = -1
    ring
  rw [hfst]
  simp [MonoidAlgebra.one_def]

theorem multiplierKummerCyclicOneCocycle_decoratedPrimeRawAtom
    (p : Nat.Primes) :
    multiplierKummerCyclicOneCocycle (decoratedPrimeRawAtom p) = 0 := by
  rw [decoratedPrimeRawAtom, multiplierKummerCyclicOneCocycle_tprod]
  change kummerGroupRingTrace
    (multiplierToKummerGroupRing (decoratedPrimeForward p) *
      kummerGroupRingDerivation
        (multiplierToKummerGroupRing (decoratedPrimeBackward p))) = 0
  simp

theorem multiplierKummerCyclicOneCocycle_coinvariantCorrection
    (p : Nat.Primes) :
    multiplierKummerCyclicOneCocycle
        (decoratedPrimeCoinvariantCorrection p) =
      (Real.log (p : ℝ) : ℂ) := by
  rw [decoratedPrimeCoinvariantCorrection,
    multiplierKummerCyclicOneCocycle_tprod]
  change kummerGroupRingTrace
      (multiplierToKummerGroupRing
          (dil (ccmRationalAdelicPrimeScaling p)) *
        kummerGroupRingDerivation
          (multiplierToKummerGroupRing
            (SkewMonoidAlgebra.single
              (ccmRationalAdelicPrimeScaling p)⁻¹
              (decoratedPrimeCoinvariantPotential p)))) = _
  rw [multiplierToKummerGroupRing_dil,
    multiplierToKummerGroupRing_single,
    multiplierCoefficientAugmentation_coinvariantPotential]
  simp only [neg_mul, one_mul, map_neg,
    kummerGroupRingDerivation_of,
    ccmRationalAdelicKummerLogWeight_inv,
    ccmRationalAdelicKummerLogWeight_primeScaling]
  simp [MonoidAlgebra.of_apply, smul_eq_mul]

theorem multiplierKummerCyclicOneCocycle_decoratedPrimeCorrectedCycle
    (p : Nat.Primes) :
    multiplierKummerCyclicOneCocycle (decoratedPrimeCorrectedCycle p) =
      -(Real.log (p : ℝ) : ℂ) := by
  rw [decoratedPrimeCorrectedCycle, map_sub,
    multiplierKummerCyclicOneCocycle_decoratedPrimeRawAtom,
    multiplierKummerCyclicOneCocycle_coinvariantCorrection]
  simp

def decoratedPrimeCorrectedHochschildCycle (p : Nat.Primes) :
    multiplierHochschildOneCycles :=
  ⟨decoratedPrimeCorrectedCycle p,
    LinearMap.mem_ker.mpr (decoratedPrimeCorrectedCycle_boundary p)⟩

def decoratedPrimeCorrectedHochschildClass (p : Nat.Primes) :
    MultiplierHochschildOneHomology :=
  multiplierHochschildOneBoundaries.mkQ
    (decoratedPrimeCorrectedHochschildCycle p)

@[simp] theorem multiplierKummerHomologyRegulator_decoratedPrimeCorrectedClass
    (p : Nat.Primes) :
    multiplierKummerHomologyRegulator
        (decoratedPrimeCorrectedHochschildClass p) =
      -(Real.log (p : ℝ) : ℂ) := by
  change multiplierKummerCyclicOneCocycle
      (decoratedPrimeCorrectedCycle p) = _
  exact multiplierKummerCyclicOneCocycle_decoratedPrimeCorrectedCycle p

theorem decoratedPrimeCorrectedHochschildClass_ne_zero (p : Nat.Primes) :
    decoratedPrimeCorrectedHochschildClass p ≠ 0 := by
  intro hzero
  have hread := congrArg multiplierKummerHomologyRegulator hzero
  rw [multiplierKummerHomologyRegulator_decoratedPrimeCorrectedClass,
    map_zero] at hread
  exact (neg_ne_zero.mpr (primeLogComplex_ne_zero p)) hread

def decoratedPrimeXiHomologyLanding (rho : XiDivisorSupport) :
    MultiplierHochschildOneHomology →ₗ[ℂ] ℂ :=
  ccmRationalAdelicPrimeXiCartierCoefficient rho •
    multiplierKummerHomologyRegulator

@[simp] theorem decoratedPrimeXiHomologyLanding_primeCorrectedClass
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    decoratedPrimeXiHomologyLanding rho
        (decoratedPrimeCorrectedHochschildClass p) =
      -(Real.log (p : ℝ) : ℂ) *
        ccmRationalAdelicPrimeXiCartierCoefficient rho := by
  rw [decoratedPrimeXiHomologyLanding, LinearMap.smul_apply,
    multiplierKummerHomologyRegulator_decoratedPrimeCorrectedClass]
  simp only [smul_eq_mul]
  ring

theorem decoratedPrimeXiHomologyLanding_eq_signedKummerLanding
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    decoratedPrimeXiHomologyLanding rho
        (decoratedPrimeCorrectedHochschildClass p) =
      ccmRationalAdelicPrimeXiSignedKummerLanding p rho := by
  rw [decoratedPrimeXiHomologyLanding_primeCorrectedClass,
    ccmRationalAdelicPrimeXiSignedKummerLanding_eq]

theorem decoratedPrimeXiHomologyLanding_ne_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    decoratedPrimeXiHomologyLanding rho
        (decoratedPrimeCorrectedHochschildClass p) ≠ 0 := by
  rw [decoratedPrimeXiHomologyLanding_eq_signedKummerLanding]
  exact ccmRationalAdelicPrimeXiSignedKummerLanding_ne_zero p rho

end
end RouteRMultiplierKOne

/-! ## Route-R-facing exported endpoints -/

/-- Explicit normalized coefficient potential whose prime-dilation coboundary is the raw
Bruhat-decorated Hochschild boundary. -/
noncomputable def ccmRationalAdelicPrimeCorrectedMultiplierCoinvariantPotential
    (p : Nat.Primes) : RouteRMultiplierKOne.MCore :=
  RouteRMultiplierKOne.decoratedPrimeCoinvariantPotential p

/-- Coefficient-faithful corrected Bruhat-decorated prime chain. -/
noncomputable def ccmRationalAdelicPrimeCorrectedMultiplierCycle
    (p : Nat.Primes) : CCMRationalAdelicPrimeMultiplierDegreeOneSource :=
  RouteRMultiplierKOne.decoratedPrimeCorrectedCycle p

/-- Corrected decorated chain is a genuine Hochschild one-cycle. -/
theorem ccmRationalAdelicPrimeCorrectedMultiplierCycle_boundary_eq_zero
    (p : Nat.Primes) :
    RouteRMultiplierKOne.mBoundaryOne
        (ccmRationalAdelicPrimeCorrectedMultiplierCycle p) = 0 :=
  RouteRMultiplierKOne.decoratedPrimeCorrectedCycle_boundary p

/-- Genuine homology class of the corrected decorated prime cycle. -/
noncomputable def ccmRationalAdelicPrimeCorrectedMultiplierHomologyClass
    (p : Nat.Primes) : CCMRationalAdelicPrimeMultiplierHochschildOneHomology :=
  RouteRMultiplierKOne.decoratedPrimeCorrectedHochschildClass p

/-- Kummer regulator reads the corrected decorated class as `-log p`. -/
@[simp] theorem ccmRationalAdelicPrimeMultiplierKummerRegulator_correctedClass
    (p : Nat.Primes) :
    ccmRationalAdelicPrimeMultiplierKummerHomologyRegulator
        (ccmRationalAdelicPrimeCorrectedMultiplierHomologyClass p) =
      -(Real.log (p : ℝ) : ℂ) :=
  RouteRMultiplierKOne.multiplierKummerHomologyRegulator_decoratedPrimeCorrectedClass p

/-- Coefficient-faithful corrected decorated prime class survives in genuine `HH1`. -/
theorem ccmRationalAdelicPrimeCorrectedMultiplierHomologyClass_ne_zero
    (p : Nat.Primes) :
    ccmRationalAdelicPrimeCorrectedMultiplierHomologyClass p ≠ 0 :=
  RouteRMultiplierKOne.decoratedPrimeCorrectedHochschildClass_ne_zero p

/-- Xi landing of the genuine corrected decorated homology class. -/
noncomputable def ccmRationalAdelicPrimeCorrectedMultiplierXiLanding
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℂ :=
  RouteRMultiplierKOne.decoratedPrimeXiHomologyLanding rho
    (ccmRationalAdelicPrimeCorrectedMultiplierHomologyClass p)

/-- New genuine-homology landing is exactly the established fixed signed Kummer Xi landing. -/
theorem ccmRationalAdelicPrimeCorrectedMultiplierXiLanding_eq_signedKummerLanding
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeCorrectedMultiplierXiLanding p rho =
      ccmRationalAdelicPrimeXiSignedKummerLanding p rho :=
  RouteRMultiplierKOne.decoratedPrimeXiHomologyLanding_eq_signedKummerLanding p rho

/-- Genuine corrected multiplier Xi landing retains both prime and Xi coefficient. -/
theorem ccmRationalAdelicPrimeCorrectedMultiplierXiLanding_ne_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeCorrectedMultiplierXiLanding p rho ≠ 0 :=
  RouteRMultiplierKOne.decoratedPrimeXiHomologyLanding_ne_zero p rho

end RHTower

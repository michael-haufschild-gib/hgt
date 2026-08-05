import GaloisForLFunctions.RHTower.RouteRPreDivisorRationalAdelicCorrectedMultiplierXiLanding
import GaloisForLFunctions.RHTower.CCMRationalAdelicPrimeIsotropyStokesRegulator

/-!
# Corrected multiplier Gamma-orientation descent for Route R

The corrected Bruhat-decorated multiplier class is a genuine nonzero `HH₁` class, and its Xi
landing is nonzero.  This module caps its Kummer regulator with the retained rational-adelic
prime-isotropy class and the explicit fixed-physical Hodge-mate coefficient.  The independent
period-one Stokes regulator reads the cap exactly, so the cap is null precisely when the Hodge
coefficient is zero.

Functional-equation reflection exposes the remaining producer sharply.  The Xi jet contributes
its expected parity `(-1)^m`, while the Hodge-mate coefficient contributes one additional minus
sign.  Thus the explicit physical cap has *opposite* Gamma parity unconditionally.  Requiring a
comparison that fixes the same source orientation in both Gamma fibres to have Xi-jet parity is
equivalent to nullity of the cap, to the same-fibre source-dagger identity, and to the critical-line
condition.

The hostile test at the end proves that ordinary cyclic source dagger does not fix that orientation:
it flips the nonzero Kummer period and makes dagger-transported naturality unconditional.  Hence the
remaining law must be genuinely same-fibre and fixed-orientation.  No critical-line placement,
mate-coefficient vanishing, or RH premise is used.
-/

open Complex
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- The fixed physical Hodge-mate coefficient is odd under functional-equation reflection. -/
theorem ccmRationalAdelicPrimeXiHodgeMateCoefficient_reflection
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiHodgeMateCoefficient p (xiZeroReflectEquiv rho) =
      -ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho := by
  rw [ccmRationalAdelicPrimeXiHodgeMateCoefficient,
    ccmRationalAdelicPrimeXiHodgeMateCoefficient,
    primeDepthBVWoldReesCoronaWeight,
    primeDepthBVWoldReesCoronaWeight,
    primeDepthBVWoldXiCenteredRate,
    primeDepthBVWoldXiCenteredRate,
    xiZeroReflectEquiv_apply]
  simp only [Complex.sub_re, Complex.one_re]
  ring

/-- The genuine corrected multiplier Xi landing has exactly the Xi-jet reflection parity. -/
theorem ccmRationalAdelicPrimeCorrectedMultiplierXiLanding_reflection
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeCorrectedMultiplierXiLanding p (xiZeroReflectEquiv rho) =
      (-1 : ℂ) ^ xiSupportMultiplicity rho *
        ccmRationalAdelicPrimeCorrectedMultiplierXiLanding p rho := by
  rw [ccmRationalAdelicPrimeCorrectedMultiplierXiLanding_eq_signedKummerLanding,
    ccmRationalAdelicPrimeCorrectedMultiplierXiLanding_eq_signedKummerLanding,
    ccmRationalAdelicPrimeXiSignedKummerLanding_reflection]

/-- Cap comparison from genuine multiplier `HH₁` to the retained relative prime-isotropy class.
It combines the Kummer period, first nonzero Xi jet, and explicit fixed-physical Hodge port. -/
def ccmRationalAdelicPrimeXiCentralBocksteinCapComparison
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeMultiplierHochschildOneHomology →ₗ[ℂ]
      (ccmRationalAdelicPrimeRelativeComplex p).H1 where
  toFun x :=
    ((ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho : ℂ) *
      ccmRationalAdelicPrimeXiCartierCoefficient rho *
      ccmRationalAdelicPrimeMultiplierKummerHomologyRegulator x) •
        ccmRationalAdelicPrimeRelativeClass p
  map_add' x y := by
    rw [map_add]
    module
  map_smul' c x := by
    rw [map_smul]
    simp only [RingHom.id_apply]
    module

/-- On the corrected decorated class, the cap coefficient is `K` times its genuine Xi landing. -/
theorem ccmRationalAdelicPrimeXiCentralBocksteinCapComparison_correctedClass
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiCentralBocksteinCapComparison p rho
        (ccmRationalAdelicPrimeCorrectedMultiplierHomologyClass p) =
      ((ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho : ℂ) *
        ccmRationalAdelicPrimeCorrectedMultiplierXiLanding p rho) •
          ccmRationalAdelicPrimeRelativeClass p := by
  change
    ((ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho : ℂ) *
      ccmRationalAdelicPrimeXiCartierCoefficient rho *
      ccmRationalAdelicPrimeMultiplierKummerHomologyRegulator
        (ccmRationalAdelicPrimeCorrectedMultiplierHomologyClass p)) •
          ccmRationalAdelicPrimeRelativeClass p = _
  rw [ccmRationalAdelicPrimeMultiplierKummerRegulator_correctedClass,
    ccmRationalAdelicPrimeCorrectedMultiplierXiLanding_eq_signedKummerLanding,
    ccmRationalAdelicPrimeXiSignedKummerLanding_eq]
  congr 1
  ring

/-- Explicit central-Bockstein cap class on the retained ordinary-prime atom. -/
def ccmRationalAdelicPrimeXiCentralBocksteinCapClass
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    (ccmRationalAdelicPrimeRelativeComplex p).H1 :=
  ccmRationalAdelicPrimeXiCentralBocksteinCapComparison p rho
    (ccmRationalAdelicPrimeCorrectedMultiplierHomologyClass p)

/-- Independent Stokes regulator reads the full fixed-physical cap coefficient exactly. -/
theorem ccmRationalAdelicPrimeRelativeH1StokesRegulator_centralBocksteinCapClass
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeRelativeH1StokesRegulator p
        (ccmRationalAdelicPrimeXiCentralBocksteinCapClass p rho) =
      (ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho : ℂ) *
        ccmRationalAdelicPrimeCorrectedMultiplierXiLanding p rho := by
  rw [ccmRationalAdelicPrimeXiCentralBocksteinCapClass,
    ccmRationalAdelicPrimeXiCentralBocksteinCapComparison_correctedClass,
    map_smul,
    ccmRationalAdelicPrimeRelativeH1StokesRegulator_class,
    smul_eq_mul, mul_one]

/-- Stokes faithfulness plus Xi/Kummer non-erasure makes cap nullity exactly `K = 0`. -/
theorem ccmRationalAdelicPrimeXiCentralBocksteinCapClass_eq_zero_iff_hodgeMate
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiCentralBocksteinCapClass p rho = 0 ↔
      ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho = 0 := by
  constructor
  · intro hzero
    have hread := congrArg
      (ccmRationalAdelicPrimeRelativeH1StokesRegulator p) hzero
    rw [ccmRationalAdelicPrimeRelativeH1StokesRegulator_centralBocksteinCapClass,
      map_zero] at hread
    have hcoefficient :
        (ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho : ℂ) = 0 :=
      (mul_eq_zero.mp hread).resolve_right
        (ccmRationalAdelicPrimeCorrectedMultiplierXiLanding_ne_zero p rho)
    exact_mod_cast hcoefficient
  · intro hzero
    have hzero' :
        (ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho : ℂ) = 0 := by
      exact_mod_cast hzero
    rw [ccmRationalAdelicPrimeXiCentralBocksteinCapClass,
      ccmRationalAdelicPrimeXiCentralBocksteinCapComparison_correctedClass,
      hzero', zero_mul, zero_smul]

/-- The explicit physical cap has the opposite of source Xi-jet parity. -/
theorem ccmRationalAdelicPrimeXiCentralBocksteinCapClass_reflection
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiCentralBocksteinCapClass p (xiZeroReflectEquiv rho) =
      -((-1 : ℂ) ^ xiSupportMultiplicity rho •
        ccmRationalAdelicPrimeXiCentralBocksteinCapClass p rho) := by
  rw [ccmRationalAdelicPrimeXiCentralBocksteinCapClass,
    ccmRationalAdelicPrimeXiCentralBocksteinCapClass,
    ccmRationalAdelicPrimeXiCentralBocksteinCapComparison_correctedClass,
    ccmRationalAdelicPrimeXiCentralBocksteinCapComparison_correctedClass,
    ccmRationalAdelicPrimeXiHodgeMateCoefficient_reflection,
    ccmRationalAdelicPrimeCorrectedMultiplierXiLanding_reflection]
  push_cast
  module

/-- Exact remaining naturality square: source Gamma orientation contributes only Xi-jet parity. -/
def CCMRationalAdelicPrimeXiCorrectedMultiplierGammaOrientationDescent
    (p : Nat.Primes) (rho : XiDivisorSupport) : Prop :=
  ccmRationalAdelicPrimeXiCentralBocksteinCapClass p (xiZeroReflectEquiv rho) =
    (-1 : ℂ) ^ xiSupportMultiplicity rho •
      ccmRationalAdelicPrimeXiCentralBocksteinCapClass p rho

/-- Source-parity descent is equivalent to annihilation of the explicit Hodge-mate coefficient. -/
theorem ccmRationalAdelicPrimeXiCorrectedMultiplierGammaOrientationDescent_iff_hodgeMate
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiCorrectedMultiplierGammaOrientationDescent p rho ↔
      ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho = 0 := by
  constructor
  · intro hdescent
    have hread := congrArg
      (ccmRationalAdelicPrimeRelativeH1StokesRegulator p) hdescent
    change
      ccmRationalAdelicPrimeRelativeH1StokesRegulator p
          (ccmRationalAdelicPrimeXiCentralBocksteinCapClass p
            (xiZeroReflectEquiv rho)) =
        ccmRationalAdelicPrimeRelativeH1StokesRegulator p
          ((-1 : ℂ) ^ xiSupportMultiplicity rho •
            ccmRationalAdelicPrimeXiCentralBocksteinCapClass p rho) at hread
    rw [ccmRationalAdelicPrimeRelativeH1StokesRegulator_centralBocksteinCapClass,
      map_smul,
      ccmRationalAdelicPrimeRelativeH1StokesRegulator_centralBocksteinCapClass,
      ccmRationalAdelicPrimeXiHodgeMateCoefficient_reflection,
      ccmRationalAdelicPrimeCorrectedMultiplierXiLanding_reflection] at hread
    simp only [smul_eq_mul] at hread
    let a : ℂ :=
      (-1 : ℂ) ^ xiSupportMultiplicity rho *
        ((ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho : ℂ) *
          ccmRationalAdelicPrimeCorrectedMultiplierXiLanding p rho)
    have ha : -a = a := by
      simpa [a, mul_assoc, mul_left_comm, mul_comm] using hread
    have hazero : a = 0 := by
      linear_combination (-1 / 2 : ℂ) * ha
    have hparity : (-1 : ℂ) ^ xiSupportMultiplicity rho ≠ 0 :=
      pow_ne_zero _ (by norm_num)
    have hproduct :
        (ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho : ℂ) *
          ccmRationalAdelicPrimeCorrectedMultiplierXiLanding p rho = 0 :=
      (mul_eq_zero.mp hazero).resolve_left hparity
    have hcoefficient :
        (ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho : ℂ) = 0 :=
      (mul_eq_zero.mp hproduct).resolve_right
        (ccmRationalAdelicPrimeCorrectedMultiplierXiLanding_ne_zero p rho)
    exact_mod_cast hcoefficient
  · intro hzero
    have hreflected :
        ccmRationalAdelicPrimeXiHodgeMateCoefficient p
            (xiZeroReflectEquiv rho) = 0 := by
      rw [ccmRationalAdelicPrimeXiHodgeMateCoefficient_reflection, hzero, neg_zero]
    unfold CCMRationalAdelicPrimeXiCorrectedMultiplierGammaOrientationDescent
    rw [(ccmRationalAdelicPrimeXiCentralBocksteinCapClass_eq_zero_iff_hodgeMate
        p (xiZeroReflectEquiv rho)).2 hreflected,
      (ccmRationalAdelicPrimeXiCentralBocksteinCapClass_eq_zero_iff_hodgeMate
        p rho).2 hzero,
      smul_zero]

/-- The new naturality square is exactly the already isolated same-fibre source-dagger law. -/
theorem ccmRationalAdelicPrimeXiCorrectedMultiplierGammaOrientationDescent_iff_sourceDagger
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiCorrectedMultiplierGammaOrientationDescent p rho ↔
      CCMRationalAdelicPrimeXiSourceDaggerIdentity p rho :=
  (ccmRationalAdelicPrimeXiCorrectedMultiplierGammaOrientationDescent_iff_hodgeMate
    p rho).trans
      (ccmRationalAdelicPrimeXiSourceDaggerIdentity_iff_hodgeMateCoefficient_eq_zero
        p rho).symm

/-- Equivalent fixed same-fibre norm form. -/
theorem ccmRationalAdelicPrimeXiCorrectedMultiplierGammaOrientationDescent_iff_sameFiberNorm
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiCorrectedMultiplierGammaOrientationDescent p rho ↔
      CCMRationalAdelicPrimeXiSameFiberNormIdentity p rho :=
  (ccmRationalAdelicPrimeXiCorrectedMultiplierGammaOrientationDescent_iff_hodgeMate
    p rho).trans
      (ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_hodgeMateCoefficient_eq_zero
        p rho).symm

/-- Equivalent fixed physical signed-Kummer defect form. -/
theorem ccmRationalAdelicPrimeXiCorrectedMultiplierGammaOrientationDescent_iff_physicalDefect
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiCorrectedMultiplierGammaOrientationDescent p rho ↔
      ccmRationalAdelicPrimeXiSignedKummerPhysicalDefect p rho = 0 :=
  (ccmRationalAdelicPrimeXiCorrectedMultiplierGammaOrientationDescent_iff_hodgeMate
    p rho).trans
      (ccmRationalAdelicPrimeXiSignedKummerPhysicalDefect_eq_zero_iff_hodgeMate
        p rho).symm

/-! ## Hostile source-orientation test

Degree-one source reversal is not invisible: the Kummer regulator is cyclically odd.  Transporting
the corrected class by this genuine source dagger cancels the extra reflection sign of the Hodge
port.  Hence dagger-transported Gamma naturality is unconditional and cannot itself annihilate the
physical class.  The RH-bearing law above specifically requires a fixed same-source orientation;
it must not be replaced by ordinary cyclic reversal.
-/

namespace RouteRMultiplierKOne

/-- Genuine degree-one cyclic reversal on the multiplier bar source. -/
def multiplierDegreeOneCyclicRotation : MC1 →ₗ[ℂ] MC1 :=
  (cyclicBarRotate (R := ℂ) (A := Mult) 1).toLinearMap

/-- Kummer period is odd under genuine degree-one cyclic reversal. -/
theorem multiplierKummerCyclicOneCocycle_comp_rotation :
    multiplierKummerCyclicOneCocycle.comp multiplierDegreeOneCyclicRotation =
      -multiplierKummerCyclicOneCocycle := by
  apply PiTensorProduct.ext
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    LinearMap.neg_apply]
  change multiplierKummerCyclicOneCocycle
      (cyclicBarRotate (R := ℂ) (A := Mult) 1
        (PiTensorProduct.tprod ℂ x)) = _
  rw [cyclicBarRotate_tprod,
    multiplierKummerCyclicOneCocycle_tprod,
    multiplierKummerCyclicOneCocycle_tprod]
  exact multiplierKummerCyclicOneCocycle_cyclic (x 1) (x 0)

/-- Hochschild degree-one boundary is odd under cyclic reversal. -/
theorem mBoundaryOne_comp_multiplierDegreeOneCyclicRotation :
    mBoundaryOne.comp multiplierDegreeOneCyclicRotation = -mBoundaryOne := by
  apply PiTensorProduct.ext
  ext x : 1
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    LinearMap.neg_apply]
  change mBoundaryOne
      (cyclicBarRotate (R := ℂ) (A := Mult) 1
        (PiTensorProduct.tprod ℂ x)) = _
  rw [cyclicBarRotate_tprod, mBoundaryOne_tprod', mBoundaryOne_tprod']
  simp only [cyclicBarRotateTuple_zero, cyclicBarRotateTuple_one]
  simpa [sub_eq_add_neg] using
    (add_comm (x 1 * x 0) (-(x 0 * x 1)))

/-- Cyclic reversal of the corrected decorated cycle remains a genuine Hochschild cycle. -/
def decoratedPrimeCorrectedRotatedHochschildCycle (p : Nat.Primes) :
    multiplierHochschildOneCycles :=
  ⟨multiplierDegreeOneCyclicRotation (decoratedPrimeCorrectedCycle p), by
    apply LinearMap.mem_ker.mpr
    have h := LinearMap.congr_fun
      mBoundaryOne_comp_multiplierDegreeOneCyclicRotation
        (decoratedPrimeCorrectedCycle p)
    rw [LinearMap.comp_apply, LinearMap.neg_apply,
      decoratedPrimeCorrectedCycle_boundary, neg_zero] at h
    exact h⟩

/-- Homology class of the genuinely source-reversed corrected prime cycle. -/
def decoratedPrimeCorrectedRotatedHochschildClass (p : Nat.Primes) :
    MultiplierHochschildOneHomology :=
  multiplierHochschildOneBoundaries.mkQ
    (decoratedPrimeCorrectedRotatedHochschildCycle p)

/-- Reversed corrected class has the opposite, nonzero Kummer period `+log p`. -/
@[simp] theorem multiplierKummerHomologyRegulator_rotatedCorrectedClass
    (p : Nat.Primes) :
    multiplierKummerHomologyRegulator
        (decoratedPrimeCorrectedRotatedHochschildClass p) =
      (Real.log (p : ℝ) : ℂ) := by
  change multiplierKummerCyclicOneCocycle
      (multiplierDegreeOneCyclicRotation (decoratedPrimeCorrectedCycle p)) = _
  have h := LinearMap.congr_fun
    multiplierKummerCyclicOneCocycle_comp_rotation
      (decoratedPrimeCorrectedCycle p)
  rw [LinearMap.comp_apply, LinearMap.neg_apply,
    multiplierKummerCyclicOneCocycle_decoratedPrimeCorrectedCycle] at h
  simpa using h

/-- Source reversal is genuinely visible in multiplier homology. -/
theorem decoratedPrimeCorrectedRotatedHochschildClass_ne_original
    (p : Nat.Primes) :
    decoratedPrimeCorrectedRotatedHochschildClass p ≠
      decoratedPrimeCorrectedHochschildClass p := by
  intro heq
  have hread := congrArg multiplierKummerHomologyRegulator heq
  rw [multiplierKummerHomologyRegulator_rotatedCorrectedClass,
    multiplierKummerHomologyRegulator_decoratedPrimeCorrectedClass] at hread
  have hzero : (Real.log (p : ℝ) : ℂ) = 0 := by
    linear_combination (1 / 2 : ℂ) * hread
  exact primeLogComplex_ne_zero p hzero

end RouteRMultiplierKOne

/-- Route-facing source-reversed corrected multiplier class. -/
def ccmRationalAdelicPrimeCorrectedMultiplierRotatedHomologyClass
    (p : Nat.Primes) : CCMRationalAdelicPrimeMultiplierHochschildOneHomology :=
  RouteRMultiplierKOne.decoratedPrimeCorrectedRotatedHochschildClass p

/-- Exact Kummer period of the source-reversed corrected class. -/
@[simp] theorem ccmRationalAdelicPrimeMultiplierKummerRegulator_rotatedCorrectedClass
    (p : Nat.Primes) :
    ccmRationalAdelicPrimeMultiplierKummerHomologyRegulator
        (ccmRationalAdelicPrimeCorrectedMultiplierRotatedHomologyClass p) =
      (Real.log (p : ℝ) : ℂ) :=
  RouteRMultiplierKOne.multiplierKummerHomologyRegulator_rotatedCorrectedClass p

/-- Source-reversed and fixed-orientation corrected classes are distinct. -/
theorem ccmRationalAdelicPrimeCorrectedMultiplierRotatedHomologyClass_ne_original
    (p : Nat.Primes) :
    ccmRationalAdelicPrimeCorrectedMultiplierRotatedHomologyClass p ≠
      ccmRationalAdelicPrimeCorrectedMultiplierHomologyClass p :=
  RouteRMultiplierKOne.decoratedPrimeCorrectedRotatedHochschildClass_ne_original p

/-- With genuine source dagger transport, Gamma-orientation naturality holds unconditionally.
The source Kummer sign and physical Hodge sign cancel. -/
theorem ccmRationalAdelicPrimeXiCentralBocksteinCapComparison_dagger_reflection
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiCentralBocksteinCapComparison p (xiZeroReflectEquiv rho)
        (ccmRationalAdelicPrimeCorrectedMultiplierRotatedHomologyClass p) =
      (-1 : ℂ) ^ xiSupportMultiplicity rho •
        ccmRationalAdelicPrimeXiCentralBocksteinCapClass p rho := by
  change
    ((ccmRationalAdelicPrimeXiHodgeMateCoefficient p (xiZeroReflectEquiv rho) : ℂ) *
      ccmRationalAdelicPrimeXiCartierCoefficient (xiZeroReflectEquiv rho) *
      ccmRationalAdelicPrimeMultiplierKummerHomologyRegulator
        (ccmRationalAdelicPrimeCorrectedMultiplierRotatedHomologyClass p)) •
          ccmRationalAdelicPrimeRelativeClass p = _
  rw [ccmRationalAdelicPrimeMultiplierKummerRegulator_rotatedCorrectedClass,
    ccmRationalAdelicPrimeXiHodgeMateCoefficient_reflection,
    ccmRationalAdelicPrimeXiCartierCoefficient_reflection,
    ccmRationalAdelicPrimeXiCentralBocksteinCapClass,
    ccmRationalAdelicPrimeXiCentralBocksteinCapComparison_correctedClass,
    ccmRationalAdelicPrimeCorrectedMultiplierXiLanding_eq_signedKummerLanding,
    ccmRationalAdelicPrimeXiSignedKummerLanding_eq]
  push_cast
  module

/-- At one fixed ordinary prime, source Gamma-orientation descent at every Xi divisor is RH. -/
theorem forall_ccmRationalAdelicPrimeXiCorrectedMultiplierGammaOrientationDescent_iff_RH
    (p : Nat.Primes) :
    (∀ rho : XiDivisorSupport,
      CCMRationalAdelicPrimeXiCorrectedMultiplierGammaOrientationDescent p rho) ↔
      RiemannHypothesis := by
  rw [← forall_ccmRationalAdelicPrimeXiSourceDaggerIdentity_iff_riemannHypothesis p]
  exact forall_congr' fun rho =>
    ccmRationalAdelicPrimeXiCorrectedMultiplierGammaOrientationDescent_iff_sourceDagger
      p rho

end

end RHTower

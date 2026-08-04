import GaloisForLFunctions.RHTower.PrimeDepthBVWoldReesCoronaQuotient
import GaloisForLFunctions.RHTower.DeningerMeyerReflectedGaussianHarmonicSourcePrimitive

/-!
# Completed-Xi fixed-corona polarization normal form

The multiplicity-exact completed Xi carrier has a canonical orthonormal coordinate
line at every divisor copy.  This file identifies the real polarization on two
copies of that line with Route R's fixed boundary-plus-hidden product metric.

The hidden coordinate is untwisted by the actual completed-Xi Hodge weight.  The
resulting comparison is coefficient-faithful, sends the rational-adelic physical
coefficient to the fixed zero-hidden lift, sends its Hodge mate to the fixed hidden
mate, and carries the source resolved coefficient to the existing harmonic corona
graph.  Every statement is unconditional and remains true off the critical line;
the residual Route-R shear appears explicitly as the Hodge-mate coefficient.
-/

open Complex
open GaloisForLFunctions.IrregularStokes

namespace RHTower

noncomputable section

/-! ## Canonical fixed polarizations -/

/-- Two completed-Xi coefficients at one multiplicity-exact divisor copy. -/
abbrev CompletedXiSameFiberHodgePlane := ℂ × ℂ

/-- Route R's boundary-plus-hidden real corona plane. -/
abbrev PrimeDepthBVWoldFixedCoronaPlane :=
  PrimeDepthBVWoldReesCoronaCoordinate ×
    PrimeDepthBVWoldReesCoronaCoordinate

/-- Literal one-coordinate vector in the completed Xi Hilbert carrier. -/
def completedXiSameFiberVector (q : XiZeroCopy) (c : ℂ) : XiDivisorL2 :=
  lp.single 2 q c

/-- Real part of the completed-Xi Hilbert polarization on one fixed coordinate. -/
def completedXiSameFiberPolarization
    (q : XiZeroCopy) (c d : ℂ) : ℝ :=
  (inner ℂ (completedXiSameFiberVector q c)
    (completedXiSameFiberVector q d)).re

/-- Fixed product polarization on two copies of one completed-Xi coordinate line. -/
def completedXiSameFiberHodgePlanePolarization
    (q : XiZeroCopy)
    (z u : CompletedXiSameFiberHodgePlane) : ℝ :=
  completedXiSameFiberPolarization q z.1 u.1 +
    completedXiSameFiberPolarization q z.2 u.2

/-- Route R's fixed same-fibre product polarization.  Both blocks use the literal
identity metric `primeDepthBVWoldReesCoronaMetric`; no transported metric occurs. -/
def primeDepthBVWoldFixedCoronaPolarization
    (z u : PrimeDepthBVWoldFixedCoronaPlane) : ℝ :=
  dotProduct z.1
      (Matrix.mulVec primeDepthBVWoldReesCoronaMetric u.1) +
    dotProduct z.2
      (Matrix.mulVec primeDepthBVWoldReesCoronaMetric u.2)

/-- The pointwise completed-Xi Hodge weight has square minus one. -/
@[simp]
theorem deningerXiHarmonicHodgeWeight_sq (q : XiZeroCopy) :
    deningerXiHarmonicHodgeWeight q *
        deningerXiHarmonicHodgeWeight q = -1 := by
  rw [deningerXiHarmonicHodgeWeight]
  have hs :
      (((deningerFreqSign (q.1 : ℂ).im : ℝ) : ℂ) *
        ((deningerFreqSign (q.1 : ℂ).im : ℝ) : ℂ)) = 1 := by
    exact_mod_cast deningerFreqSign_sq (q.1 : ℂ).im
  have hI : Complex.I * Complex.I = -1 := by
    simpa only [pow_two] using Complex.I_sq
  rw [mul_mul_mul_comm, hI, hs]
  ring

/-- One completed-Xi coordinate has exactly the standard complex polarization. -/
theorem completedXiSameFiberPolarization_eq
    (q : XiZeroCopy) (c d : ℂ) :
    completedXiSameFiberPolarization q c d =
      (c * (starRingEnd ℂ d)).re := by
  unfold completedXiSameFiberPolarization completedXiSameFiberVector
  rw [lp.inner_single_left]
  simp
  ring

/-- Coefficient realification preserves the fixed real polarization exactly. -/
theorem primeDepthBVWoldReesCoronaRealification_dotProduct
    (c d : ℂ) :
    dotProduct
        (primeDepthBVWoldReesCoronaRealification c)
        (primeDepthBVWoldReesCoronaRealification d) =
      (c * (starRingEnd ℂ d)).re := by
  simp [dotProduct, primeDepthBVWoldReesCoronaRealification,
    Complex.mul_re]

/-- Realification is coefficient-faithful. -/
theorem primeDepthBVWoldReesCoronaRealification_injective :
    Function.Injective primeDepthBVWoldReesCoronaRealification := by
  intro c d h
  apply Complex.ext
  · have h0 := congrFun h 0
    simpa [primeDepthBVWoldReesCoronaRealification] using h0
  · have h1 := congrFun h 1
    simpa [primeDepthBVWoldReesCoronaRealification] using h1

@[simp]
theorem primeDepthBVWoldReesCoronaRealification_zero :
    primeDepthBVWoldReesCoronaRealification 0 = 0 := by
  ext k
  fin_cases k <;> rfl

theorem primeDepthBVWoldReesCoronaRealification_neg (c : ℂ) :
    primeDepthBVWoldReesCoronaRealification (-c) =
      -primeDepthBVWoldReesCoronaRealification c := by
  ext k
  fin_cases k <;> simp [primeDepthBVWoldReesCoronaRealification]

theorem primeDepthBVWoldReesCoronaRealification_real_smul
    (a : ℝ) (c : ℂ) :
    primeDepthBVWoldReesCoronaRealification ((a : ℂ) * c) =
      a • primeDepthBVWoldReesCoronaRealification c := by
  ext k
  fin_cases k <;>
    simp [primeDepthBVWoldReesCoronaRealification, Complex.mul_re,
      Complex.mul_im]

/-! ## Canonical Hodge untwisting -/

/-- Unique hidden-fibre trivialization compatible with the actual completed-Xi
Hodge weight. -/
def completedXiHodgeHiddenUntwist
    (q : XiZeroCopy) (c : ℂ) : PrimeDepthBVWoldReesCoronaCoordinate :=
  primeDepthBVWoldReesCoronaRealification
    (-deningerXiHarmonicHodgeWeight q * c)

/-- Fixed-polarization comparison from the completed-Xi Hodge plane to Route R's
fixed boundary-plus-hidden corona plane. -/
def completedXiFixedCoronaComparison
    (q : XiZeroCopy) (z : CompletedXiSameFiberHodgePlane) :
    PrimeDepthBVWoldFixedCoronaPlane :=
  (primeDepthBVWoldReesCoronaRealification z.1,
    completedXiHodgeHiddenUntwist q z.2)

/-- Odd Hodge rotation on the completed-Xi coefficient plane. -/
def completedXiSameFiberHodgeRotation
    (q : XiZeroCopy) (z : CompletedXiSameFiberHodgePlane) :
    CompletedXiSameFiberHodgePlane :=
  (deningerXiHarmonicHodgeWeight q * z.2,
    deningerXiHarmonicHodgeWeight q * z.1)

/-- Fixed odd Hodge rotation on Route R's product corona plane. -/
def primeDepthBVWoldFixedCoronaHodgeRotation
    (z : PrimeDepthBVWoldFixedCoronaPlane) :
    PrimeDepthBVWoldFixedCoronaPlane :=
  (-z.2, z.1)

/-- Multiplication by the Hodge untwisting phase preserves the complex
polarization before taking real parts. -/
theorem completedXiHodgeHiddenUntwist_mul_star
    (q : XiZeroCopy) (c d : ℂ) :
    (-deningerXiHarmonicHodgeWeight q * c) *
        (starRingEnd ℂ
          (-deningerXiHarmonicHodgeWeight q * d)) =
      c * (starRingEnd ℂ d) := by
  rw [deningerXiHarmonicHodgeWeight, deningerFreqSign]
  split_ifs <;> norm_num
  all_goals
    calc
      -(Complex.I * c * (Complex.I * (starRingEnd ℂ d))) =
          -(Complex.I * Complex.I) *
            (c * (starRingEnd ℂ d)) := by ring
      _ = c * (starRingEnd ℂ d) := by
        rw [show Complex.I * Complex.I = -1 by
          simpa only [pow_two] using Complex.I_sq]
        ring

/-- The hidden untwisting is an isometry for the fixed real polarization. -/
theorem completedXiHodgeHiddenUntwist_dotProduct
    (q : XiZeroCopy) (c d : ℂ) :
    dotProduct (completedXiHodgeHiddenUntwist q c)
        (completedXiHodgeHiddenUntwist q d) =
      completedXiSameFiberPolarization q c d := by
  change
    dotProduct
        (primeDepthBVWoldReesCoronaRealification
          (-deningerXiHarmonicHodgeWeight q * c))
        (primeDepthBVWoldReesCoronaRealification
          (-deningerXiHarmonicHodgeWeight q * d)) = _
  rw [
    primeDepthBVWoldReesCoronaRealification_dotProduct,
    completedXiHodgeHiddenUntwist_mul_star,
    completedXiSameFiberPolarization_eq]

/-- Main fixed-polarization theorem: the comparison preserves the literal
completed-Xi and Route-R product polarizations exactly. -/
theorem completedXiFixedCoronaComparison_polarization
    (q : XiZeroCopy) (z u : CompletedXiSameFiberHodgePlane) :
    primeDepthBVWoldFixedCoronaPolarization
        (completedXiFixedCoronaComparison q z)
        (completedXiFixedCoronaComparison q u) =
      completedXiSameFiberHodgePlanePolarization q z u := by
  simp only [primeDepthBVWoldFixedCoronaPolarization,
    completedXiFixedCoronaComparison,
    primeDepthBVWoldReesCoronaMetric, Matrix.one_mulVec]
  rw [primeDepthBVWoldReesCoronaRealification_dotProduct,
    completedXiHodgeHiddenUntwist_dotProduct,
    completedXiSameFiberHodgePlanePolarization,
    completedXiSameFiberPolarization_eq q z.1 u.1,
    completedXiSameFiberPolarization_eq q z.2 u.2]

/-- The comparison retains both complex coefficients. -/
theorem completedXiFixedCoronaComparison_injective (q : XiZeroCopy) :
    Function.Injective (completedXiFixedCoronaComparison q) := by
  intro z u h
  apply Prod.ext
  · apply primeDepthBVWoldReesCoronaRealification_injective
    exact congrArg Prod.fst h
  · have hwne : deningerXiHarmonicHodgeWeight q ≠ 0 := by
      intro hw
      have hn := norm_deningerXiHarmonicHodgeWeight q
      rw [hw, norm_zero] at hn
      norm_num at hn
    have hh := congrArg Prod.snd h
    change
      primeDepthBVWoldReesCoronaRealification
          (-deningerXiHarmonicHodgeWeight q * z.2) =
        primeDepthBVWoldReesCoronaRealification
          (-deningerXiHarmonicHodgeWeight q * u.2) at hh
    have hmul :=
      primeDepthBVWoldReesCoronaRealification_injective hh
    exact mul_left_cancel₀ (neg_ne_zero.mpr hwne) hmul

/-- The actual completed-Xi Hodge multiplier acts on the one-coordinate vector
by the same pointwise Hodge weight used in the comparison. -/
theorem deningerXiHarmonicHodge_completedXiSameFiberVector
    (q : XiZeroCopy) (c : ℂ) :
    deningerXiHarmonicHodge (completedXiSameFiberVector q c) =
      completedXiSameFiberVector q
        (deningerXiHarmonicHodgeWeight q * c) := by
  ext r
  rw [deningerXiHarmonicHodge_apply]
  by_cases hrq : r = q
  · subst r
    simp [completedXiSameFiberVector,
      deningerXiHarmonicHodgeWeight]
  · simp [completedXiSameFiberVector, lp.single_apply, hrq]

/-- Hodge untwisting sends the source Hodge mate to the fixed hidden mate. -/
@[simp]
theorem completedXiHodgeHiddenUntwist_hodge
    (q : XiZeroCopy) (c : ℂ) :
    completedXiHodgeHiddenUntwist q
        (deningerXiHarmonicHodgeWeight q * c) =
      primeDepthBVWoldReesCoronaRealification c := by
  rw [completedXiHodgeHiddenUntwist]
  congr 1
  rw [← mul_assoc, neg_mul, deningerXiHarmonicHodgeWeight_sq]
  ring

/-- The source and target odd-Hodge rotations are intertwined exactly. -/
theorem completedXiFixedCoronaComparison_hodge
    (q : XiZeroCopy) (z : CompletedXiSameFiberHodgePlane) :
    completedXiFixedCoronaComparison q
        (completedXiSameFiberHodgeRotation q z) =
      primeDepthBVWoldFixedCoronaHodgeRotation
        (completedXiFixedCoronaComparison q z) := by
  unfold completedXiFixedCoronaComparison
    completedXiSameFiberHodgeRotation
    primeDepthBVWoldFixedCoronaHodgeRotation
  apply Prod.ext
  · change
      primeDepthBVWoldReesCoronaRealification
          (deningerXiHarmonicHodgeWeight q * z.2) =
        -completedXiHodgeHiddenUntwist q z.2
    have hneg :=
      primeDepthBVWoldReesCoronaRealification_neg
        (-deningerXiHarmonicHodgeWeight q * z.2)
    simpa [completedXiHodgeHiddenUntwist] using hneg
  · exact completedXiHodgeHiddenUntwist_hodge q z.1

/-- Both source and target Hodge rotations have square minus one. -/
theorem completedXiSameFiberHodgeRotation_sq
    (q : XiZeroCopy) (z : CompletedXiSameFiberHodgePlane) :
    completedXiSameFiberHodgeRotation q
        (completedXiSameFiberHodgeRotation q z) = -z := by
  apply Prod.ext <;>
    simp [completedXiSameFiberHodgeRotation,
      ← mul_assoc, deningerXiHarmonicHodgeWeight_sq]

/-- The hidden trivialization is forced by compatibility with the actual Hodge
weight; even linearity is unnecessary for uniqueness. -/
theorem completedXiHodgeHiddenUntwist_unique
    (q : XiZeroCopy)
    (T : ℂ → PrimeDepthBVWoldReesCoronaCoordinate)
    (hT : ∀ c : ℂ,
      T (deningerXiHarmonicHodgeWeight q * c) =
        primeDepthBVWoldReesCoronaRealification c) :
    T = completedXiHodgeHiddenUntwist q := by
  funext z
  have hz :
      deningerXiHarmonicHodgeWeight q *
          (-deningerXiHarmonicHodgeWeight q * z) = z := by
    rw [← mul_assoc, mul_neg,
      deningerXiHarmonicHodgeWeight_sq]
    ring
  calc
    T z = T (deningerXiHarmonicHodgeWeight q *
        (-deningerXiHarmonicHodgeWeight q * z)) := by rw [hz]
    _ = primeDepthBVWoldReesCoronaRealification
        (-deningerXiHarmonicHodgeWeight q * z) := hT _
    _ = completedXiHodgeHiddenUntwist q z := rfl

/-! ## Zero-hidden physical lift and resolved graph -/

/-- The fixed hidden Hodge mate of a physical coefficient. -/
def primeDepthBVWoldReesCoronaHodgeMateLift
    (c : ℂ) : PrimeDepthBVWoldFixedCoronaPlane :=
  (0, primeDepthBVWoldReesCoronaRealification c)

/-- The completed-Xi physical coefficient lands on Route R's fixed zero-hidden
section, not on a transported harmonic section. -/
@[simp]
theorem completedXiFixedCoronaComparison_zeroHidden
    (q : XiZeroCopy) (c : ℂ) :
    completedXiFixedCoronaComparison q (c, 0) =
      primeDepthBVWoldReesCoronaScalarLift c := by
  apply Prod.ext
  · rfl
  · simp [completedXiFixedCoronaComparison,
      completedXiHodgeHiddenUntwist,
      primeDepthBVWoldReesCoronaScalarLift]

/-- The completed-Xi Hodge mate lands on the fixed hidden mate. -/
@[simp]
theorem completedXiFixedCoronaComparison_hodgeMate
    (q : XiZeroCopy) (c : ℂ) :
    completedXiFixedCoronaComparison q
        (completedXiSameFiberHodgeRotation q (c, 0)) =
      primeDepthBVWoldReesCoronaHodgeMateLift c := by
  rw [completedXiFixedCoronaComparison_hodge]
  simp [primeDepthBVWoldFixedCoronaHodgeRotation,
    completedXiFixedCoronaComparison,
    completedXiHodgeHiddenUntwist,
    primeDepthBVWoldReesCoronaHodgeMateLift]

/-- Source coefficient pair whose Hodge-mate coefficient records a real corona
shear `K`. -/
def completedXiResolvedCoefficientLift
    (q : XiZeroCopy) (K : ℝ) (c : ℂ) :
    CompletedXiSameFiberHodgePlane :=
  (c, -((K : ℂ) * deningerXiHarmonicHodgeWeight q * c))

/-- The source resolved coefficient lands on the explicit fixed-metric graph.
This identity holds for every real `K`, including off-line Route-R weights. -/
theorem completedXiFixedCoronaComparison_resolvedCoefficientLift
    (q : XiZeroCopy) (K : ℝ) (c : ℂ) :
    completedXiFixedCoronaComparison q
        (completedXiResolvedCoefficientLift q K c) =
      (primeDepthBVWoldReesCoronaRealification c,
        -K • primeDepthBVWoldReesCoronaRealification c) := by
  apply Prod.ext
  · rfl
  · rw [completedXiFixedCoronaComparison,
      completedXiResolvedCoefficientLift,
      completedXiHodgeHiddenUntwist]
    have hcomplex :
        -deningerXiHarmonicHodgeWeight q *
            (-((K : ℂ) * deningerXiHarmonicHodgeWeight q * c)) =
          (-K : ℂ) * c := by
      calc
        -deningerXiHarmonicHodgeWeight q *
            (-((K : ℂ) * deningerXiHarmonicHodgeWeight q * c)) =
          (K : ℂ) *
            (deningerXiHarmonicHodgeWeight q *
              deningerXiHarmonicHodgeWeight q) * c := by ring
        _ = (-K : ℂ) * c := by
          rw [deningerXiHarmonicHodgeWeight_sq]
          ring
    change
      primeDepthBVWoldReesCoronaRealification
          (-deningerXiHarmonicHodgeWeight q *
            (-((K : ℂ) * deningerXiHarmonicHodgeWeight q * c))) =
        -K • primeDepthBVWoldReesCoronaRealification c
    rw [hcomplex]
    simpa using
      (primeDepthBVWoldReesCoronaRealification_real_smul (-K) c)

/-- Existing harmonic corona graph is exactly the scalar graph with coefficient
`primeDepthBVWoldReesCoronaWeight`. -/
theorem primeDepthBVWoldReesCoronaResolvedLift_eq_graph
    (a : ℝ) (i j : PrimeDepthBVWoldCell) (c : ℂ) :
    primeDepthBVWoldReesCoronaResolvedLift a i j c =
      (primeDepthBVWoldReesCoronaRealification c,
        -(primeDepthBVWoldReesCoronaWeight a i j) •
          primeDepthBVWoldReesCoronaRealification c) := by
  apply Prod.ext
  · rfl
  · ext k
    simp [primeDepthBVWoldReesCoronaResolvedLift,
      CoronaSchur.harmonicGraph, CoronaSchur.hiddenMinimizer,
      primeDepthBVWoldReesCoronaCoupling,
      primeDepthBVWoldReesCoronaMetric,
      Matrix.smul_mulVec]

/-- Exact identification of the completed-Xi resolved coefficient with Route R's
existing harmonic corona graph. -/
theorem completedXiFixedCoronaComparison_resolvedLift
    (q : XiZeroCopy) (a : ℝ) (i j : PrimeDepthBVWoldCell) (c : ℂ) :
    completedXiFixedCoronaComparison q
        (completedXiResolvedCoefficientLift q
          (primeDepthBVWoldReesCoronaWeight a i j) c) =
      primeDepthBVWoldReesCoronaResolvedLift a i j c := by
  rw [completedXiFixedCoronaComparison_resolvedCoefficientLift,
    primeDepthBVWoldReesCoronaResolvedLift_eq_graph]

/-! ## Rational-adelic actual-Xi specialization -/

/-- First multiplicity copy of one actual Xi support point. -/
def ccmRationalAdelicPrimeXiLeadingZeroCopy
    (rho : XiDivisorSupport) : XiZeroCopy :=
  ⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩

/-- Actual rational-adelic leading-Xi coefficient placed on its canonical
completed-Xi coordinate line. -/
def ccmRationalAdelicPrimeXiCompletedPhysicalVector
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (x : (ccmRationalAdelicPrimeRelativeComplex p).H1) : XiDivisorL2 :=
  completedXiSameFiberVector
    (ccmRationalAdelicPrimeXiLeadingZeroCopy rho)
    (ccmRationalAdelicPrimeXiReesCoronaCoefficient p rho x)

/-- Coefficient extraction recovers the literal rational-adelic leading-Xi
coefficient, with no radial normalization. -/
@[simp]
theorem ccmRationalAdelicPrimeXiCompletedPhysicalVector_apply
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (x : (ccmRationalAdelicPrimeRelativeComplex p).H1) :
    ccmRationalAdelicPrimeXiCompletedPhysicalVector p rho x
        (ccmRationalAdelicPrimeXiLeadingZeroCopy rho) =
      ccmRationalAdelicPrimeXiReesCoronaCoefficient p rho x := by
  simp [ccmRationalAdelicPrimeXiCompletedPhysicalVector,
    completedXiSameFiberVector]

/-- On the retained period-one source atom, the completed coefficient is the
actual nonzero multiplicity-leading Xi jet. -/
theorem ccmRationalAdelicPrimeXiCompletedPhysicalVector_class
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiCompletedPhysicalVector p rho
        (ccmRationalAdelicPrimeRelativeClass p) =
      completedXiSameFiberVector
        (ccmRationalAdelicPrimeXiLeadingZeroCopy rho)
        (iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho)) := by
  rw [ccmRationalAdelicPrimeXiCompletedPhysicalVector,
    ccmRationalAdelicPrimeXiReesCoronaCoefficient_class]

/-- The retained completed-Xi physical vector is nonzero unconditionally. -/
theorem ccmRationalAdelicPrimeXiCompletedPhysicalVector_class_ne_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiCompletedPhysicalVector p rho
        (ccmRationalAdelicPrimeRelativeClass p) ≠ 0 := by
  intro hzero
  have hq := congrArg
    (fun v : XiDivisorL2 =>
      v (ccmRationalAdelicPrimeXiLeadingZeroCopy rho)) hzero
  rw [ccmRationalAdelicPrimeXiCompletedPhysicalVector_apply,
    ccmRationalAdelicPrimeXiReesCoronaCoefficient_class] at hq
  exact iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho hq

/-- The completed-Xi coefficient plane lands exactly on the already fixed
rational-adelic physical corona comparison. -/
theorem ccmRationalAdelicPrimeXiCompletedPhysical_zeroHidden
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (x : (ccmRationalAdelicPrimeRelativeComplex p).H1) :
    completedXiFixedCoronaComparison
        (ccmRationalAdelicPrimeXiLeadingZeroCopy rho)
        (ccmRationalAdelicPrimeXiReesCoronaCoefficient p rho x, 0) =
      ccmRationalAdelicPrimeXiPhysicalReesCoronaComparison p rho x := by
  rw [completedXiFixedCoronaComparison_zeroHidden,
    ccmRationalAdelicPrimeXiPhysicalReesCoronaComparison]

/-- Fixed same-fibre corona polarization of two physical rational-adelic
landings equals their literal completed-Xi polarization. -/
theorem ccmRationalAdelicPrimeXiCompletedPhysical_polarization
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (x y : (ccmRationalAdelicPrimeRelativeComplex p).H1) :
    primeDepthBVWoldFixedCoronaPolarization
        (ccmRationalAdelicPrimeXiPhysicalReesCoronaComparison p rho x)
        (ccmRationalAdelicPrimeXiPhysicalReesCoronaComparison p rho y) =
      completedXiSameFiberPolarization
        (ccmRationalAdelicPrimeXiLeadingZeroCopy rho)
        (ccmRationalAdelicPrimeXiReesCoronaCoefficient p rho x)
        (ccmRationalAdelicPrimeXiReesCoronaCoefficient p rho y) := by
  rw [← ccmRationalAdelicPrimeXiCompletedPhysical_zeroHidden,
    ← ccmRationalAdelicPrimeXiCompletedPhysical_zeroHidden,
    completedXiFixedCoronaComparison_polarization]
  simp [completedXiSameFiberHodgePlanePolarization,
    completedXiSameFiberPolarization_eq]

/-- The retained atom's completed-Xi physical landing is the fixed zero-hidden
lift of its actual leading Xi jet. -/
theorem ccmRationalAdelicPrimeXiCompletedPhysical_class_zeroHidden
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    completedXiFixedCoronaComparison
        (ccmRationalAdelicPrimeXiLeadingZeroCopy rho)
        (iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho), 0) =
      ccmRationalAdelicPrimeXiPhysicalReesCoronaComparison p rho
        (ccmRationalAdelicPrimeRelativeClass p) := by
  rw [ccmRationalAdelicPrimeXiPhysicalReesCoronaComparison,
    ccmRationalAdelicPrimeXiReesCoronaCoefficient_class,
    completedXiFixedCoronaComparison_zeroHidden]

/-- The same comparison carries the explicit completed Hodge-mate coefficient
to Route R's resolved harmonic graph, retaining the off-line shear rather than
assuming it vanishes. -/
theorem ccmRationalAdelicPrimeXiCompletedResolved_class
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    completedXiFixedCoronaComparison
        (ccmRationalAdelicPrimeXiLeadingZeroCopy rho)
        (completedXiResolvedCoefficientLift
          (ccmRationalAdelicPrimeXiLeadingZeroCopy rho)
          (primeDepthBVWoldReesCoronaWeight
            (primeDepthBVWoldXiCenteredRate rho)
            (ccmRationalAdelicPrimeRelativeXiCellZero p)
            (ccmRationalAdelicPrimeRelativeXiCellOne p))
          (iteratedDeriv (xiSupportMultiplicity rho) XiC
            (xiSpectralPointSupport rho))) =
      ccmRationalAdelicPrimeXiResolvedReesCoronaComparison p rho
        (ccmRationalAdelicPrimeRelativeClass p) := by
  rw [ccmRationalAdelicPrimeXiResolvedReesCoronaComparison,
    ccmRationalAdelicPrimeXiReesCoronaCoefficient_class]
  exact completedXiFixedCoronaComparison_resolvedLift _ _ _ _ _

end

end RHTower

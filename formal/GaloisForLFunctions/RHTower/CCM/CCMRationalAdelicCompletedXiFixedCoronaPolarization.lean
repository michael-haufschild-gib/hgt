import GaloisForLFunctions.RHTower.PrimeDepthBVWoldReesCoronaQuotient
import GaloisForLFunctions.RHTower.PrimeDepthBVWoldReesCoronaContractionNoGo
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerReflectedGaussianHarmonicSourcePrimitive

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
    (T : ℂ → PrimeDepthBVWoldReesCoronaCoordinate) :
    (∀ c : ℂ,
      T (deningerXiHarmonicHodgeWeight q * c) =
        primeDepthBVWoldReesCoronaRealification c) ↔
      T = completedXiHodgeHiddenUntwist q := by
  constructor
  · intro hT
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
  · intro hT c
    rw [hT]
    exact completedXiHodgeHiddenUntwist_hodge q c

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

/-! ## Fixed same-fibre shear rigidity -/

/-- Self-polarization of one completed-Xi coefficient is its squared
complex norm. -/
theorem completedXiSameFiberPolarization_self
    (q : XiZeroCopy) (c : ℂ) :
    completedXiSameFiberPolarization q c c = Complex.normSq c := by
  rw [completedXiSameFiberPolarization_eq]
  simp [Complex.normSq, Complex.mul_re]

/-- Exact fixed-polarization energy of the resolved coefficient.  The
Hodge-mate coefficient contributes the positive excess `K^(2 : ℕ)`. -/
theorem completedXiResolvedCoefficientLift_fixedPolarization
    (q : XiZeroCopy) (K : ℝ) (c : ℂ) :
    completedXiSameFiberHodgePlanePolarization q
        (completedXiResolvedCoefficientLift q K c)
        (completedXiResolvedCoefficientLift q K c) =
      (1 + K ^ (2 : ℕ)) * completedXiSameFiberPolarization q c c := by
  have hweight :
      Complex.normSq (deningerXiHarmonicHodgeWeight q) = 1 := by
    rw [Complex.normSq_eq_norm_sq,
      norm_deningerXiHarmonicHodgeWeight]
    norm_num
  rw [completedXiSameFiberHodgePlanePolarization,
    completedXiResolvedCoefficientLift]
  rw [completedXiSameFiberPolarization_self,
    completedXiSameFiberPolarization_self,
    Complex.normSq_neg, Complex.normSq_mul,
    Complex.normSq_mul, Complex.normSq_ofReal, hweight]
  ring

/-- Exact unconditional classification of resolved versus physical fixed
same-fibre norms.  Equality occurs precisely when either the Hodge-mate shear
vanishes or the physical coefficient itself vanishes. -/
theorem completedXiResolvedCoefficientLift_fixedNorm_eq_iff
    (q : XiZeroCopy) (K : ℝ) (c : ℂ) :
    completedXiSameFiberHodgePlanePolarization q
        (completedXiResolvedCoefficientLift q K c)
        (completedXiResolvedCoefficientLift q K c) =
      completedXiSameFiberHodgePlanePolarization q (c, 0) (c, 0) ↔
        K = 0 ∨ c = 0 := by
  rw [completedXiResolvedCoefficientLift_fixedPolarization]
  have hphysical :
      completedXiSameFiberHodgePlanePolarization q (c, 0) (c, 0) =
        completedXiSameFiberPolarization q c c := by
    simp [completedXiSameFiberHodgePlanePolarization,
      completedXiSameFiberPolarization_self]
  rw [hphysical]
  rw [completedXiSameFiberPolarization_self]
  constructor
  · intro h
    by_cases hc : c = 0
    · exact Or.inr hc
    · left
      have hpos : 0 < Complex.normSq c := Complex.normSq_pos.mpr hc
      have hKsq : K ^ (2 : ℕ) = 0 := by nlinarith
      exact sq_eq_zero_iff.mp hKsq
  · rintro (hK | hc)
    · subst K
      norm_num
    · subst c
      simp

/-- Fixed same-fibre norm preservation on every physical coefficient is
equivalent to zero Hodge-mate shear. -/
theorem completedXiResolvedCoefficientLift_fixedNorm_preserving_iff
    (q : XiZeroCopy) (K : ℝ) :
    (∀ c : ℂ,
      completedXiSameFiberHodgePlanePolarization q
          (completedXiResolvedCoefficientLift q K c)
          (completedXiResolvedCoefficientLift q K c) =
        completedXiSameFiberHodgePlanePolarization q (c, 0) (c, 0)) ↔
      K = 0 := by
  constructor
  · intro h
    have hclass :=
      (completedXiResolvedCoefficientLift_fixedNorm_eq_iff q K 1).mp (h 1)
    simpa using hclass
  · intro hK c
    exact
      (completedXiResolvedCoefficientLift_fixedNorm_eq_iff q K c).2 (Or.inl hK)

/-- Shear carrying a zero-hidden completed-Xi coefficient to its resolved
Hodge-mate graph. -/
def completedXiSameFiberResolvedShear
    (q : XiZeroCopy) (K : ℝ)
    (z : CompletedXiSameFiberHodgePlane) :
    CompletedXiSameFiberHodgePlane :=
  (z.1, z.2 - (K : ℂ) * deningerXiHarmonicHodgeWeight q * z.1)

@[simp]
theorem completedXiSameFiberResolvedShear_physical
    (q : XiZeroCopy) (K : ℝ) (c : ℂ) :
    completedXiSameFiberResolvedShear q K (c, 0) =
      completedXiResolvedCoefficientLift q K c := by
  simp [completedXiSameFiberResolvedShear,
    completedXiResolvedCoefficientLift]

/-- The resolved shear preserves the literal fixed same-fibre norm on the
whole coefficient plane exactly when its Hodge-mate coefficient vanishes. -/
theorem completedXiSameFiberResolvedShear_fixedNorm_iff
    (q : XiZeroCopy) (K : ℝ) :
    (∀ z : CompletedXiSameFiberHodgePlane,
      completedXiSameFiberHodgePlanePolarization q
          (completedXiSameFiberResolvedShear q K z)
          (completedXiSameFiberResolvedShear q K z) =
        completedXiSameFiberHodgePlanePolarization q z z) ↔
      K = 0 := by
  constructor
  · intro h
    have h1 := h (1, 0)
    rw [completedXiSameFiberResolvedShear_physical] at h1
    have hclass :=
      (completedXiResolvedCoefficientLift_fixedNorm_eq_iff q K 1).mp h1
    simpa using hclass
  · intro hK z
    subst K
    simp [completedXiSameFiberResolvedShear]

/-- Source-dagger form of the same rigidity: the resolved shear commutes
with the fixed completed-Xi odd Hodge rotation exactly for `K = 0`. -/
theorem completedXiSameFiberResolvedShear_commutes_hodge_iff
    (q : XiZeroCopy) (K : ℝ) :
    (∀ z : CompletedXiSameFiberHodgePlane,
      completedXiSameFiberResolvedShear q K
          (completedXiSameFiberHodgeRotation q z) =
        completedXiSameFiberHodgeRotation q
          (completedXiSameFiberResolvedShear q K z)) ↔
      K = 0 := by
  constructor
  · intro h
    have hfirst := congrArg Prod.fst (h (1, 0))
    simp only [completedXiSameFiberResolvedShear,
      completedXiSameFiberHodgeRotation, mul_zero, mul_one,
      zero_sub, sub_zero] at hfirst
    change (0 : ℂ) = deningerXiHarmonicHodgeWeight q *
      (-((K : ℂ) * deningerXiHarmonicHodgeWeight q)) at hfirst
    have hzeroC : (0 : ℂ) = (K : ℂ) := by
      calc
        0 = deningerXiHarmonicHodgeWeight q *
            (-((K : ℂ) * deningerXiHarmonicHodgeWeight q)) := hfirst
        _ = (K : ℂ) := by
          rw [show deningerXiHarmonicHodgeWeight q *
              (-((K : ℂ) * deningerXiHarmonicHodgeWeight q)) =
            -(K : ℂ) * (deningerXiHarmonicHodgeWeight q *
              deningerXiHarmonicHodgeWeight q) by ring,
            deningerXiHarmonicHodgeWeight_sq]
          ring
    exact_mod_cast hzeroC.symm
  · intro hK z
    subst K
    simp [completedXiSameFiberResolvedShear,
      completedXiSameFiberHodgeRotation]

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

/-- Target-side unconditional classification of fixed same-fibre norm rigidity.
The explicit Route-R graph and zero-hidden lift have the same fixed product norm
exactly when the shear or the physical coefficient vanishes. -/
theorem completedXiFixedCoronaComparison_resolved_fixedNorm_eq_iff
    (q : XiZeroCopy) (K : ℝ) (c : ℂ) :
    primeDepthBVWoldFixedCoronaPolarization
        (primeDepthBVWoldReesCoronaRealification c,
          -K • primeDepthBVWoldReesCoronaRealification c)
        (primeDepthBVWoldReesCoronaRealification c,
          -K • primeDepthBVWoldReesCoronaRealification c) =
      primeDepthBVWoldFixedCoronaPolarization
        (primeDepthBVWoldReesCoronaScalarLift c)
        (primeDepthBVWoldReesCoronaScalarLift c) ↔
      K = 0 ∨ c = 0 := by
  rw [← completedXiFixedCoronaComparison_resolvedCoefficientLift q K c,
    ← completedXiFixedCoronaComparison_zeroHidden q c,
    completedXiFixedCoronaComparison_polarization,
    completedXiFixedCoronaComparison_polarization]
  exact completedXiResolvedCoefficientLift_fixedNorm_eq_iff q K c

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

/-- Explicit Hodge-mate coefficient of the actual retained rational-adelic
adjacent-depth Route-R atom. -/
def ccmRationalAdelicPrimeXiHodgeMateCoefficient
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℝ :=
  primeDepthBVWoldReesCoronaWeight
    (primeDepthBVWoldXiCenteredRate rho)
    (ccmRationalAdelicPrimeRelativeXiCellZero p)
    (ccmRationalAdelicPrimeRelativeXiCellOne p)

/-- The actual Hodge-mate coefficient vanishes exactly at critical-line support.
The prime-dependent adjacent attenuation is strictly positive, so it cannot erase
the centered horizontal Xi rate. -/
theorem ccmRationalAdelicPrimeXiHodgeMateCoefficient_eq_zero_iff_re_eq_half
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [ccmRationalAdelicPrimeXiHodgeMateCoefficient,
    primeDepthBVWoldReesCoronaWeight_adjacent_eq_zero_iff,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Actual fixed same-fibre norm identity for the retained period-one source
atom.  This proposition contains no line-placement premise. -/
def CCMRationalAdelicPrimeXiSameFiberNormIdentity
    (p : Nat.Primes) (rho : XiDivisorSupport) : Prop :=
  completedXiSameFiberHodgePlanePolarization
      (ccmRationalAdelicPrimeXiLeadingZeroCopy rho)
      (completedXiResolvedCoefficientLift
        (ccmRationalAdelicPrimeXiLeadingZeroCopy rho)
        (ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho)
        (iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho)))
      (completedXiResolvedCoefficientLift
        (ccmRationalAdelicPrimeXiLeadingZeroCopy rho)
        (ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho)
        (iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho))) =
    completedXiSameFiberHodgePlanePolarization
      (ccmRationalAdelicPrimeXiLeadingZeroCopy rho)
      (iteratedDeriv (xiSupportMultiplicity rho) XiC
        (xiSpectralPointSupport rho), 0)
      (iteratedDeriv (xiSupportMultiplicity rho) XiC
        (xiSpectralPointSupport rho), 0)

/-- Source-dagger form of the actual retained-atom identity: the resolved
source shear commutes with the literal completed-Xi Hodge rotation. -/
def CCMRationalAdelicPrimeXiSourceDaggerIdentity
    (p : Nat.Primes) (rho : XiDivisorSupport) : Prop :=
  ∀ z : CompletedXiSameFiberHodgePlane,
    completedXiSameFiberResolvedShear
        (ccmRationalAdelicPrimeXiLeadingZeroCopy rho)
        (ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho)
        (completedXiSameFiberHodgeRotation
          (ccmRationalAdelicPrimeXiLeadingZeroCopy rho) z) =
      completedXiSameFiberHodgeRotation
        (ccmRationalAdelicPrimeXiLeadingZeroCopy rho)
        (completedXiSameFiberResolvedShear
          (ccmRationalAdelicPrimeXiLeadingZeroCopy rho)
          (ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho) z)

/-- Exact formal closure of the Hodge-mate coefficient gap: the actual
same-fibre norm identity is equivalent to `K = 0`, using the already proved
non-erasure of the multiplicity-leading Xi coefficient. -/
theorem ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_hodgeMateCoefficient_eq_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiSameFiberNormIdentity p rho ↔
      ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho = 0 := by
  unfold CCMRationalAdelicPrimeXiSameFiberNormIdentity
  rw [completedXiResolvedCoefficientLift_fixedNorm_eq_iff]
  exact or_iff_left (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)

/-- Equivalent source-dagger closure of the same explicit coefficient. -/
theorem ccmRationalAdelicPrimeXiSourceDaggerIdentity_iff_hodgeMateCoefficient_eq_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiSourceDaggerIdentity p rho ↔
      ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho = 0 := by
  exact completedXiSameFiberResolvedShear_commutes_hodge_iff
    (ccmRationalAdelicPrimeXiLeadingZeroCopy rho)
    (ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho)

/-- The retained atom has equal resolved and physical fixed norms exactly when
its Xi support lies on the critical line. -/
theorem ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_re_eq_half
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiSameFiberNormIdentity p rho ↔
      (rho : ℂ).re = 1 / 2 :=
  (ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_hodgeMateCoefficient_eq_zero
    p rho).trans
    (ccmRationalAdelicPrimeXiHodgeMateCoefficient_eq_zero_iff_re_eq_half p rho)

/-- The retained source shear commutes with the fixed Hodge rotation exactly
when its Xi support lies on the critical line. -/
theorem ccmRationalAdelicPrimeXiSourceDaggerIdentity_iff_re_eq_half
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiSourceDaggerIdentity p rho ↔
      (rho : ℂ).re = 1 / 2 :=
  (ccmRationalAdelicPrimeXiSourceDaggerIdentity_iff_hodgeMateCoefficient_eq_zero
    p rho).trans
    (ccmRationalAdelicPrimeXiHodgeMateCoefficient_eq_zero_iff_re_eq_half p rho)

/-- Fixed-norm and source-dagger identities are two exact presentations of
the same retained-atom condition. -/
theorem ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_sourceDaggerIdentity
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiSameFiberNormIdentity p rho ↔
      CCMRationalAdelicPrimeXiSourceDaggerIdentity p rho :=
  (ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_re_eq_half p rho).trans
    (ccmRationalAdelicPrimeXiSourceDaggerIdentity_iff_re_eq_half p rho).symm

/-- At any one fixed ordinary prime, fixed-norm preservation for every actual
Xi support point is exactly the Riemann hypothesis. -/
theorem forall_ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_riemannHypothesis
    (p : Nat.Primes) :
    (∀ rho : XiDivisorSupport,
      CCMRationalAdelicPrimeXiSameFiberNormIdentity p rho) ↔
      RiemannHypothesis := by
  constructor
  · intro hidentity
    rw [rh_iff_xi_ne_zero_right]
    intro s hs hzero
    let rho : XiDivisorSupport :=
      ⟨s, mem_xi_divisor_support_of_eq_zero hzero⟩
    have hhalf :=
      (ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_re_eq_half p rho).mp
        (hidentity rho)
    have hright := mem_rightHalf.mp hs
    dsimp [rho] at hhalf
    linarith
  · intro hRH rho
    exact
      (ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_re_eq_half p rho).2
        (xi_divisor_support_re_eq_half_of_rh hRH rho)

/-- At any one fixed ordinary prime, source-dagger compatibility for every
actual Xi support point is exactly the Riemann hypothesis. -/
theorem forall_ccmRationalAdelicPrimeXiSourceDaggerIdentity_iff_riemannHypothesis
    (p : Nat.Primes) :
    (∀ rho : XiDivisorSupport,
      CCMRationalAdelicPrimeXiSourceDaggerIdentity p rho) ↔
      RiemannHypothesis := by
  rw [← forall_ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_riemannHypothesis p]
  exact forall_congr' fun rho =>
    (ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_sourceDaggerIdentity p rho).symm

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

namespace RHTower

noncomputable section

/-! ## Selector no-gos: invariant lines and comparison gauge

A candidate source selector for vanishing of the Hodge-mate coefficient would
supply, at each divisor copy, a coefficient-faithful line preserved by the
resolved shear, or a comparison identifying the resolved and zero-hidden
landings.  Both shapes are classified unconditionally.  The resolved shear is
unipotent, so a shear-invariant line that retains the boundary coefficient
exists exactly at zero shear; and every polarization-preserving comparison
transports one and the same strictly positive energy gap, so no choice of
comparison can identify the two landings away from zero shear.  Neither
structure can therefore produce the vanishing; each re-encodes it. -/

/-- Unipotent rigidity of the resolved shear: a coefficient-faithful vector
spans a shear-invariant line exactly at zero Hodge-mate shear.  No metric,
positivity, or Hodge-rotation datum enters. -/
theorem completedXiSameFiberResolvedShear_eigenvector_iff
    (q : XiZeroCopy) (K : ℝ) (v : CompletedXiSameFiberHodgePlane)
    (hv : v.1 ≠ 0) :
    (∃ lam : ℂ, completedXiSameFiberResolvedShear q K v = lam • v) ↔
      K = 0 := by
  constructor
  · rintro ⟨lam, hlam⟩
    have hw : deningerXiHarmonicHodgeWeight q ≠ 0 := by
      intro hzero
      have hn := norm_deningerXiHarmonicHodgeWeight q
      rw [hzero, norm_zero] at hn
      norm_num at hn
    have hfst : v.1 = lam * v.1 := by
      have h := congrArg Prod.fst hlam
      simp only [completedXiSameFiberResolvedShear, Prod.smul_fst,
        smul_eq_mul] at h
      exact h
    have hlam1 : lam = 1 := by
      have h1 : lam * v.1 = 1 * v.1 := by rw [← hfst, one_mul]
      exact mul_right_cancel₀ hv h1
    have hsnd :
        v.2 - (K : ℂ) * deningerXiHarmonicHodgeWeight q * v.1 = v.2 := by
      have h := congrArg Prod.snd hlam
      simp only [completedXiSameFiberResolvedShear, Prod.smul_snd,
        smul_eq_mul, hlam1, one_mul] at h
      exact h
    have hzero :
        (K : ℂ) * deningerXiHarmonicHodgeWeight q * v.1 = 0 :=
      sub_eq_self.mp hsnd
    have hKC : (K : ℂ) = 0 := by
      rcases mul_eq_zero.mp hzero with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact h'
        · exact absurd h' hw
      · exact absurd h hv
    exact_mod_cast hKC
  · intro hK
    subst hK
    refine ⟨1, ?_⟩
    simp [completedXiSameFiberResolvedShear]

/-- Existence of a shear-invariant coefficient-faithful line at the retained
rational-adelic atom.  This is the transport-preservation-plus-faithfulness
part of any candidate source selector, with no lift-identification clause. -/
def CCMRationalAdelicPrimeXiInvariantFaithfulLine
    (p : Nat.Primes) (rho : XiDivisorSupport) : Prop :=
  ∃ v : CompletedXiSameFiberHodgePlane, v.1 ≠ 0 ∧
    ∃ lam : ℂ,
      completedXiSameFiberResolvedShear
          (ccmRationalAdelicPrimeXiLeadingZeroCopy rho)
          (ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho) v =
        lam • v

/-- The invariant-faithful-line interface is exactly vanishing of the
Hodge-mate coefficient: the two selector clauses alone already carry the whole
annihilation content, so the lift-identification clause is redundant. -/
theorem ccmRationalAdelicPrimeXiInvariantFaithfulLine_iff_hodgeMateCoefficient_eq_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiInvariantFaithfulLine p rho ↔
      ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho = 0 := by
  constructor
  · rintro ⟨v, hv, hlam⟩
    exact (completedXiSameFiberResolvedShear_eigenvector_iff
      (ccmRationalAdelicPrimeXiLeadingZeroCopy rho)
      (ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho) v hv).mp hlam
  · intro hK
    refine ⟨(1, 0), one_ne_zero, ?_⟩
    exact (completedXiSameFiberResolvedShear_eigenvector_iff
      (ccmRationalAdelicPrimeXiLeadingZeroCopy rho)
      (ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho) (1, 0)
      one_ne_zero).mpr hK

/-- A shear-invariant coefficient-faithful line exists at the retained atom
exactly at critical-line support. -/
theorem ccmRationalAdelicPrimeXiInvariantFaithfulLine_iff_re_eq_half
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiInvariantFaithfulLine p rho ↔
      (rho : ℂ).re = 1 / 2 :=
  (ccmRationalAdelicPrimeXiInvariantFaithfulLine_iff_hodgeMateCoefficient_eq_zero
    p rho).trans
    (ccmRationalAdelicPrimeXiHodgeMateCoefficient_eq_zero_iff_re_eq_half p rho)

/-- Energy-gap invariance: every polarization-preserving comparison, with no
linearity or continuity assumption, transports the same resolved-over-physical
energy excess `K^(2 : ℕ) * normSq c`. -/
theorem completedXiFixedCorona_comparison_energyGap
    (q : XiZeroCopy) (K : ℝ) (c : ℂ)
    (Phi : CompletedXiSameFiberHodgePlane → PrimeDepthBVWoldFixedCoronaPlane)
    (hPhi : ∀ z u : CompletedXiSameFiberHodgePlane,
      primeDepthBVWoldFixedCoronaPolarization (Phi z) (Phi u) =
        completedXiSameFiberHodgePlanePolarization q z u) :
    primeDepthBVWoldFixedCoronaPolarization
        (Phi (completedXiResolvedCoefficientLift q K c))
        (Phi (completedXiResolvedCoefficientLift q K c)) -
      primeDepthBVWoldFixedCoronaPolarization (Phi (c, 0)) (Phi (c, 0)) =
      K ^ (2 : ℕ) * Complex.normSq c := by
  have hphys :
      completedXiSameFiberHodgePlanePolarization q (c, 0) (c, 0) =
        Complex.normSq c := by
    rw [completedXiSameFiberHodgePlanePolarization,
      completedXiSameFiberPolarization_self,
      completedXiSameFiberPolarization_self]
    simp
  rw [hPhi, hPhi, completedXiResolvedCoefficientLift_fixedPolarization,
    hphys, completedXiSameFiberPolarization_self]
  ring

/-- No polarization-preserving comparison identifies the resolved landing with
the physical landing at nonzero shear on a nonzero retained coefficient: the
energy gap is a gauge invariant of the polarization class. -/
theorem completedXiFixedCorona_comparison_separates
    (q : XiZeroCopy) (K : ℝ) (c : ℂ) (hK : K ≠ 0) (hc : c ≠ 0)
    (Phi : CompletedXiSameFiberHodgePlane → PrimeDepthBVWoldFixedCoronaPlane)
    (hPhi : ∀ z u : CompletedXiSameFiberHodgePlane,
      primeDepthBVWoldFixedCoronaPolarization (Phi z) (Phi u) =
        completedXiSameFiberHodgePlanePolarization q z u) :
    Phi (completedXiResolvedCoefficientLift q K c) ≠ Phi (c, 0) := by
  intro heq
  have hgap := completedXiFixedCorona_comparison_energyGap q K c Phi hPhi
  rw [heq, sub_self] at hgap
  exact (mul_ne_zero (pow_ne_zero 2 hK)
    ((Complex.normSq_pos.mpr hc).ne')) hgap.symm

/-- Off critical-line support, the retained atom's resolved and physical
landings stay separated under every polarization-preserving comparison, so
re-choosing the comparison cannot produce the missing annihilation. -/
theorem ccmRationalAdelicPrimeXi_offLine_no_comparison_identifies
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (hoff : (rho : ℂ).re ≠ 1 / 2)
    (Phi : CompletedXiSameFiberHodgePlane → PrimeDepthBVWoldFixedCoronaPlane)
    (hPhi : ∀ z u : CompletedXiSameFiberHodgePlane,
      primeDepthBVWoldFixedCoronaPolarization (Phi z) (Phi u) =
        completedXiSameFiberHodgePlanePolarization
          (ccmRationalAdelicPrimeXiLeadingZeroCopy rho) z u) :
    Phi (completedXiResolvedCoefficientLift
          (ccmRationalAdelicPrimeXiLeadingZeroCopy rho)
          (ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho)
          (iteratedDeriv (xiSupportMultiplicity rho) XiC
            (xiSpectralPointSupport rho))) ≠
      Phi (iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho), 0) :=
  completedXiFixedCorona_comparison_separates
    (ccmRationalAdelicPrimeXiLeadingZeroCopy rho)
    (ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho)
    (iteratedDeriv (xiSupportMultiplicity rho) XiC
      (xiSpectralPointSupport rho))
    (fun h => hoff
      ((ccmRationalAdelicPrimeXiHodgeMateCoefficient_eq_zero_iff_re_eq_half
        p rho).mp h))
    (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)
    Phi hPhi

end

end RHTower

import GaloisForLFunctions.RHTower.XiHurwitzOrientationPositivePairedSource
import GaloisForLFunctions.RHTower.CriticalTraceMomentGerm
import GaloisForLFunctions.RHTower.PrimeArchCentralMomentGerm

/-!
# The real positive-paired boundary kernel is a seam-log Loewner kernel

At real regular points the continued prime--archimedean source trace is real, and the reduced
positive-paired kernel collapses to a single divided difference of the square-descended normalized
germ `G(x²) = -T(x)/x`.

Writing the confluent boundary kernel with its analytic diagonal value, the finite matrices of the
paired source kernel are exactly the positive diagonal congruence `D · L_G · D` of the confluent
Loewner matrices of `G`, with `D = diag (2x_i)`.  Positivity, inertia, rank, and nullity therefore
agree.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## Reality of the source on the real boundary -/

theorem continuedPrimeArchSourceRelativeTrace_ofReal_im {x : ℝ}
    (hx : CCMContinuedCauchyDomain (x : ℂ)) :
    (continuedPrimeArchSourceRelativeTrace ((x : ℝ) : ℂ)).im = 0 := by
  have h := continuedPrimeArchSourceRelativeTrace_conj hx
  rw [Complex.conj_ofReal] at h
  have him := congrArg Complex.im h
  simp only [Complex.conj_im] at him
  linarith

/-- The real value of the continued source at a real regular point. -/
def sourceRealTrace (x : ℝ) : ℝ :=
  (continuedPrimeArchSourceRelativeTrace ((x : ℝ) : ℂ)).re

theorem continuedPrimeArchSourceRelativeTrace_ofReal {x : ℝ}
    (hx : CCMContinuedCauchyDomain (x : ℂ)) :
    continuedPrimeArchSourceRelativeTrace ((x : ℝ) : ℂ) = ((sourceRealTrace x : ℝ) : ℂ) := by
  apply Complex.ext
  · rfl
  · rw [continuedPrimeArchSourceRelativeTrace_ofReal_im hx]
    simp

/-! ## The square-descended normalized germ on the real boundary -/

/-- The square-descended normalized source germ, evaluated through its square root:
`seamLogGermReal x = G (x²) = -T(x)/x`. -/
def seamLogGermReal (x : ℝ) : ℝ := -sourceRealTrace x / x

/-! ## The reduced paired kernel on the real boundary -/

/-- **Off-diagonal boundary value.**  At distinct nonzero real regular points the reduced paired
kernel is the seam-log divided difference. -/
theorem ccmPositivePairedReducedKernel_ofReal {x y : ℝ}
    (hx : CCMContinuedCauchyDomain (x : ℂ)) (hy : CCMContinuedCauchyDomain (y : ℂ))
    (hxy : x ≠ y) (hsum : x + y ≠ 0) :
    ccmPositivePairedReducedKernel ((x : ℝ) : ℂ) ((y : ℝ) : ℂ) =
      4 * (x * sourceRealTrace y - y * sourceRealTrace x) / (x ^ (2 : ℕ) - y ^ (2 : ℕ)) := by
  have hTx := continuedPrimeArchSourceRelativeTrace_ofReal hx
  have hTy := continuedPrimeArchSourceRelativeTrace_ofReal hy
  have hdiff : ((x : ℝ) : ℂ) - ((y : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sub]
    exact_mod_cast sub_ne_zero.mpr hxy
  have hplus : ((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add]
    exact_mod_cast hsum
  have hsq : ((x : ℝ) : ℂ) ^ (2 : ℕ) - ((y : ℝ) : ℂ) ^ (2 : ℕ) ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hplus hdiff
  rw [ccmPositivePairedReducedKernel, Complex.conj_ofReal, hTx, hTy]
  have hcplx :
      (((((sourceRealTrace y : ℝ) : ℂ)) - ((sourceRealTrace x : ℝ) : ℂ)) /
          (((x : ℝ) : ℂ) - ((y : ℝ) : ℂ)) +
        ((((sourceRealTrace y : ℝ) : ℂ)) + ((sourceRealTrace x : ℝ) : ℂ)) /
          (((x : ℝ) : ℂ) + ((y : ℝ) : ℂ))) =
        (((2 * (x * sourceRealTrace y - y * sourceRealTrace x) /
          (x ^ (2 : ℕ) - y ^ (2 : ℕ)) : ℝ)) : ℂ) := by
    push_cast
    field_simp
    ring
  rw [show (starRingEnd ℂ) (((sourceRealTrace y : ℝ) : ℂ)) = ((sourceRealTrace y : ℝ) : ℂ) from
      Complex.conj_ofReal _]
  rw [hcplx]
  simp only [Complex.ofReal_re]
  ring

/-! ## The boundary trace and its seam-log germ -/

/-- The real boundary value of the Xi logarithmic current. -/
def xiBoundaryTrace (x : ℝ) : ℝ := (logDeriv XiC ((x : ℝ) : ℂ)).re

theorem continuedPrimeArchSourceRelativeTrace_eq_logDeriv_XiC_of_domain_xiPositivePairedRealLoewnerSeam
    {z : ℂ} (hzdom : CCMContinuedCauchyDomain z) :
    continuedPrimeArchSourceRelativeTrace z = logDeriv XiC z := by
  rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
    hzdom.1 hzdom.2.1 hzdom.2.2.1]
  symm
  exact logDeriv_XiC_eq_relativeResolventTrace
    (XiC_ne_zero_of_continuedPrimeArch_domain hzdom.1 hzdom.2.1 hzdom.2.2.1)

theorem xiBoundaryTrace_eq_sourceRealTrace {x : ℝ}
    (hx : CCMContinuedCauchyDomain (x : ℂ)) :
    xiBoundaryTrace x = sourceRealTrace x := by
  rw [xiBoundaryTrace, sourceRealTrace,
    continuedPrimeArchSourceRelativeTrace_eq_logDeriv_XiC_of_domain_xiPositivePairedRealLoewnerSeam hx]

/-- The square-descended normalized germ, read through its square root:
`xiBoundarySeamGerm x = G (x²) = -T(x)/x`. -/
def xiBoundarySeamGerm (x : ℝ) : ℝ := -xiBoundaryTrace x / x

/-- The confluent Loewner entry of the seam-log germ in the squared coordinate. -/
def xiBoundaryLoewner (x y : ℝ) : ℝ :=
  if x = y then deriv xiBoundarySeamGerm x / (2 * x)
  else (xiBoundarySeamGerm x - xiBoundarySeamGerm y) / (x ^ (2 : ℕ) - y ^ (2 : ℕ))

/-- The confluent real-boundary paired kernel: the positive diagonal congruence of the seam-log
Loewner kernel. -/
def xiConfluentPairedKernel (x y : ℝ) : ℝ := 4 * x * y * xiBoundaryLoewner x y

/-- **Exact diagonal congruence.**  Every entry of the confluent boundary kernel is the
corresponding Loewner entry conjugated by the positive diagonal `2x`. -/
theorem xiConfluentPairedKernel_eq_congruence (x y : ℝ) :
    xiConfluentPairedKernel x y = (2 * x) * xiBoundaryLoewner x y * (2 * y) := by
  rw [xiConfluentPairedKernel]
  ring

/-- **Off-diagonal identification.**  At distinct nonzero real regular points the reduced paired
source kernel is the confluent boundary kernel. -/
theorem ccmPositivePairedReducedKernel_eq_confluent {x y : ℝ}
    (hx : CCMContinuedCauchyDomain (x : ℂ)) (hy : CCMContinuedCauchyDomain (y : ℂ))
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : x ≠ y) (hsum : x + y ≠ 0) :
    ccmPositivePairedReducedKernel ((x : ℝ) : ℂ) ((y : ℝ) : ℂ) =
      xiConfluentPairedKernel x y := by
  rw [ccmPositivePairedReducedKernel_ofReal hx hy hxy hsum, xiConfluentPairedKernel,
    xiBoundaryLoewner, if_neg hxy, xiBoundarySeamGerm, xiBoundarySeamGerm,
    xiBoundaryTrace_eq_sourceRealTrace hx, xiBoundaryTrace_eq_sourceRealTrace hy]
  have hsq : x ^ (2 : ℕ) - y ^ (2 : ℕ) ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hsum (sub_ne_zero.mpr hxy)
  field_simp
  ring

/-! ## The confluent diagonal -/

theorem differentiableAt_logDeriv_XiC {z : ℂ} (hz : XiC z ≠ 0) :
    DifferentiableAt ℂ (logDeriv XiC) z := by
  have hd : DifferentiableAt ℂ (deriv XiC) z :=
    ((XiC_analytic.deriv) z (Set.mem_univ z)).differentiableAt
  have hf : DifferentiableAt ℂ XiC z := XiC_differentiable z
  have hrw : logDeriv XiC = fun w : ℂ => deriv XiC w / XiC w := rfl
  rw [hrw]
  exact hd.div hf hz

theorem hasDerivAt_xiBoundaryTrace {x : ℝ} (hx : XiC ((x : ℝ) : ℂ) ≠ 0) :
    HasDerivAt xiBoundaryTrace ((deriv (logDeriv XiC) ((x : ℝ) : ℂ)).re) x := by
  have hcx : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  have hL : HasDerivAt (logDeriv XiC) (deriv (logDeriv XiC) ((x : ℝ) : ℂ)) ((x : ℝ) : ℂ) :=
    (differentiableAt_logDeriv_XiC hx).hasDerivAt
  have hcomp : HasDerivAt (fun t : ℝ => logDeriv XiC ((t : ℝ) : ℂ))
      (deriv (logDeriv XiC) ((x : ℝ) : ℂ)) x := by
    have hraw := hL.scomp x hcx
    simpa only [Function.comp_apply, smul_eq_mul, one_mul] using! hraw
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hcomp

theorem deriv_xiBoundaryTrace {x : ℝ} (hx : XiC ((x : ℝ) : ℂ) ≠ 0) :
    deriv xiBoundaryTrace x = (deriv (logDeriv XiC) ((x : ℝ) : ℂ)).re :=
  (hasDerivAt_xiBoundaryTrace hx).deriv

theorem hasDerivAt_xiBoundarySeamGerm {x : ℝ} (hx0 : x ≠ 0)
    (hx : XiC ((x : ℝ) : ℂ) ≠ 0) :
    HasDerivAt xiBoundarySeamGerm
      ((-(deriv xiBoundaryTrace x) * x + xiBoundaryTrace x) / x ^ (2 : ℕ)) x := by
  have hT := hasDerivAt_xiBoundaryTrace hx
  rw [← deriv_xiBoundaryTrace hx] at hT
  have hid : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
  have hdiv := (hT.neg).div hid hx0
  have hform : xiBoundarySeamGerm = fun t : ℝ => -xiBoundaryTrace t / t := rfl
  rw [hform]
  have hnum : (-(deriv xiBoundaryTrace x) * x + xiBoundaryTrace x) / x ^ (2 : ℕ) =
      (-(deriv xiBoundaryTrace x) * x - (-xiBoundaryTrace x) * 1) / x ^ (2 : ℕ) := by ring
  rw [hnum]
  exact hdiv

/-- **The confluent diagonal.**  The boundary value of the paired kernel on the diagonal is the
analytic regularization `2(-T'(x) + T(x)/x)`. -/
theorem xiConfluentPairedKernel_self {x : ℝ} (hx0 : x ≠ 0)
    (hx : XiC ((x : ℝ) : ℂ) ≠ 0) :
    xiConfluentPairedKernel x x =
      2 * (-(deriv xiBoundaryTrace x) + xiBoundaryTrace x / x) := by
  have hderiv := (hasDerivAt_xiBoundarySeamGerm hx0 hx).deriv
  rw [xiConfluentPairedKernel, xiBoundaryLoewner, if_pos rfl, hderiv]
  field_simp
  ring

/-! ## Finite diagonal congruence -/

/-- The seam-log Loewner entry is symmetric. -/
theorem xiBoundaryLoewner_symm (x y : ℝ) :
    xiBoundaryLoewner x y = xiBoundaryLoewner y x := by
  rw [xiBoundaryLoewner, xiBoundaryLoewner]
  by_cases h : x = y
  · rw [if_pos h, if_pos h.symm, h]
  · rw [if_neg h, if_neg (Ne.symm h)]
    rcases eq_or_ne (x ^ (2 : ℕ) - y ^ (2 : ℕ)) 0 with h0 | h0
    · have h0' : y ^ (2 : ℕ) - x ^ (2 : ℕ) = 0 := by linarith
      rw [h0, h0']
      simp
    · have h0' : y ^ (2 : ℕ) - x ^ (2 : ℕ) ≠ 0 := by
        intro hcon
        exact h0 (by linarith)
      field_simp
      ring

/-- **Finite congruence of quadratic forms.**  The paired confluent kernel and the seam-log Loewner
kernel differ by the positive diagonal scaling `2x`. -/
theorem xiConfluentPairedQuadratic_eq {n : ℕ} (x c : Fin n → ℝ) :
    ∑ i, ∑ j, c i * xiConfluentPairedKernel (x i) (x j) * c j =
      ∑ i, ∑ j, (2 * x i * c i) * xiBoundaryLoewner (x i) (x j) * (2 * x j * c j) := by
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [xiConfluentPairedKernel]
  ring

/-- **Congruence transfers positivity in both directions.** -/
theorem xiConfluentPairedQuadratic_nonneg_iff {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, x i ≠ 0) :
    (∀ c : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, c i * xiConfluentPairedKernel (x i) (x j) * c j) ↔
      (∀ d : Fin n → ℝ, 0 ≤ ∑ i, ∑ j,
        d i * xiBoundaryLoewner (x i) (x j) * d j) := by
  constructor
  · intro h d
    have hc := h (fun i => d i / (2 * x i))
    rw [xiConfluentPairedQuadratic_eq] at hc
    refine le_of_le_of_eq hc (Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_)
    have hxi : x i ≠ 0 := hx i
    have hxj : x j ≠ 0 := hx j
    field_simp
  · intro h c
    rw [xiConfluentPairedQuadratic_eq]
    exact h (fun i => 2 * x i * c i)

/-! ## Identification with the normalized trace-moment germ -/

/-- The real boundary seam germ is the real part of the normalized trace-moment germ. -/
theorem xiBoundarySeamGerm_eq_normalizedTraceMomentGerm {x : ℝ} (hx0 : x ≠ 0)
    (hx : CCMContinuedCauchyDomain (x : ℂ)) :
    ((xiBoundarySeamGerm x : ℝ) : ℂ) =
      normalizedTraceMomentGerm continuedPrimeArchSourceRelativeTrace ((x : ℝ) : ℂ) := by
  have hxc : ((x : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hx0
  rw [normalizedTraceMomentGerm, dslope_of_ne _ hxc, slope_def_module,
    continuedPrimeArchSourceRelativeTrace_zero]
  rw [xiBoundarySeamGerm, xiBoundaryTrace_eq_sourceRealTrace hx, sourceRealTrace,
    continuedPrimeArchSourceRelativeTrace_ofReal hx]
  push_cast
  simp only [sub_zero, smul_eq_mul, Complex.ofReal_re]
  field_simp

/-! ## The totalized diagonal is not the confluent boundary value -/

/-- The totalized value of the reduced kernel at a real diagonal node drops the divided-difference
block, so it is not the analytic boundary regularization. -/
theorem ccmPositivePairedReducedKernel_self_ofReal {x : ℝ} (hx0 : x ≠ 0)
    (hx : CCMContinuedCauchyDomain (x : ℂ)) :
    ccmPositivePairedReducedKernel ((x : ℝ) : ℂ) ((x : ℝ) : ℂ) =
      2 * (sourceRealTrace x / x) := by
  have hTx := continuedPrimeArchSourceRelativeTrace_ofReal hx
  have hxc : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx0
  rw [ccmPositivePairedReducedKernel, Complex.conj_ofReal, hTx,
    show (starRingEnd ℂ) (((sourceRealTrace x : ℝ) : ℂ)) = ((sourceRealTrace x : ℝ) : ℂ) from
      Complex.conj_ofReal _]
  have hzero : (((sourceRealTrace x : ℝ) : ℂ) - ((sourceRealTrace x : ℝ) : ℂ)) /
      (((x : ℝ) : ℂ) - ((x : ℝ) : ℂ)) = 0 := by simp
  rw [hzero, zero_add]
  have hval : (((sourceRealTrace x : ℝ) : ℂ) + ((sourceRealTrace x : ℝ) : ℂ)) /
      (((x : ℝ) : ℂ) + ((x : ℝ) : ℂ)) = ((sourceRealTrace x / x : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [hval]
  simp

/-- **The confluent correction.**  The analytic boundary diagonal differs from the totalized
diagonal by exactly twice the boundary derivative. -/
theorem xiConfluentPairedKernel_self_sub_totalized {x : ℝ} (hx0 : x ≠ 0)
    (hx : CCMContinuedCauchyDomain (x : ℂ))
    (hXi : XiC ((x : ℝ) : ℂ) ≠ 0) :
    xiConfluentPairedKernel x x -
        ccmPositivePairedReducedKernel ((x : ℝ) : ℂ) ((x : ℝ) : ℂ) =
      -2 * deriv xiBoundaryTrace x := by
  rw [xiConfluentPairedKernel_self hx0 hXi,
    ccmPositivePairedReducedKernel_self_ofReal hx0 hx,
    xiBoundaryTrace_eq_sourceRealTrace hx]
  ring

end

end RHTower

import GaloisForLFunctions.RHTower.CompleteResolutionLabelBlindObserverRigidity
import GaloisForLFunctions.RHTower.PrimeGammaBocksteinReesCoronaComparison
import GaloisForLFunctions.RHTower.RiemannSourceForcedHorizontalVanishingFrontier

/-!
# Source-zero to horizontal carrier

This module constructs a pre-scalar carrier of the horizontal Xi-divisor class.  For every
multiplicity copy of every Xi zero it retains two complementary pieces of source data:

* the complete-resolution displacement between the two functional-equation orientations;
* the full ordinary-prime family of signed Gamma Bockstein coefficients.

The first component is an actual nonzero zero-mass source class off the critical line, while the
second orients that class at every prime and lands coefficient-faithfully in the physical
Rees--corona quotient.  Neither prime labels nor divisor-multiplicity copies are summed before the
construction.  The two components have exactly the same zero radical and both reverse sign under
`rho ↦ 1 - conj rho`.

All results are unconditional.  Global annihilation of the carrier is proved equivalent to RH;
it is not assumed or proved here.
-/

open Complex

namespace RHTower

noncomputable section

/-- Critical-line reflection on the open critical strip used by the complete source resolution. -/
def completeResolutionOpenCriticalStripReflection
    (s : CompleteResolutionOpenCriticalStrip) : CompleteResolutionOpenCriticalStrip :=
  ⟨1 - star s.1, by
    have hstarRe : (star s.1).re = s.1.re := by simp
    simp only [sub_re, one_re]
    rw [hstarRe]
    constructor <;> linarith [s.2.1, s.2.2]⟩

/-- Strip reflection is an involution before any source scalarization. -/
@[simp] theorem completeResolutionOpenCriticalStripReflection_involutive
    (s : CompleteResolutionOpenCriticalStrip) :
    completeResolutionOpenCriticalStripReflection
        (completeResolutionOpenCriticalStripReflection s) = s := by
  apply Subtype.ext
  simp [completeResolutionOpenCriticalStripReflection]

/-- Forget only the upper strip bound, retaining the same source point. -/
def completeResolutionOpenCriticalStripToRightHalfPlane
    (s : CompleteResolutionOpenCriticalStrip) : CompleteResolutionRightHalfPlane :=
  ⟨s.1, s.2.1⟩

/-- Reflection displacement is literally the oriented edge between the two strip points in the
complete source embedding. -/
theorem completeResolutionReflectionSourceDisplacement_eq_orientedEdge
    (K : ℕ) (s : CompleteResolutionOpenCriticalStrip) :
    completeResolutionReflectionSourceDisplacement K s =
      completeResolutionSourceEmbedding K
          (completeResolutionOpenCriticalStripToRightHalfPlane s) -
        completeResolutionSourceEmbedding K
          (completeResolutionOpenCriticalStripToRightHalfPlane
            (completeResolutionOpenCriticalStripReflection s)) := by
  rw [completeResolutionReflectionSourceDisplacement]
  congr 2

/-- The complete-resolution source displacement is reflection-odd. -/
@[simp] theorem completeResolutionReflectionSourceDisplacement_reflection
    (K : ℕ) (s : CompleteResolutionOpenCriticalStrip) :
    completeResolutionReflectionSourceDisplacement K
        (completeResolutionOpenCriticalStripReflection s) =
      -completeResolutionReflectionSourceDisplacement K s := by
  rw [completeResolutionReflectionSourceDisplacement_eq_orientedEdge,
    completeResolutionReflectionSourceDisplacement_eq_orientedEdge]
  rw [completeResolutionOpenCriticalStripReflection_involutive]
  abel

/-- Signed Gamma Bockstein coefficient is odd in horizontal grade. -/
@[simp] theorem primeGammaCofinalBocksteinCoefficient_neg
    (t : ℝ) (p : Nat.Primes) :
    primeGammaCofinalBocksteinCoefficient (-t) p =
      -primeGammaCofinalBocksteinCoefficient t p := by
  simp [primeGammaCofinalBocksteinCoefficient]

/-- Positive horizontal grade has negative Bockstein orientation at every ordinary prime. -/
theorem primeGammaCofinalBocksteinCoefficient_neg_of_pos
    {t : ℝ} (ht : 0 < t) (p : Nat.Primes) :
    primeGammaCofinalBocksteinCoefficient t p < 0 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hdensity : 0 < primeActivationOccupancyFisherDensity p := by
    rw [primeActivationOccupancyFisherDensity_eq]
    positivity
  have hpow : (p : ℝ) ^ (-t) < (p : ℝ) ^ t :=
    Real.strictMono_rpow_of_base_gt_one hp1 (by linarith)
  rw [primeGammaCofinalBocksteinCoefficient,
    primeActivationOccupancyFisherTwist,
    primeActivationOccupancyFisherTwist]
  exact sub_neg.mpr (mul_lt_mul_of_pos_right hpow hdensity)

/-- Negative horizontal grade has positive Bockstein orientation at every ordinary prime. -/
theorem primeGammaCofinalBocksteinCoefficient_pos_of_neg
    {t : ℝ} (ht : t < 0) (p : Nat.Primes) :
    0 < primeGammaCofinalBocksteinCoefficient t p := by
  have hneg : 0 < -t := by linarith
  have h := primeGammaCofinalBocksteinCoefficient_neg_of_pos hneg p
  rw [primeGammaCofinalBocksteinCoefficient_neg] at h
  linarith

/-- An actual Xi-divisor multiplicity copy, viewed as a complete-resolution strip point. -/
def xiZeroCopyCompleteResolutionStripPoint
    (q : XiZeroCopy) : CompleteResolutionOpenCriticalStrip :=
  ⟨(q.1 : ℂ), xi_divisor_support_re_mem_open_unit q.1⟩

/-- Multiplicity-copy reflection agrees with reflection of its complete-resolution strip point. -/
@[simp] theorem xiZeroCopyCompleteResolutionStripPoint_reflection
    (q : XiZeroCopy) :
    xiZeroCopyCompleteResolutionStripPoint (xiZeroCopyLineConjEquiv q) =
      completeResolutionOpenCriticalStripReflection
        (xiZeroCopyCompleteResolutionStripPoint q) := by
  apply Subtype.ext
  rfl

/-- Complete-resolution part of the source-zero horizontal carrier. -/
def sourceZeroHorizontalResolutionCarrier
    (K : ℕ) (q : XiZeroCopy) : CompleteResolutionSourceSpace :=
  completeResolutionReflectionSourceDisplacement K
    (xiZeroCopyCompleteResolutionStripPoint q)

/-- Prime-labelled signed part of the source-zero horizontal carrier. -/
def sourceZeroHorizontalPrimeCarrier
    (q : XiZeroCopy) (p : Nat.Primes) : ℝ :=
  primeGammaCofinalBocksteinCoefficient
    (primeDepthBVWoldXiCenteredRate q.1) p

/-- Nonlinear cofinal reader of the complete source tail.  Unlike a bounded label-blind linear
consumer, this retains the ordered source coordinates before taking their adjacent-ratio limit. -/
def sourceZeroHorizontalTailLog (q : XiZeroCopy) : ℝ :=
  Real.log ‖shellTransferCharacter (q.1 : ℂ)‖

/-- The tail log is read by the normalized adjacent-coordinate ratios of the actual complete
source vector, for every starting shell `K`. -/
theorem completeResolutionSourceTail_reads_sourceZeroHorizontalTailLog
    (K : ℕ) (q : XiZeroCopy) :
    Filter.Tendsto
      (fun n : ℕ =>
        completeResolutionNormalizedSourceTailRatio K n
          (completeResolutionOpenCriticalStripToRightHalfPlane
            (xiZeroCopyCompleteResolutionStripPoint q)))
      Filter.atTop (nhds (shellTransferCharacter (q.1 : ℂ))) ∧
    sourceZeroHorizontalTailLog q =
      (1 / 2 - (q.1 : ℂ).re) * Real.log 2 := by
  simpa [sourceZeroHorizontalTailLog,
    completeResolutionOpenCriticalStripToRightHalfPlane,
    xiZeroCopyCompleteResolutionStripPoint] using
    completeResolutionNormalizedSourceTailRatio_orientation K
      (completeResolutionOpenCriticalStripToRightHalfPlane
        (xiZeroCopyCompleteResolutionStripPoint q))

/-- The ordered cofinal source reader itself retains both orientations. -/
@[simp] theorem sourceZeroHorizontalTailLog_reflection
    (K : ℕ) (q : XiZeroCopy) :
    sourceZeroHorizontalTailLog (xiZeroCopyLineConjEquiv q) =
      -sourceZeroHorizontalTailLog q := by
  rw [(completeResolutionSourceTail_reads_sourceZeroHorizontalTailLog K
      (xiZeroCopyLineConjEquiv q)).2,
    (completeResolutionSourceTail_reads_sourceZeroHorizontalTailLog K q).2]
  change (1 / 2 - (1 - star (q.1 : ℂ)).re) * Real.log 2 =
    -((1 / 2 - (q.1 : ℂ).re) * Real.log 2)
  simp
  ring

/-- Cofinal source-tail orientation vanishes exactly at reflection fixed points. -/
theorem sourceZeroHorizontalTailLog_eq_zero_iff
    (K : ℕ) (q : XiZeroCopy) :
    sourceZeroHorizontalTailLog q = 0 ↔ (q.1 : ℂ).re = 1 / 2 := by
  rw [(completeResolutionSourceTail_reads_sourceZeroHorizontalTailLog K q).2]
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  constructor
  · intro h
    have hfactor : 1 / 2 - (q.1 : ℂ).re = 0 :=
      (mul_eq_zero.mp h).resolve_right hlog
    linarith
  · intro h
    rw [h]
    norm_num

/-- Exact Frankenstein relation: the horizontal grade used by every prime Bockstein is recovered
from the nonlinear cofinal tail of the complete source vector. -/
theorem primeDepthBVWoldXiCenteredRate_eq_sourceTailLog
    (K : ℕ) (q : XiZeroCopy) :
    primeDepthBVWoldXiCenteredRate q.1 =
      -2 * sourceZeroHorizontalTailLog q / Real.log 2 := by
  have hlog : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  rw [(completeResolutionSourceTail_reads_sourceZeroHorizontalTailLog K q).2,
    primeDepthBVWoldXiCenteredRate]
  field_simp
  ring

/-- Every retained prime label is therefore a source-tail Bockstein, not a scalar chosen after
inspection of the zero. -/
theorem sourceZeroHorizontalPrimeCarrier_eq_sourceTailBockstein
    (K : ℕ) (q : XiZeroCopy) (p : Nat.Primes) :
    sourceZeroHorizontalPrimeCarrier q p =
      primeGammaCofinalBocksteinCoefficient
        (-2 * sourceZeroHorizontalTailLog q / Real.log 2) p := by
  rw [sourceZeroHorizontalPrimeCarrier,
    primeDepthBVWoldXiCenteredRate_eq_sourceTailLog K q]

/-- Pre-scalar target retaining the complete source labels and every ordinary-prime label. -/
abbrev SourceZeroHorizontalCarrierSpace :=
  CompleteResolutionSourceSpace × (Nat.Primes → ℝ)

/-- Per-multiplicity-copy carrier before bounded scalarization. -/
def sourceZeroHorizontalCarrierAt
    (K : ℕ) (q : XiZeroCopy) : SourceZeroHorizontalCarrierSpace :=
  (sourceZeroHorizontalResolutionCarrier K q,
    sourceZeroHorizontalPrimeCarrier q)

/-- Global carrier indexed by the multiplicity-exact Xi divisor. -/
def sourceZeroHorizontalCarrier
    (K : ℕ) : XiZeroCopy → SourceZeroHorizontalCarrierSpace :=
  sourceZeroHorizontalCarrierAt K

/-- The complete-resolution component reverses under the line-conjugate orientation. -/
@[simp] theorem sourceZeroHorizontalResolutionCarrier_reflection
    (K : ℕ) (q : XiZeroCopy) :
    sourceZeroHorizontalResolutionCarrier K (xiZeroCopyLineConjEquiv q) =
      -sourceZeroHorizontalResolutionCarrier K q := by
  rw [sourceZeroHorizontalResolutionCarrier,
    sourceZeroHorizontalResolutionCarrier,
    xiZeroCopyCompleteResolutionStripPoint_reflection,
    completeResolutionReflectionSourceDisplacement_reflection]

/-- Every prime-labelled component reverses under the line-conjugate orientation. -/
@[simp] theorem sourceZeroHorizontalPrimeCarrier_reflection
    (q : XiZeroCopy) (p : Nat.Primes) :
    sourceZeroHorizontalPrimeCarrier (xiZeroCopyLineConjEquiv q) p =
      -sourceZeroHorizontalPrimeCarrier q p := by
  rw [sourceZeroHorizontalPrimeCarrier,
    sourceZeroHorizontalPrimeCarrier]
  change primeGammaCofinalBocksteinCoefficient
      (primeDepthBVWoldXiCenteredRate (xiZeroLineConjEquiv q.1)) p = _
  rw [primeDepthBVWoldXiCenteredRate_reflection,
    primeGammaCofinalBocksteinCoefficient_neg]

/-- The full pre-scalar carrier preserves both reflection orientations by negation. -/
@[simp] theorem sourceZeroHorizontalCarrierAt_reflection
    (K : ℕ) (q : XiZeroCopy) :
    sourceZeroHorizontalCarrierAt K (xiZeroCopyLineConjEquiv q) =
      -sourceZeroHorizontalCarrierAt K q := by
  apply Prod.ext
  · exact sourceZeroHorizontalResolutionCarrier_reflection K q
  · funext p
    exact sourceZeroHorizontalPrimeCarrier_reflection q p

/-- Resolution component vanishes exactly on the critical line. -/
theorem sourceZeroHorizontalResolutionCarrier_eq_zero_iff
    (K : ℕ) (q : XiZeroCopy) :
    sourceZeroHorizontalResolutionCarrier K q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  exact completeResolutionReflectionSourceDisplacement_eq_zero_iff K
    (xiZeroCopyCompleteResolutionStripPoint q)

/-- Every retained prime component has the same exact critical-line radical. -/
theorem sourceZeroHorizontalPrimeCarrier_eq_zero_iff
    (q : XiZeroCopy) (p : Nat.Primes) :
    sourceZeroHorizontalPrimeCarrier q p = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [sourceZeroHorizontalPrimeCarrier,
    primeGammaCofinalBocksteinCoefficient_eq_zero_iff,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- New cross-corpus bridge: complete source displacement and each prime Bockstein have the same
zero radical, without scalarizing either family. -/
theorem sourceZeroHorizontalResolutionCarrier_eq_zero_iff_primeCarrier
    (K : ℕ) (q : XiZeroCopy) (p : Nat.Primes) :
    sourceZeroHorizontalResolutionCarrier K q = 0 ↔
      sourceZeroHorizontalPrimeCarrier q p = 0 := by
  rw [sourceZeroHorizontalResolutionCarrier_eq_zero_iff,
    sourceZeroHorizontalPrimeCarrier_eq_zero_iff]

/-- The full carrier vanishes exactly on the critical line. -/
theorem sourceZeroHorizontalCarrierAt_eq_zero_iff
    (K : ℕ) (q : XiZeroCopy) :
    sourceZeroHorizontalCarrierAt K q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    apply (sourceZeroHorizontalResolutionCarrier_eq_zero_iff K q).1
    exact congrArg Prod.fst h
  · intro hline
    apply Prod.ext
    · exact (sourceZeroHorizontalResolutionCarrier_eq_zero_iff K q).2 hline
    · funext p
      exact (sourceZeroHorizontalPrimeCarrier_eq_zero_iff q p).2 hline

/-- The new carrier and the retained Gamma/co-Poisson horizontal class have the same fibrewise
zero radical. -/
theorem sourceZeroHorizontalCarrierAt_eq_zero_iff_horizontalDefect
    (K : ℕ) (q : XiZeroCopy) :
    sourceZeroHorizontalCarrierAt K q = 0 ↔
      riemannSourceGammaCoPoissonHorizontalDefect q.1 = 0 := by
  rw [sourceZeroHorizontalCarrierAt_eq_zero_iff,
    riemannSourceGammaCoPoissonHorizontalDefect_eq_zero_iff]

/-- Off line, the source component is a genuine nonzero zero-mass class and every retained prime
component remains nonzero before scalarization. -/
theorem sourceZeroHorizontalCarrierAt_offLine_beforeScalarization
    (K : ℕ) (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    sourceZeroHorizontalResolutionCarrier K q ≠ 0 ∧
      sourceFusionCodiagonal (sourceZeroHorizontalResolutionCarrier K q) = 0 ∧
      ∀ p : Nat.Primes, sourceZeroHorizontalPrimeCarrier q p ≠ 0 := by
  refine ⟨(not_congr
      (sourceZeroHorizontalResolutionCarrier_eq_zero_iff K q)).mpr hoff, ?_, ?_⟩
  · exact sourceFusionCodiagonal_completeResolutionReflectionSourceDisplacement K
      (xiZeroCopyCompleteResolutionStripPoint q)
  · intro p
    exact (not_congr
      (sourceZeroHorizontalPrimeCarrier_eq_zero_iff q p)).mpr hoff

/-- Right-half zeros have negative orientation at every retained prime label. -/
theorem sourceZeroHorizontalPrimeCarrier_neg_of_rightHalf
    (q : XiZeroCopy) (hhalf : 1 / 2 < (q.1 : ℂ).re) (p : Nat.Primes) :
    sourceZeroHorizontalPrimeCarrier q p < 0 := by
  apply primeGammaCofinalBocksteinCoefficient_neg_of_pos
  rw [primeDepthBVWoldXiCenteredRate]
  linarith

/-- Left-half zeros have positive orientation at every retained prime label. -/
theorem sourceZeroHorizontalPrimeCarrier_pos_of_leftHalf
    (q : XiZeroCopy) (hhalf : (q.1 : ℂ).re < 1 / 2) (p : Nat.Primes) :
    0 < sourceZeroHorizontalPrimeCarrier q p := by
  apply primeGammaCofinalBocksteinCoefficient_pos_of_neg
  rw [primeDepthBVWoldXiCenteredRate]
  linarith

/-- The cofinal source-tail reader and every ordinary-prime Bockstein give the same orientation:
their product is strictly positive exactly off the critical line.  This is the retained
horizontal orientation before any bounded label-blind scalarization. -/
theorem sourceZeroHorizontalTailLog_mul_primeCarrier_pos_iff
    (K : ℕ) (q : XiZeroCopy) (p : Nat.Primes) :
    0 < sourceZeroHorizontalTailLog q *
        sourceZeroHorizontalPrimeCarrier q p ↔
      (q.1 : ℂ).re ≠ 1 / 2 := by
  constructor
  · intro hpos hline
    have hzero := (sourceZeroHorizontalPrimeCarrier_eq_zero_iff q p).2 hline
    rw [hzero, mul_zero] at hpos
    exact lt_irrefl 0 hpos
  · intro hoff
    rcases lt_or_gt_of_ne hoff with hleft | hright
    · apply mul_pos
      · rw [(completeResolutionSourceTail_reads_sourceZeroHorizontalTailLog K q).2]
        exact mul_pos (sub_pos.mpr hleft) (Real.log_pos (by norm_num))
      · exact sourceZeroHorizontalPrimeCarrier_pos_of_leftHalf q hleft p
    · apply mul_pos_of_neg_of_neg
      · rw [(completeResolutionSourceTail_reads_sourceZeroHorizontalTailLog K q).2]
        exact mul_neg_of_neg_of_pos (sub_neg.mpr hright)
          (Real.log_pos (by norm_num))
      · exact sourceZeroHorizontalPrimeCarrier_neg_of_rightHalf q hright p

/-- The prime-labelled carrier transports the actual leading Xi jet, including its divisor and
multiplicity provenance, into the physical Rees--corona quotient. -/
theorem sourceZeroHorizontalPrimeCarrier_realification_eq_physicalCorona
    (q : XiZeroCopy) (p : Nat.Primes) :
    sourceZeroHorizontalPrimeCarrier q p •
        primeDepthBVWoldReesCoronaRealification
          (ccmRationalAdelicPrimeXiReesCoronaCoefficient p q.1
            (ccmRationalAdelicPrimeRelativeClass p)) =
      -primeGammaBocksteinReesCoronaFactor
          (primeDepthBVWoldXiCenteredRate q.1) p •
        primeDepthBVWoldReesCoronaQuotient
          (primeDepthBVWoldXiCenteredRate q.1)
          (ccmRationalAdelicPrimeRelativeXiCellZero p)
          (ccmRationalAdelicPrimeRelativeXiCellOne p)
          (ccmRationalAdelicPrimeXiPhysicalReesCoronaComparison p q.1
            (ccmRationalAdelicPrimeRelativeClass p)) := by
  exact ccmRationalAdelicPrimeXiGammaBockstein_realification_eq_physicalCorona p q.1

/-- Global annihilation of the multiplicity-exact, prime-labelled carrier. -/
def SourceZeroHorizontalCarrierVanishes (K : ℕ) : Prop :=
  sourceZeroHorizontalCarrier K = 0

/-- The constructed source-zero carrier has no hidden slack: global annihilation is exactly the
existing source-forced horizontal vanishing frontier. -/
theorem sourceZeroHorizontalCarrierVanishes_iff_sourceForcedHorizontalVanishing
    (K : ℕ) :
    SourceZeroHorizontalCarrierVanishes K ↔
      XiSourceForcedHorizontalVanishing := by
  constructor
  · intro h rho
    let q : XiZeroCopy :=
      ⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩
    apply (sourceZeroHorizontalCarrierAt_eq_zero_iff_horizontalDefect K q).1
    exact congrFun h q
  · intro h
    funext q
    apply (sourceZeroHorizontalCarrierAt_eq_zero_iff_horizontalDefect K q).2
    exact h q.1

/-- Exact endpoint audit: annihilating the constructed carrier is equivalent to RH. -/
theorem sourceZeroHorizontalCarrierVanishes_iff_riemannHypothesis
    (K : ℕ) :
    SourceZeroHorizontalCarrierVanishes K ↔ RiemannHypothesis := by
  rw [sourceZeroHorizontalCarrierVanishes_iff_sourceForcedHorizontalVanishing,
    xiSourceForcedHorizontalVanishing_iff_riemannHypothesis]

end

end RHTower

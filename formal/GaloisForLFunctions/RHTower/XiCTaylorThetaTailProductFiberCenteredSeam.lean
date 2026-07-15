import GaloisForLFunctions.RHTower.XiCTaylorThetaTailArithmeticPhaseSeam
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberHermitianCollapse

/-!
# Concrete common-centre seam on a theta product fibre

The positive-half-line endpoint prevents the arithmetic translates of the first theta-density
atom from sharing one tail.  Splitting every tail at a common nonnegative centre `c` gives an
exact signed interval block from `c` to `log n`; the interval is oriented, so the same formula
handles the two opposite divisor displacements without a case split.

This module keeps the value block, derivative block, and their self-current together.  It then
combines that concrete window current with the unavoidable Hermitian-polarization defect.  The
result is the exact untruncated product-fibre bridge needed before adjoining the already explicit
finite cosine--sine top edge.  No sign or norm estimate is used here.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- A tail based at `a` is a tail based at `c` minus the oriented block from `c` to `a`.
The orientation convention makes this valid in both orders. -/
theorem thetaCuspTailSecondDensityAtomOnePhaseTail_eq_center_sub_block
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) {z : ℂ} (hz : 0 ≤ z.im) :
    thetaCuspTailSecondDensityAtomOnePhaseTail a z =
      thetaCuspTailSecondDensityAtomOnePhaseTail c z -
        thetaCuspTailSecondDensityAtomOnePhaseBlock c a z := by
  have h0 := integrableOn_thetaCuspTailSecondDensityAtom_one_mul_phase hz
  have haInt := h0.mono_set (Ioi_subset_Ioi ha)
  have hcInt := h0.mono_set (Ioi_subset_Ioi hc)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hcInt haInt
  unfold thetaCuspTailSecondDensityAtomOnePhaseTail
    thetaCuspTailSecondDensityAtomOnePhaseBlock
  linear_combination hsplit

/-- Spectral-derivative companion of the oriented common-centre block identity. -/
theorem thetaCuspTailSecondDensityAtomOnePhaseTailDerivative_eq_center_sub_block
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) {z : ℂ} (hz : 0 ≤ z.im) :
    thetaCuspTailSecondDensityAtomOnePhaseTailDerivative a z =
      thetaCuspTailSecondDensityAtomOnePhaseTailDerivative c z -
        thetaCuspTailSecondDensityAtomOnePhaseBlockDerivative c a z := by
  have h0 := integrableOn_thetaCuspTailSecondDensityAtom_one_mul_phaseDerivative hz
  have haInt := h0.mono_set (Ioi_subset_Ioi ha)
  have hcInt := h0.mono_set (Ioi_subset_Ioi hc)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hcInt haInt
  unfold thetaCuspTailSecondDensityAtomOnePhaseTailDerivative
    thetaCuspTailSecondDensityAtomOnePhaseBlockDerivative
  linear_combination hsplit

/-- Value defect produced by sweeping the endpoint from a common centre `c` to the logarithmic
endpoint of the zero-based positive atom `n`. -/
def thetaProductFiberCenteredPhaseWindowValueDefect
    (c : ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  -thetaCriticalTranslateCoefficient (n + 1) z *
    thetaCuspTailSecondDensityAtomOnePhaseBlock
      c (Real.log (n + 1 : ℕ)) z

/-- Derivative defect of the same swept window.  The logarithmic phase drift remains attached to
the block instead of being estimated separately. -/
def thetaProductFiberCenteredPhaseWindowDerivativeDefect
    (c : ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  thetaCriticalTranslateCoefficient (n + 1) z *
    (-thetaCuspTailSecondDensityAtomOnePhaseBlockDerivative
        c (Real.log (n + 1 : ℕ)) z +
      ((Real.log (n + 1 : ℕ) : ℝ) : ℂ) * I *
        thetaCuspTailSecondDensityAtomOnePhaseBlock
          c (Real.log (n + 1 : ℕ)) z)

/-- The actual arithmetic phase value is its common-centre translate model plus the concrete
oriented endpoint block. -/
theorem thetaCuspTailSecondDensityAtomPhase_eq_commonCenterModel_add_window
    (n : ℕ) {c : ℝ} (hc : 0 ≤ c) {z : ℂ} (hz : 0 ≤ z.im) :
    thetaCuspTailSecondDensityAtomPhase (n + 1) z =
      thetaProductFiberCommonTailModelValue z
          (thetaCuspTailSecondDensityAtomOnePhaseTail c z) n +
        thetaProductFiberCenteredPhaseWindowValueDefect c z n := by
  rw [thetaCuspTailSecondDensityAtomPhase_eq_centeredTail (Nat.succ_pos n)]
  rw [thetaCuspTailSecondDensityAtomOnePhaseTail_eq_center_sub_block
    (Real.log_nonneg (by exact_mod_cast Nat.succ_pos n)) hc hz]
  unfold thetaProductFiberCommonTailModelValue
    thetaProductFiberCenteredPhaseWindowValueDefect
    thetaCriticalTranslateCoefficient spectralTranslationPhase
  ring

/-- Derivative companion of the concrete common-centre decomposition. -/
theorem thetaCuspTailSecondDensityAtomPhaseDerivative_eq_commonCenterModel_add_window
    (n : ℕ) {c : ℝ} (hc : 0 ≤ c) {z : ℂ} (hz : 0 ≤ z.im) :
    thetaCuspTailSecondDensityAtomPhaseDerivative (n + 1) z =
      thetaProductFiberCommonTailModelDerivative z
          (thetaCuspTailSecondDensityAtomOnePhaseTail c z)
          (thetaCuspTailSecondDensityAtomOnePhaseTailDerivative c z) n +
        thetaProductFiberCenteredPhaseWindowDerivativeDefect c z n := by
  rw [thetaCuspTailSecondDensityAtomPhaseDerivative_eq_centeredTail
    (Nat.succ_pos n) z hz]
  rw [thetaCuspTailSecondDensityAtomOnePhaseTail_eq_center_sub_block
      (Real.log_nonneg (by exact_mod_cast Nat.succ_pos n)) hc hz,
    thetaCuspTailSecondDensityAtomOnePhaseTailDerivative_eq_center_sub_block
      (Real.log_nonneg (by exact_mod_cast Nat.succ_pos n)) hc hz]
  unfold thetaProductFiberCommonTailModelDerivative
    thetaProductFiberCenteredPhaseWindowDerivativeDefect
    thetaCriticalTranslateCoefficient spectralTranslationPhase
  ring

/-- Exact untruncated phase current of one fixed positive product fibre. -/
def thetaProductFiberActualPhaseCurrent
    (k : ℕ) (z : ℂ) : ℝ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    (thetaCuspTailSecondDensityAtomPhaseDerivative (q.1 + 1) z *
      (starRingEnd ℂ)
        (thetaCuspTailSecondDensityAtomPhase (q.2 + 1) z)).im

/-- The complete concrete window current: the common-model/window mixed currents and the window
self-current are retained in one expression. -/
def thetaProductFiberCenteredPhaseWindowJointCurrent
    (k : ℕ) (c : ℝ) (z : ℂ) : ℝ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    ((thetaProductFiberCommonTailModelDerivative z
          (thetaCuspTailSecondDensityAtomOnePhaseTail c z)
          (thetaCuspTailSecondDensityAtomOnePhaseTailDerivative c z) q.1 *
        (starRingEnd ℂ)
          (thetaProductFiberCenteredPhaseWindowValueDefect c z q.2)).im +
      (thetaProductFiberCenteredPhaseWindowDerivativeDefect c z q.1 *
        (starRingEnd ℂ)
          (thetaProductFiberCommonTailModelValue z
            (thetaCuspTailSecondDensityAtomOnePhaseTail c z) q.2)).im +
      (thetaProductFiberCenteredPhaseWindowDerivativeDefect c z q.1 *
        (starRingEnd ℂ)
          (thetaProductFiberCenteredPhaseWindowValueDefect c z q.2)).im)

/-- The concrete corrected seam at centre `c`: the algebraic Hermitian-polarization residue and
all three oriented endpoint-window currents are one object. -/
def thetaProductFiberCenteredCorrectedPhaseSeamCurrent
    (k : ℕ) (c : ℝ) (z : ℂ) : ℝ :=
  xiCTaylorThetaTailCoreProductFiberPolarizationDefectCurrent k z
      (thetaCuspTailSecondDensityAtomOnePhaseTail c z)
      (thetaCuspTailSecondDensityAtomOnePhaseTailDerivative c z) +
    thetaProductFiberCenteredPhaseWindowJointCurrent k c z

/-- Exact common-tail plus concrete-window decomposition of the actual untruncated phase fibre. -/
theorem thetaProductFiberActualPhaseCurrent_eq_commonTail_add_centeredWindow
    (k : ℕ) {c : ℝ} (hc : 0 ≤ c) {z : ℂ} (hz : 0 ≤ z.im) :
    thetaProductFiberActualPhaseCurrent k z =
      xiCTaylorThetaTailCoreProductFiberCommonTailBaseCurrent k z
          (thetaCuspTailSecondDensityAtomOnePhaseTail c z)
          (thetaCuspTailSecondDensityAtomOnePhaseTailDerivative c z) +
        thetaProductFiberCenteredPhaseWindowJointCurrent k c z := by
  unfold thetaProductFiberActualPhaseCurrent
    xiCTaylorThetaTailCoreProductFiberCommonTailBaseCurrent
    thetaProductFiberCenteredPhaseWindowJointCurrent
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [thetaCuspTailSecondDensityAtomPhaseDerivative_eq_commonCenterModel_add_window
      q.1 hc hz,
    thetaCuspTailSecondDensityAtomPhase_eq_commonCenterModel_add_window q.2 hc hz,
    map_add]
  simp only [add_mul, mul_add, Complex.add_im]
  ring

/-- **Concrete corrected product-fibre bridge.**  At any nonnegative common centre, the actual
untruncated phase current is the favorable coherent prime-oriented base plus the unavoidable
Hermitian-polarization defect and the complete oriented endpoint-window current. -/
theorem thetaProductFiberActualPhaseCurrent_eq_coherentBase_add_polarization_add_centeredWindow
    (k : ℕ) {c : ℝ} (hc : 0 ≤ c) {z : ℂ} (hz : 0 ≤ z.im) :
    thetaProductFiberActualPhaseCurrent k z =
      xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent k z
          (thetaCuspTailSecondDensityAtomOnePhaseTail c z) +
        (xiCTaylorThetaTailCoreProductFiberPolarizationDefectCurrent k z
            (thetaCuspTailSecondDensityAtomOnePhaseTail c z)
            (thetaCuspTailSecondDensityAtomOnePhaseTailDerivative c z) +
          thetaProductFiberCenteredPhaseWindowJointCurrent k c z) := by
  rw [thetaProductFiberActualPhaseCurrent_eq_commonTail_add_centeredWindow k hc hz]
  unfold xiCTaylorThetaTailCoreProductFiberPolarizationDefectCurrent
  ring

/-- Named form of the concrete bridge. -/
theorem thetaProductFiberActualPhaseCurrent_eq_coherentBase_add_correctedCenteredSeam
    (k : ℕ) {c : ℝ} (hc : 0 ≤ c) {z : ℂ} (hz : 0 ≤ z.im) :
    thetaProductFiberActualPhaseCurrent k z =
      xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent k z
          (thetaCuspTailSecondDensityAtomOnePhaseTail c z) +
        thetaProductFiberCenteredCorrectedPhaseSeamCurrent k c z := by
  rw [thetaProductFiberActualPhaseCurrent_eq_coherentBase_add_polarization_add_centeredWindow
    k hc hz]
  rfl

/-- The concrete corrected seam is an upper majorant of the actual phase fibre.  Thus extracting
the favorable coherent phase does not make the anisotropic upper-bound problem smaller. -/
theorem thetaProductFiberActualPhaseCurrent_le_correctedCenteredSeam
    (k : ℕ) {c : ℝ} (hc : 0 ≤ c) {z : ℂ} (hz : 0 < z.im) :
    thetaProductFiberActualPhaseCurrent k z ≤
      thetaProductFiberCenteredCorrectedPhaseSeamCurrent k c z := by
  rw [thetaProductFiberActualPhaseCurrent_eq_coherentBase_add_correctedCenteredSeam
    k hc hz.le]
  linarith [xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent_nonpos_all k hz
    (thetaCuspTailSecondDensityAtomOnePhaseTail c z)]

/-- The majorization is strict on every nontrivial fibre whenever the common-centre tail does not
vanish. -/
theorem thetaProductFiberActualPhaseCurrent_lt_correctedCenteredSeam
    {k : ℕ} (hk : 1 < k) {c : ℝ} (hc : 0 ≤ c) {z : ℂ} (hz : 0 < z.im)
    (hTail : thetaCuspTailSecondDensityAtomOnePhaseTail c z ≠ 0) :
    thetaProductFiberActualPhaseCurrent k z <
      thetaProductFiberCenteredCorrectedPhaseSeamCurrent k c z := by
  have hbase :
      xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent k z
          (thetaCuspTailSecondDensityAtomOnePhaseTail c z) < 0 := by
    unfold xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent
    exact mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr hTail)
      (thetaProductFiberCenteredPhase_current_lt_zero hk hz)
  rw [thetaProductFiberActualPhaseCurrent_eq_coherentBase_add_correctedCenteredSeam
    k hc hz.le]
  linarith

/-- Canonical specialization at the product-fibre centre `log k / 2`. -/
theorem thetaProductFiberActualPhaseCurrent_eq_canonicalCoherentBase_add_jointSeam
    {k : ℕ} (hk : 0 < k) {z : ℂ} (hz : 0 ≤ z.im) :
    thetaProductFiberActualPhaseCurrent k z =
      xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent k z
          (thetaCuspTailSecondDensityAtomOnePhaseTail (Real.log k / 2) z) +
        (xiCTaylorThetaTailCoreProductFiberPolarizationDefectCurrent k z
            (thetaCuspTailSecondDensityAtomOnePhaseTail (Real.log k / 2) z)
            (thetaCuspTailSecondDensityAtomOnePhaseTailDerivative (Real.log k / 2) z) +
          thetaProductFiberCenteredPhaseWindowJointCurrent
            k (Real.log k / 2) z) := by
  exact
    thetaProductFiberActualPhaseCurrent_eq_coherentBase_add_polarization_add_centeredWindow
      k (div_nonneg (Real.log_nonneg (by exact_mod_cast hk)) (by norm_num)) hz

end

end RHTower

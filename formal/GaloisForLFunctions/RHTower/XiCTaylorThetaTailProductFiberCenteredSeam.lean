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

/-! ## Exact boundary current of the canonical common tail -/

/-- Mass of the first canonical density atom beyond a nonnegative common centre. -/
def thetaCuspTailSecondDensityAtomOneTailMass (c : ℝ) : ℝ :=
  ∫ u : ℝ in Ioi c, thetaCuspTailSecondDensityAtom 1 u

/-- First moment of the same tail. -/
def thetaCuspTailSecondDensityAtomOneTailFirstMoment (c : ℝ) : ℝ :=
  ∫ u : ℝ in Ioi c, u * thetaCuspTailSecondDensityAtom 1 u

/-- First moment measured from the common centre. -/
def thetaCuspTailSecondDensityAtomOneCenteredTailFirstMoment (c : ℝ) : ℝ :=
  ∫ u : ℝ in Ioi c, (u - c) * thetaCuspTailSecondDensityAtom 1 u

lemma integrableOn_thetaCuspTailSecondDensityAtomOne_tailMass
    {c : ℝ} (hc : 0 ≤ c) :
    IntegrableOn (thetaCuspTailSecondDensityAtom 1) (Ioi c) := by
  have h := (integrableOn_thetaCuspTailSecondDensityAtom_mul_complexPower 0 0).re
  have hcsub : Ioi c ⊆ Ioi 0 := Ioi_subset_Ioi hc
  have h' := h.mono_measure (Measure.restrict_mono hcsub le_rfl)
  change Integrable (fun x : ℝ => thetaCuspTailSecondDensityAtom 1 x)
    (volume.restrict (Ioi c))
  apply h'.congr
  filter_upwards with x
  simp only [Nat.zero_add, pow_zero, mul_one]
  change ((thetaCuspTailSecondDensityAtom 1 x : ℂ).re) =
    thetaCuspTailSecondDensityAtom 1 x
  rfl

lemma integrableOn_thetaCuspTailSecondDensityAtomOne_tailFirstMoment
    {c : ℝ} (hc : 0 ≤ c) :
    IntegrableOn
      (fun u : ℝ => u * thetaCuspTailSecondDensityAtom 1 u) (Ioi c) := by
  have huC := (integrableOn_thetaCuspTailSecondDensityAtom_mul_complexPower 0 1).re
  have huC' := huC.mono_measure
    (Measure.restrict_mono (Ioi_subset_Ioi hc) le_rfl)
  change Integrable
    (fun u : ℝ => u * thetaCuspTailSecondDensityAtom 1 u)
      (volume.restrict (Ioi c))
  apply huC'.congr
  filter_upwards with u
  simp only [pow_one]
  rw [← Complex.ofReal_mul]
  change thetaCuspTailSecondDensityAtom 1 u * u =
    u * thetaCuspTailSecondDensityAtom 1 u
  ring

lemma integrableOn_thetaCuspTailSecondDensityAtomOne_centeredTailFirstMoment
    {c : ℝ} (hc : 0 ≤ c) :
    IntegrableOn
      (fun u : ℝ => (u - c) * thetaCuspTailSecondDensityAtom 1 u) (Ioi c) := by
  have h0 := integrableOn_thetaCuspTailSecondDensityAtomOne_tailMass hc
  have hu := integrableOn_thetaCuspTailSecondDensityAtomOne_tailFirstMoment hc
  convert hu.sub (h0.const_mul c) using 1
  funext u
  simp only [Pi.sub_apply]
  ring

/-- Every nonnegative common centre leaves strictly positive first-atom tail mass. -/
theorem thetaCuspTailSecondDensityAtomOneTailMass_pos
    {c : ℝ} (hc : 0 ≤ c) :
    0 < thetaCuspTailSecondDensityAtomOneTailMass c := by
  let f : ℝ → ℝ := thetaCuspTailSecondDensityAtom 1
  have hf : Integrable f (volume.restrict (Ioi c)) :=
    integrableOn_thetaCuspTailSecondDensityAtomOne_tailMass hc
  have hf0 : 0 ≤ᵐ[volume.restrict (Ioi c)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (thetaCuspTailSecondDensityAtom_pos Nat.zero_lt_one
      (le_trans hc hu.le)).le
  rw [thetaCuspTailSecondDensityAtomOneTailMass,
    integral_pos_iff_support_of_nonneg_ae hf0 hf]
  have hsub : Ioi c ⊆ Function.support f := by
    intro u hu
    exact (thetaCuspTailSecondDensityAtom_pos Nat.zero_lt_one
      (le_trans hc hu.le)).ne'
  have hmono : (volume.restrict (Ioi c)) (Ioi c) ≤
      (volume.restrict (Ioi c)) (Function.support f) := measure_mono hsub
  have hpos : 0 < (volume.restrict (Ioi c)) (Ioi c) := by
    simp
  exact lt_of_lt_of_le hpos hmono

/-- The first moment measured from a nonnegative common centre is strictly positive. -/
theorem thetaCuspTailSecondDensityAtomOneCenteredTailFirstMoment_pos
    {c : ℝ} (hc : 0 ≤ c) :
    0 < thetaCuspTailSecondDensityAtomOneCenteredTailFirstMoment c := by
  let f : ℝ → ℝ := fun u =>
    (u - c) * thetaCuspTailSecondDensityAtom 1 u
  have hf : Integrable f (volume.restrict (Ioi c)) :=
    integrableOn_thetaCuspTailSecondDensityAtomOne_centeredTailFirstMoment hc
  have hf0 : 0 ≤ᵐ[volume.restrict (Ioi c)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (sub_nonneg.mpr hu.le)
      (thetaCuspTailSecondDensityAtom_pos Nat.zero_lt_one
        (le_trans hc hu.le)).le
  rw [thetaCuspTailSecondDensityAtomOneCenteredTailFirstMoment,
    integral_pos_iff_support_of_nonneg_ae hf0 hf]
  have hsub : Ioi c ⊆ Function.support f := by
    intro u hu
    exact mul_ne_zero (sub_ne_zero.mpr hu.ne')
      (thetaCuspTailSecondDensityAtom_pos Nat.zero_lt_one
        (le_trans hc hu.le)).ne'
  have hmono : (volume.restrict (Ioi c)) (Ioi c) ≤
      (volume.restrict (Ioi c)) (Function.support f) := measure_mono hsub
  have hpos : 0 < (volume.restrict (Ioi c)) (Ioi c) := by
    simp
  exact lt_of_lt_of_le hpos hmono

lemma thetaCuspTailSecondDensityAtomOneCenteredTailFirstMoment_eq
    {c : ℝ} (hc : 0 ≤ c) :
    thetaCuspTailSecondDensityAtomOneCenteredTailFirstMoment c =
      thetaCuspTailSecondDensityAtomOneTailFirstMoment c -
        c * thetaCuspTailSecondDensityAtomOneTailMass c := by
  have hu := integrableOn_thetaCuspTailSecondDensityAtomOne_tailFirstMoment hc
  have h0 := integrableOn_thetaCuspTailSecondDensityAtomOne_tailMass hc
  unfold thetaCuspTailSecondDensityAtomOneCenteredTailFirstMoment
    thetaCuspTailSecondDensityAtomOneTailFirstMoment
    thetaCuspTailSecondDensityAtomOneTailMass
  rw [show (fun u : ℝ =>
      (u - c) * thetaCuspTailSecondDensityAtom 1 u) =
      (fun u : ℝ =>
        u * thetaCuspTailSecondDensityAtom 1 u -
          c * thetaCuspTailSecondDensityAtom 1 u) by
    funext u
    ring]
  rw [integral_sub hu (h0.const_mul c), integral_const_mul]

lemma thetaCuspTailSecondDensityAtomOnePhaseTail_zero (c : ℝ) :
    thetaCuspTailSecondDensityAtomOnePhaseTail c 0 =
      (thetaCuspTailSecondDensityAtomOneTailMass c : ℂ) := by
  unfold thetaCuspTailSecondDensityAtomOnePhaseTail
    thetaCuspTailSecondDensityAtomOneTailMass spectralTranslationPhase
  simp only [mul_zero, Complex.exp_zero, mul_one]
  exact integral_ofReal
    (X := ℝ) (μ := volume.restrict (Ioi c)) (𝕜 := ℂ)

lemma thetaCuspTailSecondDensityAtomOnePhaseTailDerivative_zero (c : ℝ) :
    thetaCuspTailSecondDensityAtomOnePhaseTailDerivative c 0 =
      I * (thetaCuspTailSecondDensityAtomOneTailFirstMoment c : ℂ) := by
  unfold thetaCuspTailSecondDensityAtomOnePhaseTailDerivative
    thetaCuspTailSecondDensityAtomOneTailFirstMoment spectralTranslationPhase
  simp only [mul_zero, Complex.exp_zero, mul_one]
  rw [show (fun u : ℝ =>
      (thetaCuspTailSecondDensityAtom 1 u : ℂ) * ((u : ℂ) * I)) =
      fun u : ℝ => I * ((u * thetaCuspTailSecondDensityAtom 1 u : ℝ) : ℂ) by
    funext u
    push_cast
    ring]
  rw [integral_const_mul]
  congr 1
  exact integral_ofReal
    (X := ℝ) (μ := volume.restrict (Ioi c)) (𝕜 := ℂ)

/-- At the real spectral origin the exact canonical common-tail bracket is the product of its
tail mass and its first moment measured from the common centre. -/
theorem thetaCuspTailSecondDensityAtomOneCenteredTail_boundaryCurrent_eq
    {c : ℝ} (hc : 0 ≤ c) :
    (thetaCuspTailSecondDensityAtomOnePhaseTailDerivative c 0 *
        (starRingEnd ℂ)
          (thetaCuspTailSecondDensityAtomOnePhaseTail c 0)).im -
      c * Complex.normSq
        (thetaCuspTailSecondDensityAtomOnePhaseTail c 0) =
      thetaCuspTailSecondDensityAtomOneTailMass c *
        thetaCuspTailSecondDensityAtomOneCenteredTailFirstMoment c := by
  rw [thetaCuspTailSecondDensityAtomOnePhaseTail_zero,
    thetaCuspTailSecondDensityAtomOnePhaseTailDerivative_zero,
    thetaCuspTailSecondDensityAtomOneCenteredTailFirstMoment_eq hc]
  simp only [Complex.conj_ofReal, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, add_zero,
    Complex.normSq_apply]
  ring

/-- Consequently the canonical common-tail bracket has strictly positive boundary orientation;
the Hermitian/coherent sign mismatch is present for the exact density, not only for an abstract
unit-tail model. -/
theorem thetaCuspTailSecondDensityAtomOneCenteredTail_boundaryCurrent_pos
    {c : ℝ} (hc : 0 ≤ c) :
    0 <
      (thetaCuspTailSecondDensityAtomOnePhaseTailDerivative c 0 *
          (starRingEnd ℂ)
            (thetaCuspTailSecondDensityAtomOnePhaseTail c 0)).im -
        c * Complex.normSq
          (thetaCuspTailSecondDensityAtomOnePhaseTail c 0) := by
  rw [thetaCuspTailSecondDensityAtomOneCenteredTail_boundaryCurrent_eq hc]
  exact mul_pos (thetaCuspTailSecondDensityAtomOneTailMass_pos hc)
    (thetaCuspTailSecondDensityAtomOneCenteredTailFirstMoment_pos hc)

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

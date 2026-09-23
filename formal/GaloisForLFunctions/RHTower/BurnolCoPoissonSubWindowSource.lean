import GaloisForLFunctions.RHTower.BurnolCoPoissonWindowIndicator
import GaloisForLFunctions.RHTower.BurnolCoPoissonIndicatorVector
import GaloisForLFunctions.RHTower.BurnolCoPoissonMellinNonvanishing

/-!
# Sub-window co-Poisson sources and Sonine vectors

Every multiplicative sub-window `[c,d]` gives a co-Poisson pair: the reciprocal function on `[c,d]`
and the indicator of the inverted window `[1/d,1/c]`.  Both carry the full analytic data, so the
`L^(2 : ℕ)` intertwining applies and the pair produces a vector of the extended Sonine space at aperture
`min (c, 1/d)`.

The Mellin transform of that vector is `(d^(-w) - c^(-w)) zeta(w)/w` up to the archimedean factor,
so for `c < d` it witnesses nonvanishing at every point of the strip where zeta does not vanish ---
a two-parameter family of witnesses at every aperture.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

variable {c d : ℝ}

theorem norm_le_of_decayProfile' {f : ℝ → ℂ} {C : ℝ}
    (h : ∀ t : ℝ, ‖f t‖ ≤ C * (1 + |t|)⁻¹) (t : ℝ) : ‖f t‖ ≤ C := by
  have hC : 0 ≤ C := by
    have h0 := h 0
    simp only [abs_zero, add_zero, inv_one, mul_one] at h0
    exact le_trans (norm_nonneg _) h0
  refine (h t).trans ?_
  have hden : (1 : ℝ) ≤ 1 + |t| := by
    have habs := abs_nonneg t
    linarith
  have hinv : (1 + |t|)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hden
  calc C * (1 + |t|)⁻¹ ≤ C * 1 := mul_le_mul_of_nonneg_left hinv hC
    _ = C := mul_one C

theorem coPoissonReciprocalSeed_subWindow_eq (hc : 0 < c) (hcd : c ≤ d) :
    coPoissonReciprocalSeed (coPoissonSubWindowSeed c d) = coPoissonWindowIndicatorSeed d⁻¹ c⁻¹ :=
  funext (coPoissonReciprocalSeed_coPoissonSubWindowSeed hc hcd)

/-- The aperture attached to a sub-window. -/
def subWindowAperture (c d : ℝ) : ℝ := min c d⁻¹

theorem subWindowAperture_pos (hc : 0 < c) (hcd : c ≤ d) : 0 < subWindowAperture c d :=
  lt_min hc (inv_pos.mpr (lt_of_lt_of_le hc hcd))

theorem inv_le_inv_of_window (hc : 0 < c) (hcd : c ≤ d) : d⁻¹ ≤ c⁻¹ := by
  rw [inv_le_inv₀ (lt_of_lt_of_le hc hcd) hc]
  exact hcd

theorem support_subWindow_symmetric (hc : 0 < c) (hcd : c ≤ d) :
    Function.support (coPoissonSubWindowSeed c d) ⊆
      Icc (subWindowAperture c d) (subWindowAperture c d)⁻¹ :=
  support_coPoissonSubWindowSeed_symmetric hc hcd

theorem support_reciprocal_subWindow_symmetric (hc : 0 < c) (hcd : c ≤ d) :
    Function.support (coPoissonReciprocalSeed (coPoissonSubWindowSeed c d)) ⊆
      Icc (subWindowAperture c d) (subWindowAperture c d)⁻¹ := by
  have hdinv : (0 : ℝ) < d⁻¹ := inv_pos.mpr (lt_of_lt_of_le hc hcd)
  rw [coPoissonReciprocalSeed_subWindow_eq hc hcd]
  have h := support_coPoissonWindowIndicatorSeed_symmetric hdinv (inv_le_inv_of_window hc hcd)
  rw [inv_inv] at h
  rw [subWindowAperture, min_comm]
  exact h

theorem integrable_reciprocal_subWindow (hc : 0 < c) (hcd : c ≤ d) :
    Integrable (coPoissonReciprocalSeed (coPoissonSubWindowSeed c d)) := by
  rw [coPoissonReciprocalSeed_subWindow_eq hc hcd]
  exact integrable_coPoissonWindowIndicatorSeed _ _

theorem measurable_reciprocal_subWindow_coPoisson (hc : 0 < c) (hcd : c ≤ d) :
    Measurable (burnolCoPoissonRightSum (coPoissonReciprocalSeed (coPoissonSubWindowSeed c d))) := by
  rw [coPoissonReciprocalSeed_subWindow_eq hc hcd]
  exact measurable_burnolCoPoissonRightSum_coPoissonWindowIndicatorSeed
    (inv_pos.mpr (lt_of_lt_of_le hc hcd)) (inv_le_inv_of_window hc hcd)

theorem memLp_reciprocal_subWindow (hc : 0 < c) (hcd : c ≤ d) :
    MemLp (burnolCoPoissonRightSum (coPoissonReciprocalSeed (coPoissonSubWindowSeed c d)))
      2 volume := by
  rw [coPoissonReciprocalSeed_subWindow_eq hc hcd]
  exact memLp_two_burnolCoPoissonRightSum_coPoissonWindowIndicatorSeed
    (inv_pos.mpr (lt_of_lt_of_le hc hcd)) (inv_le_inv_of_window hc hcd)

theorem star_reciprocal_subWindow_coPoisson (hc : 0 < c) (hcd : c ≤ d) (t : ℝ) :
    (starRingEnd ℂ)
        (burnolCoPoissonRightSum (coPoissonReciprocalSeed (coPoissonSubWindowSeed c d)) t) =
      burnolCoPoissonRightSum (coPoissonReciprocalSeed (coPoissonSubWindowSeed c d)) t := by
  rw [coPoissonReciprocalSeed_subWindow_eq hc hcd]
  exact star_burnolCoPoissonRightSum_coPoissonWindowIndicatorSeed
    (inv_pos.mpr (lt_of_lt_of_le hc hcd)) (inv_le_inv_of_window hc hcd) t

theorem norm_reciprocal_subWindow_coPoisson_le (hc : 0 < c) (hcd : c ≤ d) :
    ∀ t : ℝ,
      ‖burnolCoPoissonRightSum (coPoissonReciprocalSeed (coPoissonSubWindowSeed c d)) t‖ ≤
        8 * (d⁻¹ + c⁻¹) +
          (max (2 * c⁻¹) 1 / d⁻¹ + (Real.log c⁻¹ - Real.log d⁻¹)) * (1 + max (2 * c⁻¹) 1) := by
  rw [coPoissonReciprocalSeed_subWindow_eq hc hcd]
  exact norm_le_of_decayProfile'
    (norm_burnolCoPoissonRightSum_coPoissonWindowIndicatorSeed_le_profile
      (inv_pos.mpr (lt_of_lt_of_le hc hcd)) (inv_le_inv_of_window hc hcd))

/-- **The intertwining for a sub-window pair.** -/
theorem fourierUnitary_coPoissonSubWindowVector (hc : 0 < c) (hcd : c ≤ d) :
    fourierUnitary ((memLp_two_burnolCoPoissonRightSum_coPoissonSubWindowSeed hc hcd).toLp _) =
      (memLp_reciprocal_subWindow hc hcd).toLp _ :=
  fourierUnitary_coPoissonVector (subWindowAperture_pos hc hcd)
    (integrable_coPoissonSubWindowSeed hc) (support_subWindow_symmetric hc hcd)
    (integrable_reciprocal_subWindow hc hcd) (support_reciprocal_subWindow_symmetric hc hcd)
    (measurable_burnolCoPoissonRightSum_coPoissonSubWindowSeed hc hcd)
    (norm_le_of_decayProfile'
      (norm_burnolCoPoissonRightSum_coPoissonSubWindowSeed_le_profile hc hcd))
    (measurable_reciprocal_subWindow_coPoisson hc hcd)
    (norm_reciprocal_subWindow_coPoisson_le hc hcd)
    (star_burnolCoPoissonRightSum_coPoissonSubWindowSeed hc hcd)
    (star_reciprocal_subWindow_coPoisson hc hcd)
    (memLp_two_burnolCoPoissonRightSum_coPoissonSubWindowSeed hc hcd)
    (memLp_reciprocal_subWindow hc hcd)


/-! ## The sub-window Sonine vector -/

/-- The sub-window co-Poisson vector inside the even carrier. -/
def coPoissonSubWindowEven (hc : 0 < c) (hcd : c ≤ d) : evenSubspace :=
  ⟨(memLp_two_burnolCoPoissonRightSum_coPoissonSubWindowSeed hc hcd).toLp _,
    memLp_toLp_mem_evenSubspace _ (burnolCoPoissonRightSum_even (coPoissonSubWindowSeed c d))⟩

theorem coPoissonSubWindowEven_coeFn (hc : 0 < c) (hcd : c ≤ d) :
    (((coPoissonSubWindowEven hc hcd : evenSubspace) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      burnolCoPoissonRightSum (coPoissonSubWindowSeed c d) :=
  (memLp_two_burnolCoPoissonRightSum_coPoissonSubWindowSeed hc hcd).coeFn_toLp

theorem soninHeadConstant_coPoissonSubWindowEven (hc : 0 < c) (hcd : c ≤ d) :
    SoninHeadConstant (subWindowAperture c d)
      (((coPoissonSubWindowEven hc hcd : evenSubspace) : SoninL2) : ℝ → ℂ) := by
  obtain ⟨k, hk⟩ := soninHeadConstant_burnolCoPoissonRightSum (support_subWindow_symmetric hc hcd)
  refine ⟨k, ?_⟩
  filter_upwards [ae_restrict_of_ae (coPoissonSubWindowEven_coeFn hc hcd), hk] with t h1 h2
  rw [h1, h2]

theorem coeFn_soninCosineUnitary_coPoissonSubWindowEven (hc : 0 < c) (hcd : c ≤ d) :
    ((((soninCosineUnitary (coPoissonSubWindowEven hc hcd) : evenSubspace)) : SoninL2) :
        ℝ → ℂ) =ᵐ[volume]
      burnolCoPoissonRightSum (coPoissonReciprocalSeed (coPoissonSubWindowSeed c d)) := by
  have hvector :
      ((soninCosineUnitary (coPoissonSubWindowEven hc hcd) : evenSubspace) : SoninL2) =
        (memLp_reciprocal_subWindow hc hcd).toLp _ := by
    change fourierUnitary
        ((memLp_two_burnolCoPoissonRightSum_coPoissonSubWindowSeed hc hcd).toLp _ : SoninL2) = _
    exact fourierUnitary_coPoissonSubWindowVector hc hcd
  rw [hvector]
  exact (memLp_reciprocal_subWindow hc hcd).coeFn_toLp

theorem soninHeadConstant_cosine_coPoissonSubWindowEven (hc : 0 < c) (hcd : c ≤ d) :
    SoninHeadConstant (subWindowAperture c d)
      (((soninCosineUnitary (coPoissonSubWindowEven hc hcd) : evenSubspace) : SoninL2) :
        ℝ → ℂ) := by
  obtain ⟨k, hk⟩ :=
    soninHeadConstant_burnolCoPoissonRightSum (support_reciprocal_subWindow_symmetric hc hcd)
  refine ⟨k, ?_⟩
  filter_upwards [ae_restrict_of_ae (coeFn_soninCosineUnitary_coPoissonSubWindowEven hc hcd), hk]
    with t h1 h2
  rw [h1, h2]

/-- **The sub-window Sonine vector.** -/
def coPoissonSubWindowSonin (hc : 0 < c) (hcd : c ≤ d) :
    soninExtendedSpace (subWindowAperture c d) :=
  ⟨coPoissonSubWindowEven hc hcd,
    mem_soninExtendedSpace.mpr ⟨soninHeadConstant_coPoissonSubWindowEven hc hcd,
      soninHeadConstant_cosine_coPoissonSubWindowEven hc hcd⟩⟩

/-- **A sub-window co-Poisson source.** -/
def coPoissonSubWindowSource (hc : 0 < c) (hcd : c ≤ d) :
    BurnolCoPoissonSource (subWindowAperture c d) where
  seed := coPoissonSubWindowSeed c d
  seed_integrable := integrable_coPoissonSubWindowSeed hc
  seed_support := support_subWindow_symmetric hc hcd
  vector := coPoissonSubWindowSonin hc hcd
  vector_eq_sum := coPoissonSubWindowEven_coeFn hc hcd


/-! ## The Mellin evaluation and the witness -/

/-- **The completed Mellin evaluation of a sub-window Sonine vector.** -/
theorem soninMellinEvaluation_coPoissonSubWindowSonin (hc : 0 < c) (hcd : c ≤ d)
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    soninMellinEvaluation w
        (((coPoissonSubWindowSonin hc hcd :
          soninExtendedSpace (subWindowAperture c d)) : evenSubspace) : SoninL2) =
      mellinCompletionFactor w *
        ((((d : ℝ) : ℂ) ^ (-w) - ((c : ℝ) : ℂ) ^ (-w)) * (-(riemannZeta w / w))) := by
  have hint : (∫ t in Set.Ioi (0 : ℝ),
      ((((coPoissonSubWindowSonin hc hcd :
        soninExtendedSpace (subWindowAperture c d)) : evenSubspace) : SoninL2) : ℝ → ℂ) t *
        soninMellinKernel w t) =
      ∫ t in Set.Ioi (0 : ℝ),
        burnolCoPoissonRightSum (coPoissonSubWindowSeed c d) t * (t : ℂ) ^ (-w) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (coPoissonSubWindowEven_coeFn hc hcd)] with t ht
    rw [soninMellinKernel]
    exact congrArg (fun z : ℂ => z * (t : ℂ) ^ (-w)) ht
  rw [soninMellinEvaluation, hint, integral_Ioi_burnolCoPoisson_subWindow_cpow hc hcd hw0 hw1]

/-- **The sub-window factor never vanishes.**  Distinct window ends give distinct moduli off the
imaginary axis. -/
theorem subWindowFactor_ne_zero (hc : 0 < c) (hcd : c < d) {w : ℂ} (hw : 0 < w.re) :
    ((d : ℝ) : ℂ) ^ (-w) - ((c : ℝ) : ℂ) ^ (-w) ≠ 0 := by
  have hd : (0 : ℝ) < d := lt_trans hc hcd
  intro h
  have heq : ((d : ℝ) : ℂ) ^ (-w) = ((c : ℝ) : ℂ) ^ (-w) := by
    linear_combination h
  have hnorm : ‖((d : ℝ) : ℂ) ^ (-w)‖ = ‖((c : ℝ) : ℂ) ^ (-w)‖ := by rw [heq]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hd, Complex.norm_cpow_eq_rpow_re_of_pos hc,
    Complex.neg_re] at hnorm
  have hbase : c ^ w.re < d ^ w.re := Real.rpow_lt_rpow hc.le hcd hw
  have hcpow : (0 : ℝ) < c ^ w.re := Real.rpow_pos_of_pos hc _
  have hdpow : (0 : ℝ) < d ^ w.re := Real.rpow_pos_of_pos hd _
  rw [Real.rpow_neg hd.le, Real.rpow_neg hc.le] at hnorm
  have hinv : (d ^ w.re)⁻¹ < (c ^ w.re)⁻¹ := by
    rw [inv_lt_inv₀ hdpow hcpow]
    exact hbase
  rw [hnorm] at hinv
  exact lt_irrefl _ hinv

/-- **A two-parameter family of witnesses.**  For `c < d` the sub-window Sonine vector has
nonvanishing completed Mellin evaluation at every point of the strip where zeta does not vanish, so
the evaluation vector is nonzero at every aperture below `min (c, 1/d)`. -/
theorem burnolExtendedSoninEvaluationVector_ne_zero_of_subWindow
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hz : riemannZeta w ≠ 0)
    (hc : 0 < c) (hcd : c < d) {a : ℝ} (ha : 0 < a) (hab : a ≤ subWindowAperture c d) :
    burnolExtendedSoninEvaluationVector w a hlo hhi ha ≠ 0 := by
  have hw0 : (0 : ℝ) < w.re := by linarith
  have hwne : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw0
    exact lt_irrefl 0 hw0
  refine burnolExtendedSoninEvaluationVector_ne_zero_of_witness hlo hhi ha
    (subWindowAperture_pos hc hcd.le) hab (coPoissonSubWindowSonin hc hcd.le) ?_
  rw [soninMellinEvaluation_coPoissonSubWindowSonin hc hcd.le hw0 hhi]
  refine mul_ne_zero (mellinCompletionFactor_ne_zero hw0) (mul_ne_zero
    (subWindowFactor_ne_zero hc hcd hw0) ?_)
  simpa using div_ne_zero hz hwne


/-! ## The dichotomy for the whole family -/

/-- **Each sub-window witness is exactly as good as the nonvanishing of zeta.** -/
theorem soninMellinEvaluation_coPoissonSubWindowSonin_ne_zero_iff (hc : 0 < c) (hcd : c < d)
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    soninMellinEvaluation w
        (((coPoissonSubWindowSonin hc hcd.le :
          soninExtendedSpace (subWindowAperture c d)) : evenSubspace) : SoninL2) ≠ 0 ↔
      riemannZeta w ≠ 0 := by
  have hwne : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw0
    exact lt_irrefl 0 hw0
  rw [soninMellinEvaluation_coPoissonSubWindowSonin hc hcd.le hw0 hw1]
  constructor
  · intro h hz
    exact h (by rw [hz]; simp)
  · intro hz
    refine mul_ne_zero (mellinCompletionFactor_ne_zero hw0) (mul_ne_zero
      (subWindowFactor_ne_zero hc hcd hw0) ?_)
    simpa using div_ne_zero hz hwne

/-- **At a zeta zero the evaluator annihilates every sub-window vector.**  The whole explicit family
lies in the kernel of the evaluation there, so a witness must come from its orthogonal
complement. -/
theorem soninMellinEvaluation_coPoissonSubWindowSonin_eq_zero (hc : 0 < c) (hcd : c ≤ d)
    {w : ℂ} (hw0 : 0 < w.re) (hz : riemannZeta w = 0) :
    soninMellinEvaluation w
        (((coPoissonSubWindowSonin hc hcd :
          soninExtendedSpace (subWindowAperture c d)) : evenSubspace) : SoninL2) = 0 := by
  have hw1 : w.re < 1 := riemannZeta_zero_re_lt_one hz
  rw [soninMellinEvaluation_coPoissonSubWindowSonin hc hcd hw0 hw1, hz]
  simp

theorem inner_burnolExtendedSoninEvaluationVector_coPoissonSubWindowSonin_eq_zero
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hz : riemannZeta w = 0)
    (hc : 0 < c) (hcd : c ≤ d) :
    ⟪burnolExtendedSoninEvaluationVector w (subWindowAperture c d) hlo hhi
        (subWindowAperture_pos hc hcd), coPoissonSubWindowSonin hc hcd⟫_ℂ = 0 := by
  rw [inner_burnolExtendedSoninEvaluationVector]
  exact soninMellinEvaluation_coPoissonSubWindowSonin_eq_zero hc hcd (by linarith) hz


/-! ## The family at a fixed aperture -/

/-- A sub-window Sonine vector read at any smaller aperture.  Shrinking the aperture weakens the
constant-head conditions, so the same vector lies in the larger space. -/
def coPoissonSubWindowSoninAt {A : ℝ} (hc : 0 < c) (hcd : c ≤ d) (hAle : A ≤ subWindowAperture c d) :
    soninExtendedSpace A :=
  ⟨coPoissonSubWindowEven hc hcd, soninExtendedSpace_mono hAle
    (coPoissonSubWindowSonin hc hcd).property⟩

@[simp] theorem coe_coPoissonSubWindowSoninAt {A : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (hAle : A ≤ subWindowAperture c d) :
    ((coPoissonSubWindowSoninAt hc hcd hAle : soninExtendedSpace A) : evenSubspace) =
      coPoissonSubWindowEven hc hcd := rfl

/-- **The one-parameter family at a fixed aperture.**  For `a <= d <= 1/a` the window `[a,d]` has
aperture exactly `a`, so the whole family lives in one extended Sonine space. -/
theorem subWindowAperture_left_eq {a d : ℝ} (ha : 0 < a) (had : a ≤ d) (hd : d ≤ a⁻¹) :
    subWindowAperture a d = a := by
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le ha had
  have h : a ≤ d⁻¹ := by
    rw [le_inv_comm₀ ha hdpos]
    exact hd
  exact min_eq_left h

/-- **At a zeta zero the evaluator annihilates the whole family, read at a common aperture.** -/
theorem inner_burnolExtendedSoninEvaluationVector_subWindowAt_eq_zero
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hz : riemannZeta w = 0)
    {A : ℝ} (hA : 0 < A) (hc : 0 < c) (hcd : c ≤ d) (hAle : A ≤ subWindowAperture c d) :
    ⟪burnolExtendedSoninEvaluationVector w A hlo hhi hA,
        coPoissonSubWindowSoninAt hc hcd hAle⟫_ℂ = 0 := by
  rw [inner_burnolExtendedSoninEvaluationVector, coe_coPoissonSubWindowSoninAt]
  have hval := soninMellinEvaluation_coPoissonSubWindowSonin_eq_zero hc hcd
    (by linarith : (0 : ℝ) < w.re) hz
  exact hval

/-- **Off the zero set the same family is a witness at that aperture.** -/
theorem inner_burnolExtendedSoninEvaluationVector_subWindowAt_ne_zero
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hz : riemannZeta w ≠ 0)
    {A : ℝ} (hA : 0 < A) (hc : 0 < c) (hcd : c < d) (hAle : A ≤ subWindowAperture c d) :
    ⟪burnolExtendedSoninEvaluationVector w A hlo hhi hA,
        coPoissonSubWindowSoninAt hc hcd.le hAle⟫_ℂ ≠ 0 := by
  rw [inner_burnolExtendedSoninEvaluationVector, coe_coPoissonSubWindowSoninAt]
  exact (soninMellinEvaluation_coPoissonSubWindowSonin_ne_zero_iff hc hcd
    (by linarith : (0 : ℝ) < w.re) hhi).mpr hz


/-! ## The explicit co-Poisson subspace at a fixed aperture -/

/-- The generating set of sub-window Sonine vectors readable at aperture `A`. -/
def burnolSubWindowGenerators (A : ℝ) : Set (soninExtendedSpace A) :=
  {f | ∃ (c d : ℝ) (hc : 0 < c) (hcd : c ≤ d) (hAle : A ≤ subWindowAperture c d),
    f = coPoissonSubWindowSoninAt hc hcd hAle}

/-- The closed span of the explicit sub-window co-Poisson vectors at aperture `A`. -/
def burnolSubWindowSpace (A : ℝ) : Submodule ℂ (soninExtendedSpace A) :=
  (Submodule.span ℂ (burnolSubWindowGenerators A)).topologicalClosure

/-- **At a zeta zero the evaluator annihilates the whole explicit subspace.**  This is the
concrete form of the statement that the evaluator lies in the co-Poisson quotient there. -/
theorem inner_eq_zero_of_mem_burnolSubWindowSpace
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hz : riemannZeta w = 0)
    {A : ℝ} (hA : 0 < A) (u : soninExtendedSpace A) (hu : u ∈ burnolSubWindowSpace A) :
    ⟪burnolExtendedSoninEvaluationVector w A hlo hhi hA, u⟫_ℂ = 0 := by
  letI : Fact (0 < A) := ⟨hA⟩
  set k := burnolExtendedSoninEvaluationVector w A hlo hhi hA with hk
  set K : Submodule ℂ (soninExtendedSpace A) :=
    LinearMap.ker ((innerSL ℂ k).toLinearMap) with hK
  have hclosed : IsClosed (K : Set (soninExtendedSpace A)) :=
    (innerSL ℂ k).isClosed_ker
  have hgen : burnolSubWindowGenerators A ⊆ (K : Set (soninExtendedSpace A)) := by
    rintro f ⟨c, d, hc, hcd, hAle, rfl⟩
    rw [SetLike.mem_coe, hK, LinearMap.mem_ker]
    show ⟪k, coPoissonSubWindowSoninAt hc hcd hAle⟫_ℂ = 0
    exact inner_burnolExtendedSoninEvaluationVector_subWindowAt_eq_zero hlo hhi hz hA hc hcd hAle
  have hle : burnolSubWindowSpace A ≤ K :=
    (Submodule.span ℂ (burnolSubWindowGenerators A)).topologicalClosure_minimal
      (Submodule.span_le.mpr hgen) hclosed
  have := hle hu
  rw [hK, LinearMap.mem_ker] at this
  exact this

/-- **Off the zero set the explicit subspace already detects the evaluator.** -/
theorem burnolExtendedSoninEvaluationVector_notMem_orthogonal_of_ne_zero
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hz : riemannZeta w ≠ 0)
    {A : ℝ} (hA : 0 < A) (hc : 0 < c) (hcd : c < d) (hAle : A ≤ subWindowAperture c d) :
    coPoissonSubWindowSoninAt hc hcd.le hAle ∈ burnolSubWindowSpace A ∧
      ⟪burnolExtendedSoninEvaluationVector w A hlo hhi hA,
        coPoissonSubWindowSoninAt hc hcd.le hAle⟫_ℂ ≠ 0 := by
  refine ⟨?_, inner_burnolExtendedSoninEvaluationVector_subWindowAt_ne_zero hlo hhi hz hA hc hcd
    hAle⟩
  refine (Submodule.span ℂ (burnolSubWindowGenerators A)).le_topologicalClosure ?_
  exact Submodule.subset_span ⟨c, d, hc, hcd.le, hAle, rfl⟩


/-! ## Nontriviality -/

/-- Below the lower window end the co-Poisson value is the nonzero correction constant. -/
theorem burnolCoPoissonRightSum_coPoissonSubWindowSeed_eq_const (hc : 0 < c) (hcd : c ≤ d)
    {t : ℝ} (ht : 0 < t) (htc : t < c) :
    burnolCoPoissonRightSum (coPoissonSubWindowSeed c d) t = ((-(c⁻¹ - d⁻¹) : ℝ) : ℂ) := by
  have hd : (0 : ℝ) < d := lt_of_lt_of_le hc hcd
  have hcard : (Finset.Icc ⌈t / d⌉₊ ⌊t / c⌋₊).card = 0 := by
    have hfloor : ⌊t / c⌋₊ = 0 := by
      refine Nat.floor_eq_zero.mpr ?_
      rw [div_lt_one hc]
      exact htc
    have hceil : 1 ≤ ⌈t / d⌉₊ := Nat.one_le_ceil_iff.mpr (by positivity)
    rw [hfloor, Nat.card_Icc]
    omega
  rw [burnolCoPoissonRightSum_coPoissonSubWindowSeed_eq_card hc hcd ht, hcard]
  norm_num

/-- **The sub-window co-Poisson vector is nonzero.**  It is a nonzero constant on the whole segment
below the lower window end. -/
theorem coPoissonSubWindowEven_ne_zero (hc : 0 < c) (hcd : c < d) :
    coPoissonSubWindowEven hc hcd.le ≠ 0 := by
  have hd : (0 : ℝ) < d := lt_trans hc hcd
  have hgap : (0 : ℝ) < c⁻¹ - d⁻¹ := by
    rw [sub_pos, inv_lt_inv₀ hd hc]
    exact hcd
  intro hzero
  have hae : (((coPoissonSubWindowEven hc hcd.le : evenSubspace) : SoninL2) : ℝ → ℂ)
      =ᵐ[volume] 0 := by
    have hz : ((coPoissonSubWindowEven hc hcd.le : evenSubspace) : SoninL2) = 0 := by
      rw [hzero]
      rfl
    rw [hz]
    exact Lp.coeFn_zero _ _ _
  have hcontra : ∀ᵐ t ∂(volume.restrict (Set.Ioo (0 : ℝ) c)), (0 : ℂ) = ((-(c⁻¹ - d⁻¹) : ℝ) : ℂ) := by
    filter_upwards [ae_restrict_of_ae hae,
      ae_restrict_of_ae (coPoissonSubWindowEven_coeFn hc hcd.le),
      ae_restrict_mem measurableSet_Ioo] with t h1 h2 ht
    have h1' : (((coPoissonSubWindowEven hc hcd.le : evenSubspace) : SoninL2) : ℝ → ℂ) t =
        (0 : ℂ) := h1
    rw [← h1', h2, burnolCoPoissonRightSum_coPoissonSubWindowSeed_eq_const hc hcd.le ht.1 ht.2]
  have hne : ((0 : ℂ)) ≠ ((-(c⁻¹ - d⁻¹) : ℝ) : ℂ) := by
    intro h
    have := congrArg Complex.re h.symm
    rw [Complex.ofReal_re, Complex.zero_re] at this
    linarith
  have hvol : (volume.restrict (Set.Ioo (0 : ℝ) c)) Set.univ ≠ 0 := by
    rw [Measure.restrict_apply_univ, Real.volume_Ioo]
    simp only [sub_zero]
    exact ne_of_gt (by exact_mod_cast ENNReal.ofReal_pos.mpr hc)
  rw [Filter.eventually_iff, mem_ae_iff] at hcontra
  refine hvol ?_
  have hset : {t : ℝ | (0 : ℂ) = ((-(c⁻¹ - d⁻¹) : ℝ) : ℂ)}ᶜ = Set.univ := by
    ext t
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact hne
  rwa [hset] at hcontra

/-- **The explicit co-Poisson subspace is nontrivial at every aperture.** -/
theorem burnolSubWindowSpace_ne_bot {A : ℝ} (hc : 0 < c) (hcd : c < d)
    (hAle : A ≤ subWindowAperture c d) : burnolSubWindowSpace A ≠ ⊥ := by
  intro hbot
  have hmem : coPoissonSubWindowSoninAt hc hcd.le hAle ∈ burnolSubWindowSpace A := by
    refine (Submodule.span ℂ (burnolSubWindowGenerators A)).le_topologicalClosure ?_
    exact Submodule.subset_span ⟨c, d, hc, hcd.le, hAle, rfl⟩
  rw [hbot, Submodule.mem_bot] at hmem
  refine coPoissonSubWindowEven_ne_zero hc hcd ?_
  have := congrArg (fun f : soninExtendedSpace A => (f : evenSubspace)) hmem
  simpa using this


/-- **Distinct windows give distinct vectors.**  The constant below the lower window end determines
the upper window end, so the explicit family is genuinely a family. -/
theorem coPoissonSubWindowEven_inj_right {c d₁ d₂ : ℝ} (hc : 0 < c) (h1 : c ≤ d₁) (h2 : c ≤ d₂)
    (heq : coPoissonSubWindowEven hc h1 = coPoissonSubWindowEven hc h2) : d₁ = d₂ := by
  have hd₁ : (0 : ℝ) < d₁ := lt_of_lt_of_le hc h1
  have hd₂ : (0 : ℝ) < d₂ := lt_of_lt_of_le hc h2
  have hmeas : volume.restrict (Set.Ioo (0 : ℝ) c) ≠ 0 := by
    intro hzero
    have hu : (volume.restrict (Set.Ioo (0 : ℝ) c)) Set.univ = 0 := by rw [hzero]; rfl
    rw [Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero] at hu
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) hu
  haveI : (ae (volume.restrict (Set.Ioo (0 : ℝ) c))).NeBot := ae_neBot.mpr hmeas
  have hae : ∀ᵐ _t ∂(volume.restrict (Set.Ioo (0 : ℝ) c)),
      ((-(c⁻¹ - d₁⁻¹) : ℝ) : ℂ) = ((-(c⁻¹ - d₂⁻¹) : ℝ) : ℂ) := by
    have hcoe : (((coPoissonSubWindowEven hc h1 : evenSubspace) : SoninL2) : ℝ → ℂ)
        =ᵐ[volume] (((coPoissonSubWindowEven hc h2 : evenSubspace) : SoninL2) : ℝ → ℂ) := by
      rw [heq]
    filter_upwards [ae_restrict_of_ae hcoe,
      ae_restrict_of_ae (coPoissonSubWindowEven_coeFn hc h1),
      ae_restrict_of_ae (coPoissonSubWindowEven_coeFn hc h2),
      ae_restrict_mem measurableSet_Ioo] with t h12 hv1 hv2 ht
    rw [← burnolCoPoissonRightSum_coPoissonSubWindowSeed_eq_const hc h1 ht.1 ht.2,
      ← burnolCoPoissonRightSum_coPoissonSubWindowSeed_eq_const hc h2 ht.1 ht.2,
      ← hv1, ← hv2, h12]
  have hconst := Filter.eventually_const.mp hae
  have hreal : -(c⁻¹ - d₁⁻¹) = -(c⁻¹ - d₂⁻¹) := by
    have := congrArg Complex.re hconst
    rwa [Complex.ofReal_re, Complex.ofReal_re] at this
  have hinv : d₁⁻¹ = d₂⁻¹ := by linarith
  rw [← inv_inv d₁, ← inv_inv d₂, hinv]


/-- **Burnol's own co-Poisson source space is nontrivial.**  The sub-window source supplies a
nonzero generator, so the closed source space of the corpus definition is not `bot`. -/
theorem burnolCoPoissonSourceSpace_ne_bot (hc : 0 < c) (hcd : c < d) :
    burnolCoPoissonSourceSpace (subWindowAperture c d) ≠ ⊥ := by
  intro hbot
  have hgen : (coPoissonSubWindowEven hc hcd.le) ∈
      burnolCoPoissonGeneratorSet (subWindowAperture c d) :=
    ⟨coPoissonSubWindowSource hc hcd.le, Or.inl rfl⟩
  have hspan : (coPoissonSubWindowEven hc hcd.le) ∈
      burnolCoPoissonAlgebraicSourceSpace (subWindowAperture c d) :=
    Submodule.subset_span hgen
  have hmem : (coPoissonSubWindowEven hc hcd.le) ∈
      burnolCoPoissonSourceSpace (subWindowAperture c d) :=
    (burnolCoPoissonAlgebraicSourceSpace (subWindowAperture c d)).le_topologicalClosure hspan
  rw [hbot, Submodule.mem_bot] at hmem
  exact coPoissonSubWindowEven_ne_zero hc hcd hmem

/-- **The co-Poisson quotient space is a proper subspace.**  Since the source space is nontrivial,
the quotient is not everything. -/
theorem burnolCoPoissonQuotientSpace_ne_soninExtendedSpace (hc : 0 < c) (hcd : c < d) :
    burnolCoPoissonQuotientSpace (subWindowAperture c d) ≠
      soninExtendedSpace (subWindowAperture c d) := by
  intro heq
  have hv : (coPoissonSubWindowEven hc hcd.le) ∈ soninExtendedSpace (subWindowAperture c d) :=
    (coPoissonSubWindowSonin hc hcd.le).property
  have hmemQ : (coPoissonSubWindowEven hc hcd.le) ∈
      burnolCoPoissonQuotientSpace (subWindowAperture c d) := by
    rw [heq]
    exact hv
  have hgen : (coPoissonSubWindowEven hc hcd.le) ∈
      burnolCoPoissonSourceSpace (subWindowAperture c d) :=
    (burnolCoPoissonAlgebraicSourceSpace (subWindowAperture c d)).le_topologicalClosure
      (Submodule.subset_span ⟨coPoissonSubWindowSource hc hcd.le, Or.inl rfl⟩)
  have hself := hmemQ.2 _ hgen
  rw [inner_self_eq_zero] at hself
  exact coPoissonSubWindowEven_ne_zero hc hcd hself

end RHTower

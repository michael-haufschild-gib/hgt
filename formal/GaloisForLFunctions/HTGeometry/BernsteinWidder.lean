import GaloisForLFunctions.HTGeometry.CompletelyMonotoneSampling

/-!
# Bernstein--Widder representation on the positive half-line

This file completes the continuous half of the Bernstein--Widder theorem from the existing
Hausdorff moment theorem.  Spectral coordinates are compactified by `z = exp (-r)`: level `n`
samples use mesh `1 / (n+1)`, and the map `y ↦ y^(n+1)` puts every representing Hausdorff measure
on the same compact interval.  Adjacent mesh moments squeeze every positive real exponent, so a
compact weak limit gives the full Laplace representation without noncompact tightness machinery.
-/

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Continuous finite-difference formulation of complete monotonicity on `(0,∞)`. -/
def CompletelyMonotoneOn (H : ℝ → ℝ) : Prop :=
  CompletelyMonotoneDiff H ∧ ContinuousOn H (Ioi 0)

theorem completelyMonotoneDiff_congr_Ioi {F G : ℝ → ℝ}
    (hFG : EqOn F G (Ioi 0)) (hF : CompletelyMonotoneDiff F) :
    CompletelyMonotoneDiff G := by
  intro k delta hdelta t ht
  have hiter : (fwdDiff delta)^[k] G t = (fwdDiff delta)^[k] F t := by
    rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
    apply Finset.sum_congr rfl
    intro j hj
    congr 2
    symm
    apply hFG
    rw [mem_Ioi]
    exact add_pos_of_pos_of_nonneg ht (nsmul_nonneg hdelta.le j)
  rw [hiter]
  exact hF k delta hdelta t ht

theorem CompletelyMonotoneOn.congr_Ioi {F G : ℝ → ℝ}
    (hF : CompletelyMonotoneOn F) (hFG : EqOn F G (Ioi 0)) :
    CompletelyMonotoneOn G := by
  refine ⟨completelyMonotoneDiff_congr_Ioi hFG hF.1, ?_⟩
  exact hF.2.congr fun x hx => (hFG hx).symm

/-- The mesh-`1/(n+1)` sample used in the Bernstein compactness argument. -/
def bernsteinSampleSequence (H : ℝ → ℝ) (n m : ℕ) : ℝ :=
  H ((m + 1 : ℕ) / (n + 1 : ℕ))

theorem bernsteinSampleSequence_completelyMonotone {H : ℝ → ℝ}
    (hH : CompletelyMonotoneDiff H) (n : ℕ) :
    HausdorffCompletelyMonotone (bernsteinSampleSequence H n) := by
  have hsample := hausdorffCompletelyMonotone_sample hH
    (a := ((n + 1 : ℕ) : ℝ)⁻¹) (δ := ((n + 1 : ℕ) : ℝ)⁻¹)
    (by positivity) (by positivity)
  convert hsample using 1
  funext m
  rw [bernsteinSampleSequence]
  congr 1
  push_cast
  field_simp
  ring

/-- Chosen Hausdorff source for one Bernstein mesh. -/
noncomputable def bernsteinSampleMeasure (H : ℝ → ℝ) (hH : CompletelyMonotoneDiff H)
    (n : ℕ) : Measure HausdorffSourceSpace :=
  Classical.choose
    (exists_hausdorffSource_of_completelyMonotone
      (bernsteinSampleSequence_completelyMonotone hH n))

instance bernsteinSampleMeasure_isFinite (H : ℝ → ℝ) (hH : CompletelyMonotoneDiff H)
    (n : ℕ) : IsFiniteMeasure (bernsteinSampleMeasure H hH n) :=
  (Classical.choose_spec
    (exists_hausdorffSource_of_completelyMonotone
      (bernsteinSampleSequence_completelyMonotone hH n))).1

theorem hausdorffMoment_bernsteinSampleMeasure (H : ℝ → ℝ)
    (hH : CompletelyMonotoneDiff H) (n : ℕ) :
    hausdorffMoment (bernsteinSampleMeasure H hH n) = bernsteinSampleSequence H n :=
  (Classical.choose_spec
    (exists_hausdorffSource_of_completelyMonotone
      (bernsteinSampleSequence_completelyMonotone hH n))).2

/-- Compactify the level-`n` Hausdorff coordinate to the common coordinate `z = exp (-r)`. -/
def bernsteinCompactify (n : ℕ) (y : HausdorffSourceSpace) : HausdorffSourceSpace :=
  ⟨(y : ℝ) ^ (n + 1),
    pow_nonneg y.property.1 _,
    pow_le_one₀ y.property.1 y.property.2⟩

theorem continuous_bernsteinCompactify (n : ℕ) : Continuous (bernsteinCompactify n) := by
  unfold bernsteinCompactify
  fun_prop

/-- The level-`n` sample source in the fixed compact Laplace coordinate. -/
def bernsteinCompactMeasure (H : ℝ → ℝ) (hH : CompletelyMonotoneDiff H) (n : ℕ) :
    Measure HausdorffSourceSpace :=
  Measure.map (bernsteinCompactify n) (bernsteinSampleMeasure H hH n)

instance bernsteinCompactMeasure_isFinite (H : ℝ → ℝ) (hH : CompletelyMonotoneDiff H)
    (n : ℕ) : IsFiniteMeasure (bernsteinCompactMeasure H hH n) :=
  Measure.isFiniteMeasure_map _ _

theorem bernsteinCompactMeasure_univ (H : ℝ → ℝ) (hH : CompletelyMonotoneDiff H)
    (n : ℕ) :
    bernsteinCompactMeasure H hH n Set.univ =
      ENNReal.ofReal (H (((n + 1 : ℕ) : ℝ)⁻¹)) := by
  rw [bernsteinCompactMeasure, Measure.map_apply
    (continuous_bernsteinCompactify n).measurable MeasurableSet.univ]
  simp only [preimage_univ]
  have hm := congrFun (hausdorffMoment_bernsteinSampleMeasure H hH n) 0
  have hm' : (bernsteinSampleMeasure H hH n Set.univ).toReal =
      H (((n + 1 : ℕ) : ℝ)⁻¹) := by
    simpa [hausdorffMoment, bernsteinSampleSequence, measureReal_def] using hm
  rw [← hm', ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem bernsteinCompactMeasure_gridMoment (H : ℝ → ℝ)
    (hH : CompletelyMonotoneDiff H) (n : ℕ) {m : ℕ} (hm : 0 < m) :
    (∫ z : HausdorffSourceSpace,
        (z : ℝ) ^ ((m : ℝ) / ((n + 1 : ℕ) : ℝ)) ∂bernsteinCompactMeasure H hH n) =
      H (((m + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
  rw [bernsteinCompactMeasure, integral_map
    (continuous_bernsteinCompactify n).aemeasurable]
  · have hpoint : ∀ y : HausdorffSourceSpace,
        ((bernsteinCompactify n y : HausdorffSourceSpace) : ℝ) ^
            ((m : ℝ) / ((n + 1 : ℕ) : ℝ)) = (y : ℝ) ^ m := by
      intro y
      rw [bernsteinCompactify]
      change ((y : ℝ) ^ (n + 1)) ^ ((m : ℝ) / ((n + 1 : ℕ) : ℝ)) = (y : ℝ) ^ m
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul y.property.1]
      have hden : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hexp : (((n + 1 : ℕ) : ℝ)) *
          ((m : ℝ) / ((n + 1 : ℕ) : ℝ)) = (m : ℝ) := by field_simp
      rw [hexp, Real.rpow_natCast]
    simp_rw [hpoint]
    have hmoment := congrFun (hausdorffMoment_bernsteinSampleMeasure H hH n) m
    exact hmoment
  · fun_prop (disch := positivity)

/-- Every positive value of a completely monotone profile is bounded by its finite right limit
at zero. -/
theorem completelyMonotoneDiff_le_zeroLimit {H : ℝ → ℝ} {L t : ℝ}
    (hH : CompletelyMonotoneDiff H)
    (hlim : Tendsto H (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 L)) (ht : 0 < t) :
    H t ≤ L := by
  by_contra hle
  have hLt : L < H t := lt_of_not_ge hle
  have hsmall : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0), H s < H t :=
    hlim.eventually (Iio_mem_nhds hLt)
  have hlt : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0), s ≤ t :=
    Filter.Eventually.filter_mono inf_le_left (Iic_mem_nhds ht)
  have hanti : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0), H t ≤ H s := by
    filter_upwards [self_mem_nhdsWithin, hlt] with s hs hst
    exact completelyMonotoneDiff_antitone hH hs hst
  obtain ⟨s, hts, hst⟩ := (hanti.and hsmall).exists
  exact (not_lt_of_ge hts) hst

/-- Reciprocal linear mesh tends to zero through positive values. -/
theorem tendsto_bernsteinMesh_zero :
    Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) atTop
      (nhdsWithin (0 : ℝ) (Ioi 0)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
      apply tendsto_atTop.2
      intro b
      filter_upwards [eventually_ge_atTop b] with a ha
      omega
    have h := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp hshift
    convert h using 1
    funext n
    norm_num [Function.comp_def]
  · filter_upwards with n
    show 0 < (((n + 1 : ℕ) : ℝ))⁻¹
    positivity

/-- The lower mesh point `floor(t(n+1))/(n+1)` converges to `t`. -/
theorem tendsto_bernsteinFloorMesh (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ =>
      ((⌊t * ((n + 1 : ℕ) : ℝ)⌋₊ : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 t) := by
  let d : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)
  let s : ℕ → ℝ := fun n => ((⌊t * d n⌋₊ : ℕ) : ℝ) / d n
  have hmesh : Tendsto (fun n : ℕ => (1 : ℝ) / d n) atTop (𝓝 0) := by
    have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
      apply tendsto_atTop.2
      intro b
      filter_upwards [eventually_ge_atTop b] with a ha
      omega
    have h := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp hshift
    convert h using 1
    funext n
    norm_num [d, Function.comp_def]
  have hlower : ∀ n : ℕ, t - 1 / d n ≤ s n := by
    intro n
    have hfloor := Nat.lt_floor_add_one (t * d n)
    have hd : 0 < d n := by dsimp [d]; positivity
    have : t < s n + 1 / d n := by
      dsimp [s]
      calc
        t = (t * d n) / d n := by field_simp
        _ < (((⌊t * d n⌋₊ : ℕ) : ℝ) + 1) / d n :=
          (div_lt_div_iff₀ hd hd).2 (by simpa only [mul_one] using mul_lt_mul_of_pos_right hfloor hd)
        _ = ((⌊t * d n⌋₊ : ℕ) : ℝ) / d n + 1 / d n := by ring
    linarith
  have hupper : ∀ n : ℕ, s n ≤ t := by
    intro n
    have hd : 0 < d n := by dsimp [d]; positivity
    dsimp [s]
    rw [div_le_iff₀ hd]
    exact Nat.floor_le (mul_nonneg ht hd.le)
  have hlowerlim : Tendsto (fun n => t - 1 / d n) atTop (𝓝 t) := by
    convert tendsto_const_nhds.sub hmesh using 1
    simp
  have hs : Tendsto s atTop (𝓝 t) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowerlim tendsto_const_nhds
      (Eventually.of_forall hlower) (Eventually.of_forall hupper)
  exact hs

/-- Real-power test function on the compact Laplace coordinate. -/
def bernsteinRpowTest (t : ℝ) (ht : 0 < t) :
    BoundedContinuousFunction HausdorffSourceSpace ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z => (z : ℝ) ^ t, by fun_prop (disch := positivity)⟩

@[simp] theorem bernsteinRpowTest_apply (t : ℝ) (ht : 0 < t)
    (z : HausdorffSourceSpace) : bernsteinRpowTest t ht z = (z : ℝ) ^ t := rfl

/-- Real powers decrease with the exponent on the compact unit interval. -/
theorem hausdorff_rpow_antitone_exponent (z : HausdorffSourceSpace) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) : (z : ℝ) ^ t ≤ (z : ℝ) ^ s := by
  rcases eq_or_lt_of_le z.property.1 with hz | hz
  · rw [← hz]
    by_cases ht0 : t = 0
    · subst t
      have hs0 : s = 0 := le_antisymm hst hs
      simp [hs0]
    · have ht : 0 < t := lt_of_le_of_ne (hs.trans hst) (Ne.symm ht0)
      rw [Real.zero_rpow ht.ne']
      exact Real.rpow_nonneg (by norm_num) s
  · exact Real.rpow_le_rpow_of_exponent_ge hz z.property.2 hst

/-- Missing mass is placed at the compactification point `z=0`; positive real-power moments do
not see it. -/
def bernsteinCompletedCompactMeasure (H : ℝ → ℝ) (hH : CompletelyMonotoneDiff H)
    (L : ℝ) (n : ℕ) : Measure HausdorffSourceSpace :=
  bernsteinCompactMeasure H hH n +
    ENNReal.ofReal (L - H (((n + 1 : ℕ) : ℝ)⁻¹)) •
      Measure.dirac (⟨0, by simp⟩ : HausdorffSourceSpace)

theorem bernsteinCompletedCompactMeasure_univ (H : ℝ → ℝ)
    (hH : CompletelyMonotoneDiff H) {L : ℝ}
    (hbound : ∀ t : ℝ, 0 < t → H t ≤ L) (n : ℕ) :
    bernsteinCompletedCompactMeasure H hH L n Set.univ = ENNReal.ofReal L := by
  have hstep0 : 0 ≤ H (((n + 1 : ℕ) : ℝ)⁻¹) :=
    completelyMonotoneDiff_nonneg hH (by positivity)
  have hstepL : H (((n + 1 : ℕ) : ℝ)⁻¹) ≤ L := hbound _ (by positivity)
  rw [bernsteinCompletedCompactMeasure, Measure.add_apply, bernsteinCompactMeasure_univ,
    Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.univ]
  simp only [Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply, smul_eq_mul, mul_one]
  calc
    ENNReal.ofReal (H (((n + 1 : ℕ) : ℝ)⁻¹)) +
        ENNReal.ofReal (L - H (((n + 1 : ℕ) : ℝ)⁻¹)) =
        ENNReal.ofReal (H (((n + 1 : ℕ) : ℝ)⁻¹) +
          (L - H (((n + 1 : ℕ) : ℝ)⁻¹))) :=
      (ENNReal.ofReal_add hstep0 (sub_nonneg.mpr hstepL)).symm
    _ = ENNReal.ofReal L := by congr 1; ring

/-- Fixed-mass compact probability approximant. -/
noncomputable def bernsteinProbabilityMeasure (H : ℝ → ℝ)
    (hH : CompletelyMonotoneDiff H) (L : ℝ) (hL : 0 < L)
    (hbound : ∀ t : ℝ, 0 < t → H t ≤ L) (n : ℕ) :
    ProbabilityMeasure HausdorffSourceSpace :=
  ⟨(ENNReal.ofReal L)⁻¹ • bernsteinCompletedCompactMeasure H hH L n, by
    constructor
    rw [Measure.smul_apply, bernsteinCompletedCompactMeasure_univ H hH hbound,
      smul_eq_mul]
    exact ENNReal.inv_mul_cancel
      (by simp [ENNReal.ofReal_eq_zero, not_le, hL]) ENNReal.ofReal_ne_top⟩

theorem integral_bernsteinProbabilityMeasure_gridMoment (H : ℝ → ℝ)
    (hH : CompletelyMonotoneDiff H) {L : ℝ} (hL : 0 < L)
    (hbound : ∀ t : ℝ, 0 < t → H t ≤ L) (n : ℕ) {m : ℕ} (hm : 0 < m) :
    (∫ z : HausdorffSourceSpace,
        (z : ℝ) ^ ((m : ℝ) / ((n + 1 : ℕ) : ℝ))
          ∂(bernsteinProbabilityMeasure H hH L hL hbound n :
            ProbabilityMeasure HausdorffSourceSpace)) =
      L⁻¹ * H (((m + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
  let f : HausdorffSourceSpace → ℝ := fun z =>
    (z : ℝ) ^ ((m : ℝ) / ((n + 1 : ℕ) : ℝ))
  have hfcont : Continuous f := by
    dsimp [f]
    fun_prop (disch := positivity)
  have hficompact : Integrable f (bernsteinCompactMeasure H hH n) :=
    integrable_of_continuous _ hfcont
  have hfidirac : Integrable f
      (ENNReal.ofReal (L - H (((n + 1 : ℕ) : ℝ)⁻¹)) •
        Measure.dirac (⟨0, by simp⟩ : HausdorffSourceSpace)) := by
    refine (integrable_dirac ?_).smul_measure ENNReal.ofReal_ne_top
    exact ENNReal.coe_lt_top
  change ∫ z, f z ∂((ENNReal.ofReal L)⁻¹ •
    bernsteinCompletedCompactMeasure H hH L n) = _
  rw [integral_smul_measure, bernsteinCompletedCompactMeasure,
    integral_add_measure hficompact hfidirac, integral_smul_measure, integral_dirac]
  have hzero : f (⟨0, by simp⟩ : HausdorffSourceSpace) = 0 := by
    dsimp [f]
    rw [Real.zero_rpow]
    positivity
  rw [hzero, smul_zero, add_zero, bernsteinCompactMeasure_gridMoment H hH n hm,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hL.le, smul_eq_mul]

/-- Compact Bernstein--Widder theorem.  A continuous completely monotone profile with finite
right limit at zero is the full real-power moment profile of a finite measure on `[0,1]`. -/
theorem exists_compactLaplaceMeasure_of_completelyMonotoneOn
    {H : ℝ → ℝ} {L : ℝ} (hH : CompletelyMonotoneOn H)
    (hlim : Tendsto H (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 L)) :
    ∃ rho : Measure HausdorffSourceSpace, IsFiniteMeasure rho ∧
      ∀ t : ℝ, 0 < t → H t = ∫ z : HausdorffSourceSpace, (z : ℝ) ^ t ∂rho := by
  have hL0 : 0 ≤ L := by
    apply isClosed_Ici.mem_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact completelyMonotoneDiff_nonneg hH.1 ht
  rcases eq_or_lt_of_le hL0 with hLzero | hL
  · subst L
    refine ⟨0, by infer_instance, fun t ht => ?_⟩
    have hle := completelyMonotoneDiff_le_zeroLimit hH.1 hlim ht
    have hnonneg := completelyMonotoneDiff_nonneg hH.1 ht
    simp only [integral_zero_measure]
    linarith
  · have hbound : ∀ t : ℝ, 0 < t → H t ≤ L := fun t ht =>
      completelyMonotoneDiff_le_zeroLimit hH.1 hlim ht
    let P : ℕ → ProbabilityMeasure HausdorffSourceSpace :=
      fun n => bernsteinProbabilityMeasure H hH.1 L hL hbound n
    obtain ⟨Q, hQ⟩ := exists_clusterPt_of_compactSpace (Filter.map P atTop)
    have hmoment : ∀ t : ℝ, 0 < t →
        ∫ z : HausdorffSourceSpace, (z : ℝ) ^ t ∂(Q : Measure HausdorffSourceSpace) =
          L⁻¹ * H t := by
      intro t ht
      let m : ℕ → ℕ := fun n => ⌊t * ((n + 1 : ℕ) : ℝ)⌋₊
      let s : ℕ → ℝ := fun n => (m n : ℝ) / ((n + 1 : ℕ) : ℝ)
      have hs : Tendsto s atTop (𝓝 t) := by
        simpa only [s, m] using tendsto_bernsteinFloorMesh t ht.le
      have hmesh : Tendsto (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ))
          atTop (𝓝 0) := by
        simpa only [one_div] using
          (tendsto_nhdsWithin_iff.mp tendsto_bernsteinMesh_zero).1
      have hargUpper : Tendsto (fun n : ℕ =>
          (((m n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))) atTop (𝓝 t) := by
        have hsum : Tendsto (fun n => s n + 1 / ((n + 1 : ℕ) : ℝ))
            atTop (𝓝 t) := by simpa using hs.add hmesh
        convert hsum using 1
        funext n
        dsimp [s]
        push_cast
        ring
      have hargLower : Tendsto (fun n : ℕ =>
          (((m n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))) atTop (𝓝 t) := by
        have htwo : Tendsto (fun n : ℕ => (2 : ℝ) *
            ((1 : ℝ) / ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
          simpa using hmesh.const_mul 2
        have hsum : Tendsto (fun n => s n + 2 * (1 / ((n + 1 : ℕ) : ℝ)))
            atTop (𝓝 t) := by simpa using hs.add htwo
        convert hsum using 1
        funext n
        dsimp [s]
        push_cast
        ring
      have hcont : ContinuousAt H t :=
        (hH.2 t ht).continuousAt (Ioi_mem_nhds ht)
      have hupperLim : Tendsto (fun n : ℕ =>
          L⁻¹ * H (((m n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)))
          atTop (𝓝 (L⁻¹ * H t)) :=
        (hcont.tendsto.comp hargUpper).const_mul _
      have hlowerLim : Tendsto (fun n : ℕ =>
          L⁻¹ * H (((m n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)))
          atTop (𝓝 (L⁻¹ * H t)) :=
        (hcont.tendsto.comp hargLower).const_mul _
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / t)
      have hmpos : ∀ᶠ n in atTop, 0 < m n := by
        filter_upwards [eventually_ge_atTop N] with n hn
        have hcast : (N : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
          exact_mod_cast (le_trans hn (Nat.le_add_right n 1))
        have hmul : 1 < t * ((n + 1 : ℕ) : ℝ) := by
          have htN : 1 < t * (N : ℝ) := by
            have := mul_lt_mul_of_pos_left hN ht
            field_simp at this
            exact this
          exact lt_of_lt_of_le htN (mul_le_mul_of_nonneg_left hcast ht.le)
        have hnlt : ¬ m n < 1 := by
          change ¬ ⌊t * ((n + 1 : ℕ) : ℝ)⌋₊ < 1
          rw [Nat.floor_lt (mul_nonneg ht.le (by positivity))]
          exact not_lt.mpr (by simpa using hmul.le)
        omega
      have hsqueeze : ∀ᶠ n in atTop,
          L⁻¹ * H (((m n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) ≤
            ∫ z : HausdorffSourceSpace, (z : ℝ) ^ t ∂(P n : Measure _) ∧
          (∫ z : HausdorffSourceSpace, (z : ℝ) ^ t ∂(P n : Measure _)) ≤
            L⁻¹ * H (((m n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
        filter_upwards [hmpos] with n hmn
        have hden : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
        have hs0 : 0 ≤ s n := div_nonneg (by positivity) hden.le
        have hst : s n ≤ t := by
          dsimp [s]
          rw [div_le_iff₀ hden]
          exact Nat.floor_le (mul_nonneg ht.le hden.le)
        have htNext : t ≤ ((m n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := by
          apply le_of_lt
          rw [lt_div_iff₀ hden]
          simpa only [m, Nat.cast_add, Nat.cast_one] using
            Nat.lt_floor_add_one (t * ((n + 1 : ℕ) : ℝ))
        have hflow : Integrable (fun z : HausdorffSourceSpace =>
            (z : ℝ) ^ (((m n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)))
            (P n : Measure _) := by
          apply integrable_of_continuous
          fun_prop (disch := positivity)
        have hft : Integrable (fun z : HausdorffSourceSpace => (z : ℝ) ^ t)
            (P n : Measure _) := by
          apply integrable_of_continuous
          fun_prop (disch := positivity)
        have hfup : Integrable (fun z : HausdorffSourceSpace =>
            (z : ℝ) ^ (s n)) (P n : Measure _) := by
          apply integrable_of_continuous
          fun_prop (disch := positivity)
        have hlower : (∫ z : HausdorffSourceSpace,
              (z : ℝ) ^ (((m n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) ∂(P n : Measure _)) ≤
            ∫ z : HausdorffSourceSpace, (z : ℝ) ^ t ∂(P n : Measure _) := by
          apply integral_mono hflow hft
          intro z
          exact hausdorff_rpow_antitone_exponent z ht.le htNext
        have hupper : (∫ z : HausdorffSourceSpace, (z : ℝ) ^ t ∂(P n : Measure _)) ≤
            ∫ z : HausdorffSourceSpace, (z : ℝ) ^ (s n) ∂(P n : Measure _) := by
          apply integral_mono hft hfup
          intro z
          exact hausdorff_rpow_antitone_exponent z hs0 hst
        dsimp [P] at hlower hupper ⊢
        rw [integral_bernsteinProbabilityMeasure_gridMoment H hH.1 hL hbound n
          (show 0 < m n + 1 by omega)] at hlower
        rw [show s n = (m n : ℝ) / ((n + 1 : ℕ) : ℝ) by rfl,
          integral_bernsteinProbabilityMeasure_gridMoment H hH.1 hL hbound n hmn] at hupper
        exact ⟨hlower, hupper⟩
      have htend : Tendsto (fun n : ℕ =>
          ∫ z : HausdorffSourceSpace, (z : ℝ) ^ t ∂(P n : Measure _))
          atTop (𝓝 (L⁻¹ * H t)) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowerLim hupperLim
          (hsqueeze.mono fun _ h => h.1) (hsqueeze.mono fun _ h => h.2)
      have hfunctional := ProbabilityMeasure.continuous_integral_boundedContinuousFunction
        (bernsteinRpowTest t ht)
      have hcluster : ClusterPt
          (∫ z : HausdorffSourceSpace, (z : ℝ) ^ t ∂(Q : Measure _))
          (Filter.map (fun n : ℕ =>
            ∫ z : HausdorffSourceSpace, (z : ℝ) ^ t ∂(P n : Measure _)) atTop) := by
        have hmap := hQ.map hfunctional.continuousAt tendsto_map
        rw [Filter.map_map] at hmap
        change ClusterPt
          ((fun mu : ProbabilityMeasure HausdorffSourceSpace =>
            ∫ z : HausdorffSourceSpace, (z : ℝ) ^ t ∂(mu : Measure _)) Q)
          (Filter.map ((fun mu : ProbabilityMeasure HausdorffSourceSpace =>
            ∫ z : HausdorffSourceSpace, (z : ℝ) ^ t ∂(mu : Measure _)) ∘ P) atTop)
        exact hmap
      exact eq_of_clusterPt_of_tendsto_seq hcluster htend
    let rho : Measure HausdorffSourceSpace := ENNReal.ofReal L • (Q : Measure _)
    have hrhoFinite : IsFiniteMeasure rho := by
      dsimp [rho]
      letI : IsProbabilityMeasure (Q : Measure HausdorffSourceSpace) := Q.2
      constructor
      rw [Measure.smul_apply, smul_eq_mul]
      rw [measure_univ, mul_one]
      exact ENNReal.ofReal_lt_top
    refine ⟨rho, hrhoFinite, fun t ht => ?_⟩
    dsimp [rho]
    rw [integral_smul_measure, ENNReal.toReal_ofReal hL.le, smul_eq_mul,
      hmoment t ht]
    field_simp

/-- Positive part of the compact Laplace coordinate. -/
def positiveHausdorffSource : Set HausdorffSourceSpace :=
  {z | 0 < (z : ℝ)}

theorem measurableSet_positiveHausdorffSource : MeasurableSet positiveHausdorffSource := by
  change MeasurableSet ((fun z : HausdorffSourceSpace => (z : ℝ)) ⁻¹' Ioi 0)
  exact measurableSet_Ioi.preimage continuous_subtype_val.measurable

/-- Inverse exponential compactification `z ↦ -log z`.  Its value at `z=0` is irrelevant because
the source is restricted to the positive compact coordinate before mapping. -/
def inverseLaplaceCompactification (z : HausdorffSourceSpace) : ℝ :=
  -Real.log (z : ℝ)

theorem measurable_inverseLaplaceCompactification :
    Measurable inverseLaplaceCompactification := by
  unfold inverseLaplaceCompactification
  fun_prop

/-- Push a compact real-power source back to the nonnegative Laplace half-line. -/
def bernsteinHalfLineMeasure (rho : Measure HausdorffSourceSpace) : Measure ℝ :=
  Measure.map inverseLaplaceCompactification (rho.restrict positiveHausdorffSource)

instance bernsteinHalfLineMeasure_isFinite (rho : Measure HausdorffSourceSpace)
    [IsFiniteMeasure rho] : IsFiniteMeasure (bernsteinHalfLineMeasure rho) :=
  Measure.isFiniteMeasure_map _ _

theorem bernsteinHalfLineMeasure_carried_Ici (rho : Measure HausdorffSourceSpace) :
    bernsteinHalfLineMeasure rho (Ici (0 : ℝ))ᶜ = 0 := by
  rw [bernsteinHalfLineMeasure, Measure.map_apply measurable_inverseLaplaceCompactification
    measurableSet_Ici.compl]
  rw [Measure.restrict_apply
    (measurableSet_Ici.compl.preimage measurable_inverseLaplaceCompactification)]
  apply measure_mono_null _ (measure_empty)
  rintro z ⟨hzneg, hzpos⟩
  have hzpos' : 0 < (z : ℝ) := hzpos
  have hzlog : Real.log (z : ℝ) ≤ 0 := Real.log_nonpos hzpos'.le z.property.2
  simp only [mem_preimage, mem_compl_iff, mem_Ici, not_le,
    inverseLaplaceCompactification] at hzneg
  exact (not_lt_of_ge (neg_nonneg.mpr hzlog) hzneg).elim

theorem integral_bernsteinHalfLineMeasure_laplace
    (rho : Measure HausdorffSourceSpace) [IsFiniteMeasure rho]
    {t : ℝ} (ht : 0 < t) :
    (∫ r : ℝ, Real.exp (-t * r) ∂bernsteinHalfLineMeasure rho) =
      ∫ z : HausdorffSourceSpace, (z : ℝ) ^ t ∂rho := by
  rw [bernsteinHalfLineMeasure, integral_map
    measurable_inverseLaplaceCompactification.aemeasurable]
  · change (∫ z : HausdorffSourceSpace in positiveHausdorffSource,
      Real.exp (-t * inverseLaplaceCompactification z) ∂rho) = _
    rw [← integral_indicator measurableSet_positiveHausdorffSource]
    apply integral_congr_ae
    filter_upwards with z
    by_cases hz : z ∈ positiveHausdorffSource
    · rw [Set.indicator_of_mem hz]
      have hzpos : 0 < (z : ℝ) := hz
      rw [Real.rpow_def_of_pos hzpos]
      unfold inverseLaplaceCompactification
      congr 1
      ring
    · rw [Set.indicator_of_notMem hz]
      have hz0 : (z : ℝ) = 0 := le_antisymm (not_lt.mp hz) z.property.1
      rw [hz0, Real.zero_rpow ht.ne']
  · fun_prop

/-- **Bernstein--Widder representation.**  Every continuous completely monotone profile on the
positive half-line with finite right limit at zero is the Laplace transform of a finite positive
measure carried by `[0,∞)`. -/
theorem exists_finiteLaplaceMeasure_of_completelyMonotoneOn
    {H : ℝ → ℝ} {L : ℝ} (hH : CompletelyMonotoneOn H)
    (hlim : Tendsto H (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 L)) :
    ∃ tau : Measure ℝ, IsFiniteMeasure tau ∧ tau (Ici (0 : ℝ))ᶜ = 0 ∧
      ∀ t : ℝ, 0 < t → H t = ∫ r : ℝ, Real.exp (-t * r) ∂tau := by
  obtain ⟨rho, hrho, hmoment⟩ :=
    exists_compactLaplaceMeasure_of_completelyMonotoneOn hH hlim
  letI : IsFiniteMeasure rho := hrho
  refine ⟨bernsteinHalfLineMeasure rho, inferInstance,
    bernsteinHalfLineMeasure_carried_Ici rho, fun t ht => ?_⟩
  rw [integral_bernsteinHalfLineMeasure_laplace rho ht]
  exact hmoment t ht

/-! ## Converse: finite positive Laplace transforms are completely monotone -/

/-- Real Laplace transform of a positive measure. -/
def finiteRealLaplace (tau : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ r : ℝ, Real.exp (-t * r) ∂tau

theorem integrable_finiteRealLaplace_differenceKernel
    (tau : Measure ℝ) [IsFiniteMeasure tau] (htau : tau (Ici (0 : ℝ))ᶜ = 0)
    {t delta : ℝ} (ht : 0 < t) (hdelta : 0 < delta) (k : ℕ) :
    Integrable (fun r : ℝ =>
      Real.exp (-t * r) * (Real.exp (-delta * r) - 1) ^ k) tau := by
  have hae : ∀ᵐ r ∂tau, r ∈ Ici (0 : ℝ) := ae_iff.mpr htau
  refine Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop) ?_
  filter_upwards [hae] with r hr
  have htr : 0 ≤ t * r := mul_nonneg ht.le hr
  have hdr : 0 ≤ delta * r := mul_nonneg hdelta.le hr
  have he1 : Real.exp (-t * r) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have he2 : Real.exp (-delta * r) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have habs : |Real.exp (-delta * r) - 1| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr he2)]
    linarith [Real.exp_pos (-delta * r)]
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  exact mul_le_one₀ he1 (pow_nonneg (abs_nonneg _) _)
    (pow_le_one₀ (abs_nonneg _) habs)

/-- Exact finite-difference kernel identity for a finite positive Laplace transform. -/
theorem fwdDiff_iter_finiteRealLaplace
    (tau : Measure ℝ) [IsFiniteMeasure tau] (htau : tau (Ici (0 : ℝ))ᶜ = 0)
    {delta : ℝ} (hdelta : 0 < delta) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    (fwdDiff delta)^[k] (finiteRealLaplace tau) t =
      ∫ r : ℝ, Real.exp (-t * r) * (Real.exp (-delta * r) - 1) ^ k ∂tau := by
  induction k generalizing t with
  | zero =>
      simp [finiteRealLaplace]
  | succ k ih =>
      rw [Function.iterate_succ_apply', fwdDiff, ih (by linarith), ih ht]
      rw [← integral_sub
        (integrable_finiteRealLaplace_differenceKernel tau htau (by linarith) hdelta k)
        (integrable_finiteRealLaplace_differenceKernel tau htau ht hdelta k)]
      apply integral_congr_ae
      filter_upwards with r
      have hexp : Real.exp (-(t + delta) * r) =
          Real.exp (-t * r) * Real.exp (-delta * r) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp, pow_succ]
      ring

/-- Every finite positive half-line Laplace transform is completely monotone in finite-difference
form. -/
theorem completelyMonotoneDiff_finiteRealLaplace
    (tau : Measure ℝ) [IsFiniteMeasure tau] (htau : tau (Ici (0 : ℝ))ᶜ = 0) :
    CompletelyMonotoneDiff (finiteRealLaplace tau) := by
  intro k delta hdelta t ht
  rw [fwdDiff_iter_finiteRealLaplace tau htau hdelta k ht]
  rw [← integral_const_mul]
  apply integral_nonneg_of_ae
  have hae : ∀ᵐ r ∂tau, r ∈ Ici (0 : ℝ) := ae_iff.mpr htau
  filter_upwards [hae] with r hr
  have hdr : 0 ≤ delta * r := mul_nonneg hdelta.le hr
  have he : Real.exp (-delta * r) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hpow : 0 ≤ (1 - Real.exp (-delta * r)) ^ k := pow_nonneg (sub_nonneg.mpr he) _
  have hsign : (-1 : ℝ) ^ k * (Real.exp (-delta * r) - 1) ^ k =
      (1 - Real.exp (-delta * r)) ^ k := by
    rw [← mul_pow]
    congr 1
    ring
  change 0 ≤ (-1 : ℝ) ^ k *
    (Real.exp (-t * r) * (Real.exp (-delta * r) - 1) ^ k)
  rw [show (-1 : ℝ) ^ k *
      (Real.exp (-t * r) * (Real.exp (-delta * r) - 1) ^ k) =
      Real.exp (-t * r) *
        ((-1 : ℝ) ^ k * (Real.exp (-delta * r) - 1) ^ k) by ring,
    hsign]
  exact mul_nonneg (Real.exp_pos _).le hpow

/-- A finite positive half-line Laplace transform is continuous on the closed right half-line. -/
theorem continuousOn_finiteRealLaplace
    (tau : Measure ℝ) [IsFiniteMeasure tau] (htau : tau (Ici (0 : ℝ))ᶜ = 0) :
    ContinuousOn (finiteRealLaplace tau) (Ici 0) := by
  intro t ht
  have hae : ∀ᵐ r ∂tau, r ∈ Ici (0 : ℝ) := ae_iff.mpr htau
  unfold finiteRealLaplace
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_
      (integrable_const 1) ?_
  · filter_upwards with s
    fun_prop
  · filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards [hae] with r hr
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hr0 : 0 ≤ r := hr
    exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hs hr0])
  · filter_upwards with r
    have hc : Continuous (fun s : ℝ => Real.exp (-s * r)) := by fun_prop
    exact (hc.tendsto t).mono_left inf_le_left

/-- At zero, a finite positive Laplace transform tends to total mass. -/
theorem tendsto_finiteRealLaplace_nhdsGT_zero
    (tau : Measure ℝ) [IsFiniteMeasure tau] (htau : tau (Ici (0 : ℝ))ᶜ = 0) :
    Tendsto (finiteRealLaplace tau) (nhdsWithin (0 : ℝ) (Ioi 0))
      (𝓝 (tau Set.univ).toReal) := by
  have hcont := continuousOn_finiteRealLaplace tau htau 0 (by simp)
  have htend := hcont.mono Ioi_subset_Ici_self
  have htend' : Tendsto (finiteRealLaplace tau) (nhdsWithin (0 : ℝ) (Ioi 0))
      (𝓝 (finiteRealLaplace tau 0)) := htend
  convert htend' using 1
  simp [finiteRealLaplace, integral_const, measureReal_def]

/-- The finite positive Laplace cone is exactly inside the continuous completely monotone cone. -/
theorem completelyMonotoneOn_finiteRealLaplace
    (tau : Measure ℝ) [IsFiniteMeasure tau] (htau : tau (Ici (0 : ℝ))ᶜ = 0) :
    CompletelyMonotoneOn (finiteRealLaplace tau) := by
  exact ⟨completelyMonotoneDiff_finiteRealLaplace tau htau,
    (continuousOn_finiteRealLaplace tau htau).mono Ioi_subset_Ici_self⟩

end

end GaloisForLFunctions.HTGeometry

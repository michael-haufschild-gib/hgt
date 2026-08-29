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
    simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, one_div] using h
  · filter_upwards with n
    exact inv_pos.mpr (by positivity)

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
    simpa only [d, Function.comp_apply, Nat.cast_add, Nat.cast_one] using h
  have hlower : ∀ n : ℕ, t - 1 / d n ≤ s n := by
    intro n
    have hfloor := Nat.lt_floor_add_one (t * d n)
    have hd : 0 < d n := by dsimp [d]; positivity
    have : t < s n + 1 / d n := by
      dsimp [s]
      calc
        t = (t * d n) / d n := by field_simp
        _ < (((⌊t * d n⌋₊ : ℕ) : ℝ) + 1) / d n :=
          (div_lt_div_iff₀ hd).2 hfloor
        _ = ((⌊t * d n⌋₊ : ℕ) : ℝ) / d n + 1 / d n := by ring
    linarith
  have hupper : ∀ n : ℕ, s n ≤ t := by
    intro n
    have hd : 0 < d n := by dsimp [d]; positivity
    dsimp [s]
    rw [div_le_iff₀ hd]
    exact Nat.floor_le (mul_nonneg ht hd.le)
  have hlowerlim : Tendsto (fun n => t - 1 / d n) atTop (𝓝 t) := by
    convert tendsto_const_nhds.sub hmesh using 1 <;> simp
  have hs : Tendsto s atTop (𝓝 t) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowerlim tendsto_const_nhds
      (Eventually.of_forall hlower) (Eventually.of_forall hupper)
  exact hs

end

end GaloisForLFunctions.HTGeometry

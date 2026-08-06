import Mathlib

/-!
# Transport distance of laws on the half line

The `W₁` transport distance between two laws on `[0,∞)` is the `L¹` distance of their survival
functions.  This file builds that distance from the layer-cake formula and proves the convergence
criterion which replaces the general optimal-transport machinery: pointwise convergence of the
survival functions together with convergence of the first moments forces the transport distance to
zero.

The mechanism is an exact algebraic identity rather than a compactness argument.  Writing
`|S - T| = S + T - 2 min S T` and using that the minimum is dominated by the limit survival
function, dominated convergence sends the integral of the minimum to the limit mean, while the two
outer integrals are the two means; the three limits cancel.
-/

open MeasureTheory Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Survival function of a law on the line. -/
def survival (μ : Measure ℝ) (t : ℝ) : ℝ := μ.real (Set.Ioi t)

/-- Transport distance of two laws on the half line: the `L¹` distance of their survival
functions. -/
def halfLineW1 (μ ν : Measure ℝ) : ℝ := ∫ t in Set.Ioi (0 : ℝ), |survival μ t - survival ν t|

theorem survival_nonneg (μ : Measure ℝ) (t : ℝ) : 0 ≤ survival μ t :=
  ENNReal.toReal_nonneg

theorem antitone_survival (μ : Measure ℝ) [IsFiniteMeasure μ] : Antitone (survival μ) := by
  intro s t hst
  exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (Set.Ioi_subset_Ioi hst))

theorem measurable_survival (μ : Measure ℝ) [IsFiniteMeasure μ] : Measurable (survival μ) :=
  (antitone_survival μ).measurable

/-- The layer-cake formula: the mean of a law on the half line is the integral of its survival
function. -/
theorem integral_survival_eq_mean {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hint : Integrable id μ) (hnn : 0 ≤ᵐ[μ] id) :
    ∫ t in Set.Ioi (0 : ℝ), survival μ t = ∫ x, x ∂μ := by
  have hlayer := hint.integral_eq_integral_meas_lt hnn
  have hsets : ∀ t : ℝ, {a : ℝ | t < id a} = Set.Ioi t := fun t => rfl
  simp only [hsets] at hlayer
  have hmean : ∫ x, x ∂μ = ∫ t in Set.Ioi (0 : ℝ), survival μ t := by
    simpa [survival, id] using hlayer
  exact hmean.symm

/-- The survival function of a law with finite mean is integrable on the half line. -/
theorem integrableOn_survival {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hint : Integrable id μ) (hnn : 0 ≤ᵐ[μ] id) :
    IntegrableOn (survival μ) (Set.Ioi (0 : ℝ)) := by
  have hmeas : AEStronglyMeasurable (survival μ) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (measurable_survival μ).aestronglyMeasurable
  have hlayer := lintegral_eq_lintegral_meas_lt μ hnn hint.aemeasurable
  have hsets : ∀ t : ℝ, {a : ℝ | t < id a} = Set.Ioi t := fun t => rfl
  simp only [hsets] at hlayer
  have hfinite : ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (survival μ t) < ⊤ := by
    have hcongr : ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (survival μ t)
        = ∫⁻ t in Set.Ioi (0 : ℝ), μ (Set.Ioi t) := by
      refine lintegral_congr fun t => ?_
      simp only [survival, Measure.real]
      exact ENNReal.ofReal_toReal (measure_ne_top μ _)
    rw [hcongr, ← hlayer]
    exact hint.lintegral_lt_top
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun t => survival_nonneg μ t)]
  exact hfinite

/-- The pointwise algebraic identity behind the transport-distance cancellation. -/
theorem abs_sub_eq_add_sub_two_min (a b : ℝ) : |a - b| = a + b - 2 * min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]
    ring

/-- **Transport convergence from survival convergence and first moments.**  If the survival
functions converge pointwise on the half line and the first moments converge, the half-line
transport distance tends to zero. -/
theorem tendsto_halfLineW1_of_tendsto_survival {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] (μ : ι → Measure ℝ) (ν : Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [IsFiniteMeasure ν]
    (hint : ∀ i, Integrable id (μ i)) (hnn : ∀ i, 0 ≤ᵐ[μ i] id)
    (hintν : Integrable id ν) (hnnν : 0 ≤ᵐ[ν] id)
    (hsurv : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      Tendsto (fun i => survival (μ i) t) l (𝓝 (survival ν t)))
    (hmean : Tendsto (fun i => ∫ x, x ∂(μ i)) l (𝓝 (∫ x, x ∂ν))) :
    Tendsto (fun i => halfLineW1 (μ i) ν) l (𝓝 0) := by
  set m : ℝ := ∫ x, x ∂ν with hm
  have hνint : IntegrableOn (survival ν) (Set.Ioi (0 : ℝ)) := integrableOn_survival hintν hnnν
  have hμint : ∀ i, IntegrableOn (survival (μ i)) (Set.Ioi (0 : ℝ)) :=
    fun i => integrableOn_survival (hint i) (hnn i)
  -- the integral of the pointwise minimum tends to the limit mean
  have hminInt : ∀ i, IntegrableOn (fun t => min (survival (μ i) t) (survival ν t))
      (Set.Ioi (0 : ℝ)) := by
    intro i
    refine Integrable.mono hνint
      ((measurable_survival (μ i)).min (measurable_survival ν)).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun t => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (le_min (survival_nonneg _ t) (survival_nonneg _ t)),
      abs_of_nonneg (survival_nonneg _ t)]
    exact min_le_right _ _
  have hminTendsto : Tendsto
      (fun i => ∫ t in Set.Ioi (0 : ℝ), min (survival (μ i) t) (survival ν t)) l (𝓝 m) := by
    have hlim : ∫ t in Set.Ioi (0 : ℝ), survival ν t = m := integral_survival_eq_mean hintν hnnν
    rw [← hlim]
    refine tendsto_integral_filter_of_dominated_convergence (survival ν) ?_ ?_ hνint ?_
    · exact Filter.Eventually.of_forall fun i =>
        ((measurable_survival (μ i)).min (measurable_survival ν)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun i => Filter.Eventually.of_forall fun t => ?_
      rw [Real.norm_eq_abs,
        abs_of_nonneg (le_min (survival_nonneg _ t) (survival_nonneg _ t))]
      exact min_le_right _ _
    · filter_upwards [hsurv] with t ht
      have hmin := ht.min (tendsto_const_nhds (x := survival ν t))
      simpa using hmin
  -- assemble the three integrals
  have hsplit : ∀ i, halfLineW1 (μ i) ν
      = (∫ t in Set.Ioi (0 : ℝ), survival (μ i) t) + (∫ t in Set.Ioi (0 : ℝ), survival ν t)
        - 2 * ∫ t in Set.Ioi (0 : ℝ), min (survival (μ i) t) (survival ν t) := by
    intro i
    have hcongr : halfLineW1 (μ i) ν
        = ∫ t in Set.Ioi (0 : ℝ),
            (survival (μ i) t + survival ν t - 2 * min (survival (μ i) t) (survival ν t)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      exact abs_sub_eq_add_sub_two_min _ _
    rw [hcongr, integral_sub (by exact (hμint i).add hνint) (by exact (hminInt i).const_mul 2),
      integral_add (hμint i) hνint, integral_const_mul]
  have hfinal : Tendsto (fun i => (∫ t in Set.Ioi (0 : ℝ), survival (μ i) t)
      + (∫ t in Set.Ioi (0 : ℝ), survival ν t)
      - 2 * ∫ t in Set.Ioi (0 : ℝ), min (survival (μ i) t) (survival ν t)) l (𝓝 0) := by
    have h1 : Tendsto (fun i => ∫ t in Set.Ioi (0 : ℝ), survival (μ i) t) l (𝓝 m) := by
      refine hmean.congr fun i => ?_
      exact (integral_survival_eq_mean (hint i) (hnn i)).symm
    have h2 : ∫ t in Set.Ioi (0 : ℝ), survival ν t = m := integral_survival_eq_mean hintν hnnν
    have hlim := (h1.add (tendsto_const_nhds (x := m))).sub (hminTendsto.const_mul 2)
    have harith : m + m - 2 * m = (0 : ℝ) := by ring
    rw [harith] at hlim
    simpa [h2] using hlim
  exact (hfinal.congr fun i => (hsplit i).symm)

/-- The half-line transport distance is symmetric. -/
theorem halfLineW1_symm (μ ν : Measure ℝ) : halfLineW1 μ ν = halfLineW1 ν μ :=
  integral_congr_ae (Filter.Eventually.of_forall fun _ => abs_sub_comm _ _)

/-- The half-line transport distance is nonnegative. -/
theorem halfLineW1_nonneg (μ ν : Measure ℝ) : 0 ≤ halfLineW1 μ ν :=
  setIntegral_nonneg measurableSet_Ioi fun _ _ => abs_nonneg _

/-- The half-line transport distance obeys the triangle inequality. -/
theorem halfLineW1_triangle {μ ν ρ : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure ρ]
    (hμ : IntegrableOn (survival μ) (Set.Ioi (0 : ℝ)))
    (hν : IntegrableOn (survival ν) (Set.Ioi (0 : ℝ)))
    (hρ : IntegrableOn (survival ρ) (Set.Ioi (0 : ℝ))) :
    halfLineW1 μ ρ ≤ halfLineW1 μ ν + halfLineW1 ν ρ := by
  have hint1 : IntegrableOn (fun t => |survival μ t - survival ν t|) (Set.Ioi (0 : ℝ)) :=
    (hμ.sub hν).abs
  have hint2 : IntegrableOn (fun t => |survival ν t - survival ρ t|) (Set.Ioi (0 : ℝ)) :=
    (hν.sub hρ).abs
  have hint3 : IntegrableOn (fun t => |survival μ t - survival ρ t|) (Set.Ioi (0 : ℝ)) :=
    (hμ.sub hρ).abs
  rw [halfLineW1, halfLineW1, halfLineW1, ← integral_add hint1 hint2]
  refine integral_mono hint3 (hint1.add hint2) fun t => ?_
  simpa using abs_sub_le (survival μ t) (survival ν t) (survival ρ t)

/-- **Mutual transport convergence.**  Two families of half-line laws whose survival functions and
first moments converge to those of one common limit law have vanishing mutual transport
distance. -/
theorem tendsto_halfLineW1_pair {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (μ κ : ι → Measure ℝ) (ν : Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, IsFiniteMeasure (κ i)] [IsFiniteMeasure ν]
    (hintμ : ∀ i, Integrable id (μ i)) (hnnμ : ∀ i, 0 ≤ᵐ[μ i] id)
    (hintκ : ∀ i, Integrable id (κ i)) (hnnκ : ∀ i, 0 ≤ᵐ[κ i] id)
    (hintν : Integrable id ν) (hnnν : 0 ≤ᵐ[ν] id)
    (hsurvμ : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      Tendsto (fun i => survival (μ i) t) l (𝓝 (survival ν t)))
    (hsurvκ : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      Tendsto (fun i => survival (κ i) t) l (𝓝 (survival ν t)))
    (hmeanμ : Tendsto (fun i => ∫ x, x ∂(μ i)) l (𝓝 (∫ x, x ∂ν)))
    (hmeanκ : Tendsto (fun i => ∫ x, x ∂(κ i)) l (𝓝 (∫ x, x ∂ν))) :
    Tendsto (fun i => halfLineW1 (μ i) (κ i)) l (𝓝 0) := by
  have hμν := tendsto_halfLineW1_of_tendsto_survival μ ν hintμ hnnμ hintν hnnν hsurvμ hmeanμ
  have hκν := tendsto_halfLineW1_of_tendsto_survival κ ν hintκ hnnκ hintν hnnν hsurvκ hmeanκ
  have hsymm : ∀ i, halfLineW1 ν (κ i) = halfLineW1 (κ i) ν := by
    intro i
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    exact abs_sub_comm _ _
  have hbound : ∀ i, halfLineW1 (μ i) (κ i) ≤ halfLineW1 (μ i) ν + halfLineW1 (κ i) ν := by
    intro i
    have := halfLineW1_triangle (μ := μ i) (ν := ν) (ρ := κ i)
      (integrableOn_survival (hintμ i) (hnnμ i)) (integrableOn_survival hintν hnnν)
      (integrableOn_survival (hintκ i) (hnnκ i))
    rw [hsymm i] at this
    exact this
  have hnonneg : ∀ i, 0 ≤ halfLineW1 (μ i) (κ i) := fun i =>
    integral_nonneg fun t => abs_nonneg _
  refine squeeze_zero hnonneg hbound ?_
  simpa using hμν.add hκν

open ProbabilityTheory in
/-- The survival function is the complement of the distribution function. -/
theorem survival_eq_one_sub_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    survival μ t = 1 - cdf μ t := by
  have hcompl : μ (Set.Iic t) + μ (Set.Ioi t) = 1 := by
    rw [← measure_univ (μ := μ), ← Set.Iic_union_Ioi (a := t)]
    exact (measure_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi).symm
  have hreal : (μ (Set.Iic t)).toReal + (μ (Set.Ioi t)).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hcompl]
    simp
  rw [survival, cdf_eq_real, Measure.real, Measure.real]
  linarith

open ProbabilityTheory in
/-- The mean-one exponential law has survival function `exp (-t)` on the half line. -/
theorem survival_expMeasure_one {t : ℝ} (ht : 0 ≤ t) :
    survival (expMeasure 1) t = Real.exp (-t) := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  rw [survival_eq_one_sub_cdf, cdf_expMeasure_eq one_pos, if_pos ht]
  simp

open ProbabilityTheory in
/-- The mean-one exponential law is carried by the half line. -/
theorem expMeasure_one_nonneg_ae : 0 ≤ᵐ[expMeasure 1] (id : ℝ → ℝ) := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have hIic : (expMeasure 1) (Set.Iic (0 : ℝ)) = 0 := by
    have hcdf : cdf (expMeasure 1) 0 = 0 := by
      rw [cdf_expMeasure_eq one_pos, if_pos le_rfl]
      simp
    rw [cdf_eq_real, Measure.real] at hcdf
    exact ((ENNReal.toReal_eq_zero_iff _).mp hcdf).resolve_right (measure_ne_top _ _)
  refine MeasureTheory.ae_iff.mpr ?_
  refine measure_mono_null (fun x hx => ?_) hIic
  simp only [Pi.zero_apply, id_eq, Set.mem_setOf_eq, not_le] at hx
  exact le_of_lt hx

open ProbabilityTheory in
/-- The identity is integrable for the mean-one exponential law. -/
theorem integrable_id_expMeasure_one : Integrable (id : ℝ → ℝ) (expMeasure 1) := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal expMeasure_one_nonneg_ae]
  have hlayer := lintegral_eq_lintegral_meas_lt (expMeasure 1) expMeasure_one_nonneg_ae
    measurable_id.aemeasurable
  have hsets : ∀ t : ℝ, {a : ℝ | t < id a} = Set.Ioi t := fun t => rfl
  simp only [hsets] at hlayer
  rw [hlayer]
  have hcongr : ∫⁻ t in Set.Ioi (0 : ℝ), (expMeasure 1) (Set.Ioi t)
      = ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t)) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have hsurv := survival_expMeasure_one (le_of_lt ht)
    rw [survival, Measure.real] at hsurv
    rw [← hsurv, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hcongr, ← ofReal_integral_eq_lintegral_ofReal (exp_neg_integrableOn_Ioi 0 one_pos |>.congr_fun
      (fun t _ => by simp) measurableSet_Ioi)
    (Filter.Eventually.of_forall fun t => (Real.exp_pos _).le)]
  exact ENNReal.ofReal_lt_top

open ProbabilityTheory in
/-- The mean-one exponential law has mean one. -/
theorem integral_id_expMeasure_one : ∫ x, x ∂(expMeasure 1) = 1 := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  rw [← integral_survival_eq_mean integrable_id_expMeasure_one expMeasure_one_nonneg_ae]
  rw [setIntegral_congr_fun measurableSet_Ioi
    (g := fun t => Real.exp (-t)) fun t ht => survival_expMeasure_one (le_of_lt ht)]
  exact integral_exp_neg_Ioi_zero

end

end GaloisForLFunctions.HTGeometry

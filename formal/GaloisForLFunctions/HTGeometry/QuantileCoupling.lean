import GaloisForLFunctions.HTGeometry.HalfLineTransportDistance

/-!
# The quantile function and the monotone coupling

The generalized inverse of a distribution function transports the uniform law on `(0,1)` to the
law itself.  Applying two such inverses to one uniform variable produces the monotone coupling of
two laws, whose transport cost is the `L¹` distance of the two quantile functions.

Mathlib carries the distribution function but neither the quantile function nor inverse-transform
sampling, so both are built here.  The key step is the Galois connection

`quantile μ p ≤ x ↔ p ≤ cdf μ x`   for `0 < p < 1`,

which holds because the set `{x | p ≤ cdf μ x}` is an up-set that contains its infimum: right
continuity of the distribution function passes the inequality to the boundary.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The quantile, or generalized inverse distribution, function of a law on the line. -/
def quantile (μ : Measure ℝ) (p : ℝ) : ℝ := sInf {x : ℝ | p ≤ cdf μ x}

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem quantileSet_nonempty {p : ℝ} (hp : p < 1) : {x : ℝ | p ≤ cdf μ x}.Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop μ).eventually (eventually_gt_nhds hp)).exists
  exact ⟨x, hx.le⟩

omit [IsProbabilityMeasure μ] in
theorem quantileSet_bddBelow {p : ℝ} (hp : 0 < p) : BddBelow {x : ℝ | p ≤ cdf μ x} := by
  have h := (tendsto_cdf_atBot μ).eventually (eventually_lt_nhds hp)
  rw [eventually_atBot] at h
  obtain ⟨b, hb⟩ := h
  refine ⟨b, fun x hx => ?_⟩
  by_contra hcon
  exact absurd hx (not_le.mpr (hb x (not_le.mp hcon).le))

omit [IsProbabilityMeasure μ] in
/-- The defining set of the quantile contains its own infimum: right continuity of the
distribution function passes the inequality to the boundary. -/
theorem le_cdf_quantile {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : p ≤ cdf μ (quantile μ p) := by
  have hne := quantileSet_nonempty (μ := μ) hp1
  have hbdd := quantileSet_bddBelow (μ := μ) hp0
  have habove : ∀ y ∈ Ioi (quantile μ p), p ≤ cdf μ y := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := exists_lt_of_csInf_lt hne hy
    exact le_trans hz ((cdf μ).mono hzy.le)
  have hcont : Tendsto (cdf μ) (𝓝[>] (quantile μ p)) (𝓝 (cdf μ (quantile μ p))) := by
    refine Tendsto.mono_left ((cdf μ).right_continuous (quantile μ p)) ?_
    exact nhdsWithin_mono _ Ioi_subset_Ici_self
  refine ge_of_tendsto hcont ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact habove y hy

omit [IsProbabilityMeasure μ] in
/-- **The quantile Galois connection.** -/
theorem quantile_le_iff {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {x : ℝ} :
    quantile μ p ≤ x ↔ p ≤ cdf μ x := by
  constructor
  · intro h
    exact le_trans (le_cdf_quantile hp0 hp1) ((cdf μ).mono h)
  · intro h
    exact csInf_le (quantileSet_bddBelow hp0) h

omit [IsProbabilityMeasure μ] in
theorem quantile_of_nonpos {p : ℝ} (hp : p ≤ 0) : quantile μ p = 0 := by
  have huniv : {x : ℝ | p ≤ cdf μ x} = univ := by
    ext x
    simp only [mem_setOf_eq, mem_univ, iff_true]
    exact le_trans hp (cdf_nonneg μ x)
  rw [quantile, huniv]
  refine Real.sInf_of_not_bddBelow ?_
  intro hbdd
  obtain ⟨b, hb⟩ := hbdd
  exact absurd (hb (mem_univ (b - 1))) (by linarith)

omit [IsProbabilityMeasure μ] in
theorem quantile_of_one_lt {p : ℝ} (hp : 1 < p) : quantile μ p = 0 := by
  have hempty : {x : ℝ | p ≤ cdf μ x} = ∅ := by
    ext x
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
    exact lt_of_le_of_lt (cdf_le_one μ x) hp
  rw [quantile, hempty, Real.sInf_empty]

theorem measurable_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measurable (quantile μ) := by
  refine measurable_of_Iic (f := quantile μ) fun x => ?_
  have key : quantile μ ⁻¹' Iic x
      = (Ioo 0 1 ∩ Iic (cdf μ x))
        ∪ {p : ℝ | (p ≤ 0 ∨ 1 < p) ∧ (0 : ℝ) ≤ x}
        ∪ ({(1 : ℝ)} ∩ quantile μ ⁻¹' Iic x) := by
    ext p
    simp only [mem_preimage, mem_Iic, mem_union, mem_inter_iff, mem_Ioo, mem_setOf_eq,
      mem_singleton_iff]
    constructor
    · intro hp
      rcases le_or_gt p 0 with h0 | h0
      · exact Or.inl (Or.inr ⟨Or.inl h0, by rwa [quantile_of_nonpos h0] at hp⟩)
      · rcases lt_or_ge p 1 with h1 | h1
        · exact Or.inl (Or.inl ⟨⟨h0, h1⟩, (quantile_le_iff h0 h1).mp hp⟩)

        · rcases eq_or_lt_of_le h1 with h1' | h1'
          · exact Or.inr ⟨h1'.symm, hp⟩
          · exact Or.inl (Or.inr ⟨Or.inr h1', by rwa [quantile_of_one_lt h1'] at hp⟩)
    · rintro ((⟨⟨h0, h1⟩, hcdf⟩ | ⟨hcase, hx⟩) | ⟨rfl, hp⟩)
      · exact (quantile_le_iff h0 h1).mpr hcdf
      · rcases hcase with h | h
        · rwa [quantile_of_nonpos h]
        · rwa [quantile_of_one_lt h]
      · exact hp
  rw [key]
  refine MeasurableSet.union (MeasurableSet.union ?_ ?_) ?_
  · exact measurableSet_Ioo.inter measurableSet_Iic
  · by_cases hx : (0 : ℝ) ≤ x
    · have hEq : {p : ℝ | (p ≤ 0 ∨ 1 < p) ∧ (0 : ℝ) ≤ x} = Iic (0 : ℝ) ∪ Ioi (1 : ℝ) := by
        ext p
        simp [hx]
      rw [hEq]
      exact measurableSet_Iic.union measurableSet_Ioi
    · have hEq : {p : ℝ | (p ≤ 0 ∨ 1 < p) ∧ (0 : ℝ) ≤ x} = (∅ : Set ℝ) := by
        ext p
        simp [hx]
      rw [hEq]
      exact MeasurableSet.empty
  · exact ((finite_singleton (1 : ℝ)).subset inter_subset_left).measurableSet

/-- **Inverse transform sampling.**  The quantile function pushes the uniform law on `(0,1)` to the
law itself. -/
theorem map_quantile_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measure.map (quantile μ) (volume.restrict (Ioo (0 : ℝ) 1)) = μ := by
  refine (Measure.ext_of_Iic _ _ fun x => ?_).symm
  rw [Measure.map_apply (measurable_quantile μ) measurableSet_Iic,
    Measure.restrict_apply ((measurable_quantile μ) measurableSet_Iic)]
  have hset : quantile μ ⁻¹' Iic x ∩ Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) 1 ∩ Iic (cdf μ x) := by
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioo]
    constructor
    · rintro ⟨hq, h0, h1⟩
      exact ⟨⟨h0, h1⟩, (quantile_le_iff h0 h1).mp hq⟩
    · rintro ⟨⟨h0, h1⟩, hcdf⟩
      exact ⟨(quantile_le_iff h0 h1).mpr hcdf, h0, h1⟩
  rw [hset]
  have hcdf1 : cdf μ x ≤ 1 := cdf_le_one μ x
  have hsub1 : Ioo (0 : ℝ) (cdf μ x) ⊆ Ioo (0 : ℝ) 1 ∩ Iic (cdf μ x) := fun p hp =>
    ⟨⟨hp.1, lt_of_lt_of_le hp.2 hcdf1⟩, hp.2.le⟩
  have hsub2 : Ioo (0 : ℝ) 1 ∩ Iic (cdf μ x) ⊆ Ioc (0 : ℝ) (cdf μ x) := fun p hp =>
    ⟨hp.1.1, hp.2⟩
  have hvol : volume (Ioo (0 : ℝ) 1 ∩ Iic (cdf μ x)) = ENNReal.ofReal (cdf μ x) := by
    refine le_antisymm ?_ ?_
    · have h := measure_mono (μ := (volume : Measure ℝ)) hsub2
      rwa [Real.volume_Ioc, sub_zero] at h
    · have h := measure_mono (μ := (volume : Measure ℝ)) hsub1
      rwa [Real.volume_Ioo, sub_zero] at h
  rw [hvol, cdf_eq_real, Measure.real, ENNReal.ofReal_toReal (measure_ne_top μ _)]

/-- The monotone coupling of two laws: the joint law of their two quantile functions evaluated at
one uniform variable. -/
def monotoneCoupling (μ ν : Measure ℝ) : Measure (ℝ × ℝ) :=
  Measure.map (fun p => (quantile μ p, quantile ν p)) (volume.restrict (Ioo (0 : ℝ) 1))

theorem measurable_quantilePair (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    Measurable fun p => (quantile μ p, quantile ν p) :=
  (measurable_quantile μ).prodMk (measurable_quantile ν)

/-- The first marginal of the monotone coupling is the first law. -/
theorem map_fst_monotoneCoupling (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    Measure.map Prod.fst (monotoneCoupling μ ν) = μ := by
  rw [monotoneCoupling, Measure.map_map measurable_fst (measurable_quantilePair μ ν)]
  exact map_quantile_eq μ

/-- The second marginal of the monotone coupling is the second law. -/
theorem map_snd_monotoneCoupling (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    Measure.map Prod.snd (monotoneCoupling μ ν) = ν := by
  rw [monotoneCoupling, Measure.map_map measurable_snd (measurable_quantilePair μ ν)]
  exact map_quantile_eq ν

/-- **Transport cost of the monotone coupling.**  It is the `L¹` distance of the two quantile
functions. -/
theorem lintegral_dist_monotoneCoupling (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    (∫⁻ z, ENNReal.ofReal |z.1 - z.2| ∂(monotoneCoupling μ ν))
      = ∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal |quantile μ p - quantile ν p| := by
  rw [monotoneCoupling, lintegral_map ?_ (measurable_quantilePair μ ν)]
  exact (measurable_fst.sub measurable_snd).abs.ennreal_ofReal

/-- The mean of a law is the integral of its quantile function over `(0,1)`. -/
theorem integral_quantile_eq_mean (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∫ p in Ioo (0 : ℝ) 1, quantile μ p = ∫ x, x ∂μ := by
  have h : ∫ (y : ℝ), y ∂(Measure.map (quantile μ) (volume.restrict (Ioo (0 : ℝ) 1)))
      = ∫ p, quantile μ p ∂(volume.restrict (Ioo (0 : ℝ) 1)) :=
    integral_map (measurable_quantile μ).aemeasurable measurable_id.aestronglyMeasurable
  rw [map_quantile_eq μ] at h
  exact h.symm

/-- **Transport cost of the monotone coupling**, in real-integral form. -/
theorem integral_monotoneCoupling_abs_sub (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    (∫ z, |z.1 - z.2| ∂(monotoneCoupling μ ν))
      = ∫ p in Ioo (0 : ℝ) 1, |quantile μ p - quantile ν p| := by
  have h : ∫ (z : ℝ × ℝ), |z.1 - z.2| ∂(Measure.map (fun p => (quantile μ p, quantile ν p))
        (volume.restrict (Ioo (0 : ℝ) 1)))
      = ∫ p, |quantile μ p - quantile ν p| ∂(volume.restrict (Ioo (0 : ℝ) 1)) :=
    integral_map (measurable_quantilePair μ ν).aemeasurable
      (measurable_fst.sub measurable_snd).abs.aestronglyMeasurable
  rw [monotoneCoupling]
  exact h

/-- **Scheffé cancellation.**  Nonnegative integrands converging almost everywhere with converging
integrals converge in `L¹`.  The proof is the pointwise identity `|a - b| = a + b - 2 min a b`
together with dominated convergence for the minimum. -/
theorem tendsto_integral_abs_sub_of_tendsto {α : Type*} [MeasurableSpace α] {m : Measure α}
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {f : ι → α → ℝ} {g : α → ℝ}
    (hfi : ∀ i, Integrable (f i) m) (hgi : Integrable g m)
    (hfnn : ∀ i, 0 ≤ᵐ[m] f i) (hgnn : 0 ≤ᵐ[m] g)
    (hae : ∀ᵐ x ∂m, Tendsto (fun i => f i x) l (𝓝 (g x)))
    (hint : Tendsto (fun i => ∫ x, f i x ∂m) l (𝓝 (∫ x, g x ∂m))) :
    Tendsto (fun i => ∫ x, |f i x - g x| ∂m) l (𝓝 0) := by
  have hminInt : ∀ i, Integrable (fun x => min (f i x) (g x)) m := by
    intro i
    refine hgi.mono (((hfi i).aemeasurable.min hgi.aemeasurable).aestronglyMeasurable) ?_
    filter_upwards [hfnn i, hgnn] with x hx hgx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_min hx hgx), abs_of_nonneg hgx]
    exact min_le_right _ _
  have hminTendsto : Tendsto (fun i => ∫ x, min (f i x) (g x) ∂m) l (𝓝 (∫ x, g x ∂m)) := by
    refine tendsto_integral_filter_of_dominated_convergence g ?_ ?_ hgi ?_
    · exact Filter.Eventually.of_forall fun i =>
        ((hfi i).aemeasurable.min hgi.aemeasurable).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun i => ?_
      filter_upwards [hfnn i, hgnn] with x hx hgx
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min hx hgx)]
      exact min_le_right _ _
    · filter_upwards [hae] with x hx
      have hmin := hx.min (tendsto_const_nhds (x := g x))
      simpa using hmin
  have hsplit : ∀ i, ∫ x, |f i x - g x| ∂m
      = (∫ x, f i x ∂m) + (∫ x, g x ∂m) - 2 * ∫ x, min (f i x) (g x) ∂m := by
    intro i
    calc ∫ x, |f i x - g x| ∂m
        = ∫ x, (f i x + g x - 2 * min (f i x) (g x)) ∂m :=
          integral_congr_ae (Filter.Eventually.of_forall fun x =>
            abs_sub_eq_add_sub_two_min (f i x) (g x))
      _ = (∫ x, (f i x + g x) ∂m) - ∫ x, 2 * min (f i x) (g x) ∂m :=
          integral_sub ((hfi i).add hgi) ((hminInt i).const_mul 2)
      _ = (∫ x, f i x ∂m) + (∫ x, g x ∂m) - 2 * ∫ x, min (f i x) (g x) ∂m := by
          rw [integral_add (hfi i) hgi, integral_const_mul]
  have hlim := (hint.add (tendsto_const_nhds (x := ∫ x, g x ∂m))).sub (hminTendsto.const_mul 2)
  have harith : (∫ x, g x ∂m) + (∫ x, g x ∂m) - 2 * ∫ x, g x ∂m = (0 : ℝ) := by ring
  rw [harith] at hlim
  exact hlim.congr fun i => (hsplit i).symm

/-- The quantile of a law carried by the half line is nonnegative. -/
theorem quantile_nonneg {μ : Measure ℝ} [IsProbabilityMeasure μ] (hsupp : μ (Iio 0) = 0)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 ≤ quantile μ p := by
  refine le_csInf (quantileSet_nonempty (μ := μ) hp1) ?_
  intro x hx
  by_contra hcon
  have hx0 : x < 0 := not_le.mp hcon
  have hzero : cdf μ x = 0 := by
    have hle : μ (Iic x) ≤ μ (Iio 0) := measure_mono fun y hy => lt_of_le_of_lt hy hx0
    rw [hsupp] at hle
    rw [cdf_eq_real, Measure.real, le_antisymm hle zero_le]
    simp
  rw [mem_setOf_eq, hzero] at hx
  exact absurd hx (not_le.mpr hp0)

/-- A law with finite mean has an integrable quantile function. -/
theorem integrableOn_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (id : ℝ → ℝ) μ) : IntegrableOn (quantile μ) (Ioo (0 : ℝ) 1) := by
  have hmap : Integrable (id : ℝ → ℝ)
      (Measure.map (quantile μ) (volume.restrict (Ioo (0 : ℝ) 1))) := by
    rwa [map_quantile_eq μ]
  exact (integrable_map_measure measurable_id.aestronglyMeasurable
    (measurable_quantile μ).aemeasurable).mp hmap

/-- **Vanishing monotone-coupling cost.**  If the quantile functions converge almost everywhere on
`(0,1)` and the means converge, the transport cost of the monotone coupling tends to zero.  This is
the criterion the critical two-clock transport statement consumes. -/
theorem tendsto_integral_monotoneCoupling_abs_sub {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] (μ : ι → Measure ℝ) (ν : Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [IsProbabilityMeasure ν]
    (hsupp : ∀ i, (μ i) (Iio 0) = 0) (hsuppν : ν (Iio 0) = 0)
    (hint : ∀ i, Integrable (id : ℝ → ℝ) (μ i)) (hintν : Integrable (id : ℝ → ℝ) ν)
    (hae : ∀ᵐ p ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      Tendsto (fun i => quantile (μ i) p) l (𝓝 (quantile ν p)))
    (hmean : Tendsto (fun i => ∫ x, x ∂(μ i)) l (𝓝 (∫ x, x ∂ν))) :
    Tendsto (fun i => ∫ z, |z.1 - z.2| ∂(monotoneCoupling (μ i) ν)) l (𝓝 0) := by
  have hnnν : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] quantile ν :=
    (ae_restrict_iff' measurableSet_Ioo).mpr
      (Filter.Eventually.of_forall fun p hp => quantile_nonneg hsuppν hp.1 hp.2)
  have hnn : ∀ i, 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] quantile (μ i) := fun i =>
    (ae_restrict_iff' measurableSet_Ioo).mpr
      (Filter.Eventually.of_forall fun p hp => quantile_nonneg (hsupp i) hp.1 hp.2)
  have hcost : ∀ i, ∫ z, |z.1 - z.2| ∂(monotoneCoupling (μ i) ν)
      = ∫ p, |quantile (μ i) p - quantile ν p| ∂(volume.restrict (Ioo (0 : ℝ) 1)) :=
    fun i => integral_monotoneCoupling_abs_sub (μ i) ν
  have hmeanQ : Tendsto (fun i => ∫ p, quantile (μ i) p ∂(volume.restrict (Ioo (0 : ℝ) 1))) l
      (𝓝 (∫ p, quantile ν p ∂(volume.restrict (Ioo (0 : ℝ) 1)))) := by
    rw [integral_quantile_eq_mean ν]
    exact hmean.congr fun i => (integral_quantile_eq_mean (μ i)).symm
  exact (tendsto_integral_abs_sub_of_tendsto (fun i => integrableOn_quantile (μ i) (hint i))
    (integrableOn_quantile ν hintν) hnn hnnν hae hmeanQ).congr fun i => (hcost i).symm

/-- **Quantile convergence from distribution convergence.**  At a level where the limit
distribution function is strictly increasing, pointwise convergence of the distribution functions
forces convergence of the quantiles. -/
theorem tendsto_quantile_of_tendsto_cdf {ι : Type*} {l : Filter ι}
    (μ : ι → Measure ℝ) (ν : Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] [IsProbabilityMeasure ν]
    (hcdf : ∀ t : ℝ, Tendsto (fun i => cdf (μ i) t) l (𝓝 (cdf ν t)))
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hlow : ∀ ε : ℝ, 0 < ε → cdf ν (quantile ν p - ε) < p)
    (hhigh : ∀ ε : ℝ, 0 < ε → p < cdf ν (quantile ν p + ε)) :
    Tendsto (fun i => quantile (μ i) p) l (𝓝 (quantile ν p)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hhalf : (0 : ℝ) < ε / 2 := by linarith
  have h1 : ∀ᶠ i in l, cdf (μ i) (quantile ν p - ε / 2) < p :=
    (hcdf (quantile ν p - ε / 2)).eventually (eventually_lt_nhds (hlow (ε / 2) hhalf))
  have h2 : ∀ᶠ i in l, p < cdf (μ i) (quantile ν p + ε / 2) :=
    (hcdf (quantile ν p + ε / 2)).eventually (eventually_gt_nhds (hhigh (ε / 2) hhalf))
  filter_upwards [h1, h2] with i hi1 hi2
  have hupper : quantile (μ i) p ≤ quantile ν p + ε / 2 :=
    (quantile_le_iff hp0 hp1).mpr hi2.le
  have hlower : quantile ν p - ε / 2 < quantile (μ i) p := by
    by_contra hcon
    exact absurd ((quantile_le_iff hp0 hp1).mp (not_lt.mp hcon)) (not_le.mpr hi1)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Below the exponential quantile level the distribution function stays below the level. -/
theorem cdf_expMeasure_one_lt_of_lt {p x : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hx : x < -Real.log (1 - p)) : cdf (expMeasure 1) x < p := by
  have h1p : 0 < 1 - p := by linarith
  rw [cdf_expMeasure_eq one_pos]
  split_ifs with hx0
  · have hlog : Real.log (1 - p) < -x := by linarith
    have hexp : 1 - p < Real.exp (-x) := by
      have := Real.exp_lt_exp.mpr hlog
      rwa [Real.exp_log h1p] at this
    have : Real.exp (-(1 * x)) = Real.exp (-x) := by ring_nf
    rw [this]
    linarith
  · exact hp0

/-- Above the exponential quantile level the distribution function passes the level. -/
theorem lt_cdf_expMeasure_one_of_lt {p x : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hx : -Real.log (1 - p) < x) : p < cdf (expMeasure 1) x := by
  have h1p : 0 < 1 - p := by linarith
  have hlogle : Real.log (1 - p) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hx0 : 0 ≤ x := le_of_lt (lt_of_le_of_lt (by linarith) hx)
  rw [cdf_expMeasure_eq one_pos, if_pos hx0]
  have hlog : -x < Real.log (1 - p) := by linarith
  have hexp : Real.exp (-x) < 1 - p := by
    have := Real.exp_lt_exp.mpr hlog
    rwa [Real.exp_log h1p] at this
  have hrw : Real.exp (-(1 * x)) = Real.exp (-x) := by ring_nf
  rw [hrw]
  linarith

/-- The quantile function of the mean-one exponential law. -/
theorem quantile_expMeasure_one {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    quantile (expMeasure 1) p = -Real.log (1 - p) := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  refine le_antisymm ?_ ?_
  · refine (quantile_le_iff hp0 hp1).mpr ?_
    have h1p : 0 < 1 - p := by linarith
    have hx0 : (0 : ℝ) ≤ -Real.log (1 - p) := by
      have := Real.log_nonpos (by linarith : (0:ℝ) ≤ 1 - p) (by linarith : 1 - p ≤ 1)
      linarith
    rw [cdf_expMeasure_eq one_pos, if_pos hx0]
    have hrw : Real.exp (-(1 * -Real.log (1 - p))) = 1 - p := by
      rw [show -(1 * -Real.log (1 - p)) = Real.log (1 - p) by ring, Real.exp_log h1p]
    rw [hrw]
    linarith
  · by_contra hcon
    have hlt : quantile (expMeasure 1) p < -Real.log (1 - p) := not_le.mp hcon
    exact absurd (le_cdf_quantile hp0 hp1) (not_le.mpr (cdf_expMeasure_one_lt_of_lt hp0 hp1 hlt))

/-- **Quantile convergence to the exponential law.**  Pointwise convergence of the distribution
functions to the mean-one exponential law forces convergence of every quantile. -/
theorem tendsto_quantile_expMeasure_one {ι : Type*} {l : Filter ι}
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hcdf : ∀ t : ℝ, Tendsto (fun i => cdf (μ i) t) l (𝓝 (cdf (expMeasure 1) t)))
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (fun i => quantile (μ i) p) l (𝓝 (quantile (expMeasure 1) p)) := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  refine tendsto_quantile_of_tendsto_cdf μ (expMeasure 1) hcdf hp0 hp1 ?_ ?_
  · intro ε hε
    refine cdf_expMeasure_one_lt_of_lt hp0 hp1 ?_
    rw [quantile_expMeasure_one hp0 hp1]
    linarith
  · intro ε hε
    refine lt_cdf_expMeasure_one_of_lt hp0 hp1 ?_
    rw [quantile_expMeasure_one hp0 hp1]
    linarith

/-- The mean-one exponential law charges no negative half line. -/
theorem expMeasure_one_Iio_zero : (expMeasure 1) (Iio (0 : ℝ)) = 0 := by
  have h := MeasureTheory.ae_iff.mp expMeasure_one_nonneg_ae
  have hset : {x : ℝ | ¬ (0 : ℝ → ℝ) x ≤ (id : ℝ → ℝ) x} = Iio (0 : ℝ) := by
    ext x
    simp
  rwa [hset] at h

/-- **Vanishing critical transport cost against the exponential law.**  Half-line laws whose
distribution functions converge to the mean-one exponential law and whose means converge to one
have monotone couplings with vanishing transport cost. -/
theorem tendsto_integral_monotoneCoupling_expMeasure_one {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hsupp : ∀ i, (μ i) (Iio 0) = 0) (hint : ∀ i, Integrable (id : ℝ → ℝ) (μ i))
    (hcdf : ∀ t : ℝ, Tendsto (fun i => cdf (μ i) t) l (𝓝 (cdf (expMeasure 1) t)))
    (hmean : Tendsto (fun i => ∫ x, x ∂(μ i)) l (𝓝 1)) :
    Tendsto (fun i => ∫ z, |z.1 - z.2| ∂(monotoneCoupling (μ i) (expMeasure 1))) l (𝓝 0) := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  refine tendsto_integral_monotoneCoupling_abs_sub μ (expMeasure 1) hsupp expMeasure_one_Iio_zero
    hint integrable_id_expMeasure_one ?_ ?_
  · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun p hp => ?_)
    exact tendsto_quantile_expMeasure_one μ hcdf hp.1 hp.2
  · rw [integral_id_expMeasure_one]
    exact hmean

end

end GaloisForLFunctions.HTGeometry

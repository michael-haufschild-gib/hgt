import GaloisForLFunctions.HTGeometry.SummableSpectrumScrewRecurrence

/-!
# The limiting value distribution of a summable-spectrum screw line

The invariant law of the relation hull has full support on it: an open set meeting the
hull is translated by hull elements to a finite cover of the hull, and all translates
carry the same mass.

Pushing that law forward along the phase-defect energy produces the limiting
distribution of the screw series. Uniform time sampling converges weakly to it, and its
support is exactly the interval `[0, M]` of cofinally recurrent values. Neither
simplicity of the spectrum nor rational independence of the frequencies is used.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I : Type*} [Countable I]

/-! ## Full support of the invariant law -/

/-- Translation of the invariant law by a hull element preserves every measure. -/
theorem screwHaar_preimage_add {omega : I → ℝ} {z : I → UnitAddCircle}
    (hz : z ∈ screwHull omega) {S : Set (I → UnitAddCircle)} (hS : MeasurableSet S) :
    (screwHaar omega : Measure (I → UnitAddCircle)) {x | x + z ∈ S} =
      (screwHaar omega : Measure (I → UnitAddCircle)) S := by
  have hzann : z ∈ screwAnnihilator omega := by
    rwa [← screwHull_eq_screwAnnihilator omega]
  have hmeas : Measurable (fun x : I → UnitAddCircle => x + z) := by fun_prop
  have hmap := screwHaar_map_add_self hzann
  have := congrArg (fun mu : Measure (I → UnitAddCircle) => mu S) hmap
  rwa [Measure.map_apply hmeas hS] at this

/-- **Full support.** Any open set meeting the relation hull carries positive invariant
mass: finitely many hull translates of it already cover the hull. -/
theorem screwHaar_pos_of_isOpen {omega : I → ℝ} {U : Set (I → UnitAddCircle)}
    (hU : IsOpen U) (hne : (U ∩ screwHull omega).Nonempty) :
    0 < (screwHaar omega : Measure (I → UnitAddCircle)) U := by
  classical
  obtain ⟨x0, hx0U, hx0K⟩ := hne
  set mu : Measure (I → UnitAddCircle) := (screwHaar omega : Measure (I → UnitAddCircle))
  have hcopen : ∀ z : I → UnitAddCircle, IsOpen {x : I → UnitAddCircle | x + z ∈ U} :=
    fun z => hU.preimage (by fun_prop)
  have hcover : screwHull omega ⊆ ⋃ z ∈ screwHull omega, {x : I → UnitAddCircle | x + z ∈ U} := by
    intro k hk
    refine Set.mem_biUnion (sub_mem_screwHull hx0K hk) ?_
    show k + (x0 - k) ∈ U
    rwa [add_sub_cancel]
  obtain ⟨Z, hZsub, hZfin, hZcover⟩ :=
    (isCompact_screwHull omega).elim_finite_subcover_image (fun z _ => hcopen z) hcover
  by_contra hzero
  have hzero' : mu U = 0 := nonpos_iff_eq_zero.mp (le_of_not_gt hzero)
  have hpieces : ∀ z ∈ Z, mu {x : I → UnitAddCircle | x + z ∈ U} = 0 := by
    intro z hz
    rw [screwHaar_preimage_add (hZsub hz) hU.measurableSet, hzero']
  have hsub : screwHull omega ⊆
      ⋃ z ∈ hZfin.toFinset, {x : I → UnitAddCircle | x + z ∈ U} := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := Set.mem_iUnion₂.mp (hZcover hx)
    exact Set.mem_biUnion (hZfin.mem_toFinset.mpr hz) hzx
  have hle : mu (screwHull omega) ≤ 0 := by
    calc mu (screwHull omega)
        ≤ mu (⋃ z ∈ hZfin.toFinset, {x : I → UnitAddCircle | x + z ∈ U}) :=
          measure_mono hsub
      _ ≤ ∑ z ∈ hZfin.toFinset, mu {x : I → UnitAddCircle | x + z ∈ U} :=
          measure_biUnion_finset_le _ _
      _ = 0 := Finset.sum_eq_zero fun z hz => hpieces z (hZfin.mem_toFinset.mp hz)
  rw [screwHaar_measure_hull omega] at hle
  simp at hle


/-- **Support of the invariant law.** The invariant law of the screw line is supported
exactly on the relation hull. -/
theorem screwHaar_support (omega : I → ℝ) :
    (screwHaar omega : Measure (I → UnitAddCircle)).support = screwHull omega := by
  refine Set.Subset.antisymm ?_ ?_
  · refine Measure.support_subset_of_isClosed (isClosed_screwHull omega) ?_
    rw [mem_ae_iff, measure_compl (isClosed_screwHull omega).measurableSet
      (measure_ne_top _ _), screwHaar_measure_hull omega, measure_univ, tsub_self]
  · intro x hx
    rw [Measure.mem_support_iff_forall]
    intro U hU
    obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.mp hU
    exact lt_of_lt_of_le (screwHaar_pos_of_isOpen hVopen ⟨x, hxV, hx⟩) (measure_mono hVU)

/-! ## The limiting value distribution -/

variable {a : I → ℝ}

/-- Limiting value distribution of the screw series: the invariant hull law pushed
forward along the phase-defect energy. -/
def screwValueLaw (hpos : ∀ i, 0 ≤ a i) (hsum : Summable a) (omega : I → ℝ) :
    ProbabilityMeasure ℝ :=
  (screwHaar omega).map (screwValue_continuous hpos hsum).measurable.aemeasurable

theorem screwValueLaw_toMeasure (hpos : ∀ i, 0 ≤ a i) (hsum : Summable a) (omega : I → ℝ) :
    (screwValueLaw hpos hsum omega : Measure ℝ) =
      Measure.map (screwValue a) (screwHaar omega : Measure (I → UnitAddCircle)) :=
  ProbabilityMeasure.toMeasure_map _ _

/-- Uniform time sampling of the energy is an ordinary time average. -/
theorem integral_comp_screwValue_phaseLaw (hpos : ∀ i, 0 ≤ a i) (hsum : Summable a)
    (omega : I → ℝ) (A : ℝ) {phi : ℝ → ℝ} (hphi : Continuous phi) :
    (∫ x, phi (screwValue a x)
        ∂(infiniteTorusPhaseProbabilityMeasure omega A : Measure (I → UnitAddCircle))) =
      ∫ u in (0 : ℝ)..1, phi (screwSeries a omega (A * (2 * u - 1))) := by
  rw [infiniteTorusPhaseProbabilityMeasure, ProbabilityMeasure.toMeasure_map]
  rw [integral_map (φ := infiniteTorusPhasePoint omega A)
      (f := fun x => phi (screwValue a x))
      (infiniteTorusPhasePoint_continuous omega A).aemeasurable
      ((hphi.comp (screwValue_continuous hpos hsum)).aestronglyMeasurable)]
  have hpt : ∀ u : ℝ,
      screwValue a (infiniteTorusPhasePoint omega A u) =
        screwSeries a omega (A * (2 * u - 1)) := by
    intro u
    rw [screwSeries_eq_screwValue]
    congr 1
    funext i
    simp only [infiniteTorusPhasePoint, screwPhase]
    ring_nf
  simp_rw [hpt]
  rw [show ((infiniteTorusUnitIntervalProbabilityMeasure : Measure ℝ)) =
    volume.restrict (Ioc 0 1) from rfl]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

/-- **Weak convergence of the sampled laws.** The laws of the screw series under uniform
time sampling converge to the limiting value distribution. -/
theorem tendsto_screwValueLaw (hpos : ∀ i, 0 ≤ a i) (hsum : Summable a) (omega : I → ℝ) :
    Tendsto
      (fun A : ℝ =>
        (infiniteTorusPhaseProbabilityMeasure omega A).map
          (screwValue_continuous hpos hsum).measurable.aemeasurable)
      atTop (𝓝 (screwValueLaw hpos hsum omega)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ (screwHaar_tendsto omega)
    (screwValue_continuous hpos hsum)

/-- **Value-distribution law.** For every bounded continuous test function the uniform
time average of the screw series converges to the integral against the limiting
distribution. No simplicity or rational-independence hypothesis is used. -/
theorem tendsto_timeAverage_screwSeries (hpos : ∀ i, 0 ≤ a i) (hsum : Summable a)
    (omega : I → ℝ) (g : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun A : ℝ => ∫ u in (0 : ℝ)..1, g (screwSeries a omega (A * (2 * u - 1))))
      atTop (𝓝 (∫ y, g y ∂(screwValueLaw hpos hsum omega : Measure ℝ))) := by
  have hconv :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto).mp
      (tendsto_screwValueLaw hpos hsum omega) g
  have hrw : ∀ A : ℝ,
      (∫ y, g y
        ∂(Measure.map (screwValue a)
          (infiniteTorusPhaseProbabilityMeasure omega A : Measure (I → UnitAddCircle)))) =
      ∫ u in (0 : ℝ)..1, g (screwSeries a omega (A * (2 * u - 1))) := by
    intro A
    rw [integral_map (φ := screwValue a) (f := fun y : ℝ => g y)
      (screwValue_continuous hpos hsum).measurable.aemeasurable
      g.continuous.aestronglyMeasurable]
    exact integral_comp_screwValue_phaseLaw hpos hsum omega A g.continuous
  simpa [hrw] using hconv

/-- **Support of the limiting distribution.** It is exactly the interval of cofinally
recurrent values. -/
theorem screwValueLaw_support (hpos : ∀ i, 0 ≤ a i) (hsum : Summable a) (omega : I → ℝ) :
    (screwValueLaw hpos hsum omega : Measure ℝ).support =
      Set.Icc 0 (screwHullMax a omega) := by
  have hmeas : Measurable (screwValue a) := (screwValue_continuous hpos hsum).measurable
  have hmap := screwValueLaw_toMeasure hpos hsum omega
  refine Set.Subset.antisymm ?_ ?_
  · refine Measure.support_subset_of_isClosed isClosed_Icc ?_
    rw [mem_ae_iff, hmap,
      Measure.map_apply hmeas (measurableSet_Icc.compl)]
    have hsubset : (screwValue a ⁻¹' (Set.Icc 0 (screwHullMax a omega))ᶜ) ⊆
        (screwHull omega)ᶜ := by
      intro x hx
      simp only [Set.mem_preimage, Set.mem_compl_iff] at hx ⊢
      intro hxK
      exact hx ⟨screwValue_nonneg hpos x, screwValue_le_screwHullMax hpos hsum hxK⟩
    have hnull : (screwHaar omega : Measure (I → UnitAddCircle)) (screwHull omega)ᶜ = 0 := by
      rw [measure_compl (isClosed_screwHull omega).measurableSet (measure_ne_top _ _),
        screwHaar_measure_hull omega, measure_univ, tsub_self]
    exact nonpos_iff_eq_zero.mp (le_trans (measure_mono hsubset) hnull.le)
  · intro y hy
    rw [Measure.mem_support_iff_forall]
    intro U hU
    obtain ⟨V, hVU, hVopen, hyV⟩ := mem_nhds_iff.mp hU
    have hpre : IsOpen (screwValue a ⁻¹' V) := hVopen.preimage (screwValue_continuous hpos hsum)
    have hne : ((screwValue a ⁻¹' V) ∩ screwHull omega).Nonempty := by
      rw [← screwValue_image_screwHull hpos hsum] at hy
      obtain ⟨z, hz, hzval⟩ := hy
      exact ⟨z, by simp only [Set.mem_preimage, hzval]; exact hyV, hz⟩
    have hposV : 0 < (screwValueLaw hpos hsum omega : Measure ℝ) V := by
      rw [hmap, Measure.map_apply hmeas hVopen.measurableSet]
      exact screwHaar_pos_of_isOpen hpre hne
    exact lt_of_lt_of_le hposV (measure_mono hVU)


/-! ## Uniqueness of the invariant law -/

omit [Countable I] in
/-- A character with nonzero detuning is nontrivial somewhere on the hull. -/
theorem exists_screwHull_infiniteTorusFourier_ne_one {omega : I → ℝ} {n : I →₀ ℤ}
    (hn : infiniteTorusCharacterDetuning n omega ≠ 0) :
    ∃ z ∈ screwHull omega, infiniteTorusFourier n z ≠ 1 := by
  set lam : ℝ := infiniteTorusCharacterDetuning n omega with hlam
  refine ⟨screwPhase omega (Real.pi / lam), screwPhase_mem_screwHull omega _, ?_⟩
  rw [infiniteTorusFourier_screwPhase]
  rw [show ((Real.pi / lam * lam : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) by field_simp]
  rw [Complex.exp_pi_mul_I]
  norm_num

/-- **Uniqueness of the invariant law.** The limit law of uniform time sampling is the only
probability law carried by the relation hull and invariant under all its translations; it
is therefore the Haar probability measure of the hull. -/
theorem screwHaar_unique {omega : I → ℝ} (nu : ProbabilityMeasure (I → UnitAddCircle))
    (hcarrier : (nu : Measure (I → UnitAddCircle)) (screwHull omega) = 1)
    (hinv : ∀ z ∈ screwHull omega,
      Measure.map (fun x : I → UnitAddCircle => x + z)
          (nu : Measure (I → UnitAddCircle)) =
        (nu : Measure (I → UnitAddCircle))) :
    nu = screwHaar omega := by
  have hnull : (nu : Measure (I → UnitAddCircle)) (screwHull omega)ᶜ = 0 := by
    rw [measure_compl (isClosed_screwHull omega).measurableSet (measure_ne_top _ _),
      hcarrier, measure_univ, tsub_self]
  refine probabilityMeasure_ext_of_infiniteTorusFourier_integral_eq nu (screwHaar omega) ?_
  intro n
  rw [screwHaar_fourier]
  by_cases hd : infiniteTorusCharacterDetuning n omega = 0
  · rw [if_pos hd]
    have hae : (fun x => infiniteTorusFourier n x) =ᵐ[(nu : Measure (I → UnitAddCircle))]
        fun _ => (1 : ℂ) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨screwHull omega, ?_, ?_⟩
      · rw [mem_ae_iff]
        exact hnull
      · intro x hx
        exact (screwHull_subset_screwAnnihilator omega hx) n hd
    rw [integral_congr_ae hae, integral_const]
    simp
  · rw [if_neg hd]
    obtain ⟨z, hzK, hzne⟩ := exists_screwHull_infiniteTorusFourier_ne_one hd
    have hmeas : Measurable (fun x : I → UnitAddCircle => x + z) := by fun_prop
    have hstep :
        (∫ x, infiniteTorusFourier n x ∂(nu : Measure (I → UnitAddCircle))) =
          infiniteTorusFourier n z *
            ∫ x, infiniteTorusFourier n x ∂(nu : Measure (I → UnitAddCircle)) := by
      conv_lhs => rw [← hinv z hzK]
      rw [integral_map hmeas.aemeasurable
        (infiniteTorusFourier n).continuous.aestronglyMeasurable]
      simp only [infiniteTorusFourier_add_point]
      rw [integral_mul_const, mul_comm]
    have hfactor :
        (1 - infiniteTorusFourier n z) *
          (∫ x, infiniteTorusFourier n x ∂(nu : Measure (I → UnitAddCircle))) = 0 := by
      rw [sub_mul, one_mul, ← hstep, sub_self]
    rcases mul_eq_zero.mp hfactor with h | h
    · exact absurd (by linear_combination -h : infiniteTorusFourier n z = 1) hzne
    · exact h

end

end GaloisForLFunctions.HTGeometry

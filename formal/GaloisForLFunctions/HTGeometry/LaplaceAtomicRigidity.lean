import GaloisForLFunctions.HTGeometry.RepairedFrequencyDensityLaplace
import GaloisForLFunctions.HTGeometry.CompactDeterminacy

/-!
# Laplace rigidity of an absolutely continuous density against finitely many atoms

If an integrable density `g` on `(0, ∞)` and finitely many atoms `c_i δ_{p_i}` at distinct points
`p_i > 0` have the same Laplace transform on `t > 0`, then `g = 0` almost everywhere and every
`c_i = 0`: the positive and negative parts assemble two finite measures on `[0, ∞)` with equal
Laplace transforms, which coincide by Laplace uniqueness; evaluating on the atoms and off them
separates the mutually singular parts.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*}

theorem posPart_negPart_real (x : ℝ) : ((x.toNNReal : ℝ) - ((-x).toNNReal : ℝ)) = x := by
  rw [Real.coe_toNNReal', Real.coe_toNNReal', max_zero_sub_max_neg_zero_eq_self]

/-- The measure `u⁺ dr + ∑ c_i⁻ δ_{p_i}` (or its mirror) assembled from a real density and real
atoms. -/
def laplaceSplitMeasure (u : ℝ → ℝ) (s : Finset ι) (p : ι → ℝ) (c : ι → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun r => ((u r).toNNReal : ℝ≥0∞)) +
    ∑ i ∈ s, ((-c i).toNNReal : ℝ≥0∞) • Measure.dirac (p i)

theorem laplaceSplitMeasure_isFinite {u : ℝ → ℝ} (hu : IntegrableOn u (Ioi 0)) (s : Finset ι)
    (p : ι → ℝ) (c : ι → ℝ) : IsFiniteMeasure (laplaceSplitMeasure u s p c) := by
  have h1 : IsFiniteMeasure ((volume.restrict (Ioi 0)).withDensity
      (fun r => ((u r).toNNReal : ℝ≥0∞))) := by
    refine isFiniteMeasure_withDensity ?_
    have : ∫⁻ r in Ioi 0, ((u r).toNNReal : ℝ≥0∞) ≤ ∫⁻ r in Ioi 0, ‖u r‖ₑ := by
      refine lintegral_mono fun r => ?_
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofNNReal_toNNReal]
      exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    exact (this.trans_lt hu.2).ne
  refine ⟨?_⟩
  unfold laplaceSplitMeasure
  rw [Measure.add_apply, Measure.finsetSum_apply]
  refine ENNReal.add_lt_top.2 ⟨measure_lt_top _ _, ENNReal.sum_lt_top.2 fun i _ => ?_⟩
  rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.coe_lt_top

theorem laplaceSplitMeasure_compl_Ici {u : ℝ → ℝ} (s : Finset ι) {p : ι → ℝ}
    (hp : ∀ i ∈ s, 0 < p i) (c : ι → ℝ) : laplaceSplitMeasure u s p c (Ici 0)ᶜ = 0 := by
  unfold laplaceSplitMeasure
  rw [Measure.add_apply, Measure.finsetSum_apply, withDensity_apply _ measurableSet_Ici.compl]
  have h1 : (volume.restrict (Ioi (0 : ℝ))).restrict (Ici 0)ᶜ = 0 := by
    rw [Measure.restrict_restrict measurableSet_Ici.compl]
    have : (Ici (0 : ℝ))ᶜ ∩ Ioi 0 = ∅ := by
      ext r
      simp only [mem_inter_iff, mem_compl_iff, mem_Ici, mem_Ioi, mem_empty_iff_false, iff_false,
        not_and, not_lt]
      intro h
      exact (not_le.1 h).le
    rw [this, Measure.restrict_empty]
  rw [h1, lintegral_zero_measure, zero_add]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Ici.compl, smul_eq_mul]
  have : p i ∉ (Ici (0 : ℝ))ᶜ := by
    simp only [mem_compl_iff, mem_Ici, not_not]
    exact (hp i hi).le
  rw [Set.indicator_of_notMem this, mul_zero]

theorem integral_laplaceSplitMeasure {u : ℝ → ℝ} (hum : Measurable u) (hu : IntegrableOn u (Ioi 0))
    (s : Finset ι) (p : ι → ℝ) (c : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ r, Real.exp (-t * r) ∂laplaceSplitMeasure u s p c =
      (∫ r in Ioi 0, ((u r).toNNReal : ℝ) * Real.exp (-t * r)) +
        ∑ i ∈ s, ((-c i).toNNReal : ℝ) * Real.exp (-t * p i) := by
  have hbound : ∀ r ∈ Ioi (0 : ℝ), ‖Real.exp (-t * r)‖ ≤ 1 := fun r hr => by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    have : (0 : ℝ) < r := hr
    nlinarith
  have hwd : Integrable (fun r => Real.exp (-t * r))
      ((volume.restrict (Ioi 0)).withDensity (fun r => ((u r).toNNReal : ℝ≥0∞))) := by
    rw [integrable_withDensity_iff_integrable_smul (by fun_prop)]
    refine Integrable.mono' (hu.norm) (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [NNReal.smul_def, smul_eq_mul, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (NNReal.coe_nonneg _)]
    calc ((u r).toNNReal : ℝ) * Real.exp (-t * r) ≤ ((u r).toNNReal : ℝ) * 1 := by
          gcongr
          rw [Real.exp_le_one_iff]
          have : (0 : ℝ) < r := hr
          nlinarith
      _ ≤ ‖u r‖ := by rw [mul_one, Real.coe_toNNReal']; exact max_le (le_abs_self _) (norm_nonneg _)
  have hat : ∀ i ∈ s, Integrable (fun r => Real.exp (-t * r))
      (((-c i).toNNReal : ℝ≥0∞) • Measure.dirac (p i)) := fun i _ =>
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.coe_ne_top
  unfold laplaceSplitMeasure
  rw [integral_add_measure hwd (integrable_finsetSum_measure.2 hat),
    integral_finsetSum_measure hat, integral_withDensity_eq_integral_smul (by fun_prop)]
  have e1 : ∫ x in Ioi 0, (u x).toNNReal • Real.exp (-t * x) =
      ∫ r in Ioi 0, ((u r).toNNReal : ℝ) * Real.exp (-t * r) := by
    simp only [NNReal.smul_def, smul_eq_mul]
  have e2 : ∀ i, ∫ a, Real.exp (-t * a) ∂(((-c i).toNNReal : ℝ≥0∞) • Measure.dirac (p i)) =
      ((-c i).toNNReal : ℝ) * Real.exp (-t * p i) := fun i => by
    rw [integral_smul_measure, integral_dirac, ENNReal.coe_toReal, smul_eq_mul]
  rw [e1, Finset.sum_congr rfl fun i _ => e2 i]

/-- **Laplace rigidity, real form.** -/
theorem laplace_atomic_rigidity_real {u : ℝ → ℝ} (hu : IntegrableOn u (Ioi 0)) (s : Finset ι)
    {p : ι → ℝ} (hp : ∀ i ∈ s, 0 < p i) (hinj : Set.InjOn p s) (c : ι → ℝ)
    (h : ∀ t : ℝ, 0 < t →
      ∫ r in Ioi 0, u r * Real.exp (-t * r) = ∑ i ∈ s, c i * Real.exp (-t * p i)) :
    u =ᵐ[volume.restrict (Ioi 0)] 0 ∧ ∀ i ∈ s, c i = 0 := by
  -- pass to a measurable version of `u`
  set v : ℝ → ℝ := hu.aestronglyMeasurable.mk u with hv
  have hvm : Measurable v := hu.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have huv : u =ᵐ[volume.restrict (Ioi 0)] v := hu.aestronglyMeasurable.ae_eq_mk
  have hvi : IntegrableOn v (Ioi 0) := hu.congr huv
  have hnv : IntegrableOn (fun r => -v r) (Ioi 0) := hvi.neg
  have hh : ∀ t : ℝ, 0 < t →
      ∫ r in Ioi 0, v r * Real.exp (-t * r) = ∑ i ∈ s, c i * Real.exp (-t * p i) := by
    intro t ht
    rw [← h t ht]
    refine integral_congr_ae ?_
    filter_upwards [huv] with r hr
    rw [hr]
  haveI := laplaceSplitMeasure_isFinite hvi s p c
  haveI := laplaceSplitMeasure_isFinite hnv s p (fun i => -c i)
  have hmeq : laplaceSplitMeasure v s p c = laplaceSplitMeasure (fun r => -v r) s p (fun i => -c i) := by
    refine measure_eq_of_laplace_eq (laplaceSplitMeasure_compl_Ici s hp c)
      (laplaceSplitMeasure_compl_Ici s hp _) fun t ht => ?_
    rw [integral_laplaceSplitMeasure hvm hvi s p c ht.le,
      integral_laplaceSplitMeasure (u := fun r => -v r) hvm.neg hnv s p _ ht.le]
    have hint : ∀ w : ℝ → ℝ, Measurable w → IntegrableOn w (Ioi 0) →
        IntegrableOn (fun r => ((w r).toNNReal : ℝ) * Real.exp (-t * r)) (Ioi 0) := by
      intro w hw hwi
      refine Integrable.mono' hwi.norm (by fun_prop) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
      calc ((w r).toNNReal : ℝ) * Real.exp (-t * r) ≤ ((w r).toNNReal : ℝ) * 1 := by
            gcongr
            rw [Real.exp_le_one_iff]
            have : (0 : ℝ) < r := hr
            nlinarith
        _ ≤ ‖w r‖ := by rw [mul_one, Real.coe_toNNReal']; exact max_le (le_abs_self _) (norm_nonneg _)
    have key := hh t ht
    have hsplit : ∫ r in Ioi 0, v r * Real.exp (-t * r) =
        (∫ r in Ioi 0, ((v r).toNNReal : ℝ) * Real.exp (-t * r)) -
          ∫ r in Ioi 0, ((-v r).toNNReal : ℝ) * Real.exp (-t * r) := by
      have e : (fun r => v r * Real.exp (-t * r)) = fun r =>
          ((v r).toNNReal : ℝ) * Real.exp (-t * r) - ((-v r).toNNReal : ℝ) * Real.exp (-t * r) :=
        funext fun r => by rw [← sub_mul, posPart_negPart_real]
      rw [e, integral_sub (hint v hvm hvi) (hint (fun r => -v r) hvm.neg hnv)]
    have hcsplit : ∀ i, c i = ((c i).toNNReal : ℝ) - ((-c i).toNNReal : ℝ) := fun i =>
      (posPart_negPart_real (c i)).symm
    rw [hsplit] at key
    simp only [neg_neg]
    have hsum : ∑ i ∈ s, c i * Real.exp (-t * p i) =
        ∑ i ∈ s, ((c i).toNNReal : ℝ) * Real.exp (-t * p i) -
          ∑ i ∈ s, ((-c i).toNNReal : ℝ) * Real.exp (-t * p i) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [← sub_mul, ← hcsplit]
    rw [hsum] at key
    linarith
  -- the atoms vanish
  have hatoms : ∀ i ∈ s, c i = 0 := by
    intro i hi
    have hsing := congrArg (fun μ : Measure ℝ => μ {p i}) hmeq
    simp only [laplaceSplitMeasure, Measure.add_apply, Measure.finsetSum_apply,
      Measure.smul_apply, smul_eq_mul] at hsing
    have hwd : ∀ w : ℝ → ℝ, (volume.restrict (Ioi 0)).withDensity
        (fun r => ((w r).toNNReal : ℝ≥0∞)) {p i} = 0 := fun w =>
      withDensity_absolutelyContinuous _ _ (by simp)
    have hdirac : ∀ (d : ι → ℝ≥0∞), ∑ j ∈ s, d j * Measure.dirac (p j) {p i} = d i := by
      intro d
      rw [Finset.sum_eq_single i]
      · rw [Measure.dirac_apply_of_mem (mem_singleton _), mul_one]
      · intro j hj hji
        rw [Measure.dirac_apply' _ (measurableSet_singleton _), Set.indicator_of_notMem, mul_zero]
        exact fun hm => hji (hinj hj hi hm)
      · exact fun hns => absurd hi hns
    rw [hwd, hwd, zero_add, zero_add, hdirac (fun j => ((-c j).toNNReal : ℝ≥0∞)),
      hdirac (fun j => ((-(-c j)).toNNReal : ℝ≥0∞)), neg_neg, ENNReal.coe_inj] at hsing
    have h1 := congrArg (fun z : ℝ≥0 => (z : ℝ)) hsing
    simp only [Real.coe_toNNReal'] at h1
    rcases le_total (c i) 0 with hc | hc
    · have : max (-c i) 0 = -c i := max_eq_left (by linarith)
      rw [this, max_eq_right hc] at h1
      linarith
    · have : max (c i) 0 = c i := max_eq_left hc
      rw [this, max_eq_right (by linarith)] at h1
      linarith
  refine ⟨?_, hatoms⟩
  -- the absolutely continuous parts agree
  have hzero : ∀ (w : ι → ℝ), (∀ i ∈ s, w i = 0) →
      ∑ i ∈ s, ((-w i).toNNReal : ℝ≥0∞) • Measure.dirac (p i) = 0 := by
    intro w hw
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [hw i hi, neg_zero, Real.toNNReal_zero, ENNReal.coe_zero, zero_smul]
  have hwd : (volume.restrict (Ioi 0)).withDensity (fun r => ((v r).toNNReal : ℝ≥0∞)) =
      (volume.restrict (Ioi 0)).withDensity (fun r => ((-v r).toNNReal : ℝ≥0∞)) := by
    have e1 := hzero c hatoms
    have e2 := hzero (fun i => -c i) (fun i hi => by rw [hatoms i hi, neg_zero])
    unfold laplaceSplitMeasure at hmeq
    rw [e1, e2, add_zero, add_zero] at hmeq
    exact hmeq
  have hfin : ∫⁻ r in Ioi 0, ((v r).toNNReal : ℝ≥0∞) ≠ ⊤ := by
    have : ∫⁻ r in Ioi 0, ((v r).toNNReal : ℝ≥0∞) ≤ ∫⁻ r in Ioi 0, ‖v r‖ₑ := by
      refine lintegral_mono fun r => ?_
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofNNReal_toNNReal]
      exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    exact (this.trans_lt hvi.2).ne
  have hae := (withDensity_eq_iff (by fun_prop) (by fun_prop) hfin).1 hwd
  filter_upwards [hae, huv] with r hr hur
  rw [hur, Pi.zero_apply]
  have h1 := congrArg (fun z : ℝ≥0∞ => z.toReal) hr
  simp only [ENNReal.coe_toReal, Real.coe_toNNReal'] at h1
  rcases le_total (v r) 0 with hc | hc
  · rw [max_eq_right hc, max_eq_left (by linarith)] at h1
    linarith
  · rw [max_eq_left hc, max_eq_right (by linarith)] at h1
    linarith

theorem integrableOn_mul_exp {g : ℝ → ℂ} (hg : IntegrableOn g (Ioi 0)) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun r => g r * (Real.exp (-t * r) : ℂ)) (Ioi 0) := by
  refine Integrable.mono' hg.norm (hg.aestronglyMeasurable.mul (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have : Real.exp (-t * r) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : (0 : ℝ) < r := hr
    nlinarith
  exact mul_le_of_le_one_right (norm_nonneg _) this

/-- **Laplace rigidity.**  If an integrable complex density on `(0, ∞)` and finitely many complex
atoms at distinct positive points have the same Laplace transform on `t > 0`, both vanish. -/
theorem laplace_atomic_rigidity {g : ℝ → ℂ} (hg : IntegrableOn g (Ioi 0)) (s : Finset ι)
    {p : ι → ℝ} (hp : ∀ i ∈ s, 0 < p i) (hinj : Set.InjOn p s) (c : ι → ℂ)
    (h : ∀ t : ℝ, 0 < t →
      ∫ r in Ioi 0, g r * (Real.exp (-t * r) : ℂ) = ∑ i ∈ s, c i * (Real.exp (-t * p i) : ℂ)) :
    g =ᵐ[volume.restrict (Ioi 0)] 0 ∧ ∀ i ∈ s, c i = 0 := by
  have hpart : ∀ (F : ℂ →L[ℝ] ℝ), (∀ z : ℂ, ∀ a : ℝ, F (z * (a : ℂ)) = F z * a) →
      (∀ t : ℝ, 0 < t → ∫ r in Ioi 0, F (g r) * Real.exp (-t * r) =
        ∑ i ∈ s, F (c i) * Real.exp (-t * p i)) := by
    intro F hF t ht
    have h1 := congrArg F (h t ht)
    rw [← F.integral_comp_comm (integrableOn_mul_exp hg ht.le), map_sum] at h1
    simpa only [hF] using h1
  have hre := laplace_atomic_rigidity_real hg.re s hp hinj (fun i => (c i).re)
    (hpart Complex.reCLM fun z a => by simp [Complex.mul_re])
  have him := laplace_atomic_rigidity_real hg.im s hp hinj (fun i => (c i).im)
    (hpart Complex.imCLM fun z a => by simp [Complex.mul_im])
  refine ⟨?_, fun i hi => Complex.ext (hre.2 i hi) (him.2 i hi)⟩
  filter_upwards [hre.1, him.1] with r h1 h2
  exact Complex.ext h1 h2

/-- The Laplace transform of an integrable density is continuous on `[0, ∞)`. -/
theorem continuousOn_laplace {g : ℝ → ℂ} (hg : IntegrableOn g (Ioi 0)) :
    ContinuousOn (fun t : ℝ => ∫ r in Ioi 0, g r * (Real.exp (-t * r) : ℂ)) (Ici 0) := by
  refine continuousOn_of_dominated (bound := fun r => ‖g r‖)
    (fun t _ => hg.aestronglyMeasurable.mul (by fun_prop)) (fun t ht => ?_) hg.norm ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    rw [Real.exp_le_one_iff]
    have ht' : (0 : ℝ) ≤ t := ht
    have hr' : (0 : ℝ) < r := hr
    nlinarith
  · exact Eventually.of_forall fun r => (by fun_prop : Continuous fun t : ℝ =>
      g r * (Real.exp (-t * r) : ℂ)).continuousOn

/-- **Laplace uniqueness on `L¹`.**  An integrable density whose Laplace transform vanishes for
almost every `t > 0` vanishes almost everywhere. -/
theorem ae_eq_zero_of_laplace_ae_eq_zero {g : ℝ → ℂ} (hg : IntegrableOn g (Ioi 0))
    (h : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∫ r in Ioi 0, g r * (Real.exp (-t * r) : ℂ) = 0) :
    g =ᵐ[volume.restrict (Ioi 0)] 0 := by
  have heq : Set.EqOn (fun t : ℝ => ∫ r in Ioi 0, g r * (Real.exp (-t * r) : ℂ)) (fun _ => 0)
      (Ioi 0) :=
    Measure.eqOn_of_ae_eq h ((continuousOn_laplace hg).mono Ioi_subset_Ici_self) continuousOn_const
      (by rw [interior_Ioi, closure_Ioi]; exact Ioi_subset_Ici_self)
  exact (laplace_atomic_rigidity (ι := Unit) hg ∅ (p := fun _ => 1) (by simp) (by simp)
    (fun _ => 0) fun t ht => by rw [Finset.sum_empty]; exact heq ht).1

/-! ## Laplace uniqueness at the lattice `t ∈ aℕ` -/

/-- **Discrete Laplace uniqueness.**  Finite measures carried by `[0, ∞)` whose Laplace transforms
agree at every `t = k a`, `k ∈ ℕ`, `a > 0`, coincide: after the rescaling `r ↦ a r` the values are the
moments of the compactifications `e^{-r}`, which determine finite measures on `[0, 1]`. -/
theorem measure_eq_of_laplace_nat_eq {tau sigma : Measure ℝ} [IsFiniteMeasure tau]
    [IsFiniteMeasure sigma] (htau : tau (Ici 0)ᶜ = 0) (hsigma : sigma (Ici 0)ᶜ = 0) {a : ℝ}
    (ha : 0 < a)
    (h : ∀ k : ℕ, ∫ r, Real.exp (-((k : ℝ) * a) * r) ∂tau =
      ∫ r, Real.exp (-((k : ℝ) * a) * r) ∂sigma) : tau = sigma := by
  have hemb : MeasurableEmbedding (fun r : ℝ => a * r) :=
    (Homeomorph.mulLeft₀ a ha.ne').isClosedEmbedding.measurableEmbedding
  have hcar : ∀ μ : Measure ℝ, μ (Ici 0)ᶜ = 0 → Measure.map (fun r : ℝ => a * r) μ (Ici 0)ᶜ = 0 := by
    intro μ hμ
    rw [Measure.map_apply hemb.measurable measurableSet_Ici.compl]
    refine measure_mono_null (fun r hr => ?_) hμ
    simp only [mem_preimage, mem_compl_iff, mem_Ici, not_le] at hr ⊢
    by_contra h0
    push Not at h0
    nlinarith
  have hmoment : ∀ (μ : Measure ℝ) (k : ℕ), ∫ x, x ^ k ∂compactifiedLaplaceMeasure
      (Measure.map (fun r : ℝ => a * r) μ) = ∫ r, Real.exp (-((k : ℝ) * a) * r) ∂μ := by
    intro μ k
    rw [compactifiedLaplaceMeasure_moment, integral_map hemb.measurable.aemeasurable (by fun_prop)]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only
    ring_nf
  have hint : ∀ (μ : Measure ℝ) [IsFiniteMeasure μ], μ (Ici 0)ᶜ = 0 → ∀ k : ℕ,
      Integrable (fun x : ℝ => x ^ k) (compactifiedLaplaceMeasure (Measure.map (fun r : ℝ => a * r) μ)) := by
    intro μ _ hμ k
    apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
    filter_upwards [ae_iff.mpr (compactifiedLaplaceMeasure_carried_Icc _ (hcar μ hμ))] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx.1 k)]
    exact pow_le_one₀ hx.1 hx.2
  have hcompact : compactifiedLaplaceMeasure (Measure.map (fun r : ℝ => a * r) tau) =
      compactifiedLaplaceMeasure (Measure.map (fun r : ℝ => a * r) sigma) := by
    refine _root_.HTGeometry.measure_eq_of_moments_eq_of_carried
      (s := fun k => ∫ x, x ^ k ∂compactifiedLaplaceMeasure (Measure.map (fun r : ℝ => a * r) tau))
      (compactifiedLaplaceMeasure_carried_Icc _ (hcar tau htau))
      (compactifiedLaplaceMeasure_carried_Icc _ (hcar sigma hsigma)) (fun k => rfl)
      (hint tau htau) (fun k => ?_) (hint sigma hsigma)
    rw [hmoment, hmoment, h k]
  exact hemb.map_injective (measurableEmbedding_laplaceCompactification.map_injective hcompact)

/-- **Lattice Laplace uniqueness on `L¹`, real form.** -/
theorem ae_eq_zero_of_laplace_nat_eq_zero_real {u : ℝ → ℝ} (hu : IntegrableOn u (Ioi 0)) {a : ℝ}
    (ha : 0 < a) (h : ∀ k : ℕ, ∫ r in Ioi 0, u r * Real.exp (-((k : ℝ) * a) * r) = 0) :
    u =ᵐ[volume.restrict (Ioi 0)] 0 := by
  set v : ℝ → ℝ := hu.aestronglyMeasurable.mk u with hv
  have hvm : Measurable v := hu.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have huv : u =ᵐ[volume.restrict (Ioi 0)] v := hu.aestronglyMeasurable.ae_eq_mk
  have hvi : IntegrableOn v (Ioi 0) := hu.congr huv
  have hnv : IntegrableOn (fun r => -v r) (Ioi 0) := hvi.neg
  haveI := laplaceSplitMeasure_isFinite hvi (∅ : Finset Unit) (fun _ => 1) (fun _ => 0)
  haveI := laplaceSplitMeasure_isFinite hnv (∅ : Finset Unit) (fun _ => 1) (fun _ => 0)
  have hmeq : laplaceSplitMeasure v (∅ : Finset Unit) (fun _ => 1) (fun _ => 0) =
      laplaceSplitMeasure (fun r => -v r) (∅ : Finset Unit) (fun _ => 1) (fun _ => 0) := by
    refine measure_eq_of_laplace_nat_eq (laplaceSplitMeasure_compl_Ici _ (by simp) _)
      (laplaceSplitMeasure_compl_Ici _ (by simp) _) ha fun k => ?_
    have hk : 0 ≤ (k : ℝ) * a := by positivity
    rw [integral_laplaceSplitMeasure hvm hvi _ _ _ hk,
      integral_laplaceSplitMeasure (u := fun r => -v r) hvm.neg hnv _ _ _ hk,
      Finset.sum_empty, add_zero, add_zero]
    have hint : ∀ w : ℝ → ℝ, Measurable w → IntegrableOn w (Ioi 0) →
        IntegrableOn (fun r => ((w r).toNNReal : ℝ) * Real.exp (-((k : ℝ) * a) * r)) (Ioi 0) := by
      intro w hw hwi
      refine Integrable.mono' hwi.norm (by fun_prop) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le,
        Real.norm_of_nonneg (NNReal.coe_nonneg _)]
      calc ((w r).toNNReal : ℝ) * Real.exp (-((k : ℝ) * a) * r) ≤ ((w r).toNNReal : ℝ) * 1 := by
            gcongr
            rw [Real.exp_le_one_iff]
            have : (0 : ℝ) < r := hr
            nlinarith
        _ ≤ ‖w r‖ := by
            rw [mul_one, Real.coe_toNNReal']
            exact max_le (le_abs_self _) (norm_nonneg _)
    have key : ∫ r in Ioi 0, v r * Real.exp (-((k : ℝ) * a) * r) = 0 := by
      refine (integral_congr_ae ?_).trans (h k)
      filter_upwards [huv] with r hr
      rw [hr]
    have e : (fun r => v r * Real.exp (-((k : ℝ) * a) * r)) = fun r =>
        ((v r).toNNReal : ℝ) * Real.exp (-((k : ℝ) * a) * r) -
          ((-v r).toNNReal : ℝ) * Real.exp (-((k : ℝ) * a) * r) :=
      funext fun r => by rw [← sub_mul, posPart_negPart_real]
    rw [e, integral_sub (hint v hvm hvi) (hint (fun r => -v r) hvm.neg hnv)] at key
    linarith
  have hwd : (volume.restrict (Ioi 0)).withDensity (fun r => ((v r).toNNReal : ℝ≥0∞)) =
      (volume.restrict (Ioi 0)).withDensity (fun r => ((-v r).toNNReal : ℝ≥0∞)) := by
    unfold laplaceSplitMeasure at hmeq
    simpa only [Finset.sum_empty, add_zero] using hmeq
  have hfin : ∫⁻ r in Ioi 0, ((v r).toNNReal : ℝ≥0∞) ≠ ⊤ := by
    have : ∫⁻ r in Ioi 0, ((v r).toNNReal : ℝ≥0∞) ≤ ∫⁻ r in Ioi 0, ‖v r‖ₑ := by
      refine lintegral_mono fun r => ?_
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofNNReal_toNNReal]
      exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    exact (this.trans_lt hvi.2).ne
  have hae := (withDensity_eq_iff (by fun_prop) (by fun_prop) hfin).1 hwd
  filter_upwards [hae, huv] with r hr hur
  rw [hur, Pi.zero_apply]
  have h1 := congrArg (fun z : ℝ≥0∞ => z.toReal) hr
  simp only [ENNReal.coe_toReal, Real.coe_toNNReal'] at h1
  rcases le_total (v r) 0 with hc | hc
  · rw [max_eq_right hc, max_eq_left (by linarith)] at h1
    linarith
  · rw [max_eq_left hc, max_eq_right (by linarith)] at h1
    linarith

/-- **Lattice Laplace uniqueness on `L¹`.**  An integrable complex density on `(0, ∞)` whose
Laplace transform vanishes at every `t = k a`, `k ∈ ℕ`, vanishes almost everywhere. -/
theorem ae_eq_zero_of_laplace_nat_eq_zero {g : ℝ → ℂ} (hg : IntegrableOn g (Ioi 0)) {a : ℝ}
    (ha : 0 < a) (h : ∀ k : ℕ, ∫ r in Ioi 0, g r * (Real.exp (-((k : ℝ) * a) * r) : ℂ) = 0) :
    g =ᵐ[volume.restrict (Ioi 0)] 0 := by
  have hpart : ∀ (F : ℂ →L[ℝ] ℝ), (∀ z : ℂ, ∀ b : ℝ, F (z * (b : ℂ)) = F z * b) →
      ∀ k : ℕ, ∫ r in Ioi 0, F (g r) * Real.exp (-((k : ℝ) * a) * r) = 0 := by
    intro F hF k
    have h1 := congrArg F (h k)
    rw [← F.integral_comp_comm (integrableOn_mul_exp hg (by positivity)), map_zero] at h1
    simpa only [hF] using h1
  have hre := ae_eq_zero_of_laplace_nat_eq_zero_real hg.re ha
    (hpart Complex.reCLM fun z b => by simp [Complex.mul_re])
  have him := ae_eq_zero_of_laplace_nat_eq_zero_real hg.im ha
    (hpart Complex.imCLM fun z b => by simp [Complex.mul_im])
  filter_upwards [hre, him] with r h1 h2
  exact Complex.ext h1 h2

end GaloisForLFunctions.HTGeometry

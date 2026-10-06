import GaloisForLFunctions.HTGeometry.CountableObservableEntropy

/-!
# Conditional entropy along a generating filtration tends to zero

Let `g_k` be countably-valued observables whose σ-algebras `σ(g_k)` increase, and let `f` be a
countably-valued observable of finite entropy, measurable for `⋁_k σ(g_k)`.  Then

`H_μ(f | g_k) → 0`.

The conditional expectation of an indicator given a countable partition is the cell average
`μ(A ∩ [g = g ω]) / μ[g = g ω]`; the conditional entropy is `∑_a ∫ η(E[1_{f=a} | g])`; Lévy's
upward theorem sends each `E[1_{f=a} | g_k]` to `1_{f=a}` almost everywhere, so each integrand
tends to `η(0) = η(1) = 0` under the bound `η ≤ 1`, and the label sum converges by dominated
convergence under the summable bound `η(μ{f = a})` given by conditioning reducing entropy.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ObservableEntropy

theorem negMulLog_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : Real.negMulLog x ≤ 1 := by
  rcases hx0.eq_or_lt with rfl | hx
  · simp
  have h := Real.log_le_sub_one_of_pos (inv_pos.2 hx)
  rw [Real.log_inv] at h
  have : Real.negMulLog x = x * (-Real.log x) := by rw [Real.negMulLog]; ring
  rw [this]
  have hmul := mul_le_mul_of_nonneg_left h hx.le
  rw [mul_sub, mul_inv_cancel₀ hx.ne', mul_one] at hmul
  linarith

/-- `η(s/t) t = s log(t/s)` for masses `s ≤ t < ∞`. -/
theorem ofReal_negMulLog_div_mul {s t : ℝ≥0∞} (hst : s ≤ t) (ht : t ≠ ⊤) :
    ENNReal.ofReal (Real.negMulLog (s.toReal / t.toReal)) * t = condTerm s t := by
  by_cases ht0 : t.toReal = 0
  · have ht0' : t = 0 := ((ENNReal.toReal_eq_zero_iff t).1 ht0).resolve_right ht
    have hs0 : s = 0 := le_antisymm (ht0' ▸ hst) (zero_le)
    rw [ht0', hs0, mul_zero, condTerm_zero_left]
  have htpos : 0 < t.toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm ht0)
  have hs : s ≠ ⊤ := ne_top_of_le_ne_top ht hst
  have hdiv : 0 ≤ Real.negMulLog (s.toReal / t.toReal) :=
    Real.negMulLog_nonneg (div_nonneg ENNReal.toReal_nonneg htpos.le)
      ((div_le_one htpos).2 (ENNReal.toReal_mono ht hst))
  rw [← ENNReal.ofReal_toReal ht, ← ENNReal.ofReal_mul' ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal ht, condTerm]
  congr 1
  by_cases hs0 : s.toReal = 0
  · rw [hs0]; simp
  have hspos : 0 < s.toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hs0)
  rw [Real.negMulLog, show t.toReal / s.toReal = (s.toReal / t.toReal)⁻¹ by rw [inv_div],
    Real.log_inv]
  field_simp

variable {Ω : Type*} [m0 : MeasurableSpace Ω] (μ : Measure Ω)
variable {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
  [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β]

/-- The cell average `μ(A ∩ [g = g ω]) / μ[g = g ω]`. -/
def cellAverage (g : Ω → β) (A : Set Ω) (ω : Ω) : ℝ :=
  (μ (A ∩ g ⁻¹' {g ω})).toReal / (μ (g ⁻¹' {g ω})).toReal

theorem measurable_cellAverage_comap (g : Ω → β) (A : Set Ω) :
    Measurable[MeasurableSpace.comap g inferInstance] (cellAverage μ g A) :=
  (measurable_of_countable fun b => (μ (A ∩ g ⁻¹' {b})).toReal / (μ (g ⁻¹' {b})).toReal).comp
    (comap_measurable g)

theorem measurable_cellAverage {g : Ω → β} (hg : Measurable g) (A : Set Ω) :
    Measurable (cellAverage μ g A) :=
  (measurable_cellAverage_comap μ g A).mono hg.comap_le le_rfl

omit [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β] in
theorem cellAverage_nonneg (g : Ω → β) (A : Set Ω) (ω : Ω) : 0 ≤ cellAverage μ g A ω :=
  div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

omit [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β] in
theorem cellAverage_le_one [IsFiniteMeasure μ] (g : Ω → β) (A : Set Ω) (ω : Ω) :
    cellAverage μ g A ω ≤ 1 := by
  rw [cellAverage]
  exact div_le_one_of_le₀ (ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono inter_subset_right)) ENNReal.toReal_nonneg

omit [MeasurableSingletonClass β] [Countable β] m0 in
/-- A `σ(g)`-measurable real function is constant on the fibres of `g`. -/
theorem eq_of_measurable_comap {g : Ω → β} {h : Ω → ℝ}
    (hh : Measurable[MeasurableSpace.comap g inferInstance] h) {ω ω' : Ω} (hωω' : g ω = g ω') :
    h ω' = h ω := by
  obtain ⟨B, -, hB⟩ := MeasurableSpace.measurableSet_comap.1 (hh (measurableSet_singleton (h ω)))
  have h1 : ω ∈ g ⁻¹' B := by rw [hB]; rfl
  have h2 : ω' ∈ g ⁻¹' B := by
    simp only [mem_preimage] at h1 ⊢
    rwa [← hωω']
  rw [hB] at h2
  exact h2

/-- **Conditional expectation on a countable partition**: `E[1_A | σ(g)]` is the cell average. -/
theorem condExp_indicator_ae_eq_cellAverage [IsFiniteMeasure μ] {g : Ω → β} (hg : Measurable g)
    {A : Set Ω} (hA : MeasurableSet A) :
    μ[A.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap g inferInstance] =ᵐ[μ]
      cellAverage μ g A := by
  have hm : MeasurableSpace.comap g inferInstance ≤ m0 := hg.comap_le
  set E := μ[A.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap g inferInstance]
  have hEm : Measurable[MeasurableSpace.comap g inferInstance] E :=
    stronglyMeasurable_condExp.measurable
  have hnull : μ {ω | μ (g ⁻¹' {g ω}) = 0} = 0 := by
    have : {ω | μ (g ⁻¹' {g ω}) = 0} = ⋃ b ∈ {b | μ (g ⁻¹' {b}) = 0}, g ⁻¹' {b} := by
      ext ω; simp
    rw [this, measure_biUnion_null_iff (to_countable _)]
    exact fun b hb => hb
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hnull
  simp only [mem_setOf_eq] at hω ⊢
  by_contra hpos
  apply hω
  have hcell : MeasurableSet[MeasurableSpace.comap g inferInstance] (g ⁻¹' {g ω}) :=
    MeasurableSpace.measurableSet_comap.2 ⟨{g ω}, measurableSet_singleton _, rfl⟩
  have hint := setIntegral_condExp hm ((integrable_const (μ := μ) (1 : ℝ)).indicator hA) hcell
  rw [setIntegral_congr_fun (hm _ hcell) (fun ω' hω' =>
      eq_of_measurable_comap hEm (show g ω = g ω' from (hω' : g ω' = g ω).symm)),
    setIntegral_const, setIntegral_indicator hA, setIntegral_const, smul_eq_mul, smul_eq_mul,
    mul_one] at hint
  have hpos' : 0 < μ.real (g ⁻¹' {g ω}) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hpos (measure_ne_top _ _)
  rw [cellAverage, ← measureReal_def, ← measureReal_def, eq_div_iff hpos'.ne', mul_comm, hint,
    inter_comm]

theorem lintegral_negMulLog_cellAverage [IsFiniteMeasure μ] {g : Ω → β} (hg : Measurable g)
    {A : Set Ω} :
    ∫⁻ ω, ENNReal.ofReal (Real.negMulLog (cellAverage μ g A ω)) ∂μ =
      ∑' b, condTerm (μ (A ∩ g ⁻¹' {b})) (μ (g ⁻¹' {b})) := by
  have hcover : (⋃ b, g ⁻¹' {b}) = univ := by ext ω; simp
  rw [← setLIntegral_univ, ← hcover, lintegral_iUnion (measurableSet_fiber hg)
    (fun a b hab => Set.disjoint_left.2 fun ω h1 h2 => hab ((h1 : g ω = a).symm.trans h2))]
  refine tsum_congr fun b => ?_
  rw [setLIntegral_congr_fun (measurableSet_fiber hg b) (g := fun _ =>
      ENNReal.ofReal (Real.negMulLog ((μ (A ∩ g ⁻¹' {b})).toReal / (μ (g ⁻¹' {b})).toReal)))
    (fun ω hω => by rw [cellAverage, (hω : g ω = b)]), setLIntegral_const,
    ofReal_negMulLog_div_mul (measure_mono inter_subset_right) (measure_ne_top _ _)]

/-- **Conditional entropy along a generating filtration tends to zero.** -/
theorem tendsto_obsCondEntropy_of_generating [IsProbabilityMeasure μ] {ι : ℕ → Type*}
    [∀ k, MeasurableSpace (ι k)] [∀ k, MeasurableSingletonClass (ι k)] [∀ k, Countable (ι k)]
    {g : ∀ k, Ω → ι k} (hg : ∀ k, Measurable (g k))
    (hmono : Monotone fun k => MeasurableSpace.comap (g k) inferInstance) {f : Ω → α}
    (hf : Measurable[⨆ k, MeasurableSpace.comap (g k) inferInstance] f)
    (hH : obsEntropy μ f ≠ ⊤) :
    Tendsto (fun k => obsCondEntropy μ f (g k)) atTop (𝓝 0) := by
  let ℱ : Filtration ℕ m0 :=
    ⟨fun k => MeasurableSpace.comap (g k) inferInstance, hmono, fun k => (hg k).comap_le⟩
  have hsup : (⨆ k, MeasurableSpace.comap (g k) inferInstance) ≤ m0 :=
    iSup_le fun k => (hg k).comap_le
  have hf0 : Measurable f := hf.mono hsup le_rfl
  have hlabel : ∀ a, Tendsto (fun k => ∑' b, condTerm (μ (f ⁻¹' {a} ∩ g k ⁻¹' {b}))
      (μ (g k ⁻¹' {b}))) atTop (𝓝 0) := by
    intro a
    set A := f ⁻¹' {a}
    have hA : MeasurableSet A := measurableSet_fiber hf0 a
    have hAsup : MeasurableSet[⨆ k, MeasurableSpace.comap (g k) inferInstance] A :=
      hf (measurableSet_singleton a)
    have hlevy := ((integrable_const (μ := μ) (1 : ℝ)).indicator hA).tendsto_ae_condExp (ℱ := ℱ)
      (stronglyMeasurable_const.indicator hAsup)
    have hid : ∀ᵐ ω ∂μ, ∀ k, μ[A.indicator (fun _ => (1 : ℝ)) | ℱ k] ω =
        cellAverage μ (g k) A ω :=
      ae_all_iff.2 fun k => condExp_indicator_ae_eq_cellAverage μ (hg k) hA
    simp_rw [← lintegral_negMulLog_cellAverage μ (hg _)]
    have hlim : ∀ᵐ ω ∂μ, Tendsto (fun k => ENNReal.ofReal (Real.negMulLog
        (cellAverage μ (g k) A ω))) atTop (𝓝 0) := by
      filter_upwards [hlevy, hid] with ω h1 h2
      have h1' : Tendsto (fun k => cellAverage μ (g k) A ω) atTop
          (𝓝 (A.indicator (fun _ => (1 : ℝ)) ω)) := by
        refine h1.congr fun k => ?_
        exact h2 k
      have hc := (Real.continuous_negMulLog.tendsto _).comp h1'
      have hzero : Real.negMulLog (A.indicator (fun _ => (1 : ℝ)) ω) = 0 := by
        by_cases hω : ω ∈ A <;> simp [hω]
      rw [hzero] at hc
      have := (ENNReal.continuous_ofReal.tendsto _).comp hc
      rw [ENNReal.ofReal_zero] at this
      exact this
    have h := tendsto_lintegral_of_dominated_convergence (fun _ => (1 : ℝ≥0∞))
      (fun k => ENNReal.measurable_ofReal.comp
        (Real.continuous_negMulLog.measurable.comp (measurable_cellAverage μ (hg k) A)))
      (fun k => ae_of_all _ fun ω => by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (negMulLog_le_one (cellAverage_nonneg μ _ _ _)
          (cellAverage_le_one μ _ _ _)))
      (by simp) hlim
    simpa using h
  have hbound : ∀ k a, ∑' b, condTerm (μ (f ⁻¹' {a} ∩ g k ⁻¹' {b})) (μ (g k ⁻¹' {b})) ≤
      entropyTerm (μ (f ⁻¹' {a})) := by
    intro k a
    have hs : ∑' b, μ (f ⁻¹' {a} ∩ g k ⁻¹' {b}) = μ (f ⁻¹' {a}) := by
      rw [← tsum_measure_fiber_inter μ (measurableSet_fiber (hg k)) (measurableSet_fiber hf0 a)]
      exact tsum_congr fun b => by rw [inter_comm]
    have ht : ∑' b, μ (g k ⁻¹' {b}) = 1 := by
      have := tsum_measure_fiber_inter μ (measurableSet_fiber (hg k)) MeasurableSet.univ
      simpa using this
    have h := tsum_condTerm_le (s := fun b => μ (f ⁻¹' {a} ∩ g k ⁻¹' {b}))
      (t := fun b => μ (g k ⁻¹' {b})) (fun b => measure_mono inter_subset_right)
      (by rw [ht]; exact ENNReal.one_ne_top)
    rw [hs, ht, condTerm_one_right] at h
    exact h
  have hsum : ∀ k, obsCondEntropy μ f (g k) = ∫⁻ a, ∑' b, condTerm (μ (f ⁻¹' {a} ∩ g k ⁻¹' {b}))
      (μ (g k ⁻¹' {b})) ∂Measure.count := by
    intro k
    rw [lintegral_count, obsCondEntropy, ENNReal.tsum_prod']
  simp_rw [hsum]
  have h := tendsto_lintegral_of_dominated_convergence (μ := (Measure.count : Measure α))
    (fun a => entropyTerm (μ (f ⁻¹' {a}))) (fun k => measurable_of_countable _)
    (fun k => ae_of_all _ (hbound k)) (by rw [lintegral_count]; exact hH)
    (ae_of_all _ hlabel)
  simpa using h

end GaloisForLFunctions.HTGeometry.ObservableEntropy

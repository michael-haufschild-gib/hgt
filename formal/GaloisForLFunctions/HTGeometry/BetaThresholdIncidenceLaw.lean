import GaloisForLFunctions.HTGeometry.BinomialTailBetaThreshold

/-!
# The beta-threshold complete-incidence law

A bounded replica threshold test applied to a measurable observable `Y : Ω → [0,1]` produces the
*incidence action*

`𝔍 = ∫ binomialTail r k (Y ω) dμ(ω)`.

Three unconditional facts are proved here.

* **Threshold sandwich.**  With `k = ⌈r (a+b)/2⌉` the action sits between `(1 - η) μ{Y ≥ a}` and
  `μ{Y ≥ b} + η μ(Ω)`, where `η = exp (-r (a-b)²/2)`.  Because the statement is proved for an
  arbitrary finite measure, applying it to `μ.restrict Rᶜ` gives the return-excised form: a
  target-independent return set is paid once, with coefficient one, and no mixed `R × Rᶜ` term
  is ever formed.
* **Beta coarea identity.**  The action is exactly the average of the incidence masses
  `μ{Y ≥ u}` against the unit-mass `Beta (k, r-k+1)` density.  The threshold set is formed at each
  level `u` before any averaging.
* **Strict separation from the monomial reporter.**  For a two-valued observable the action equals
  the source probability exactly, whereas the monomial Markov reporter `a^{-r} 𝔼 Y^r` overstates
  it by exactly the factor `a^{-r}`.
-/

open Finset MeasureTheory Real Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The bounded complete-incidence action of a `[0,1]`-valued observable. -/
def incidenceAction (μ : Measure Ω) (r k : ℕ) (Y : Ω → ℝ) : ℝ :=
  ∫ ω, binomialTail r k (Y ω) ∂μ

/-- The incidence action after excising a return set, integrated on the original source space. -/
def restrictedIncidenceAction (μ : Measure Ω) (r k : ℕ) (Y : Ω → ℝ) (R : Set Ω) : ℝ :=
  incidenceAction (μ.restrict Rᶜ) r k Y

theorem restrictedIncidenceAction_eq (μ : Measure Ω) (r k : ℕ) (Y : Ω → ℝ) (R : Set Ω) :
    restrictedIncidenceAction μ r k Y R = ∫ ω in Rᶜ, binomialTail r k (Y ω) ∂μ := rfl

theorem measurable_binomialTail_comp (r k : ℕ) {Y : Ω → ℝ} (hYm : Measurable Y) :
    Measurable fun ω => binomialTail r k (Y ω) :=
  (continuous_binomialTail r k).measurable.comp hYm

theorem integrable_binomialTail_comp (μ : Measure Ω) [IsFiniteMeasure μ] (r k : ℕ) {Y : Ω → ℝ}
    (hYm : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) (hY1 : ∀ ω, Y ω ≤ 1) :
    Integrable (fun ω => binomialTail r k (Y ω)) μ := by
  refine ⟨(measurable_binomialTail_comp r k hYm).aestronglyMeasurable, ?_⟩
  refine HasFiniteIntegral.of_bounded (C := 1) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (binomialTail_nonneg (hY0 ω) (hY1 ω) r k)]
  exact binomialTail_le_one (hY0 ω) (hY1 ω) r k

/-! ### The threshold sandwich -/

/-- **Upper half of the sandwich.**  Above the observational slack the action is dominated by the
incidence mass of the loose tube plus one exponentially small remainder. -/
theorem incidenceAction_le (μ : Measure Ω) [IsFiniteMeasure μ] {r : ℕ} {a b : ℝ}
    {Y : Ω → ℝ} (hYm : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) (hY1 : ∀ ω, Y ω ≤ 1)
    (hba : b < a) (ha : a < 1) :
    incidenceAction μ r (replicaThreshold r a b) Y
      ≤ μ.real {ω | b ≤ Y ω} + Real.exp (-((r : ℝ) * (a - b) ^ 2 / 2)) * μ.real Set.univ := by
  classical
  set η : ℝ := Real.exp (-((r : ℝ) * (a - b) ^ 2 / 2)) with hη
  set S : Set Ω := {ω | b ≤ Y ω} with hS
  have hSm : MeasurableSet S := measurableSet_le measurable_const hYm
  have hpt : ∀ ω, binomialTail r (replicaThreshold r a b) (Y ω)
      ≤ S.indicator (fun _ => (1 : ℝ)) ω + η := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      have := binomialTail_le_one (hY0 ω) (hY1 ω) r (replicaThreshold r a b)
      have hη0 : 0 ≤ η := (Real.exp_nonneg _)
      linarith
    · rw [Set.indicator_of_notMem hω]
      have hxb : Y ω ≤ b := le_of_lt (not_le.mp hω)
      have := binomialTail_replicaThreshold_le (r := r) hba ha (hY0 ω) hxb
      linarith
  have hint1 := integrable_binomialTail_comp μ r (replicaThreshold r a b) hYm hY0 hY1
  have hint2 : Integrable (fun ω => S.indicator (fun _ => (1 : ℝ)) ω + η) μ :=
    ((integrable_indicator_iff hSm).mpr (integrableOn_const)).add
      (integrable_const η)
  have hle := integral_mono hint1 hint2 hpt
  rw [integral_add ((integrable_indicator_iff hSm).mpr integrableOn_const)
    (integrable_const η)] at hle
  rw [integral_indicator_const (1 : ℝ) hSm, integral_const] at hle
  simp only [smul_eq_mul, mul_one] at hle
  rw [incidenceAction]
  refine hle.trans (le_of_eq ?_)
  ring

/-- **Lower half of the sandwich.**  The action recovers the tight incidence mass up to one
exponentially small factor. -/
theorem le_incidenceAction (μ : Measure Ω) [IsFiniteMeasure μ] {r : ℕ} {a b : ℝ}
    {Y : Ω → ℝ} (hYm : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) (hY1 : ∀ ω, Y ω ≤ 1)
    (hb : 0 < b) (hba : b < a) (ha : a < 1) :
    (1 - Real.exp (-((r : ℝ) * (a - b) ^ 2 / 2))) * μ.real {ω | a ≤ Y ω}
      ≤ incidenceAction μ r (replicaThreshold r a b) Y := by
  classical
  set η : ℝ := Real.exp (-((r : ℝ) * (a - b) ^ 2 / 2)) with hη
  set S : Set Ω := {ω | a ≤ Y ω} with hS
  have hSm : MeasurableSet S := measurableSet_le measurable_const hYm
  have hpt : ∀ ω, S.indicator (fun _ => (1 - η : ℝ)) ω
      ≤ binomialTail r (replicaThreshold r a b) (Y ω) := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      exact one_sub_le_binomialTail_replicaThreshold (r := r) hb hba ha hω (hY1 ω)
    · rw [Set.indicator_of_notMem hω]
      exact binomialTail_nonneg (hY0 ω) (hY1 ω) r _
  have hint1 : Integrable (fun ω => S.indicator (fun _ => (1 - η : ℝ)) ω) μ :=
    (integrable_indicator_iff hSm).mpr integrableOn_const
  have hint2 := integrable_binomialTail_comp μ r (replicaThreshold r a b) hYm hY0 hY1
  have hle := integral_mono hint1 hint2 hpt
  rw [integral_indicator_const (1 - η : ℝ) hSm] at hle
  simp only [smul_eq_mul] at hle
  rw [incidenceAction]
  refine le_trans (le_of_eq ?_) hle
  ring

/-- **Return excision is paid once.**  The high-overlap incidence mass is bounded by the return
mass plus the return-excised action, with coefficient one on the return set. -/
theorem measure_le_return_add_restrictedIncidenceAction (μ : Measure Ω) [IsFiniteMeasure μ]
    {r : ℕ} {a b : ℝ} {Y : Ω → ℝ} (hYm : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) (hY1 : ∀ ω, Y ω ≤ 1)
    (hb : 0 < b) (hba : b < a) (ha : a < 1) (R : Set Ω)
    (hη : Real.exp (-((r : ℝ) * (a - b) ^ 2 / 2)) < 1) :
    μ.real {ω | a ≤ Y ω}
      ≤ μ.real R + restrictedIncidenceAction μ r (replicaThreshold r a b) Y R
          / (1 - Real.exp (-((r : ℝ) * (a - b) ^ 2 / 2))) := by
  classical
  set η : ℝ := Real.exp (-((r : ℝ) * (a - b) ^ 2 / 2)) with hηdef
  have hpos : 0 < 1 - η := by linarith
  have hSm : MeasurableSet {ω | a ≤ Y ω} := measurableSet_le measurable_const hYm
  haveI : IsFiniteMeasure (μ.restrict Rᶜ) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_lt_top μ Rᶜ
  have hlow := le_incidenceAction (μ.restrict Rᶜ) (r := r) hYm hY0 hY1 hb hba ha
  have hrestr : (μ.restrict Rᶜ).real {ω | a ≤ Y ω} = μ.real (Rᶜ ∩ {ω | a ≤ Y ω}) := by
    rw [measureReal_def, measureReal_def, Measure.restrict_apply hSm, Set.inter_comm]
  rw [hrestr] at hlow
  have hsplit : μ.real {ω | a ≤ Y ω} ≤ μ.real R + μ.real (Rᶜ ∩ {ω | a ≤ Y ω}) := by
    have hsub : {ω | a ≤ Y ω} ⊆ R ∪ (Rᶜ ∩ {ω | a ≤ Y ω}) := by
      intro ω hω
      by_cases hωR : ω ∈ R
      · exact Or.inl hωR
      · exact Or.inr ⟨hωR, hω⟩
    calc μ.real {ω | a ≤ Y ω} ≤ μ.real (R ∪ (Rᶜ ∩ {ω | a ≤ Y ω})) :=
          measureReal_mono hsub (by finiteness)
      _ ≤ μ.real R + μ.real (Rᶜ ∩ {ω | a ≤ Y ω}) := measureReal_union_le _ _
  have hdiv : μ.real (Rᶜ ∩ {ω | a ≤ Y ω})
      ≤ restrictedIncidenceAction μ r (replicaThreshold r a b) Y R / (1 - η) := by
    rw [le_div_iff₀ hpos]
    calc μ.real (Rᶜ ∩ {ω | a ≤ Y ω}) * (1 - η)
        = (1 - η) * μ.real (Rᶜ ∩ {ω | a ≤ Y ω}) := by ring
      _ ≤ _ := hlow
  linarith

/-! ### The beta coarea identity -/

private theorem isFiniteMeasure_volume_Ioc :
    IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Ioc]
  exact ENNReal.ofReal_lt_top

/-- **The exact beta-threshold coarea law.**  The bounded replica action is a unit-mass beta
average of the complete incidence masses `μ{Y ≥ u}`; each threshold set is formed before the
averaging, so no source fibre loses multiplicity. -/
theorem incidenceAction_eq_betaCoarea (μ : Measure Ω) [IsFiniteMeasure μ] {r k : ℕ}
    (hk1 : 1 ≤ k) (hkr : k ≤ r) {Y : Ω → ℝ}
    (hYm : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) (hY1 : ∀ ω, Y ω ≤ 1) :
    incidenceAction μ r k Y
      = ∫ u in Set.Ioc (0 : ℝ) 1, betaKernel r k u * μ.real {ω | u ≤ Y ω} := by
  classical
  haveI := isFiniteMeasure_volume_Ioc
  set M : ℝ := (r : ℝ) * ((r - 1).choose (k - 1) : ℝ) with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  set G : Ω → ℝ → ℝ := fun ω u => if u ≤ Y ω then betaKernel r k (max 0 u) else 0 with hG
  have hGbound : ∀ ω u, ‖G ω u‖ ≤ M := by
    intro ω u
    simp only [hG]
    by_cases h : u ≤ Y ω
    · simp only [if_pos h]
      have h0 : (0 : ℝ) ≤ max 0 u := le_max_left _ _
      have h1 : max 0 u ≤ 1 := max_le (by norm_num) (le_trans h (hY1 ω))
      rw [Real.norm_eq_abs, abs_of_nonneg (betaKernel_nonneg h0 h1 r k)]
      exact betaKernel_le h0 h1 r k
    · simp only [if_neg h, norm_zero]
      exact hM0
  have hGmeas : Measurable (Function.uncurry G) := by
    have hS : MeasurableSet {p : Ω × ℝ | p.2 ≤ Y p.1} :=
      measurableSet_le measurable_snd (hYm.comp measurable_fst)
    have h1 : Measurable fun p : Ω × ℝ => betaKernel r k (max 0 p.2) :=
      (continuous_betaKernel r k).measurable.comp (measurable_const.max measurable_snd)
    exact Measurable.ite hS h1 measurable_const
  have hGint : Integrable (Function.uncurry G) (μ.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    refine ⟨hGmeas.aestronglyMeasurable, ?_⟩
    exact HasFiniteIntegral.of_bounded (C := M)
      (Filter.Eventually.of_forall fun p => hGbound p.1 p.2)
  have hinner : ∀ ω, ∫ u in Set.Ioc (0 : ℝ) 1, G ω u = binomialTail r k (Y ω) := by
    intro ω
    have hcongr : ∀ u ∈ Set.Ioc (0 : ℝ) 1,
        G ω u = Set.indicator {v : ℝ | v ≤ Y ω} (betaKernel r k) u := by
      intro u hu
      simp only [hG]
      by_cases h : u ≤ Y ω
      · rw [if_pos h, Set.indicator_of_mem (show u ∈ {v : ℝ | v ≤ Y ω} from h),
          max_eq_right (le_of_lt hu.1)]
      · rw [if_neg h, Set.indicator_of_notMem (show u ∉ {v : ℝ | v ≤ Y ω} from h)]
    rw [setIntegral_congr_fun measurableSet_Ioc hcongr]
    rw [MeasureTheory.setIntegral_indicator
      (show MeasurableSet {v : ℝ | v ≤ Y ω} from measurableSet_le measurable_id measurable_const)]
    have hset : Set.Ioc (0 : ℝ) 1 ∩ {v : ℝ | v ≤ Y ω} = Set.Ioc (0 : ℝ) (Y ω) := by
      ext v
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, le_trans h2 (hY1 ω)⟩, h2⟩
    rw [hset, ← intervalIntegral.integral_of_le (hY0 ω)]
    exact binomialTail_eq_intervalIntegral r k hk1 hkr (Y ω)
  have houter : ∀ u ∈ Set.Ioc (0 : ℝ) 1,
      (∫ ω, G ω u ∂μ) = betaKernel r k u * μ.real {ω | u ≤ Y ω} := by
    intro u hu
    have hSm : MeasurableSet {ω | u ≤ Y ω} := measurableSet_le measurable_const hYm
    have hfun : (fun ω => G ω u)
        = Set.indicator {ω | u ≤ Y ω} (fun _ => betaKernel r k u) := by
      funext ω
      simp only [hG]
      by_cases h : u ≤ Y ω
      · rw [if_pos h, Set.indicator_of_mem (show ω ∈ {ω' | u ≤ Y ω'} from h),
          max_eq_right (le_of_lt hu.1)]
      · rw [if_neg h, Set.indicator_of_notMem (show ω ∉ {ω' | u ≤ Y ω'} from h)]
    rw [hfun, integral_indicator_const (betaKernel r k u) hSm, smul_eq_mul, mul_comm]
  calc incidenceAction μ r k Y = ∫ ω, (∫ u in Set.Ioc (0 : ℝ) 1, G ω u) ∂μ := by
        unfold incidenceAction
        exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (hinner ω).symm)
    _ = ∫ u in Set.Ioc (0 : ℝ) 1, (∫ ω, G ω u ∂μ) := integral_integral_swap hGint
    _ = ∫ u in Set.Ioc (0 : ℝ) 1, betaKernel r k u * μ.real {ω | u ≤ Y ω} :=
        setIntegral_congr_fun measurableSet_Ioc houter

/-- **Return excision commutes with the beta-threshold decomposition.** -/
theorem restrictedIncidenceAction_eq_betaCoarea (μ : Measure Ω) [IsFiniteMeasure μ] {r k : ℕ}
    (hk1 : 1 ≤ k) (hkr : k ≤ r) {Y : Ω → ℝ}
    (hYm : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) (hY1 : ∀ ω, Y ω ≤ 1) (R : Set Ω) :
    restrictedIncidenceAction μ r k Y R
      = ∫ u in Set.Ioc (0 : ℝ) 1, betaKernel r k u * μ.real (Rᶜ ∩ {ω | u ≤ Y ω}) := by
  haveI : IsFiniteMeasure (μ.restrict Rᶜ) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_lt_top μ Rᶜ
  rw [restrictedIncidenceAction, incidenceAction_eq_betaCoarea (μ.restrict Rᶜ) hk1 hkr hYm hY0 hY1]
  refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
  have hSm : MeasurableSet {ω | u ≤ Y ω} := measurableSet_le measurable_const hYm
  rw [measureReal_def, measureReal_def, Measure.restrict_apply hSm, Set.inter_comm]

/-! ### The probability-measure sandwich and the trace-distance form -/

/-- **Equation (6).**  The threshold sandwich on a probability space. -/
theorem incidenceAction_sandwich (μ : Measure Ω) [IsProbabilityMeasure μ] {r : ℕ} {a b : ℝ}
    {Y : Ω → ℝ} (hYm : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) (hY1 : ∀ ω, Y ω ≤ 1)
    (hb : 0 < b) (hba : b < a) (ha : a < 1) :
    (1 - Real.exp (-((r : ℝ) * (a - b) ^ 2 / 2))) * μ.real {ω | a ≤ Y ω}
        ≤ incidenceAction μ r (replicaThreshold r a b) Y ∧
      incidenceAction μ r (replicaThreshold r a b) Y
        ≤ μ.real {ω | b ≤ Y ω} + Real.exp (-((r : ℝ) * (a - b) ^ 2 / 2)) := by
  refine ⟨le_incidenceAction μ hYm hY0 hY1 hb hba ha, ?_⟩
  have h := incidenceAction_le μ (r := r) hYm hY0 hY1 hba ha
  rwa [probReal_univ, mul_one] at h

/-- **Equation (7).**  Beyond replica order `2 log 2 / δ²` the bounded test recovers the tight
incidence mass up to a factor two. -/
theorem measure_le_two_mul_incidenceAction (μ : Measure Ω) [IsProbabilityMeasure μ] {r : ℕ}
    {a b : ℝ} {Y : Ω → ℝ} (hYm : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) (hY1 : ∀ ω, Y ω ≤ 1)
    (hb : 0 < b) (hba : b < a) (ha : a < 1)
    (hr : 2 * Real.log 2 / (a - b) ^ 2 ≤ (r : ℝ)) :
    μ.real {ω | a ≤ Y ω} ≤ 2 * incidenceAction μ r (replicaThreshold r a b) Y := by
  have hδ : (0 : ℝ) < (a - b) ^ 2 := by positivity
  have hlog : Real.log 2 ≤ (r : ℝ) * (a - b) ^ 2 / 2 := by
    rw [div_le_iff₀ hδ] at hr
    linarith
  have hhalf : Real.exp (-((r : ℝ) * (a - b) ^ 2 / 2)) ≤ 1 / 2 := by
    have h1 : Real.exp (-((r : ℝ) * (a - b) ^ 2 / 2)) ≤ Real.exp (-Real.log 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    rw [h2] at h1; exact h1
  have hlow := le_incidenceAction μ (r := r) hYm hY0 hY1 hb hba ha
  have hmass : (0 : ℝ) ≤ μ.real {ω | a ≤ Y ω} := measureReal_nonneg
  nlinarith [hlow, hmass, hhalf]

/-- **Equation (24).**  The pure-state trace-distance form of the sandwich: with fidelity
thresholds `1 - ε₋²` and `1 - ε₊²` the slack is `δ = ε₊² - ε₋²`. -/
theorem incidenceAction_traceDistance_sandwich (μ : Measure Ω) [IsProbabilityMeasure μ] {r : ℕ}
    {em ep : ℝ} (hem : 0 < em) (hemp : em < ep) (hep : ep < 1)
    {Y : Ω → ℝ} (hYm : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) (hY1 : ∀ ω, Y ω ≤ 1) :
    (1 - Real.exp (-((r : ℝ) * (ep ^ 2 - em ^ 2) ^ 2 / 2)))
          * μ.real {ω | 1 - em ^ 2 ≤ Y ω}
        ≤ incidenceAction μ r (replicaThreshold r (1 - em ^ 2) (1 - ep ^ 2)) Y ∧
      incidenceAction μ r (replicaThreshold r (1 - em ^ 2) (1 - ep ^ 2)) Y
        ≤ μ.real {ω | 1 - ep ^ 2 ≤ Y ω}
            + Real.exp (-((r : ℝ) * (ep ^ 2 - em ^ 2) ^ 2 / 2)) := by
  have hb : (0 : ℝ) < 1 - ep ^ 2 := by nlinarith
  have hba : (1 : ℝ) - ep ^ 2 < 1 - em ^ 2 := by nlinarith
  have ha : (1 : ℝ) - em ^ 2 < 1 := by nlinarith
  have hδ : (1 - em ^ 2) - (1 - ep ^ 2) = ep ^ 2 - em ^ 2 := by ring
  have h := incidenceAction_sandwich μ (r := r) hYm hY0 hY1 hb hba ha
  rwa [hδ] at h

/-! ### Strict separation from the monomial reporter -/

/-- For a two-valued observable the bounded incidence action is exactly the source probability. -/
theorem incidenceAction_indicator (μ : Measure Ω) [IsFiniteMeasure μ] {r k : ℕ} (hk1 : 1 ≤ k)
    (hkr : k ≤ r) {S : Set Ω} (hS : MeasurableSet S) :
    incidenceAction μ r k (S.indicator (fun _ => (1 : ℝ))) = μ.real S := by
  classical
  have hfun : (fun ω => binomialTail r k (S.indicator (fun _ => (1 : ℝ)) ω))
      = S.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω, binomialTail_one_eq_one r k hkr]
    · rw [Set.indicator_of_notMem hω, binomialTail_zero_eq_zero r k hk1]
  unfold incidenceAction
  rw [hfun, integral_indicator_const (1 : ℝ) hS, smul_eq_mul, mul_one]

/-- The raw `r`-th moment of the same two-valued observable is also the source probability, so the
monomial Markov reporter overstates the bounded action by exactly the factor `a ^ (-r)`. -/
theorem monomial_reporter_indicator (μ : Measure Ω) [IsFiniteMeasure μ] {r : ℕ} (hr : 1 ≤ r)
    {S : Set Ω} (hS : MeasurableSet S) {a : ℝ} (ha : 0 < a) :
    a ^ r * (∫ ω, (S.indicator (fun _ => (1 : ℝ)) ω) ^ r ∂μ) / a ^ r = μ.real S ∧
      (∫ ω, (S.indicator (fun _ => (1 : ℝ)) ω) ^ r ∂μ) / a ^ r
        = a ^ (-(r : ℤ)) * μ.real S := by
  classical
  have hfun : (fun ω => (S.indicator (fun _ => (1 : ℝ)) ω) ^ r)
      = S.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω, one_pow]
    · rw [Set.indicator_of_notMem hω, zero_pow (by omega)]
  have hmom : (∫ ω, (S.indicator (fun _ => (1 : ℝ)) ω) ^ r ∂μ) = μ.real S := by
    rw [hfun, integral_indicator_const (1 : ℝ) hS, smul_eq_mul, mul_one]
  have hane : a ^ r ≠ 0 := by positivity
  refine ⟨by rw [hmom]; field_simp, ?_⟩
  rw [hmom, zpow_neg, zpow_natCast]
  field_simp

/-- The exact separation factor: on a two-valued observable the monomial reporter is `a ^ (-r)`
times the bounded replica action, for every admissible threshold count. -/
theorem monomial_reporter_eq_pow_mul_incidenceAction (μ : Measure Ω) [IsFiniteMeasure μ]
    {r k : ℕ} (hk1 : 1 ≤ k) (hkr : k ≤ r) {S : Set Ω} (hS : MeasurableSet S) {a : ℝ} (ha : 0 < a) :
    (∫ ω, (S.indicator (fun _ => (1 : ℝ)) ω) ^ r ∂μ) / a ^ r
      = a ^ (-(r : ℤ)) * incidenceAction μ r k (S.indicator (fun _ => (1 : ℝ))) := by
  rw [incidenceAction_indicator μ hk1 hkr hS]
  exact (monomial_reporter_indicator μ (le_trans hk1 hkr) hS ha).2

end

end GaloisForLFunctions.HTGeometry

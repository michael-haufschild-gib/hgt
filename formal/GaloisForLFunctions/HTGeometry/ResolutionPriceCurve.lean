import GaloisForLFunctions.HTGeometry.TopologicallyAdmittedCompactEffectProperness

/-!
# The resolution price curve

For a metric space `X` and probability laws `μ₀, μ₁`, the least Lipschitz constant
`Lip(f) ∈ [0, ∞]` of a real function gives the resolution price curve

`𝓡_μ(r) = inf {Lip(e) : e : X → [0, 1], ∫ e dμ₁ - ∫ e dμ₀ ≥ r}`,

with `inf ∅ = ∞`.  The curve is nondecreasing with `𝓡_μ(0) = 0`.  For full-support laws on a
compact space no continuous effect has contrast one, so `𝓡_μ(1) = ∞`, and the effects of
Lipschitz constant at most `M` form a compact family whose contrast gap forces `𝓡_μ(r) → ∞` as
`r ↑ 1`.  For mutually singular laws inner regularity supplies disjoint closed sets carrying almost
all of each law, and the truncated distance to one of them is a Lipschitz effect of contrast
arbitrarily close to one: every level below one is reached at finite price.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## The Lipschitz norm -/

section LipNorm

variable {X : Type*} [PseudoMetricSpace X]

/-- The least Lipschitz constant `Lip(f) ∈ [0, ∞]`. -/
def lipNorm (f : X → ℝ) : ℝ≥0∞ := ⨅ (K : ℝ≥0) (_ : LipschitzWith K f), (K : ℝ≥0∞)

theorem lipNorm_le {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) : lipNorm f ≤ K :=
  iInf₂_le K hf

theorem lipschitzWith_of_lipNorm_lt_top {f : X → ℝ} (hf : lipNorm f < ⊤) :
    LipschitzWith (lipNorm f).toNNReal f := by
  intro x y
  by_cases hxy : edist x y = 0
  · have hfxy : edist (f x) (f y) = 0 := by
      have hne : ∃ K : ℝ≥0, LipschitzWith K f := by
        by_contra h
        push Not at h
        have : lipNorm f = ⊤ := by
          rw [lipNorm]
          simp only [iInf_eq_top]
          intro K hK
          exact absurd hK (h K)
        exact absurd this hf.ne
      obtain ⟨K, hK⟩ := hne
      have := hK x y
      rw [hxy, mul_zero] at this
      exact le_antisymm this bot_le
    rw [hfxy]
    exact bot_le
  have hfin : edist x y ≠ ⊤ := edist_ne_top x y
  rw [ENNReal.coe_toNNReal hf.ne, lipNorm, ENNReal.iInf_mul_of_ne hxy hfin]
  refine le_iInf fun K => ?_
  rw [ENNReal.iInf_mul_of_ne hxy hfin]
  exact le_iInf fun hK => hK x y

theorem lipNorm_lt_top_iff {f : X → ℝ} : lipNorm f < ⊤ ↔ ∃ K : ℝ≥0, LipschitzWith K f := by
  constructor
  · intro h
    exact ⟨_, lipschitzWith_of_lipNorm_lt_top h⟩
  · rintro ⟨K, hK⟩
    exact (lipNorm_le hK).trans_lt ENNReal.coe_lt_top

theorem abs_sub_le_lipNorm_mul {f : X → ℝ} (hf : lipNorm f < ⊤) (x y : X) :
    |f x - f y| ≤ (lipNorm f).toReal * dist x y := by
  have h := (lipschitzWith_of_lipNorm_lt_top hf).dist_le_mul x y
  rw [Real.dist_eq] at h
  exact h

theorem lipNorm_const (c : ℝ) : lipNorm (fun _ : X => c) = 0 :=
  le_antisymm ((lipNorm_le (LipschitzWith.const c)).trans (by simp)) bot_le

/-- A function of zero Lipschitz norm is constant on a metric space. -/
theorem eq_of_lipNorm_eq_zero {f : X → ℝ} (hf : lipNorm f = 0) (x y : X) : f x = f y := by
  have h := abs_sub_le_lipNorm_mul (hf ▸ ENNReal.zero_lt_top) x y
  rw [hf, ENNReal.toReal_zero, zero_mul] at h
  linarith [abs_nonneg (f x - f y), sub_eq_zero.mp (abs_nonpos_iff.mp h)]

end LipNorm

/-! ## The resolution price curve -/

section Price

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **(RP.3).**  The resolution price curve `𝓡_μ(r)`. -/
def lipschitzResolutionPrice (P Q : Measure X) (r : ℝ) : ℝ≥0∞ :=
  ⨅ (e : X → ℝ) (_ : ∀ x, e x ∈ Icc (0 : ℝ) 1) (_ : r ≤ hahnEffectCurrent P Q e), lipNorm e

omit [BorelSpace X] in
theorem lipschitzResolutionPrice_le (P Q : Measure X) {r : ℝ} {e : X → ℝ}
    (he : ∀ x, e x ∈ Icc (0 : ℝ) 1) (hr : r ≤ hahnEffectCurrent P Q e) :
    lipschitzResolutionPrice P Q r ≤ lipNorm e :=
  (iInf₂_le e he).trans (iInf_le _ hr)

omit [BorelSpace X] in
/-- **Theorem 2.1.**  The price curve is nondecreasing. -/
theorem lipschitzResolutionPrice_mono (P Q : Measure X) :
    Monotone (lipschitzResolutionPrice P Q) := by
  intro r r' hrr'
  refine le_iInf₂ fun e he => le_iInf fun hr' => ?_
  exact lipschitzResolutionPrice_le P Q he (hrr'.trans hr')

omit [BorelSpace X] in
/-- **Theorem 2.1.**  `𝓡_μ(0) = 0`. -/
theorem lipschitzResolutionPrice_zero (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] : lipschitzResolutionPrice P Q 0 = 0 := by
  refine le_antisymm ?_ bot_le
  have h := lipschitzResolutionPrice_le P Q (r := 0) (e := fun _ => (0 : ℝ))
    (fun _ => ⟨le_rfl, zero_le_one⟩) (by simp [hahnEffectCurrent])
  rwa [lipNorm_const] at h

/-- **Theorem 2.1 (RP.4).**  For full-support laws on a compact space, `𝓡_μ(1) = ∞`. -/
theorem lipschitzResolutionPrice_one (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q]
    [P.IsOpenPosMeasure] [Q.IsOpenPosMeasure] : lipschitzResolutionPrice P Q 1 = ⊤ := by
  rw [lipschitzResolutionPrice]
  simp only [iInf_eq_top]
  intro e he hr
  by_contra hlt
  have hfin : lipNorm e < ⊤ := lt_top_iff_ne_top.mpr hlt
  have hcont := (lipschitzWith_of_lipNorm_lt_top hfin).continuous
  have := abs_hahnEffectCurrent_lt_one P Q hcont he
  rw [abs_lt] at this
  linarith [this.2]

/-- **Theorem 2.1 (RP.4).**  `𝓡_μ(r) → ∞` as `r ↑ 1` for full-support laws on a compact space. -/
theorem tendsto_lipschitzResolutionPrice_one [CompactSpace X] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [P.IsOpenPosMeasure] [Q.IsOpenPosMeasure] :
    Tendsto (lipschitzResolutionPrice P Q) (𝓝[<] 1) (𝓝 ⊤) := by
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  intro M
  set L : ℝ≥0 := M + 1 with hLdef
  set E : Set C(X, ℝ) := {e | (∀ x, e x ∈ Icc (0 : ℝ) 1) ∧ LipschitzWith L e} with hEdef
  have hEeq : Equicontinuous fun e : E => ((e : C(X, ℝ)) : X → ℝ) :=
    (LipschitzWith.uniformEquicontinuous _ L fun (e : E) => e.2.2).equicontinuous
  have hEclosed : IsClosed E := by
    have h1 : IsClosed {e : C(X, ℝ) | ∀ x, e x ∈ Icc (0 : ℝ) 1} := isClosed_effects
    have h2 : IsClosed {e : C(X, ℝ) | LipschitzWith L e} := by
      have : {e : C(X, ℝ) | LipschitzWith L e}
          = ⋂ x, ⋂ y, {e : C(X, ℝ) | dist (e x) (e y) ≤ L * dist x y} := by
        ext e
        simp only [mem_setOf_eq, mem_iInter]
        exact ⟨fun h x y => h.dist_le_mul x y, fun h => LipschitzWith.of_dist_le_mul h⟩
      rw [this]
      exact isClosed_iInter fun x => isClosed_iInter fun y =>
        isClosed_le ((continuous_eval_const x).dist (continuous_eval_const y)) continuous_const
    exact h1.inter h2
  have hEcompact : IsCompact E := by
    have := isCompact_closure_of_equicontinuous (F := E) (fun e he => he.1) hEeq
    rwa [hEclosed.closure_eq] at this
  have hEne : E.Nonempty := ⟨ContinuousMap.const X 0, fun _ => ⟨le_rfl, zero_le_one⟩,
    LipschitzWith.const' 0⟩
  obtain ⟨hη, hle⟩ := effectContrastGap_pos P Q hEcompact hEne fun e he => he.1
  set η := effectContrastGap P Q E
  filter_upwards [Ioo_mem_nhdsLT (show 1 - η < 1 by linarith)] with r hr
  have hge : (L : ℝ≥0∞) ≤ lipschitzResolutionPrice P Q r := by
    refine le_iInf₂ fun e he => le_iInf fun hre => ?_
    by_contra hlt
    push Not at hlt
    have hfin : lipNorm e < ⊤ := hlt.trans ENNReal.coe_lt_top
    have hlip : LipschitzWith L e := (lipschitzWith_of_lipNorm_lt_top hfin).weaken (by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin.ne]
      exact hlt.le)
    have hmem : (⟨e, hlip.continuous⟩ : C(X, ℝ)) ∈ E := ⟨he, hlip⟩
    have h := hle _ hmem
    change |hahnEffectCurrent P Q e| ≤ 1 - η at h
    have := le_abs_self (hahnEffectCurrent P Q e)
    linarith [hr.1]
  exact lt_of_lt_of_le (by rw [hLdef]; exact_mod_cast lt_add_one M) hge

/-- **Theorem 2.1 (RP.5)–(RP.6).**  For mutually singular laws on a compact metric space every
contrast level below one is reached at finite price. -/
theorem lipschitzResolutionPrice_lt_top_of_singular [CompactSpace X] {P Q : Measure X}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ⟂ₘ Q) {r : ℝ} (hr : r < 1) :
    lipschitzResolutionPrice P Q r < ⊤ := by
  rcases le_or_gt r 0 with hr0 | hr0
  · refine (lipschitzResolutionPrice_le P Q (e := fun _ => (0 : ℝ))
      (fun _ => ⟨le_rfl, zero_le_one⟩) (by simp [hahnEffectCurrent]; exact hr0)).trans_lt ?_
    rw [lipNorm_const]
    exact ENNReal.zero_lt_top
  set ε : ℝ := (1 - r) / 4 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hS := hPQ.measurableSet_nullSet
  obtain ⟨F, hFS, hFc, hF⟩ := hS.exists_isClosed_lt_add (μ := Q) (measure_ne_top Q _)
    (ε := ENNReal.ofReal ε) (by simpa using hε)
  obtain ⟨G, hGS, hGc, hG⟩ := hS.compl.exists_isClosed_lt_add (μ := P) (measure_ne_top P _)
    (ε := ENNReal.ofReal ε) (by simpa using hε)
  have hQS : Q hPQ.nullSet = 1 := by
    rw [← prob_compl_eq_zero_iff hS]
    exact hPQ.measure_compl_nullSet
  have hPSc : P hPQ.nullSetᶜ = 1 := by
    rw [prob_compl_eq_one_iff hS]
    exact hPQ.measure_nullSet
  rw [hQS] at hF
  rw [hPSc] at hG
  have hQF : 1 - ε < Q.real F := by
    have h1 : (1 : ℝ≥0∞) < ENNReal.ofReal (Q.real F + ε) := by
      rw [ENNReal.ofReal_add measureReal_nonneg hε.le, Measure.real_def,
        ENNReal.ofReal_toReal (measure_ne_top Q _)]
      exact hF
    have := (ENNReal.one_lt_ofReal).mp h1
    linarith
  have hPG : 1 - ε < P.real G := by
    have h1 : (1 : ℝ≥0∞) < ENNReal.ofReal (P.real G + ε) := by
      rw [ENNReal.ofReal_add measureReal_nonneg hε.le, Measure.real_def,
        ENNReal.ofReal_toReal (measure_ne_top P _)]
      exact hG
    have := (ENNReal.one_lt_ofReal).mp h1
    linarith
  have hFne : F.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, measureReal_empty] at hQF
    linarith
  have hGne : G.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, measureReal_empty] at hPG
    linarith
  have hdisj : ∀ x ∈ F, x ∉ G := fun x hxF hxG => hGS hxG (hFS hxF)
  obtain ⟨x₀, hx₀F, hmin⟩ := hFc.isCompact.exists_isMinOn hFne
    (continuous_infDist_pt G).continuousOn
  set δ : ℝ := infDist x₀ G with hδdef
  have hδ : 0 < δ := (infDist_pos_iff_notMem_closure hGne).mp (by
    rw [hGc.closure_eq]; exact hdisj x₀ hx₀F)
  set e : X → ℝ := fun x => min 1 (infDist x G / δ) with hedef
  have hlip : LipschitzWith (⟨1 / δ, by positivity⟩ : ℝ≥0) e := by
    refine LipschitzWith.const_min ?_ 1
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h := (lipschitz_infDist_pt G).dist_le_mul x y
    rw [Real.dist_eq, NNReal.coe_one, one_mul] at h
    change dist (infDist x G / δ) (infDist y G / δ) ≤ 1 / δ * dist x y
    rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hδ]
    calc |infDist x G - infDist y G| / δ = 1 / δ * |infDist x G - infDist y G| := by ring
      _ ≤ 1 / δ * dist x y := mul_le_mul_of_nonneg_left h (by positivity)
  have hemeas : Measurable e := hlip.continuous.measurable
  have heb : ∀ x, e x ∈ Icc (0 : ℝ) 1 := fun x =>
    ⟨le_min zero_le_one (div_nonneg infDist_nonneg hδ.le), min_le_left _ _⟩
  have heF : ∀ x ∈ F, e x = 1 := fun x hx => by
    have h := hmin hx
    simp only [mem_setOf_eq] at h
    rw [hedef]
    exact min_eq_left ((one_le_div hδ).mpr h)
  have heG : ∀ x ∈ G, e x = 0 := fun x hx => by
    rw [hedef]
    simp [infDist_zero_of_mem hx]
  have hint : ∀ (μ : Measure X) [IsProbabilityMeasure μ], Integrable e μ := fun μ _ =>
    integrable_of_bound hemeas (C := 1) fun x => abs_le.mpr ⟨by linarith [(heb x).1], (heb x).2⟩
  have hQe : Q.real F ≤ ∫ x, e x ∂Q := by
    have h1 : ∫ x, F.indicator (fun _ => (1 : ℝ)) x ∂Q = Q.real F := by
      rw [integral_indicator_const _ hFc.measurableSet, smul_eq_mul, mul_one]
    rw [← h1]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator hFc.measurableSet) (hint Q)
      fun x => ?_
    by_cases hx : x ∈ F
    · simp [indicator_of_mem hx, heF x hx]
    · simp [indicator_of_notMem hx, (heb x).1]
  have hPe : ∫ x, e x ∂P ≤ P.real Gᶜ := by
    have h1 : ∫ x, Gᶜ.indicator (fun _ => (1 : ℝ)) x ∂P = P.real Gᶜ := by
      rw [integral_indicator_const _ hGc.measurableSet.compl, smul_eq_mul, mul_one]
    rw [← h1]
    refine integral_mono (hint P) ((integrable_const (1 : ℝ)).indicator hGc.measurableSet.compl)
      fun x => ?_
    by_cases hx : x ∈ G
    · simp [indicator_of_notMem (show x ∉ Gᶜ from not_not.mpr hx), heG x hx]
    · simp [indicator_of_mem (show x ∈ Gᶜ from hx), (heb x).2]
  have hPGc : P.real Gᶜ = 1 - P.real G := by
    rw [measureReal_compl hGc.measurableSet, probReal_univ]
  have hcur : r ≤ hahnEffectCurrent P Q e := by
    rw [hahnEffectCurrent]
    linarith
  exact (lipschitzResolutionPrice_le P Q heb hcur).trans_lt
    ((lipNorm_le hlip).trans_lt ENNReal.coe_lt_top)

end Price

end GaloisForLFunctions.HTGeometry

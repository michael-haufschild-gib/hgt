import GaloisForLFunctions.HTGeometry.TopologicallyAdmittedFellerAdmission

/-!
# Tensor Feller admission, decision escape, and transport

This closes the tensor-power, Neyman--Pearson/Hellinger, cofinal-fracture, and
homeomorphism-covariance clauses of ULF-TAFM-4 on top of the exact finite
admission classification.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

namespace FiniteProbabilityLaw

variable {Y : Type v} [Fintype Y]

/-- Independent finite tensor power of a finite probability law. -/
def tensorPower (p : FiniteProbabilityLaw Y) (d : ℕ) :
    FiniteProbabilityLaw (Fin d → Y) where
  prob y := ∏ i, p.prob (y i)
  nonneg y := Finset.prod_nonneg fun i _ => p.nonneg (y i)
  sum_prob := by
    classical
    rw [← Fintype.piFinset_univ,
      ← Finset.prod_univ_sum (fun _ : Fin d => (Finset.univ : Finset Y))
        (fun _ y => p.prob y)]
    simp only [p.sum_prob, Finset.prod_const_one]

theorem tensorPower_prob (p : FiniteProbabilityLaw Y) (d : ℕ) (y : Fin d → Y) :
    (p.tensorPower d).prob y = ∏ i, p.prob (y i) := rfl

theorem tensorPower_same_zero_set {p₀ p₁ : FiniteProbabilityLaw Y}
    (hzero : ∀ y, p₀.prob y = 0 ↔ p₁.prob y = 0) (d : ℕ) (y : Fin d → Y) :
    (p₀.tensorPower d).prob y = 0 ↔ (p₁.tensorPower d).prob y = 0 := by
  simp only [tensorPower_prob, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨i, _, hi⟩
    exact ⟨i, Finset.mem_univ i, (hzero (y i)).mp hi⟩
  · rintro ⟨i, _, hi⟩
    exact ⟨i, Finset.mem_univ i, (hzero (y i)).mpr hi⟩

/-- Hellinger affinity of two finite probability laws in simplex coordinates. -/
def fellerHellingerAffinity (p₀ p₁ : FiniteProbabilityLaw Y) : ℝ :=
  ∑ y, Real.sqrt (p₀.prob y * p₁.prob y)

/-- Neyman--Pearson event, oriented from `p₀` toward `p₁`. -/
def fellerDecisionEvent (p₀ p₁ : FiniteProbabilityLaw Y) : Finset Y :=
  Finset.univ.filter fun y => p₀.prob y ≤ p₁.prob y

/-- Probability contrast attained by the finite Neyman--Pearson event. -/
def fellerDecisionGap (p₀ p₁ : FiniteProbabilityLaw Y) : ℝ :=
  ∑ y ∈ fellerDecisionEvent p₀ p₁, (p₁.prob y - p₀.prob y)

private theorem sqrt_mul_lt_average {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hne : a ≠ b) :
    Real.sqrt (a * b) < (a + b) / 2 := by
  have havg : 0 < (a + b) / 2 := by
    by_cases ha0 : a = 0
    · subst a
      simp only [zero_add, div_pos_iff]
      exact Or.inl ⟨lt_of_le_of_ne hb hne, by norm_num⟩
    · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      positivity
  rw [Real.sqrt_lt' havg]
  nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hne)]

private theorem sqrt_mul_le_average {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  by_cases hne : a = b
  · subst b
    rw [show a * a = a ^ 2 by ring, Real.sqrt_sq ha]
    linarith
  · exact (sqrt_mul_lt_average ha hb hne).le

theorem fellerHellingerAffinity_nonneg (p₀ p₁ : FiniteProbabilityLaw Y) :
    0 ≤ fellerHellingerAffinity p₀ p₁ :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

theorem fellerHellingerAffinity_pos_of_same_zero_set
    (p₀ p₁ : FiniteProbabilityLaw Y)
    (hzero : ∀ y, p₀.prob y = 0 ↔ p₁.prob y = 0) :
    0 < fellerHellingerAffinity p₀ p₁ := by
  have hex : ∃ y, 0 < p₀.prob y := by
    by_contra h
    push Not at h
    have hsum : ∑ y, p₀.prob y ≤ 0 :=
      Finset.sum_nonpos fun y _ => h y
    rw [p₀.sum_prob] at hsum
    norm_num at hsum
  obtain ⟨y, hy₀⟩ := hex
  have hy₁ne : p₁.prob y ≠ 0 := by
    intro hy₁
    exact (ne_of_gt hy₀) ((hzero y).mpr hy₁)
  have hy₁ : 0 < p₁.prob y :=
    lt_of_le_of_ne (p₁.nonneg y) (Ne.symm hy₁ne)
  have hterm : 0 < Real.sqrt (p₀.prob y * p₁.prob y) :=
    Real.sqrt_pos.2 (mul_pos hy₀ hy₁)
  unfold fellerHellingerAffinity
  calc
    0 < Real.sqrt (p₀.prob y * p₁.prob y) := hterm
    _ ≤ ∑ z, Real.sqrt (p₀.prob z * p₁.prob z) :=
      Finset.single_le_sum
        (fun z (_ : z ∈ (Finset.univ : Finset Y)) =>
          Real.sqrt_nonneg (p₀.prob z * p₁.prob z))
        (Finset.mem_univ y)

theorem fellerHellingerAffinity_lt_one_of_ne
    (p₀ p₁ : FiniteProbabilityLaw Y) (hne : p₀ ≠ p₁) :
    fellerHellingerAffinity p₀ p₁ < 1 := by
  have hcoord : ∃ y, p₀.prob y ≠ p₁.prob y := by
    by_contra h
    apply hne
    have hprob : p₀.prob = p₁.prob := by
      funext y
      exact not_not.mp (not_exists.mp h y)
    cases p₀
    cases p₁
    cases hprob
    rfl
  calc
    fellerHellingerAffinity p₀ p₁ <
        ∑ y, (p₀.prob y + p₁.prob y) / 2 := by
      unfold fellerHellingerAffinity
      apply Finset.sum_lt_sum
      · intro y _
        exact sqrt_mul_le_average (p₀.nonneg y) (p₁.nonneg y)
      · obtain ⟨y, hy⟩ := hcoord
        exact ⟨y, Finset.mem_univ y,
          sqrt_mul_lt_average (p₀.nonneg y) (p₁.nonneg y) hy⟩
    _ = 1 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, p₀.sum_prob, p₁.sum_prob]
      norm_num

theorem fellerDecisionGap_eq_one_sub_sum_min
    (p₀ p₁ : FiniteProbabilityLaw Y) :
    fellerDecisionGap p₀ p₁ = 1 - ∑ y, min (p₀.prob y) (p₁.prob y) := by
  classical
  unfold fellerDecisionGap fellerDecisionEvent
  rw [Finset.sum_filter]
  calc
    (∑ y, if p₀.prob y ≤ p₁.prob y then p₁.prob y - p₀.prob y else 0) =
        (∑ y, (p₁.prob y - min (p₀.prob y) (p₁.prob y))) := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : p₀.prob y ≤ p₁.prob y
      · simp [h]
      · have h' : p₁.prob y ≤ p₀.prob y := le_of_not_ge h
        simp [h, min_eq_right h']
    _ = 1 - (∑ y, min (p₀.prob y) (p₁.prob y)) := by
      rw [Finset.sum_sub_distrib, p₁.sum_prob]

theorem one_sub_fellerHellingerAffinity_le_decisionGap
    (p₀ p₁ : FiniteProbabilityLaw Y) :
    1 - fellerHellingerAffinity p₀ p₁ ≤ fellerDecisionGap p₀ p₁ := by
  rw [fellerDecisionGap_eq_one_sub_sum_min]
  have hsum :
      ∑ y, min (p₀.prob y) (p₁.prob y) ≤
        ∑ y, Real.sqrt (p₀.prob y * p₁.prob y) := by
    apply Finset.sum_le_sum
    intro y _
    by_cases h : p₀.prob y ≤ p₁.prob y
    · rw [min_eq_left h]
      have hs : p₀.prob y ^ 2 ≤ p₀.prob y * p₁.prob y := by
        nlinarith [p₀.nonneg y]
      calc
        p₀.prob y = Real.sqrt (p₀.prob y ^ 2) :=
          (Real.sqrt_sq (p₀.nonneg y)).symm
        _ ≤ _ := Real.sqrt_le_sqrt hs
    · have h' : p₁.prob y ≤ p₀.prob y := le_of_not_ge h
      rw [min_eq_right h']
      have hs : p₁.prob y ^ 2 ≤ p₀.prob y * p₁.prob y := by
        nlinarith [p₁.nonneg y]
      calc
        p₁.prob y = Real.sqrt (p₁.prob y ^ 2) :=
          (Real.sqrt_sq (p₁.nonneg y)).symm
        _ ≤ _ := Real.sqrt_le_sqrt hs
  unfold fellerHellingerAffinity
  linarith

theorem fellerHellingerAffinity_tensorPower
    (p₀ p₁ : FiniteProbabilityLaw Y) (d : ℕ) :
    fellerHellingerAffinity (p₀.tensorPower d) (p₁.tensorPower d) =
      fellerHellingerAffinity p₀ p₁ ^ d := by
  classical
  unfold fellerHellingerAffinity
  simp only [tensorPower_prob]
  calc
    ∑ y : Fin d → Y,
        Real.sqrt ((∏ i, p₀.prob (y i)) * ∏ i, p₁.prob (y i)) =
        ∑ y : Fin d → Y,
          ∏ i, Real.sqrt (p₀.prob (y i) * p₁.prob (y i)) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.prod_mul_distrib]
      exact Real.sqrt_prod Finset.univ
        (fun i _ => mul_nonneg (p₀.nonneg (y i)) (p₁.nonneg (y i)))
    _ = ∏ _i : Fin d, ∑ y, Real.sqrt (p₀.prob y * p₁.prob y) := by
      rw [← Fintype.piFinset_univ,
        ← Finset.prod_univ_sum (fun _ : Fin d => (Finset.univ : Finset Y))
          (fun _ y => Real.sqrt (p₀.prob y * p₁.prob y))]
    _ = (∑ y, Real.sqrt (p₀.prob y * p₁.prob y)) ^ d := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end FiniteProbabilityLaw

namespace FiniteFellerKernel

variable {X : Type u} {Y : Type v}
  [PseudoMetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [Fintype Y]

/-- Continuous source effect associated with a finite target event. -/
def eventEffect (K : FiniteFellerKernel X Y) (B : Finset Y) :
    C(X, unitInterval) where
  toFun x :=
    ⟨∑ y ∈ B, ((K.coord y x : unitInterval) : ℝ),
      Finset.sum_nonneg fun y _ => (K.coord y x).2.1,
      by
        calc
          ∑ y ∈ B, ((K.coord y x : unitInterval) : ℝ) ≤
              ∑ y, ((K.coord y x : unitInterval) : ℝ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
            intro y _ _
            exact (K.coord y x).2.1
          _ = 1 := K.sum_coord x⟩
  continuous_toFun := by
    fun_prop

omit [CompactSpace X] in
theorem mixingMean_eventEffect (K : FiniteFellerKernel X Y) (B : Finset Y)
    (μ : Measure X) [IsProbabilityMeasure μ] :
    mixingMean (K.eventEffect B) μ = ∑ y ∈ B, K.pushMass μ y := by
  rw [mixingMean]
  change (∫ x, ∑ y ∈ B, ((K.coord y x : unitInterval) : ℝ) ∂μ) = _
  have hint : ∀ y ∈ B,
      Integrable (fun x => ((K.coord y x : unitInterval) : ℝ)) μ := by
    intro y _
    exact K.coord_integrable μ y
  rw [MeasureTheory.integral_finsetSum B hint]
  rfl

/-- Pull a finite Feller kernel through a source homeomorphism. -/
def transport (K : FiniteFellerKernel X Y) (τ : X ≃ₜ X) :
    FiniteFellerKernel X Y where
  coord y :=
    ⟨fun x => K.coord y (τ.symm x),
      (K.coord y).continuous.comp τ.symm.continuous⟩
  sum_coord x := by simpa using K.sum_coord (τ.symm x)

omit [CompactSpace X] in
/-- Transporting both source laws by one homeomorphism leaves every pushed
finite target law unchanged after kernel precomposition. -/
theorem transport_pushMass_map (K : FiniteFellerKernel X Y) (τ : X ≃ₜ X)
    (μ : Measure X) (y : Y) :
    (K.transport τ).pushMass (μ.map τ) y = K.pushMass μ y := by
  unfold pushMass transport
  rw [MeasureTheory.integral_map τ.measurable.aemeasurable]
  · simp
  · exact (continuous_subtype_val.comp
      ((K.coord y).continuous.comp τ.symm.continuous)).aestronglyMeasurable

omit [CompactSpace X] in
theorem map_homeomorph_symm_map (τ : X ≃ₜ X) (μ : Measure X) :
    (μ.map τ).map τ.symm = μ := by
  ext s hs
  rw [Measure.map_apply τ.symm.measurable hs,
    Measure.map_apply τ.measurable (τ.symm.measurable hs)]
  congr 1
  ext x
  simp

omit [CompactSpace X] in
/-- Homeomorphic source transport preserves the complete finite admission set. -/
theorem exists_pushMass_map_homeomorph_iff
    (τ : X ≃ₜ X) (μ : Measure X) (p : Y → ℝ) :
    (∃ K : FiniteFellerKernel X Y, ∀ y, K.pushMass (μ.map τ) y = p y) ↔
      ∃ K : FiniteFellerKernel X Y, ∀ y, K.pushMass μ y = p y := by
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K.transport τ.symm, fun y => ?_⟩
    have htransport := transport_pushMass_map K τ.symm (μ.map τ) y
    rw [map_homeomorph_symm_map] at htransport
    exact htransport.trans (hK y)
  · rintro ⟨K, hK⟩
    refine ⟨K.transport τ, fun y => ?_⟩
    exact (transport_pushMass_map K τ μ y).trans (hK y)

/-- Every finite tensor power of a common-support target pair is exactly
Feller-admitted by the same compact singular source experiment. -/
theorem exists_pushMass_eq_tensorPower
    (μ₀ μ₁ : Measure X) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (hsing : μ₀ ⟂ₘ μ₁)
    (p₀ p₁ : FiniteProbabilityLaw Y)
    (hzero : ∀ y, p₀.prob y = 0 ↔ p₁.prob y = 0)
    (d : ℕ) :
    ∃ K : FiniteFellerKernel X (Fin d → Y),
      (∀ y, K.pushMass μ₀ y = (p₀.tensorPower d).prob y) ∧
      (∀ y, K.pushMass μ₁ y = (p₁.tensorPower d).prob y) := by
  apply exists_pushMass_eq_of_mutuallySingular_of_same_zero_set μ₀ μ₁ hsing
  exact FiniteProbabilityLaw.tensorPower_same_zero_set hzero d

/-- Source effect obtained by pulling the tensor-product Neyman--Pearson event
back through an exact finite Feller admission kernel. -/
def tensorDecisionEffect (p₀ p₁ : FiniteProbabilityLaw Y) (d : ℕ)
    (K : FiniteFellerKernel X (Fin d → Y)) : C(X, unitInterval) :=
  K.eventEffect
    (FiniteProbabilityLaw.fellerDecisionEvent (p₀.tensorPower d) (p₁.tensorPower d))

omit [CompactSpace X] in
theorem tensorDecisionEffect_contrast_eq
    (μ₀ μ₁ : Measure X) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (p₀ p₁ : FiniteProbabilityLaw Y) (d : ℕ)
    (K : FiniteFellerKernel X (Fin d → Y))
    (hK₀ : ∀ y, K.pushMass μ₀ y = (p₀.tensorPower d).prob y)
    (hK₁ : ∀ y, K.pushMass μ₁ y = (p₁.tensorPower d).prob y) :
    mixingMean (tensorDecisionEffect p₀ p₁ d K) μ₁ -
        mixingMean (tensorDecisionEffect p₀ p₁ d K) μ₀ =
      FiniteProbabilityLaw.fellerDecisionGap
        (p₀.tensorPower d) (p₁.tensorPower d) := by
  rw [tensorDecisionEffect, mixingMean_eventEffect, mixingMean_eventEffect]
  simp_rw [hK₀, hK₁]
  rw [← Finset.sum_sub_distrib]
  rfl

omit [CompactSpace X] in
theorem one_sub_affinity_pow_le_tensorDecisionEffect_contrast
    (μ₀ μ₁ : Measure X) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (p₀ p₁ : FiniteProbabilityLaw Y) (d : ℕ)
    (K : FiniteFellerKernel X (Fin d → Y))
    (hK₀ : ∀ y, K.pushMass μ₀ y = (p₀.tensorPower d).prob y)
    (hK₁ : ∀ y, K.pushMass μ₁ y = (p₁.tensorPower d).prob y) :
    1 - FiniteProbabilityLaw.fellerHellingerAffinity p₀ p₁ ^ d ≤
      mixingMean (tensorDecisionEffect p₀ p₁ d K) μ₁ -
        mixingMean (tensorDecisionEffect p₀ p₁ d K) μ₀ := by
  rw [tensorDecisionEffect_contrast_eq μ₀ μ₁ p₀ p₁ d K hK₀ hK₁,
    ← FiniteProbabilityLaw.fellerHellingerAffinity_tensorPower]
  exact FiniteProbabilityLaw.one_sub_fellerHellingerAffinity_le_decisionGap _ _

omit [CompactSpace X] in
theorem tendsto_tensorDecisionEffect_contrast
    [Nonempty X]
    (μ₀ μ₁ : Measure X) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (p₀ p₁ : FiniteProbabilityLaw Y) (hne : p₀ ≠ p₁)
    (K : ∀ d, FiniteFellerKernel X (Fin d → Y))
    (hK₀ : ∀ d y, (K d).pushMass μ₀ y = (p₀.tensorPower d).prob y)
    (hK₁ : ∀ d y, (K d).pushMass μ₁ y = (p₁.tensorPower d).prob y) :
    Filter.Tendsto (fun d =>
      mixingMean (tensorDecisionEffect p₀ p₁ d (K d)) μ₁ -
        mixingMean (tensorDecisionEffect p₀ p₁ d (K d)) μ₀)
      Filter.atTop (nhds 1) := by
  let A := FiniteProbabilityLaw.fellerHellingerAffinity p₀ p₁
  have hA0 : 0 ≤ A := FiniteProbabilityLaw.fellerHellingerAffinity_nonneg p₀ p₁
  have hA1 : A < 1 := FiniteProbabilityLaw.fellerHellingerAffinity_lt_one_of_ne p₀ p₁ hne
  have hpow : Filter.Tendsto (fun d : ℕ => A ^ d) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hA0 hA1
  have hlower : Filter.Tendsto (fun d : ℕ => 1 - A ^ d)
      Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub hpow :
      Filter.Tendsto (fun d : ℕ => 1 - A ^ d) Filter.atTop (nhds (1 - 0)))
  have hupper : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
      Filter.atTop (nhds 1) := tendsto_const_nhds
  apply Filter.Tendsto.squeeze hlower hupper
  · intro d
    exact one_sub_affinity_pow_le_tensorDecisionEffect_contrast
      μ₀ μ₁ p₀ p₁ d (K d) (hK₀ d) (hK₁ d)
  · intro d
    have h₀ := mixingMean_mem_Icc (tensorDecisionEffect p₀ p₁ d (K d)) μ₀
    have h₁ := mixingMean_mem_Icc (tensorDecisionEffect p₀ p₁ d (K d)) μ₁
    linarith [h₀.1, h₁.2]

theorem tensorDecisionEffects_not_equicontinuous
    [Nonempty X]
    (μ₀ μ₁ : Measure X) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (hfull₀ : μ₀.support = Set.univ) (hfull₁ : μ₁.support = Set.univ)
    (p₀ p₁ : FiniteProbabilityLaw Y) (hne : p₀ ≠ p₁)
    (K : ∀ d, FiniteFellerKernel X (Fin d → Y))
    (hK₀ : ∀ d y, (K d).pushMass μ₀ y = (p₀.tensorPower d).prob y)
    (hK₁ : ∀ d y, (K d).pushMass μ₁ y = (p₁.tensorPower d).prob y) :
    ¬ Equicontinuous (fun d x => tensorDecisionEffect p₀ p₁ d (K d) x) := by
  apply not_equicontinuous_of_mixingMean_sub_tendsto_one
    (fun d => tensorDecisionEffect p₀ p₁ d (K d)) μ₀ μ₁ hfull₀ hfull₁
  exact tendsto_tensorDecisionEffect_contrast μ₀ μ₁ p₀ p₁ hne K hK₀ hK₁

theorem tensorDecisionEffects_no_equicontinuous_subsequence
    [Nonempty X]
    (μ₀ μ₁ : Measure X) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (hfull₀ : μ₀.support = Set.univ) (hfull₁ : μ₁.support = Set.univ)
    (p₀ p₁ : FiniteProbabilityLaw Y) (hne : p₀ ≠ p₁)
    (K : ∀ d, FiniteFellerKernel X (Fin d → Y))
    (hK₀ : ∀ d y, (K d).pushMass μ₀ y = (p₀.tensorPower d).prob y)
    (hK₁ : ∀ d y, (K d).pushMass μ₁ y = (p₁.tensorPower d).prob y)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    ¬ Equicontinuous (fun n x => tensorDecisionEffect p₀ p₁ (φ n) (K (φ n)) x) := by
  apply no_equicontinuous_subsequence_of_mixingMean_sub_tendsto_one
    (fun d => tensorDecisionEffect p₀ p₁ d (K d)) μ₀ μ₁ hfull₀ hfull₁
  · exact tendsto_tensorDecisionEffect_contrast μ₀ μ₁ p₀ p₁ hne K hK₀ hK₁
  · exact hφ

theorem tensorDecisionEffects_lipschitzConstants_tendsto_atTop
    [Nonempty X]
    (μ₀ μ₁ : Measure X) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (hfull₀ : μ₀.support = Set.univ) (hfull₁ : μ₁.support = Set.univ)
    (p₀ p₁ : FiniteProbabilityLaw Y) (hne : p₀ ≠ p₁)
    (K : ∀ d, FiniteFellerKernel X (Fin d → Y))
    (hK₀ : ∀ d y, (K d).pushMass μ₀ y = (p₀.tensorPower d).prob y)
    (hK₁ : ∀ d y, (K d).pushMass μ₁ y = (p₁.tensorPower d).prob y)
    (L : ℕ → NNReal)
    (hlip : ∀ d, LipschitzWith (L d) (tensorDecisionEffect p₀ p₁ d (K d))) :
    Filter.Tendsto L Filter.atTop Filter.atTop := by
  apply lipschitzConstants_tendsto_atTop_of_mixingMean_sub_tendsto_one
    (fun d => tensorDecisionEffect p₀ p₁ d (K d)) L μ₀ μ₁ hfull₀ hfull₁
  · exact tendsto_tensorDecisionEffect_contrast μ₀ μ₁ p₀ p₁ hne K hK₀ hK₁
  · exact hlip

/-- One coherent choice of exact finite admissions exists at every tensor depth. -/
theorem exists_tensorAdmissionKernel
    (μ₀ μ₁ : Measure X) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (hsing : μ₀ ⟂ₘ μ₁)
    (p₀ p₁ : FiniteProbabilityLaw Y)
    (hzero : ∀ y, p₀.prob y = 0 ↔ p₁.prob y = 0) :
    ∃ K : ∀ d, FiniteFellerKernel X (Fin d → Y),
      (∀ d y, (K d).pushMass μ₀ y = (p₀.tensorPower d).prob y) ∧
      (∀ d y, (K d).pushMass μ₁ y = (p₁.tensorPower d).prob y) := by
  choose K hK₀ hK₁ using
    fun d => exists_pushMass_eq_tensorPower μ₀ μ₁ hsing p₀ p₁ hzero d
  exact ⟨K, hK₀, hK₁⟩

/-- Full finite-admission/cofinal-fracture package: exact Feller realization at
every tensor depth, asymptotically perfect decision contrast, and unavoidable
escape from every equicontinuous source gauge. -/
theorem exists_tensorAdmission_with_decisionEscape
    [Nonempty X]
    (μ₀ μ₁ : Measure X) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (hsing : μ₀ ⟂ₘ μ₁)
    (hfull₀ : μ₀.support = Set.univ) (hfull₁ : μ₁.support = Set.univ)
    (p₀ p₁ : FiniteProbabilityLaw Y)
    (hzero : ∀ y, p₀.prob y = 0 ↔ p₁.prob y = 0)
    (hne : p₀ ≠ p₁) :
    ∃ K : ∀ d, FiniteFellerKernel X (Fin d → Y),
      (∀ d y, (K d).pushMass μ₀ y = (p₀.tensorPower d).prob y) ∧
      (∀ d y, (K d).pushMass μ₁ y = (p₁.tensorPower d).prob y) ∧
      Filter.Tendsto (fun d =>
        mixingMean (tensorDecisionEffect p₀ p₁ d (K d)) μ₁ -
          mixingMean (tensorDecisionEffect p₀ p₁ d (K d)) μ₀)
        Filter.atTop (nhds 1) ∧
      ¬ Equicontinuous (fun d x => tensorDecisionEffect p₀ p₁ d (K d) x) := by
  obtain ⟨K, hK₀, hK₁⟩ := exists_tensorAdmissionKernel μ₀ μ₁ hsing p₀ p₁ hzero
  refine ⟨K, hK₀, hK₁, ?_, ?_⟩
  · exact tendsto_tensorDecisionEffect_contrast μ₀ μ₁ p₀ p₁ hne K hK₀ hK₁
  · exact tensorDecisionEffects_not_equicontinuous
      μ₀ μ₁ hfull₀ hfull₁ p₀ p₁ hne K hK₀ hK₁

end FiniteFellerKernel

end


end GaloisForLFunctions.HTGeometry

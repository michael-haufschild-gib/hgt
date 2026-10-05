import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Base-norm formation measures

Let `(μ_i)_{i ∈ ι}` be probability measures on a measurable space `Ω`.  For a coefficient sequence
`d ∈ ℓ¹(ι)` the formation measure `𝔐 d (B) = (d_i μ_i(B))_i` is a countably additive
`ℓ¹(ι)`-valued measure `(BNF.3)`: its partial sums are absolutely summable in `ℓ¹` because
`Σ_k Σ_i |d_i| μ_i(B_k) ≤ ‖d‖₁`.  Its variation is the scalar measure `Σ_i |d_i| μ_i`, since the
`ℓ¹` norm of `𝔐 d (B)` already equals `Σ_i |d_i| μ_i(B)`; in particular `‖𝔐 d‖_TV = ‖d‖₁`
`(BNF.4)`.  So `𝔐` is a linear isometric embedding whose range is closed under total-variation
limits.

The mass recovery `𝖱 ν = ν(Ω)` is contractive, `‖𝖱 ν‖₁ ≤ ‖ν‖_TV`, and `𝖱 𝔐 = id`; hence `𝔐 𝖱` is a
total-variation contractive projection onto the formed range `(BNF.7)`–`(BNF.8)`.

The construction is functorial: a relabeling `σ` of channels carried by a measurable bijection
`A` of `Ω` is intertwined with the total-variation isometry `ν ↦ σ_*(A_* ν)`; a common Markov kernel
acting on the formed family preserves total variation and the common recovery; a refinement whose
marginals are the original laws pushes forward to the original formed measure.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PrimeShiftSource

/-- The coefficient base space `ℓ¹(ι)`. -/
abbrev BaseCoeff (ι : Type*) : Type _ := lp (fun _ : ι => ℂ) 1

section Coefficients

variable {ι : Type*}

theorem summable_norm_baseCoeff (d : BaseCoeff ι) : Summable fun i => ‖d i‖ := by
  have h := (memℓp_gen_iff (p := 1) (by norm_num)).1 d.2
  simpa using h

theorem norm_baseCoeff (d : BaseCoeff ι) : ‖d‖ = ∑' i, ‖d i‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp

theorem enorm_baseCoeff (d : BaseCoeff ι) : ‖d‖ₑ = ∑' i, ‖d i‖ₑ := by
  rw [← ofReal_norm, norm_baseCoeff, ENNReal.ofReal_tsum_of_nonneg (fun i => norm_nonneg _)
    (summable_norm_baseCoeff d)]
  simp only [ofReal_norm]

end Coefficients

section Formation

variable {ι α : Type*} [MeasurableSpace α] (μ : ι → Measure α) [∀ i, IsProbabilityMeasure (μ i)]

omit [MeasurableSpace α] in
theorem toReal_le_one_of_prob {m : MeasurableSpace α} (ν : Measure α) [IsProbabilityMeasure ν]
    (B : Set α) : (ν B).toReal ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)

theorem summable_mass (d : BaseCoeff ι) (B : Set α) :
    Summable fun i => ‖d i‖ * (μ i B).toReal :=
  (summable_norm_baseCoeff d).of_nonneg_of_le (fun i => by positivity)
    fun i => mul_le_of_le_one_right (norm_nonneg _) (toReal_le_one_of_prob _ _)

theorem memℓp_massVec (d : BaseCoeff ι) (B : Set α) :
    Memℓp (fun i => d i * ((μ i B).toReal : ℂ)) 1 := by
  refine (memℓp_gen_iff (p := 1) (by norm_num)).2 ?_
  simp only [ENNReal.toReal_one, Real.rpow_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ENNReal.toReal_nonneg]
  exact summable_mass μ d B

/-- The coordinate masses `(d_i μ_i(B))_i`. -/
def massVec (d : BaseCoeff ι) (B : Set α) : BaseCoeff ι := ⟨_, memℓp_massVec μ d B⟩

@[simp] theorem massVec_apply (d : BaseCoeff ι) (B : Set α) (i : ι) :
    massVec μ d B i = d i * ((μ i B).toReal : ℂ) := rfl

theorem norm_massVec (d : BaseCoeff ι) (B : Set α) :
    ‖massVec μ d B‖ = ∑' i, ‖d i‖ * (μ i B).toReal := by
  rw [norm_baseCoeff]
  refine tsum_congr fun i => ?_
  rw [massVec_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ENNReal.toReal_nonneg]

theorem enorm_massVec (d : BaseCoeff ι) (B : Set α) :
    ‖massVec μ d B‖ₑ = ∑' i, ‖d i‖ₑ * μ i B := by
  rw [← ofReal_norm, norm_massVec, ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
    (summable_mass μ d B)]
  refine tsum_congr fun i => ?_
  rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem hasSum_massVec (d : BaseCoeff ι) {f : ℕ → Set α} (hf : ∀ k, MeasurableSet (f k))
    (hd : Pairwise (Function.onFun Disjoint f)) :
    HasSum (fun k => massVec μ d (f k)) (massVec μ d (⋃ k, f k)) := by
  have hpart : ∀ s : Finset ℕ, ∑ k ∈ s, ‖massVec μ d (f k)‖ ≤ ‖d‖ := fun s => by
    simp_rw [norm_massVec]
    rw [← Summable.tsum_finsetSum fun k _ => summable_mass μ d (f k), norm_baseCoeff]
    refine Summable.tsum_le_tsum (fun i => ?_) (summable_sum fun k _ => summable_mass μ d (f k))
      (summable_norm_baseCoeff d)
    rw [← Finset.mul_sum, ← ENNReal.toReal_sum fun k _ => measure_ne_top _ _,
      ← measure_biUnion_finset (fun a _ b _ hab => hd hab) fun k _ => hf k]
    exact mul_le_of_le_one_right (norm_nonneg _) (toReal_le_one_of_prob _ _)
  have hsum : Summable fun k => massVec μ d (f k) :=
    Summable.of_norm (summable_of_sum_le (fun k => norm_nonneg _) hpart)
  convert hsum.hasSum using 1
  refine lp.ext (funext fun i => ?_)
  have h : HasSum (fun k => massVec μ d (f k) i) ((∑' k, massVec μ d (f k)) i) :=
    hsum.hasSum.mapL (lp.evalCLM ℂ (E := fun _ : ι => ℂ) (p := 1) i)
  rw [← h.tsum_eq]
  simp only [massVec_apply]
  rw [tsum_mul_left, ← Complex.ofReal_tsum, ← ENNReal.tsum_toReal_eq fun k => measure_ne_top _ _,
    measure_iUnion hd hf]

open Classical in
/-- **The formation measure `𝔐 d (B) = (d_i μ_i(B))_i` `(BNF.3)`.** -/
def formationMeasure (d : BaseCoeff ι) : VectorMeasure α (BaseCoeff ι) where
  measureOf' B := if MeasurableSet B then massVec μ d B else 0
  empty' := by
    rw [if_pos MeasurableSet.empty]
    refine lp.ext (funext fun i => ?_)
    simp
  not_measurable' _ hB := if_neg hB
  m_iUnion' f hf hd := by
    rw [if_pos (MeasurableSet.iUnion hf)]
    simp only [hf, ↓reduceIte]
    exact hasSum_massVec μ d hf hd

theorem formationMeasure_apply (d : BaseCoeff ι) {B : Set α} (hB : MeasurableSet B) :
    formationMeasure μ d B = massVec μ d B := by
  classical
  exact if_pos hB

/-- The scalar measure `Σ_i |d_i| μ_i`. -/
def massMeasure (d : BaseCoeff ι) : Measure α := Measure.sum fun i => ‖d i‖ₑ • μ i

omit [∀ i, IsProbabilityMeasure (μ i)] in
theorem massMeasure_apply (d : BaseCoeff ι) {B : Set α} (hB : MeasurableSet B) :
    massMeasure μ d B = ∑' i, ‖d i‖ₑ * μ i B := by
  rw [massMeasure, Measure.sum_apply _ hB]
  simp only [Measure.smul_apply, smul_eq_mul]

/-- **Theorem 2.1, `(BNF.4)`**: the variation of `𝔐 d` is `Σ_i |d_i| μ_i`. -/
theorem variation_formationMeasure (d : BaseCoeff ι) :
    (formationMeasure μ d).variation = massMeasure μ d := by
  refine le_antisymm (VectorMeasure.variation_le_of_forall_enorm_le fun E hE => ?_)
    (Measure.le_iff.2 fun E hE => ?_)
  · rw [formationMeasure_apply μ d hE, enorm_massVec, massMeasure_apply μ d hE]
  · rw [massMeasure_apply μ d hE, ← enorm_massVec, ← formationMeasure_apply μ d hE]
    exact VectorMeasure.enorm_measure_le_variation _ _

/-- **`(BNF.4)`**: `‖𝔐 d‖_TV = ‖d‖₁`. -/
theorem variation_formationMeasure_univ (d : BaseCoeff ι) :
    (formationMeasure μ d).variation Set.univ = ‖d‖ₑ := by
  rw [variation_formationMeasure, massMeasure_apply μ d MeasurableSet.univ, enorm_baseCoeff]
  simp [measure_univ]

theorem formationMeasure_add (d e : BaseCoeff ι) :
    formationMeasure μ (d + e) = formationMeasure μ d + formationMeasure μ e := by
  refine VectorMeasure.ext fun B hB => ?_
  rw [add_apply, formationMeasure_apply μ _ hB, formationMeasure_apply μ _ hB,
    formationMeasure_apply μ _ hB]
  refine lp.ext (funext fun i => ?_)
  simp [add_mul]

theorem formationMeasure_smul (c : ℂ) (d : BaseCoeff ι) :
    formationMeasure μ (c • d) = c • formationMeasure μ d := by
  refine VectorMeasure.ext fun B hB => ?_
  rw [smul_apply, formationMeasure_apply μ _ hB, formationMeasure_apply μ _ hB]
  refine lp.ext (funext fun i => ?_)
  simp [mul_assoc]

theorem formationMeasure_sub (d e : BaseCoeff ι) :
    formationMeasure μ (d - e) = formationMeasure μ d - formationMeasure μ e := by
  refine VectorMeasure.ext fun B hB => ?_
  rw [sub_apply, formationMeasure_apply μ _ hB, formationMeasure_apply μ _ hB,
    formationMeasure_apply μ _ hB]
  refine lp.ext (funext fun i => ?_)
  simp [sub_mul]

/-- **`𝔐` is an isometry**: `‖𝔐 d - 𝔐 e‖_TV = ‖d - e‖₁`. -/
theorem variation_formationMeasure_sub (d e : BaseCoeff ι) :
    (formationMeasure μ d - formationMeasure μ e).variation Set.univ = ‖d - e‖ₑ := by
  rw [← formationMeasure_sub, variation_formationMeasure_univ]

/-- A vector measure of zero total variation vanishes. -/
theorem eq_of_variation_sub_eq_zero {V : Type*} [NormedAddCommGroup V]
    {ν ρ : VectorMeasure α V} (h : (ν - ρ).variation Set.univ = 0) : ν = ρ := by
  refine VectorMeasure.ext fun E _ => ?_
  have h1 := VectorMeasure.enorm_measure_le_variation (ν - ρ) E
  have h2 := measure_mono (μ := (ν - ρ).variation) (Set.subset_univ E)
  rw [h] at h2
  have h3 : ‖(ν - ρ) E‖ₑ = 0 := nonpos_iff_eq_zero.1 (h1.trans h2)
  rw [enorm_eq_zero, sub_apply, sub_eq_zero] at h3
  exact h3

/-- **The formed range is closed** under total-variation limits. -/
theorem exists_formationMeasure_of_tendsto {ν : VectorMeasure α (BaseCoeff ι)}
    {d : ℕ → BaseCoeff ι}
    (h : Tendsto (fun n => (formationMeasure μ (d n) - ν).variation Set.univ) atTop (𝓝 0)) :
    ∃ d₀, ν = formationMeasure μ d₀ := by
  set b := fun n => (formationMeasure μ (d n) - ν).variation Set.univ
  have hd : ∀ m n, edist (d m) (d n) ≤ b m + b n := fun m n => by
    rw [edist_eq_enorm_sub, ← variation_formationMeasure_sub μ,
      show formationMeasure μ (d m) - formationMeasure μ (d n) =
        (formationMeasure μ (d m) - ν) - (formationMeasure μ (d n) - ν) by abel]
    exact (VectorMeasure.variation_sub_le _).trans_eq (Measure.add_apply _ _ _)
  have hcauchy : CauchySeq d := by
    rw [EMetric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1
      (h.eventually (gt_mem_nhds (ENNReal.half_pos hε.ne')))
    refine ⟨N, fun n hn => (hd n N).trans_lt ?_⟩
    calc b n + b N < ε / 2 + ε / 2 := ENNReal.add_lt_add (hN n hn) (hN N le_rfl)
      _ = ε := ENNReal.add_halves ε
  obtain ⟨d₀, hd₀⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨d₀, (eq_of_variation_sub_eq_zero ?_).symm⟩
  have hle : ∀ n, (formationMeasure μ d₀ - ν).variation Set.univ ≤ edist d₀ (d n) + b n := by
    intro n
    rw [edist_eq_enorm_sub, ← variation_formationMeasure_sub μ,
      show formationMeasure μ d₀ - ν =
        (formationMeasure μ d₀ - formationMeasure μ (d n)) + (formationMeasure μ (d n) - ν) by abel]
    exact (VectorMeasure.variation_add_le _).trans_eq (Measure.add_apply _ _ _)
  have hlim : Tendsto (fun n => edist d₀ (d n) + b n) atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := d₀)).edist hd₀).add h
    simpa using this
  exact nonpos_iff_eq_zero.1 (ge_of_tendsto' hlim hle)

/-! ### Common mass recovery -/

/-- The mass recovery `𝖱 ν = ν(Ω)` `(BNF.6)`. -/
def massRecovery (ν : VectorMeasure α (BaseCoeff ι)) : BaseCoeff ι := ν Set.univ

omit [∀ i, IsProbabilityMeasure (μ i)] in
/-- **Theorem 3.1**: `‖𝖱 ν‖₁ ≤ ‖ν‖_TV`. -/
theorem enorm_massRecovery_le (ν : VectorMeasure α (BaseCoeff ι)) :
    ‖massRecovery ν‖ₑ ≤ ν.variation Set.univ :=
  VectorMeasure.enorm_measure_le_variation ν _

/-- **Theorem 3.1**: `𝖱 𝔐 = id`. -/
theorem massRecovery_formationMeasure (d : BaseCoeff ι) :
    massRecovery (formationMeasure μ d) = d := by
  rw [massRecovery, formationMeasure_apply μ d MeasurableSet.univ]
  refine lp.ext (funext fun i => ?_)
  simp [measure_univ]

omit [∀ i, IsProbabilityMeasure (μ i)] in
theorem massRecovery_add (ν ρ : VectorMeasure α (BaseCoeff ι)) :
    massRecovery (ν + ρ) = massRecovery ν + massRecovery ρ :=
  add_apply _ _ _

omit [∀ i, IsProbabilityMeasure (μ i)] in
theorem massRecovery_smul (c : ℂ) (ν : VectorMeasure α (BaseCoeff ι)) :
    massRecovery (c • ν) = c • massRecovery ν :=
  smul_apply _ _ _

/-- **`(BNF.16)`**: a formed current that vanishes has zero source. -/
theorem formationMeasure_injective : Function.Injective (formationMeasure μ (ι := ι)) :=
  Function.LeftInverse.injective (massRecovery_formationMeasure μ)

/-- The projection `𝔐 𝖱` `(BNF.8)`. -/
def formationProjection (ν : VectorMeasure α (BaseCoeff ι)) : VectorMeasure α (BaseCoeff ι) :=
  formationMeasure μ (massRecovery ν)

/-- **`(BNF.8)`**: `𝔐 𝖱` is idempotent, fixes the formed range, has that range, and does not
increase total variation. -/
theorem formationProjection_spec :
    (∀ ν, formationProjection μ (formationProjection μ ν) = formationProjection μ ν) ∧
      (∀ d, formationProjection μ (formationMeasure μ d) = formationMeasure μ d) ∧
      Set.range (formationProjection μ) = Set.range (formationMeasure μ (ι := ι)) ∧
      ∀ ν, (formationProjection μ ν).variation Set.univ ≤ ν.variation Set.univ := by
  refine ⟨fun ν => ?_, fun d => ?_, ?_, fun ν => ?_⟩
  · rw [formationProjection, formationProjection, massRecovery_formationMeasure]
  · rw [formationProjection, massRecovery_formationMeasure]
  · ext ν
    constructor
    · rintro ⟨ρ, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨d, rfl⟩; exact ⟨formationMeasure μ d, by
        rw [formationProjection, massRecovery_formationMeasure]⟩
  · rw [formationProjection, variation_formationMeasure_univ]
    exact enorm_massRecovery_le ν

/-! ### Functorial laws -/

/-- Relabeling coefficients, `d ↦ d ∘ σ⁻¹`. -/
def relabel (σ : ι ≃ ι) : BaseCoeff ι →+ BaseCoeff ι where
  toFun d := ⟨fun i => d (σ.symm i), (memℓp_gen_iff (p := 1) (by norm_num)).2 (by
    simp only [ENNReal.toReal_one, Real.rpow_one]
    exact (σ.symm.summable_iff (f := fun i => ‖d i‖)).2 (summable_norm_baseCoeff d))⟩
  map_zero' := lp.ext (funext fun i => by simp)
  map_add' d e := lp.ext (funext fun i => by simp)

@[simp] theorem relabel_apply (σ : ι ≃ ι) (d : BaseCoeff ι) (i : ι) :
    relabel σ d i = d (σ.symm i) := rfl

/-- Relabeling is an isometry of `ℓ¹`. -/
theorem norm_relabel (σ : ι ≃ ι) (d : BaseCoeff ι) : ‖relabel σ d‖ = ‖d‖ := by
  rw [norm_baseCoeff, norm_baseCoeff]
  exact σ.symm.tsum_eq fun i => ‖d i‖

theorem continuous_relabel (σ : ι ≃ ι) : Continuous (relabel σ) :=
  (AddMonoidHomClass.isometry_of_norm (relabel σ) (norm_relabel σ)).continuous

omit [MeasurableSpace α] in
/-- The variation is unchanged by a norm-preserving map of the values. -/
theorem variation_mapRange_of_enorm_eq {m : MeasurableSpace α} {V W : Type*}
    [NormedAddCommGroup V] [NormedAddCommGroup W] (ν : VectorMeasure α V) (f : V →+ W)
    (hf : Continuous f) (h : ∀ x, ‖f x‖ₑ = ‖x‖ₑ) :
    (ν.mapRange f hf).variation = ν.variation := by
  refine le_antisymm (VectorMeasure.variation_le_of_forall_enorm_le fun E _ => ?_)
    (VectorMeasure.variation_le_of_forall_enorm_le fun E _ => ?_)
  · rw [VectorMeasure.mapRange_apply, h]
    exact VectorMeasure.enorm_measure_le_variation _ _
  · rw [← h, ← VectorMeasure.mapRange_apply ν hf]
    exact VectorMeasure.enorm_measure_le_variation _ _

omit [∀ i, IsProbabilityMeasure (μ i)] in
/-- **§6.1**: the action `ν ↦ σ_*(A_* ν)` preserves total variation. -/
theorem variation_relabel_map (σ : ι ≃ ι) (A : α ≃ᵐ α) (ν : VectorMeasure α (BaseCoeff ι)) :
    ((ν.map A).mapRange (relabel σ) (continuous_relabel σ)).variation Set.univ =
      ν.variation Set.univ := by
  rw [variation_mapRange_of_enorm_eq _ _ _ fun x => by rw [← ofReal_norm, ← ofReal_norm,
    norm_relabel], A.measurableEmbedding.variation_map,
    Measure.map_apply A.measurable MeasurableSet.univ, Set.preimage_univ]

/-- **§6.1: formation intertwines relabelings.**  If `μ_{σ i} = A_* μ_i`, then
`𝔐(d ∘ σ⁻¹) = σ_*(A_* 𝔐 d)`. -/
theorem formationMeasure_relabel (σ : ι ≃ ι) (A : α ≃ᵐ α) (hμ : ∀ i, μ (σ i) = (μ i).map A)
    (d : BaseCoeff ι) :
    formationMeasure μ (relabel σ d) =
      ((formationMeasure μ d).map A).mapRange (relabel σ) (continuous_relabel σ) := by
  refine VectorMeasure.ext fun B hB => ?_
  rw [VectorMeasure.mapRange_apply, VectorMeasure.map_apply _ A.measurable hB,
    formationMeasure_apply μ _ hB, formationMeasure_apply μ _ (A.measurable hB)]
  refine lp.ext (funext fun j => ?_)
  simp only [massVec_apply, relabel_apply]
  rw [show μ j = (μ (σ.symm j)).map A by rw [← hμ, σ.apply_symm_apply],
    Measure.map_apply A.measurable hB]

/-- **§6.2: Markov post-processing.**  A common Markov kernel acting on the formed family gives
the formed measure of the post-processed laws, with coordinates `d_i ∫ κ(t, B) dμ_i(t)`. -/
theorem formationMeasure_comp_apply {β : Type*} [MeasurableSpace β] (κ : Kernel α β)
    [IsMarkovKernel κ] (d : BaseCoeff ι) {B : Set β} (hB : MeasurableSet B) (i : ι) :
    formationMeasure (fun i => κ ∘ₘ μ i) d B i = d i * ((∫⁻ t, κ t B ∂μ i).toReal : ℂ) := by
  rw [formationMeasure_apply _ d hB, massVec_apply, Measure.bind_apply hB κ.aemeasurable]

/-- **§6.2**: post-processing by a common Markov kernel preserves total variation, and the mass
recovery remains a common left inverse. -/
theorem formationMeasure_comp_spec {β : Type*} [MeasurableSpace β] (κ : Kernel α β)
    [IsMarkovKernel κ] (d : BaseCoeff ι) :
    (formationMeasure (fun i => κ ∘ₘ μ i) d).variation Set.univ =
        (formationMeasure μ d).variation Set.univ ∧
      massRecovery (formationMeasure (fun i => κ ∘ₘ μ i) d) = d := by
  rw [variation_formationMeasure_univ, variation_formationMeasure_univ]
  exact ⟨rfl, massRecovery_formationMeasure _ d⟩

/-- **§6.3: refinement.**  If each refined law has the original law as its marginal, the refined
formed measure pushes forward to the original one. -/
theorem formationMeasure_map_marginal {β : Type*} [MeasurableSpace β] (μ' : ι → Measure β)
    [∀ i, IsProbabilityMeasure (μ' i)] {π : β → α} (hπ : Measurable π)
    (h : ∀ i, (μ' i).map π = μ i) (d : BaseCoeff ι) :
    (formationMeasure μ' d).map π = formationMeasure μ d := by
  refine VectorMeasure.ext fun B hB => ?_
  rw [VectorMeasure.map_apply _ hπ hB, formationMeasure_apply μ' _ (hπ hB),
    formationMeasure_apply μ _ hB]
  refine lp.ext (funext fun i => ?_)
  simp only [massVec_apply]
  rw [← h i, Measure.map_apply hπ hB]

end Formation

end GaloisForLFunctions.HTGeometry.PrimeShiftSource

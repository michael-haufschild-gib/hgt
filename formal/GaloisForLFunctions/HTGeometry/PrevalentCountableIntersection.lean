import GaloisForLFunctions.HTGeometry.PrevalentSets

/-!
# Countable intersections of block-controlled prevalent phases

A prevalence statement about a countable family of phases needs *one* probe that works for every
member of the family after every deterministic recentring.  When each phase is avoided by a finite
Euclidean control block — every absolutely continuous law on the block misses the bad set, whatever
the centre — the single probe is the law of the convergent random series

`V = ∑ₙ Lₙ ξₙ`,  `ξₙ` independent and uniform on the unit ball of the `n`th block.

Its support is compact because the amplitudes are summable, and its `n`th conditional law is
absolutely continuous on the `n`th block, so the block hypothesis applies after conditioning on
every other block.  Fubini over the product measure turns that into a null statement for the whole
series, and the countable union of the null sets is null.

The infinite product measure is `MeasureTheory.Measure.infinitePi`; the coordinate/complement
splitting of that measure is not in mathlib and is proved here.
-/

open MeasureTheory ProbabilityTheory MeasurableSpace Metric
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

/-! ### Splitting one coordinate off an infinite product measure -/

/-- Independence of two σ-algebras is antitone. -/
theorem indep_mono {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m₁ m₂ m₁' m₂' : MeasurableSpace Ω}
    (h : Indep m₁ m₂ μ) (h₁ : m₁' ≤ m₁) (h₂ : m₂' ≤ m₂) : Indep m₁' m₂' μ :=
  fun t1 t2 ht1 ht2 => h t1 t2 (h₁ _ ht1) (h₂ _ ht2)

variable {X : ℕ → Type} [∀ n, MeasurableSpace (X n)]

/-- **One coordinate is independent of all the others** under an infinite product measure. -/
theorem infinitePi_indepFun_eval_restrictCompl
    (P : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (P n)] (n : ℕ) :
    IndepFun (fun ξ : (∀ k, X k) => ξ n)
      (fun ξ : (∀ k, X k) => fun i : ↥({n}ᶜ : Set ℕ) => ξ (i : ℕ))
      (Measure.infinitePi P) := by
  classical
  set m : ℕ → MeasurableSpace (∀ k, X k) :=
    fun i => MeasurableSpace.comap (fun ω : (∀ k, X k) => ω i) inferInstance with hm
  have hiIndep : iIndepFun (fun i (ω : ∀ k, X k) => ω i) (Measure.infinitePi P) :=
    iIndepFun_infinitePi (X := fun i (x : X i) => x) (fun i => measurable_id)
  have hle : ∀ i, m i ≤ (inferInstance : MeasurableSpace (∀ k, X k)) :=
    fun i => (measurable_pi_apply i).comap_le
  have hdisj : Disjoint ({n} : Set ℕ) ({n}ᶜ : Set ℕ) := disjoint_compl_right
  have hind : Indep (⨆ i ∈ ({n} : Set ℕ), m i) (⨆ i ∈ ({n}ᶜ : Set ℕ), m i)
      (Measure.infinitePi P) := indep_iSup_of_disjoint hle hiIndep hdisj
  have hsing : (⨆ i ∈ ({n} : Set ℕ), m i) = m n := by simp
  have hrest : MeasurableSpace.comap
      (fun ξ : (∀ k, X k) => fun i : ↥({n}ᶜ : Set ℕ) => ξ (i : ℕ)) inferInstance
      ≤ ⨆ i ∈ ({n}ᶜ : Set ℕ), m i := by
    have hpi : (inferInstance : MeasurableSpace (∀ i : ↥({n}ᶜ : Set ℕ), X (i : ℕ)))
        = ⨆ i : ↥({n}ᶜ : Set ℕ), MeasurableSpace.comap
            (fun y : (∀ i : ↥({n}ᶜ : Set ℕ), X (i : ℕ)) => y i) inferInstance := rfl
    rw [hpi, MeasurableSpace.comap_iSup]
    refine iSup_le fun i => ?_
    rw [MeasurableSpace.comap_comp]
    exact le_iSup₂ (f := fun j (_ : j ∈ ({n}ᶜ : Set ℕ)) => m j) (i : ℕ) i.2
  exact indep_mono hind (le_of_eq hsing.symm) hrest

/-- **The joint law of one coordinate and the remaining coordinates is a product.** -/
theorem infinitePi_map_eval_restrictCompl
    (P : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (P n)] (n : ℕ) :
    (Measure.infinitePi P).map
        (fun ξ : (∀ k, X k) => (ξ n, fun i : ↥({n}ᶜ : Set ℕ) => ξ (i : ℕ)))
      = (P n).prod (Measure.infinitePi (fun i : ↥({n}ᶜ : Set ℕ) => P (i : ℕ))) := by
  have hf : AEMeasurable (fun ξ : (∀ k, X k) => ξ n) (Measure.infinitePi P) :=
    (measurable_pi_apply n).aemeasurable
  have hg : AEMeasurable
      (fun ξ : (∀ k, X k) => fun i : ↥({n}ᶜ : Set ℕ) => ξ (i : ℕ)) (Measure.infinitePi P) :=
    (measurable_pi_lambda (fun ξ : (∀ k, X k) => fun i : ↥({n}ᶜ : Set ℕ) => ξ (i : ℕ))
      fun i => measurable_pi_apply (i : ℕ)).aemeasurable
  rw [IndepFun.map_prod_eq_prod_map_map hf hg (infinitePi_indepFun_eval_restrictCompl P n),
    Measure.infinitePi_map_eval]
  congr 1
  exact Measure.map_infinitePi_infinitePi_of_inj
    (f := (Subtype.val : ↥({n}ᶜ : Set ℕ) → ℕ)) Subtype.val_injective

/-- **Fubini in the coordinate/complement splitting.**  A set of the product whose every
complement-slice is null in the distinguished coordinate is null. -/
theorem infinitePi_null_of_slice_null
    (P : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (P n)] (n : ℕ)
    {A : Set (X n × (∀ i : ↥({n}ᶜ : Set ℕ), X (i : ℕ)))} (hA : MeasurableSet A)
    (h : ∀ y, (P n) {t | (t, y) ∈ A} = 0) :
    (Measure.infinitePi P)
      {ξ : (∀ k, X k) | (ξ n, fun i : ↥({n}ᶜ : Set ℕ) => ξ (i : ℕ)) ∈ A} = 0 := by
  have hT : Measurable
      (fun ξ : (∀ k, X k) => (ξ n, fun i : ↥({n}ᶜ : Set ℕ) => ξ (i : ℕ))) :=
    (measurable_pi_apply n).prodMk
      (measurable_pi_lambda (fun ξ : (∀ k, X k) => fun i : ↥({n}ᶜ : Set ℕ) => ξ (i : ℕ))
        fun i => measurable_pi_apply (i : ℕ))
  have hmap := infinitePi_map_eval_restrictCompl P n
  have hpre : (Measure.infinitePi P)
      {ξ : (∀ k, X k) | (ξ n, fun i : ↥({n}ᶜ : Set ℕ) => ξ (i : ℕ)) ∈ A}
      = ((Measure.infinitePi P).map
          (fun ξ : (∀ k, X k) => (ξ n, fun i : ↥({n}ᶜ : Set ℕ) => ξ (i : ℕ)))) A :=
    (Measure.map_apply hT hA).symm
  rw [hpre, hmap, Measure.prod_apply_symm hA]
  have hslice : ∀ y, (P n) ((fun x => (x, y)) ⁻¹' A) = 0 := fun y => h y
  simp [hslice]

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ProbabilityTheory MeasurableSpace Metric
open scoped ENNReal NNReal

/-! ### Unit-ball block laws -/

/-- The normalized uniform law on the closed unit ball of a Euclidean block. -/
noncomputable def unitBlockLaw (d : ℕ) : Measure (Fin d → ℝ) := (cubeProbe d one_pos).measure

instance instIsProbabilityMeasure_unitBlockLaw (d : ℕ) : IsProbabilityMeasure (unitBlockLaw d) :=
  (cubeProbe d one_pos).isProbability

theorem unitBlockLaw_absolutelyContinuous (d : ℕ) :
    unitBlockLaw d ≪ (volume : Measure (Fin d → ℝ)) :=
  cubeProbe_absolutelyContinuous d one_pos

theorem unitBlockLaw_norm_gt_one (d : ℕ) : unitBlockLaw d {p : Fin d → ℝ | 1 < ‖p‖} = 0 := by
  have h := (cubeProbe d one_pos).measure_compl_carrier
  have hset : {p : Fin d → ℝ | 1 < ‖p‖} = (Metric.closedBall (0 : Fin d → ℝ) 1)ᶜ := by
    ext p
    simp [not_le]
  rw [unitBlockLaw, hset]
  exact h

/-! ### Truncation to the unit ball -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial truncation to the closed unit ball; the identity on the ball. -/
noncomputable def unitTruncate (p : E) : E := (max 1 ‖p‖)⁻¹ • p

omit [NormedSpace ℝ E] in
theorem one_le_max_one_norm (p : E) : (1 : ℝ) ≤ max 1 ‖p‖ := le_max_left _ _

theorem continuous_unitTruncate : Continuous (unitTruncate (E := E)) := by
  refine Continuous.smul ?_ continuous_id
  refine Continuous.inv₀ (continuous_const.max continuous_norm) fun p => ?_
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_max_one_norm p))

theorem norm_unitTruncate_le_one (p : E) : ‖unitTruncate p‖ ≤ 1 := by
  have hpos : (0 : ℝ) < max 1 ‖p‖ := lt_of_lt_of_le zero_lt_one (one_le_max_one_norm p)
  rw [unitTruncate, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hpos]
  rw [inv_mul_le_iff₀ hpos, mul_one]
  exact le_max_right _ _

theorem unitTruncate_eq_self {p : E} (hp : ‖p‖ ≤ 1) : unitTruncate p = p := by
  rw [unitTruncate, max_eq_left hp, inv_one, one_smul]

theorem unitTruncate_idem (p : E) : unitTruncate (unitTruncate p) = unitTruncate p :=
  unitTruncate_eq_self (norm_unitTruncate_le_one p)

/-! ### The product probe

The probe lives on the parameter space `Π n, ℝ^{d n}` with the product of the unit-ball block laws.
Nothing is required of the ambient space beyond completeness: the null sets are sets of parameters,
so no measurable structure on the ambient Banach space is ever used. -/

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]

/-- The parameter law of the probe: the infinite product of the unit-ball block laws. -/
noncomputable def blockProbeLaw (d : ℕ → ℕ) : Measure (∀ n, Fin (d n) → ℝ) :=
  Measure.infinitePi fun n => unitBlockLaw (d n)

instance instIsProbabilityMeasure_blockProbeLaw (d : ℕ → ℕ) :
    IsProbabilityMeasure (blockProbeLaw d) := by
  rw [blockProbeLaw]; infer_instance

/-- The convergent random series `∑ₙ Lₙ ξₙ`, with every block truncated to its unit ball. -/
noncomputable def productProbeMap (d : ℕ → ℕ) (L : ∀ n, (Fin (d n) → ℝ) →L[ℝ] S)
    (ξ : ∀ n, Fin (d n) → ℝ) : S := ∑' n, L n (unitTruncate (ξ n))

omit [CompleteSpace S] in
theorem norm_productProbeMap_term (d : ℕ → ℕ) (L : ∀ n, (Fin (d n) → ℝ) →L[ℝ] S)
    (n : ℕ) (p : Fin (d n) → ℝ) : ‖L n (unitTruncate p)‖ ≤ ‖L n‖ := by
  refine le_trans ((L n).le_opNorm _) ?_
  calc ‖L n‖ * ‖unitTruncate p‖ ≤ ‖L n‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_unitTruncate_le_one p) (norm_nonneg _)
    _ = ‖L n‖ := mul_one _

theorem continuous_productProbeMap {d : ℕ → ℕ} {L : ∀ n, (Fin (d n) → ℝ) →L[ℝ] S}
    (hL : Summable fun n => ‖L n‖) : Continuous (productProbeMap d L) :=
  continuous_tsum
    (fun n => (L n).continuous.comp (continuous_unitTruncate.comp (continuous_apply n)))
    hL (fun n ξ => norm_productProbeMap_term d L n (ξ n))

theorem summable_productProbeMap_terms {d : ℕ → ℕ} {L : ∀ n, (Fin (d n) → ℝ) →L[ℝ] S}
    (hL : Summable fun n => ‖L n‖) (ξ : ∀ n, Fin (d n) → ℝ) :
    Summable fun n => L n (unitTruncate (ξ n)) :=
  Summable.of_norm_bounded hL (fun n => norm_productProbeMap_term d L n (ξ n))

omit [CompleteSpace S] in
theorem productProbeMap_truncate {d : ℕ → ℕ} {L : ∀ n, (Fin (d n) → ℝ) →L[ℝ] S}
    (ξ : ∀ n, Fin (d n) → ℝ) :
    productProbeMap d L (fun n => unitTruncate (ξ n)) = productProbeMap d L ξ := by
  simp only [productProbeMap, unitTruncate_idem]

omit [CompleteSpace S] in
theorem range_productProbeMap {d : ℕ → ℕ} {L : ∀ n, (Fin (d n) → ℝ) →L[ℝ] S} :
    Set.range (productProbeMap d L)
      = productProbeMap d L ''
        (Set.univ.pi fun n => Metric.closedBall (0 : Fin (d n) → ℝ) 1) := by
  refine Set.Subset.antisymm ?_ (Set.image_subset_range _ _)
  rintro w ⟨ξ, rfl⟩
  refine ⟨fun n => unitTruncate (ξ n), ?_, productProbeMap_truncate ξ⟩
  intro n _
  simpa using norm_unitTruncate_le_one (ξ n)

/-- **The probe has compact range.** -/
theorem isCompact_range_productProbeMap {d : ℕ → ℕ} {L : ∀ n, (Fin (d n) → ℝ) →L[ℝ] S}
    (hL : Summable fun n => ‖L n‖) : IsCompact (Set.range (productProbeMap d L)) := by
  rw [range_productProbeMap]
  exact (isCompact_univ_pi fun n => isCompact_closedBall (0 : Fin (d n) → ℝ) 1).image
    (continuous_productProbeMap hL)

/-- The part of the series carried by all blocks other than the `n`th. -/
noncomputable def productProbeTail (d : ℕ → ℕ) (L : ∀ n, (Fin (d n) → ℝ) →L[ℝ] S) (n : ℕ)
    (y : ∀ i : ↥({n}ᶜ : Set ℕ), Fin (d (i : ℕ)) → ℝ) : S :=
  ∑' i : ↥({n}ᶜ : Set ℕ), L (i : ℕ) (unitTruncate (y i))

theorem continuous_productProbeTail {d : ℕ → ℕ} {L : ∀ n, (Fin (d n) → ℝ) →L[ℝ] S}
    (hL : Summable fun n => ‖L n‖) (n : ℕ) : Continuous (productProbeTail d L n) :=
  continuous_tsum
    (fun i => (L (i : ℕ)).continuous.comp (continuous_unitTruncate.comp (continuous_apply i)))
    (hL.subtype _) (fun i y => norm_productProbeMap_term d L (i : ℕ) (y i))

/-- **The block splitting of the probe series.** -/
theorem productProbeMap_split {d : ℕ → ℕ} {L : ∀ n, (Fin (d n) → ℝ) →L[ℝ] S}
    (hL : Summable fun n => ‖L n‖) (n : ℕ) (ξ : ∀ k, Fin (d k) → ℝ) :
    productProbeMap d L ξ
      = L n (unitTruncate (ξ n))
        + productProbeTail d L n (fun i : ↥({n}ᶜ : Set ℕ) => ξ (i : ℕ)) := by
  have hsum := summable_productProbeMap_terms hL ξ
  have hsplit := hsum.tsum_subtype_add_tsum_subtype_compl ({n} : Set ℕ)
  have hone : ∑' x : ↥({n} : Set ℕ), L (x : ℕ) (unitTruncate (ξ (x : ℕ)))
      = L n (unitTruncate (ξ n)) :=
    tsum_singleton n (fun k => L k (unitTruncate (ξ k)))
  rw [hone] at hsplit
  exact hsplit.symm

/-! ### The block null law -/

/-- **The probe kills the bad set of one block after every deterministic recentring.**  The
statement is about parameters only, so the ambient space needs no measurable structure. -/
theorem blockProbeLaw_block_null {d : ℕ → ℕ} {L : ∀ n, (Fin (d n) → ℝ) →L[ℝ] S}
    (hL : Summable fun n => ‖L n‖) {G : Set S} (hG : IsOpen G) (n : ℕ)
    (hblock : ∀ center : S, ∀ μ : Measure (Fin (d n) → ℝ), μ ≪ volume →
      μ {p | center + L n p ∉ G} = 0) (center : S) :
    blockProbeLaw d {ξ | center + productProbeMap d L ξ ∉ G} = 0 := by
  classical
  set A : Set ((Fin (d n) → ℝ) × (∀ i : ↥({n}ᶜ : Set ℕ), Fin (d (i : ℕ)) → ℝ)) :=
    {z | center + (L n (unitTruncate z.1) + productProbeTail d L n z.2) ∉ G} with hA
  have hcont : Continuous
      (fun z : (Fin (d n) → ℝ) × (∀ i : ↥({n}ᶜ : Set ℕ), Fin (d (i : ℕ)) → ℝ) =>
        center + (L n (unitTruncate z.1) + productProbeTail d L n z.2)) :=
    continuous_const.add
      (((L n).continuous.comp (continuous_unitTruncate.comp continuous_fst)).add
        ((continuous_productProbeTail hL n).comp continuous_snd))
  have hAmeas : MeasurableSet A :=
    (hG.isClosed_compl.preimage hcont).measurableSet
  have hslice : ∀ y, (unitBlockLaw (d n)) {t | (t, y) ∈ A} = 0 := by
    intro y
    set c : S := center + productProbeTail d L n y with hc
    have hsub : {t : Fin (d n) → ℝ | (t, y) ∈ A}
        ⊆ {t : Fin (d n) → ℝ | c + L n t ∉ G} ∪ {t : Fin (d n) → ℝ | 1 < ‖t‖} := by
      intro t ht
      by_cases hnorm : 1 < ‖t‖
      · exact Or.inr hnorm
      · refine Or.inl ?_
        have htr : unitTruncate t = t := unitTruncate_eq_self (not_lt.mp hnorm)
        simp only [hA, Set.mem_setOf_eq, htr] at ht
        simp only [Set.mem_setOf_eq, hc]
        intro hmem
        exact ht (by simpa [add_assoc, add_comm, add_left_comm] using hmem)
    refine measure_mono_null hsub ?_
    refine measure_union_null ?_ (unitBlockLaw_norm_gt_one (d n))
    exact hblock c (unitBlockLaw (d n)) (unitBlockLaw_absolutelyContinuous (d n))
  have hmain := infinitePi_null_of_slice_null (fun k => unitBlockLaw (d k)) n hAmeas hslice
  have hset : {ξ : ∀ k, Fin (d k) → ℝ | center + productProbeMap d L ξ ∉ G}
      = {ξ : ∀ k, Fin (d k) → ℝ |
          (ξ n, fun i : ↥({n}ᶜ : Set ℕ) => ξ (i : ℕ)) ∈ A} := by
    ext ξ
    simp only [Set.mem_setOf_eq, hA, productProbeMap_split hL n ξ]
  rw [blockProbeLaw, hset]
  exact hmain

/-! ### Block prevalence -/

/-- `G` is **block prevalent on `B`** when one convergent random series of finite Euclidean control
blocks makes the complement of `G` null after every deterministic recentring inside `B`. -/
def BlockPrevalentOn (B G : Set S) : Prop :=
  ∃ (d : ℕ → ℕ) (L : ∀ n, (Fin (d n) → ℝ) →L[ℝ] S) (_ : Summable fun n => ‖L n‖),
    ∀ x ∈ B, blockProbeLaw d {ξ | x + productProbeMap d L ξ ∉ G} = 0

/-- `G` is **block prevalent** when it is block prevalent on the whole space. -/
def BlockPrevalent (G : Set S) : Prop := BlockPrevalentOn (Set.univ : Set S) G

omit [CompleteSpace S] in
theorem BlockPrevalentOn.mono {B G G' : Set S} (h : BlockPrevalentOn B G) (hGG' : G ⊆ G') :
    BlockPrevalentOn B G' := by
  obtain ⟨d, L, hL, hx⟩ := h
  refine ⟨d, L, hL, fun x hxB => ?_⟩
  refine measure_mono_null (fun ξ hξ => ?_) (hx x hxB)
  exact fun hmem => hξ (hGG' hmem)

omit [CompleteSpace S] in
theorem BlockPrevalent.mono {G G' : Set S} (h : BlockPrevalent G) (hGG' : G ⊆ G') :
    BlockPrevalent G' := BlockPrevalentOn.mono h hGG'

/-- **A countable family of block-controlled phases is block prevalent.** -/
theorem blockPrevalent_iInter_of_blockControl {d : ℕ → ℕ} {L : ∀ n, (Fin (d n) → ℝ) →L[ℝ] S}
    (hL : Summable fun n => ‖L n‖) (G : ℕ → Set S) (hGopen : ∀ n, IsOpen (G n))
    (hblock : ∀ n, ∀ center : S, ∀ μ : Measure (Fin (d n) → ℝ), μ ≪ volume →
      μ {p | center + L n p ∉ G n} = 0) :
    BlockPrevalent (⋂ n, G n) := by
  refine ⟨d, L, hL, fun x _ => ?_⟩
  have hcover : {ξ : ∀ k, Fin (d k) → ℝ | x + productProbeMap d L ξ ∉ ⋂ n, G n}
      = ⋃ n, {ξ : ∀ k, Fin (d k) → ℝ | x + productProbeMap d L ξ ∉ G n} := by
    ext ξ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter]
    push Not
    rfl
  rw [hcover]
  exact measure_iUnion_null fun n =>
    blockProbeLaw_block_null hL (hGopen n) n (hblock n) x

/-- **Scalable block control gives block prevalence.**  Amplitudes are chosen internally so that
the random series converges; the hypothesis only has to hold for every positive amplitude. -/
theorem blockPrevalent_iInter_of_blockControl_scalable {d : ℕ → ℕ}
    (l : ∀ n, (Fin (d n) → ℝ) →L[ℝ] S) (G : ℕ → Set S) (hGopen : ∀ n, IsOpen (G n))
    (hblock : ∀ n, ∀ c : ℝ, 0 < c → ∀ center : S, ∀ μ : Measure (Fin (d n) → ℝ), μ ≪ volume →
      μ {p | center + (c • l n) p ∉ G n} = 0) :
    BlockPrevalent (⋂ n, G n) := by
  classical
  set c : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n / (1 + ‖l n‖) with hc
  have hden : ∀ n, (0 : ℝ) < 1 + ‖l n‖ := fun n => by positivity
  have hcpos : ∀ n, 0 < c n := fun n => by
    have : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
    exact div_pos this (hden n)
  have hbound : ∀ n, ‖c n • l n‖ ≤ (1 / 2 : ℝ) ^ n := by
    intro n
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hcpos n), hc]
    have hle : ‖l n‖ / (1 + ‖l n‖) ≤ 1 := by
      rw [div_le_one (hden n)]
      linarith [norm_nonneg (l n)]
    calc (1 / 2 : ℝ) ^ n / (1 + ‖l n‖) * ‖l n‖
        = (1 / 2 : ℝ) ^ n * (‖l n‖ / (1 + ‖l n‖)) := by ring
      _ ≤ (1 / 2 : ℝ) ^ n * 1 :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (1 / 2 : ℝ) ^ n := mul_one _
  have hLsum : Summable fun n => ‖c n • l n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound summable_geometric_two
  exact blockPrevalent_iInter_of_blockControl (L := fun n => c n • l n) hLsum G hGopen
    (fun n center μ hμ => hblock n (c n) (hcpos n) center μ hμ)

/-- **Block-prevalent global witness from compact-local block-controlled certificates.**  This is
the prevalence analogue of the sigma-compact Baire assembly: compact patches of the configuration
space are covered one by one, each by its own finite control block, and the countably many blocks
are merged into a single convergent probe series. -/
theorem globalWitness_blockPrevalent_of_sigmaCompact {H : Type*}
    [TopologicalSpace H] [SigmaCompactSpace H]
    (Witness : ℕ → S → H → Prop)
    (hcompact : ∀ (n : ℕ) (K : Set H), IsCompact K →
      ∃ (D : ℕ) (l : (Fin D → ℝ) →L[ℝ] S) (G : Set S), IsOpen G ∧
        (∀ c : ℝ, 0 < c → ∀ center : S, ∀ μ : Measure (Fin D → ℝ), μ ≪ volume →
          μ {p | center + (c • l) p ∉ G} = 0) ∧
        ∀ w ∈ G, ∀ h ∈ K, Witness n w h) :
    BlockPrevalent {w : S | ∀ n h, Witness n w h} := by
  classical
  obtain ⟨K, hKcompact, hKcover⟩ := SigmaCompactSpace.exists_compact_covering (X := H)
  have hall : ∀ p : ℕ, ∃ (D : ℕ) (lb : (Fin D → ℝ) →L[ℝ] S) (Gb : Set S), IsOpen Gb ∧
      (∀ c : ℝ, 0 < c → ∀ center : S, ∀ μ : Measure (Fin D → ℝ), μ ≪ volume →
        μ {q | center + (c • lb) q ∉ Gb} = 0) ∧
      ∀ w ∈ Gb, ∀ h ∈ K p.unpair.2, Witness p.unpair.1 w h :=
    fun p => hcompact p.unpair.1 (K p.unpair.2) (hKcompact p.unpair.2)
  choose D l G hopen hblk hwit using hall
  have hprev : BlockPrevalent (⋂ p, G p) :=
    blockPrevalent_iInter_of_blockControl_scalable l G hopen hblk
  refine hprev.mono ?_
  intro w hw n h
  have hh : h ∈ ⋃ m, K m := by rw [hKcover]; exact Set.mem_univ h
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hh
  have hp := Set.mem_iInter.mp hw (Nat.pair n m)
  have hun : (Nat.pair n m).unpair = (n, m) := Nat.unpair_pair n m
  have := hwit (Nat.pair n m) w hp
  rw [hun] at this
  exact this h hm

/-! ### Bridge to the measure-theoretic definition of prevalence -/

/-- On a Banach space carrying its Borel structure, block prevalence of an open set is prevalence
in the sense of a compactly supported probe. -/
theorem Prevalent.of_blockPrevalent [MeasurableSpace S] [BorelSpace S] {G : Set S} (hG : IsOpen G)
    (h : BlockPrevalent G) : Prevalent G := by
  obtain ⟨d, L, hL, hx⟩ := h
  refine ⟨{ measure := (blockProbeLaw d).map (productProbeMap d L)
            isProbability := Measure.isProbabilityMeasure_map
              (continuous_productProbeMap hL).measurable.aemeasurable
            carrier := Set.range (productProbeMap d L)
            isCompact_carrier := isCompact_range_productProbeMap hL
            measure_compl_carrier := by
              rw [Measure.map_apply (continuous_productProbeMap hL).measurable
                (isCompact_range_productProbeMap hL).isClosed.measurableSet.compl]
              convert measure_empty (μ := blockProbeLaw d)
              ext ξ
              simp }, fun x _ => ?_⟩
  have hsetmeas : MeasurableSet {w : S | x + w ∉ G} :=
    (hG.isClosed_compl.measurableSet).preimage (measurable_const_add x)
  show ((blockProbeLaw d).map (productProbeMap d L)) {w : S | x + w ∉ G} = 0
  rw [Measure.map_apply (continuous_productProbeMap hL).measurable hsetmeas]
  exact hx x (Set.mem_univ x)

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ProbabilityTheory MeasurableSpace Metric
open scoped ENNReal NNReal

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]

/-- **Block-prevalent global witness for a countable family of configuration spaces.**  Each
pattern has its own sigma-compact configuration space; every compact patch of every pattern is
certified by its own finite Euclidean control block, and all the blocks are merged into one
convergent probe series. -/
theorem globalWitness_blockPrevalent_of_sigmaCompact_family {H : ℕ → Type*}
    [∀ n, TopologicalSpace (H n)] [∀ n, SigmaCompactSpace (H n)]
    (Witness : ∀ n, S → H n → Prop)
    (hcompact : ∀ (n : ℕ) (K : Set (H n)), IsCompact K →
      ∃ (Dblk : ℕ) (l : (Fin Dblk → ℝ) →L[ℝ] S) (G : Set S), IsOpen G ∧
        (∀ c : ℝ, 0 < c → ∀ center : S, ∀ μ : Measure (Fin Dblk → ℝ), μ ≪ volume →
          μ {p | center + (c • l) p ∉ G} = 0) ∧
        ∀ w ∈ G, ∀ h ∈ K, Witness n w h) :
    BlockPrevalent {w : S | ∀ n h, Witness n w h} := by
  classical
  have hcov : ∀ n : ℕ, ∃ K : ℕ → Set (H n),
      (∀ m, IsCompact (K m)) ∧ (⋃ m, K m) = (Set.univ : Set (H n)) :=
    fun n => SigmaCompactSpace.exists_compact_covering (X := H n)
  choose Kc hKcCompact hKcCover using hcov
  have cert : ∀ n m : ℕ, ∃ (Dblk : ℕ) (l : (Fin Dblk → ℝ) →L[ℝ] S) (G : Set S), IsOpen G ∧
      (∀ c : ℝ, 0 < c → ∀ center : S, ∀ μ : Measure (Fin Dblk → ℝ), μ ≪ volume →
        μ {p | center + (c • l) p ∉ G} = 0) ∧
      ∀ w ∈ G, ∀ h ∈ Kc n m, Witness n w h :=
    fun n m => hcompact n (Kc n m) (hKcCompact n m)
  choose Dpat lpat Gpat hopen hblk hwit using cert
  have hprev : BlockPrevalent (⋂ p : ℕ, Gpat p.unpair.1 p.unpair.2) :=
    blockPrevalent_iInter_of_blockControl_scalable
      (d := fun p => Dpat p.unpair.1 p.unpair.2)
      (fun p => lpat p.unpair.1 p.unpair.2)
      (fun p => Gpat p.unpair.1 p.unpair.2)
      (fun p => hopen p.unpair.1 p.unpair.2)
      (fun p => hblk p.unpair.1 p.unpair.2)
  refine hprev.mono ?_
  intro w hw n h
  have hh : h ∈ ⋃ m, Kc n m := by rw [hKcCover n]; exact Set.mem_univ h
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hh
  have hmem : w ∈ Gpat n m := by
    have hpair := Set.mem_iInter.mp hw (Nat.pair n m)
    simpa using hpair
  exact hwit n m w hmem h hm

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ProbabilityTheory MeasurableSpace Metric
open scoped ENNReal NNReal

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]

/-- The probe series is bounded by the sum of the block amplitudes. -/
theorem norm_productProbeMap_le {d : ℕ → ℕ} {L : ∀ n, (Fin (d n) → ℝ) →L[ℝ] S}
    (hL : Summable fun n => ‖L n‖) (ξ : ∀ n, Fin (d n) → ℝ) :
    ‖productProbeMap d L ξ‖ ≤ ∑' n, ‖L n‖ := by
  have hsum : Summable fun n => ‖L n (unitTruncate (ξ n))‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => norm_productProbeMap_term d L n (ξ n)) hL
  refine le_trans (norm_tsum_le_tsum_norm hsum) ?_
  exact hsum.tsum_le_tsum (fun n => norm_productProbeMap_term d L n (ξ n)) hL

/-- `G` is **block prevalent with a probe of radius `r`**: the convergent block series never leaves
the ball of radius `r`, and its law makes the complement of `G` null after every deterministic
recentring.  This is the exact form the moment-fiber chart needs, where the probe has to stay
inside the positivity margin of the chart. -/
def BlockPrevalentRadius (r : ℝ) (G : Set S) : Prop :=
  ∃ (d : ℕ → ℕ) (L : ∀ n, (Fin (d n) → ℝ) →L[ℝ] S) (_ : Summable fun n => ‖L n‖),
    (∀ ξ, ‖productProbeMap d L ξ‖ ≤ r) ∧
      ∀ x : S, blockProbeLaw d {ξ | x + productProbeMap d L ξ ∉ G} = 0

omit [CompleteSpace S] in
theorem BlockPrevalentRadius.blockPrevalent {r : ℝ} {G : Set S} (h : BlockPrevalentRadius r G) :
    BlockPrevalent G := by
  obtain ⟨d, L, hL, _, hx⟩ := h
  exact ⟨d, L, hL, fun x _ => hx x⟩

omit [CompleteSpace S] in
theorem BlockPrevalentRadius.mono {r : ℝ} {G G' : Set S} (h : BlockPrevalentRadius r G)
    (hGG' : G ⊆ G') : BlockPrevalentRadius r G' := by
  obtain ⟨d, L, hL, hnorm, hx⟩ := h
  refine ⟨d, L, hL, hnorm, fun x => ?_⟩
  refine measure_mono_null (fun ξ hξ => ?_) (hx x)
  exact fun hmem => hξ (hGG' hmem)

/-- **Scalable block control gives block prevalence with an arbitrarily small probe.** -/
theorem blockPrevalentRadius_iInter_of_blockControl_scalable {d : ℕ → ℕ}
    (l : ∀ n, (Fin (d n) → ℝ) →L[ℝ] S) (G : ℕ → Set S) (hGopen : ∀ n, IsOpen (G n))
    (hblock : ∀ n, ∀ c : ℝ, 0 < c → ∀ center : S, ∀ μ : Measure (Fin (d n) → ℝ), μ ≪ volume →
      μ {p | center + (c • l n) p ∉ G n} = 0)
    {r : ℝ} (hr : 0 < r) :
    BlockPrevalentRadius r (⋂ n, G n) := by
  classical
  set c : ℕ → ℝ := fun n => (r / 2) * (1 / 2 : ℝ) ^ n / (1 + ‖l n‖) with hc
  have hden : ∀ n, (0 : ℝ) < 1 + ‖l n‖ := fun n => by positivity
  have hcpos : ∀ n, 0 < c n := fun n => by
    have h2 : (0 : ℝ) < (r / 2) * (1 / 2 : ℝ) ^ n := by positivity
    exact div_pos h2 (hden n)
  have hbound : ∀ n, ‖c n • l n‖ ≤ (r / 2) * (1 / 2 : ℝ) ^ n := by
    intro n
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hcpos n), hc]
    have hle : ‖l n‖ / (1 + ‖l n‖) ≤ 1 := by
      rw [div_le_one (hden n)]
      linarith [norm_nonneg (l n)]
    calc (r / 2) * (1 / 2 : ℝ) ^ n / (1 + ‖l n‖) * ‖l n‖
        = ((r / 2) * (1 / 2 : ℝ) ^ n) * (‖l n‖ / (1 + ‖l n‖)) := by ring
      _ ≤ ((r / 2) * (1 / 2 : ℝ) ^ n) * 1 :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (r / 2) * (1 / 2 : ℝ) ^ n := mul_one _
  have hgeom : Summable fun n : ℕ => (r / 2) * (1 / 2 : ℝ) ^ n :=
    summable_geometric_two.mul_left _
  have hLsum : Summable fun n => ‖c n • l n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hgeom
  have hnorm : ∀ ξ, ‖productProbeMap d (fun n => c n • l n) ξ‖ ≤ r := by
    intro ξ
    refine le_trans (norm_productProbeMap_le hLsum ξ) ?_
    refine le_trans (hLsum.tsum_le_tsum hbound hgeom) ?_
    rw [tsum_mul_left, tsum_geometric_two]
    linarith
  refine ⟨d, fun n => c n • l n, hLsum, hnorm, fun x => ?_⟩
  have hprev := blockPrevalent_iInter_of_blockControl (L := fun n => c n • l n) hLsum G hGopen
    (fun n center μ hμ => hblock n (c n) (hcpos n) center μ hμ)
  obtain ⟨d', L', hL', hx'⟩ := hprev
  have hcover : {ξ : ∀ k, Fin (d k) → ℝ |
      x + productProbeMap d (fun n => c n • l n) ξ ∉ ⋂ n, G n}
      = ⋃ n, {ξ : ∀ k, Fin (d k) → ℝ |
        x + productProbeMap d (fun n => c n • l n) ξ ∉ G n} := by
    ext ξ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter]
    push Not
    rfl
  rw [hcover]
  exact measure_iUnion_null fun n =>
    blockProbeLaw_block_null hLsum (hGopen n) n
      (fun center μ hμ => hblock n (c n) (hcpos n) center μ hμ) x

/-- **Small-probe block-prevalent global witness for a countable family of configuration
spaces.** -/
theorem globalWitness_blockPrevalentRadius_of_sigmaCompact_family {H : ℕ → Type*}
    [∀ n, TopologicalSpace (H n)] [∀ n, SigmaCompactSpace (H n)]
    (Witness : ∀ n, S → H n → Prop)
    (hcompact : ∀ (n : ℕ) (K : Set (H n)), IsCompact K →
      ∃ (Dblk : ℕ) (l : (Fin Dblk → ℝ) →L[ℝ] S) (G : Set S), IsOpen G ∧
        (∀ c : ℝ, 0 < c → ∀ center : S, ∀ μ : Measure (Fin Dblk → ℝ), μ ≪ volume →
          μ {p | center + (c • l) p ∉ G} = 0) ∧
        ∀ w ∈ G, ∀ h ∈ K, Witness n w h)
    {r : ℝ} (hr : 0 < r) :
    BlockPrevalentRadius r {w : S | ∀ n h, Witness n w h} := by
  classical
  have hcov : ∀ n : ℕ, ∃ K : ℕ → Set (H n),
      (∀ m, IsCompact (K m)) ∧ (⋃ m, K m) = (Set.univ : Set (H n)) :=
    fun n => SigmaCompactSpace.exists_compact_covering (X := H n)
  choose Kc hKcCompact hKcCover using hcov
  have cert : ∀ n m : ℕ, ∃ (Dblk : ℕ) (l : (Fin Dblk → ℝ) →L[ℝ] S) (G : Set S), IsOpen G ∧
      (∀ c : ℝ, 0 < c → ∀ center : S, ∀ μ : Measure (Fin Dblk → ℝ), μ ≪ volume →
        μ {p | center + (c • l) p ∉ G} = 0) ∧
      ∀ w ∈ G, ∀ h ∈ Kc n m, Witness n w h :=
    fun n m => hcompact n (Kc n m) (hKcCompact n m)
  choose Dpat lpat Gpat hopen hblk hwit using cert
  have hprev : BlockPrevalentRadius r (⋂ p : ℕ, Gpat p.unpair.1 p.unpair.2) :=
    blockPrevalentRadius_iInter_of_blockControl_scalable
      (d := fun p => Dpat p.unpair.1 p.unpair.2)
      (fun p => lpat p.unpair.1 p.unpair.2)
      (fun p => Gpat p.unpair.1 p.unpair.2)
      (fun p => hopen p.unpair.1 p.unpair.2)
      (fun p => hblk p.unpair.1 p.unpair.2) hr
  refine hprev.mono ?_
  intro w hw n h
  have hh : h ∈ ⋃ m, Kc n m := by rw [hKcCover n]; exact Set.mem_univ h
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hh
  have hmem : w ∈ Gpat n m := by
    have hpair := Set.mem_iInter.mp hw (Nat.pair n m)
    simpa using hpair
  exact hwit n m w hmem h hm

end GaloisForLFunctions.HTGeometry

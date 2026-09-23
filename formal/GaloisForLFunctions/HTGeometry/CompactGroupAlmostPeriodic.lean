import Mathlib

/-!
# Almost periodicity of continuous observables along a compact group flow

A one-parameter flow `r : ℝ → G` into a compact commutative topological group produces, from any
continuous observable `g : G → E`, the height signal `t ↦ g (r t)`.  Two facts are proved here.

* `isBohrAlmostPeriodic_of_compact_flow` — the signal is Bohr uniformly almost periodic.  The
  identity neighbourhood on which `g` moves by less than `ε` is produced by the tube lemma, and a
  finite subcover of the compact orbit closure makes the set of returns to that neighbourhood
  relatively dense.
* `eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero_compactGroupAlmostPeriodic` — an almost periodic signal vanishing at
  infinity vanishes identically: an almost period translates any height into the small tail.

For a finite measure `μ` on `G` the expectation `t ↦ ∫ f (r t · z) dμ z` of a continuous observable
is such a signal, its symbol being the continuous average `screenAverage μ f`.
-/

open Filter Topology MeasureTheory Set
open scoped Pointwise

namespace GaloisForLFunctions.HTGeometry

variable {G : Type*} [TopologicalSpace G] [CommGroup G] [IsTopologicalGroup G] [CompactSpace G]
variable {E : Type*} [NormedAddCommGroup E]

/-- **Bohr uniform almost periodicity**: for every `ε > 0` the `ε`-almost periods form a
relatively dense subset of the line. -/
def IsBohrAlmostPeriodic (F : ℝ → E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, 0 < L ∧
    ∀ x : ℝ, ∃ τ ∈ Set.Icc x (x + L), ∀ t : ℝ, ‖F (t + τ) - F t‖ ≤ ε

/-- Translating by an element close to the identity moves a continuous observable on a compact
group uniformly little.  The tube lemma over the compact second factor turns the pointwise
statement at the identity into a neighbourhood statement. -/
theorem exists_nhds_one_norm_translate_sub_le {g : G → E} (hg : Continuous g) {ε : ℝ}
    (hε : 0 < ε) : ∃ V ∈ 𝓝 (1 : G), ∀ a ∈ V, ∀ y : G, ‖g (a * y) - g y‖ ≤ ε := by
  have hcont : Continuous fun q : G × G => ‖g (q.1 * q.2) - g q.2‖ :=
    ((hg.comp continuous_mul).sub (hg.comp continuous_snd)).norm
  have hn : IsOpen {q : G × G | ‖g (q.1 * q.2) - g q.2‖ < ε} := isOpen_lt hcont continuous_const
  have hsub : ({1} : Set G) ×ˢ (Set.univ : Set G) ⊆ {q : G × G | ‖g (q.1 * q.2) - g q.2‖ < ε} := by
    rintro ⟨a, y⟩ ⟨ha, -⟩
    simp only [Set.mem_singleton_iff] at ha
    simpa [ha] using hε
  obtain ⟨u, v, hu, -, h1u, hvuniv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hn hsub
  refine ⟨u, hu.mem_nhds (Set.singleton_subset_iff.mp h1u), fun a ha y => ?_⟩
  exact le_of_lt (huv (Set.mk_mem_prod ha (hvuniv (Set.mem_univ y))))

/-- **Relative density of the returns to a neighbourhood of the identity.**  Finitely many
translates of a small open set cover the compact orbit closure, so every interval of length
`2M + 2` contains a time at which the flow lies in the given neighbourhood. -/
theorem exists_relatively_dense_mem {r : ℝ → G}
    (hadd : ∀ s t : ℝ, r (s + t) = r s * r t) {V : Set G} (hV : V ∈ 𝓝 (1 : G)) :
    ∃ L : ℝ, 0 < L ∧ ∀ x : ℝ, ∃ τ ∈ Set.Icc x (x + L), r τ ∈ V := by
  classical
  have hVinv : V⁻¹ ∈ 𝓝 (1 : G) := inv_mem_nhds_one G hV
  set W : Set G := interior V⁻¹ with hWdef
  have hW1 : (1 : G) ∈ W := mem_interior_iff_mem_nhds.mpr hVinv
  have hWopen : IsOpen W := isOpen_interior
  have hWV : W⁻¹ ⊆ V := by
    intro y hy
    have hy' : y⁻¹ ∈ W := by simpa [Set.mem_inv] using hy
    have : y⁻¹ ∈ V⁻¹ := interior_subset hy'
    simpa [Set.mem_inv] using this
  have hWinvOpen : IsOpen W⁻¹ := hWopen.inv
  set U : ℝ → Set G := fun s => (fun z => r s * z) '' W⁻¹ with hUdef
  have hUopen : ∀ s, IsOpen (U s) := fun s =>
    (Homeomorph.mulLeft (r s)).isOpenMap _ hWinvOpen
  set K : Set G := closure (Set.range r) with hKdef
  have hK : IsCompact K := isClosed_closure.isCompact
  have hcover : K ⊆ ⋃ s : ℝ, U s := by
    intro y hy
    have hopen : IsOpen ((fun z => y * z) '' W) := (Homeomorph.mulLeft y).isOpenMap _ hWopen
    have hymem : y ∈ (fun z => y * z) '' W := ⟨1, hW1, by simp⟩
    obtain ⟨z, hz, hzr⟩ := (mem_closure_iff.mp hy) _ hopen hymem
    obtain ⟨w, hw, hwy⟩ := hz
    obtain ⟨s, hs⟩ := hzr
    refine Set.mem_iUnion.mpr ⟨s, ?_⟩
    refine ⟨w⁻¹, by simpa [Set.mem_inv] using hw, ?_⟩
    rw [hs, ← hwy]
    group
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUopen hcover
  obtain ⟨M, hM⟩ := (t.image fun s : ℝ => |s|).exists_le
  have hMs : ∀ s ∈ t, |s| ≤ M := fun s hs => hM _ (Finset.mem_image_of_mem _ hs)
  refine ⟨2 * |M| + 2, by positivity, fun x => ?_⟩
  have hru : r (x + |M| + 1) ∈ K := subset_closure ⟨x + |M| + 1, rfl⟩
  obtain ⟨s, hs, hmem⟩ := Set.mem_iUnion₂.mp (ht hru)
  obtain ⟨w, hw, hwr⟩ := hmem
  have hsM : |s| ≤ |M| := le_trans (hMs s hs) (le_abs_self M)
  have hsabs := abs_le.mp hsM
  refine ⟨x + |M| + 1 - s, ⟨by linarith [hsabs.2], by linarith [hsabs.1]⟩, ?_⟩
  have hstep : r (x + |M| + 1 - s) * r s = r (x + |M| + 1) := by
    rw [← hadd]; ring_nf
  have hval : r (x + |M| + 1 - s) = w := by
    have hcancel : r (x + |M| + 1 - s) * r s = w * r s := by
      rw [hstep, ← hwr]
      exact mul_comm _ _
    exact mul_right_cancel hcancel
  rw [hval]
  exact hWV (by simpa [Set.mem_inv] using hw)

/-- **A continuous observable of a compact group flow is Bohr almost periodic.** -/
theorem isBohrAlmostPeriodic_of_compact_flow {r : ℝ → G}
    (hadd : ∀ s t : ℝ, r (s + t) = r s * r t) {g : G → E} (hg : Continuous g) :
    IsBohrAlmostPeriodic fun t => g (r t) := by
  intro ε hε
  obtain ⟨V, hV, hVprop⟩ := exists_nhds_one_norm_translate_sub_le hg hε
  obtain ⟨L, hL, hLprop⟩ := exists_relatively_dense_mem hadd hV
  refine ⟨L, hL, fun x => ?_⟩
  obtain ⟨τ, hτ, hrτ⟩ := hLprop x
  refine ⟨τ, hτ, fun t => ?_⟩
  show ‖g (r (t + τ)) - g (r t)‖ ≤ ε
  have hshift : r (t + τ) = r τ * r t := by rw [hadd, mul_comm]
  rw [hshift]
  exact hVprop _ hrτ (r t)

/-- **An almost periodic signal vanishing at infinity vanishes identically.** -/
theorem eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero_compactGroupAlmostPeriodic {F : ℝ → E}
    (hap : IsBohrAlmostPeriodic F) (hF : Tendsto F atTop (𝓝 0)) (x : ℝ) : F x = 0 := by
  have key : ∀ ε : ℝ, 0 < ε → ‖F x‖ ≤ 2 * ε := by
    intro ε hε
    obtain ⟨L, hL, hLprop⟩ := hap ε hε
    obtain ⟨T, hT⟩ := eventually_atTop.mp (NormedAddGroup.tendsto_nhds_zero.mp hF ε hε)
    obtain ⟨τ, hτ, hτprop⟩ := hLprop (|x| + T)
    have hxτ : T ≤ x + τ := by
      have h1 : |x| + T ≤ τ := hτ.1
      have h2 : -|x| ≤ x := neg_abs_le x
      linarith
    have h1 : ‖F (x + τ) - F x‖ ≤ ε := hτprop x
    have h2 : ‖F (x + τ)‖ ≤ ε := (hT _ hxτ).le
    calc ‖F x‖ = ‖F (x + τ) - (F (x + τ) - F x)‖ := by congr 1; abel
      _ ≤ ‖F (x + τ)‖ + ‖F (x + τ) - F x‖ := norm_sub_le _ _
      _ ≤ 2 * ε := by linarith
  have hzero : ‖F x‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := key (ε / 2) (by linarith)
    linarith
  exact norm_le_zero_iff.mp hzero

/-- **A continuous observable of a compact group flow that decays at infinity is identically
zero along the flow.** -/
theorem eq_zero_of_compact_flow_of_tendsto_zero {r : ℝ → G}
    (hadd : ∀ s t : ℝ, r (s + t) = r s * r t) {g : G → E} (hg : Continuous g)
    (hlim : Tendsto (fun t => g (r t)) atTop (𝓝 0)) (t : ℝ) : g (r t) = 0 :=
  eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero_compactGroupAlmostPeriodic
    (isBohrAlmostPeriodic_of_compact_flow hadd hg) hlim t

section ScreenExpectation

variable [MeasurableSpace G] [OpensMeasurableSpace G] [SecondCountableTopology G]
variable [NormedSpace ℝ E]

/-- The expectation of the observable `f` in the state obtained from `μ` by translating by `a`. -/
noncomputable def screenAverage (μ : Measure G) (f : G → E) (a : G) : E := ∫ z, f (a * z) ∂μ

omit [NormedSpace ℝ E] in
/-- A continuous observable on a compact group is integrable against every finite measure, in
every translate. -/
theorem integrable_translate (μ : Measure G) [IsFiniteMeasure μ] {f : G → E} (hf : Continuous f)
    (a : G) : Integrable (fun z => f (a * z)) μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound ((hf.comp (continuous_const_mul a)).aestronglyMeasurable) C
    (Filter.Eventually.of_forall fun z => hC _ (Set.mem_univ _))

/-- **The screen average is a continuous observable.**  Uniform smallness of translates near the
identity bounds the difference of two averages by the total mass times that smallness. -/
theorem continuous_screenAverage (μ : Measure G) [IsFiniteMeasure μ] {f : G → E}
    (hf : Continuous f) : Continuous (screenAverage μ f) := by
  refine continuous_iff_continuousAt.mpr fun a₀ => ?_
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  set m : ℝ := (μ Set.univ).toReal with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  set ε' : ℝ := ε / (m + 1) with hε'def
  have hε' : 0 < ε' := by positivity
  obtain ⟨V, hV, hVprop⟩ := exists_nhds_one_norm_translate_sub_le hf hε'
  have hpre : (fun a => a₀⁻¹ * a) ⁻¹' V ∈ 𝓝 a₀ := by
    refine ContinuousAt.preimage_mem_nhds (by fun_prop) ?_
    simpa using hV
  filter_upwards [hpre] with a ha
  have hsplit : screenAverage μ f a - screenAverage μ f a₀ = ∫ z, (f (a * z) - f (a₀ * z)) ∂μ :=
    (integral_sub (integrable_translate μ hf a) (integrable_translate μ hf a₀)).symm
  have hbd : ∀ z : G, ‖f (a * z) - f (a₀ * z)‖ ≤ ε' := by
    intro z
    have hz := hVprop _ ha (a₀ * z)
    have hrw : a₀⁻¹ * a * (a₀ * z) = a * z := by
      have hstep : a₀⁻¹ * a * (a₀ * z) = a₀⁻¹ * a₀ * (a * z) := by
        simp [mul_comm, mul_assoc, mul_left_comm]
      rw [hstep, inv_mul_cancel, one_mul]
    rwa [hrw] at hz
  have hint : ‖∫ z, (f (a * z) - f (a₀ * z)) ∂μ‖ ≤ ε' * m :=
    norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hbd)
  have hlt : ε' * m < ε := by
    rw [hε'def, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  rw [dist_eq_norm, hsplit]
  exact lt_of_le_of_lt hint hlt

/-- **The screen expectation of a bounded observable is Bohr almost periodic.** -/
theorem isBohrAlmostPeriodic_screenExpectation (μ : Measure G) [IsFiniteMeasure μ] {f : G → E}
    (hf : Continuous f) {r : ℝ → G} (hadd : ∀ s t : ℝ, r (s + t) = r s * r t) :
    IsBohrAlmostPeriodic fun t => ∫ z, f (r t * z) ∂μ :=
  isBohrAlmostPeriodic_of_compact_flow hadd (continuous_screenAverage μ hf)

/-- **A screen expectation that decays at infinity is identically zero.** -/
theorem screenExpectation_eq_zero_of_tendsto_zero (μ : Measure G) [IsFiniteMeasure μ] {f : G → E}
    (hf : Continuous f) {r : ℝ → G} (hadd : ∀ s t : ℝ, r (s + t) = r s * r t)
    (hlim : Tendsto (fun t => ∫ z, f (r t * z) ∂μ) atTop (𝓝 0)) (t : ℝ) :
    (∫ z, f (r t * z) ∂μ) = 0 :=
  eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero_compactGroupAlmostPeriodic
    (isBohrAlmostPeriodic_screenExpectation μ hf hadd) hlim t

end ScreenExpectation

end GaloisForLFunctions.HTGeometry

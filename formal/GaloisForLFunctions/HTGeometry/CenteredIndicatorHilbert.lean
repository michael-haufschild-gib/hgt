import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Centered indicators in a finite aperture

This source-independent `L²` package gives the exact Hilbert geometry of measurable subsets of a
finite positive-measure aperture.  It is the reusable core of the physical hard-aperture metric.
-/

open scoped BigOperators symmDiff
open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Indicator of `E` with its constant component on `Ω` removed. -/
def centeredIndicatorOn {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (Ω E : Set X)
    (hΩ : MeasurableSet Ω) (hΩfin : μ Ω ≠ ⊤)
    (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤) :
    Lp ℝ 2 μ :=
  indicatorConstLp 2 hE hEfin (1 : ℝ) -
    (μ.real E / μ.real Ω) • indicatorConstLp 2 hΩ hΩfin (1 : ℝ)

/-- An `L²` element which is almost everywhere either `0` or `1`. -/
def IsAEBoolean {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (u : Lp ℝ 2 μ) : Prop :=
  ∀ᵐ x ∂μ, u x = 0 ∨ u x = 1

/-- Almost-everywhere Boolean-valued `L²` elements form a sequentially closed set. -/
theorem isSeqClosed_isAEBoolean {X : Type*} [MeasurableSpace X] (μ : Measure X) :
    IsSeqClosed {u : Lp ℝ 2 μ | IsAEBoolean μ u} := by
  intro f g hf hfg
  obtain ⟨ns, _, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hfg).exists_seq_tendsto_ae
  change IsAEBoolean μ g
  change ∀ᵐ x ∂μ, g x = 0 ∨ g x = 1
  filter_upwards [hlim, countable_iInter_mem.mpr hf] with x hlimx hx
  have hmem : g x ∈ ({0, 1} : Set ℝ) := by
    apply IsClosed.mem_of_tendsto (Set.finite_singleton 1 |>.insert 0 |>.isClosed) hlimx
    filter_upwards with n
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using Set.mem_iInter.mp hx (ns n)
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem

/-- An `L²` element which vanishes almost everywhere away from `Ω`. -/
def IsAEZeroOutside {X : Type*} [MeasurableSpace X] (μ : Measure X) (Ω : Set X)
    (u : Lp ℝ 2 μ) : Prop :=
  ∀ᵐ x ∂μ, x ∉ Ω → u x = 0

/-- The condition of vanishing away from a fixed aperture is sequentially closed in `L²`. -/
theorem isSeqClosed_isAEZeroOutside {X : Type*} [MeasurableSpace X] (μ : Measure X) (Ω : Set X) :
    IsSeqClosed {u : Lp ℝ 2 μ | IsAEZeroOutside μ Ω u} := by
  intro f g hf hfg
  obtain ⟨ns, _, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hfg).exists_seq_tendsto_ae
  change IsAEZeroOutside μ Ω g
  change ∀ᵐ x ∂μ, x ∉ Ω → g x = 0
  filter_upwards [hlim, countable_iInter_mem.mpr hf] with x hlimx hx hxΩ
  apply tendsto_nhds_unique hlimx
  have heq : (fun n => f (ns n) x) = fun _ : ℕ => 0 := by
    funext n
    exact Set.mem_iInter.mp hx (ns n) hxΩ
  rw [heq]
  exact tendsto_const_nhds

/-- A Boolean `L²` element vanishing outside a finite aperture is an actual aperture indicator. -/
theorem exists_indicatorConstLp_eq_of_isAEBoolean_of_ae_zero_outside
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (Ω : Set X)
    (hΩ : MeasurableSet Ω) (hΩfin : μ Ω ≠ ⊤) (u : Lp ℝ 2 μ)
    (hu : IsAEBoolean μ u) (hzero : ∀ᵐ x ∂μ, x ∉ Ω → u x = 0) :
    ∃ (E : Set X) (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤), E ⊆ Ω ∧
      indicatorConstLp 2 hE hEfin (1 : ℝ) = u := by
  let E : Set X := Ω ∩ toMeasurable μ (u ⁻¹' {1})
  have hE : MeasurableSet E := hΩ.inter (measurableSet_toMeasurable _ _)
  have hEΩ : E ⊆ Ω := Set.inter_subset_left
  have hEfin : μ E ≠ ⊤ := measure_ne_top_of_subset hEΩ hΩfin
  refine ⟨E, hE, hEfin, hEΩ, ?_⟩
  have hpre : toMeasurable μ (u ⁻¹' {1}) =ᵐ[μ] u ⁻¹' {1} :=
    (Lp.aestronglyMeasurable u).aemeasurable.nullMeasurableSet_preimage
      (measurableSet_singleton 1) |>.toMeasurable_ae_eq
  apply Lp.ext
  have hindicator := indicatorConstLp_coeFn (p := 2) (hs := hE) (hμs := hEfin) (c := (1 : ℝ))
  filter_upwards [hindicator, hu, hzero, hpre] with x hindicator hbool hzero hpre
  rw [hindicator]
  by_cases hxΩ : x ∈ Ω
  · rcases hbool with huzero | huone
    · rw [Set.indicator_of_notMem]
      · exact huzero.symm
      · intro hxE
        change x ∈ Ω ∩ toMeasurable μ (u ⁻¹' {1}) at hxE
        have hxpre : x ∈ u ⁻¹' {1} := by
          change (u ⁻¹' {1}) x
          rw [← hpre]
          exact hxE.2
        have huone : u x = 1 := by simpa using hxpre
        exact zero_ne_one (huzero.symm.trans huone)
    · have hxpre : x ∈ u ⁻¹' {1} := by simpa using huone
      have hxmeas : x ∈ toMeasurable μ (u ⁻¹' {1}) := by
        change (toMeasurable μ (u ⁻¹' {1})) x
        rw [hpre]
        exact hxpre
      have hxE : x ∈ E := by
        change x ∈ Ω ∩ toMeasurable μ (u ⁻¹' {1})
        exact ⟨hxΩ, hxmeas⟩
      rw [Set.indicator_of_mem hxE]
      exact huone.symm
  · rw [Set.indicator_of_notMem]
    · exact (hzero hxΩ).symm
    · exact fun hxE => hxΩ hxE.1

/-- Indicators of measurable subsets of a fixed finite aperture form a closed subset of `L²`. -/
theorem isClosed_indicatorConstLp_one_of_subset
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (Ω : Set X)
    (hΩ : MeasurableSet Ω) (hΩfin : μ Ω ≠ ⊤) :
    IsClosed {u : Lp ℝ 2 μ | ∃ (E : Set X) (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤),
      E ⊆ Ω ∧ indicatorConstLp 2 hE hEfin (1 : ℝ) = u} := by
  apply IsSeqClosed.isClosed
  intro f g hf hfg
  have hfbool : ∀ n, IsAEBoolean μ (f n) := by
    intro n
    rcases hf n with ⟨E, hE, hEfin, hEΩ, hfn⟩
    rw [← hfn]
    change ∀ᵐ x ∂μ, indicatorConstLp 2 hE hEfin (1 : ℝ) x = 0 ∨
      indicatorConstLp 2 hE hEfin (1 : ℝ) x = 1
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hE) (hμs := hEfin)
      (c := (1 : ℝ))] with x hx
    rw [hx]
    by_cases hxE : x ∈ E
    · exact Or.inr (Set.indicator_of_mem hxE)
    · exact Or.inl (Set.indicator_of_notMem hxE)
  have hfzero : ∀ n, IsAEZeroOutside μ Ω (f n) := by
    intro n
    rcases hf n with ⟨E, hE, hEfin, hEΩ, hfn⟩
    rw [← hfn]
    change ∀ᵐ x ∂μ, x ∉ Ω → indicatorConstLp 2 hE hEfin (1 : ℝ) x = 0
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hE) (hμs := hEfin)
      (c := (1 : ℝ))] with x hx hxΩ
    rw [hx, Set.indicator_of_notMem]
    exact fun hxE => hxΩ (hEΩ hxE)
  exact exists_indicatorConstLp_eq_of_isAEBoolean_of_ae_zero_outside μ Ω hΩ hΩfin g
    (isSeqClosed_isAEBoolean μ f g hfbool hfg)
    (isSeqClosed_isAEZeroOutside μ Ω f g hfzero hfg)

/-- Measures of arbitrary aperture subsets admit a convergent subsequence in the closed measure
interval. -/
theorem exists_subseq_tendsto_measureReal_of_subset
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (Ω : Set X) (E : ℕ → Set X)
    (hEΩ : ∀ n, E n ⊆ Ω) :
    ∃ a ∈ Set.Icc 0 (μ.real Ω), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => μ.real (E (φ n))) atTop (𝓝 a) := by
  exact isCompact_Icc.tendsto_subseq fun n =>
    ⟨measureReal_nonneg, MeasureTheory.measureReal_mono (hEΩ n)⟩

/-- Along convergent subset measures, convergence of centered indicators reconstructs convergence
of the corresponding uncentered indicators. -/
theorem tendsto_indicatorConstLp_of_tendsto_centeredIndicatorOn_of_tendsto_measureReal
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (Ω : Set X) (E : ℕ → Set X)
    (hΩ : MeasurableSet Ω) (hΩfin : μ Ω ≠ ⊤)
    (hE : ∀ n, MeasurableSet (E n)) (hEfin : ∀ n, μ (E n) ≠ ⊤)
    {g : Lp ℝ 2 μ} {a : ℝ}
    (hcentered : Tendsto (fun n => centeredIndicatorOn μ Ω (E n) hΩ hΩfin
      (hE n) (hEfin n)) atTop (𝓝 g))
    (hmeasure : Tendsto (fun n => μ.real (E n)) atTop (𝓝 a)) :
    Tendsto (fun n => indicatorConstLp 2 (hE n) (hEfin n) (1 : ℝ)) atTop
      (𝓝 (g + (a / μ.real Ω) • indicatorConstLp 2 hΩ hΩfin (1 : ℝ))) := by
  simpa only [centeredIndicatorOn, sub_add_cancel] using
    hcentered.add (hmeasure.div_const (μ.real Ω)).smul_const

/-- Exact Gram formula for centered indicators in a finite positive-measure aperture. -/
theorem real_inner_centeredIndicatorOn
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (Ω E F : Set X)
    (hΩ : MeasurableSet Ω) (hΩfin : μ Ω ≠ ⊤)
    (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤)
    (hF : MeasurableSet F) (hFfin : μ F ≠ ⊤)
    (hEΩ : E ⊆ Ω) (hFΩ : F ⊆ Ω) (hΩpos : 0 < μ.real Ω) :
    inner ℝ (centeredIndicatorOn μ Ω E hΩ hΩfin hE hEfin)
        (centeredIndicatorOn μ Ω F hΩ hΩfin hF hFfin) =
      μ.real (E ∩ F) - μ.real E * μ.real F / μ.real Ω := by
  simp only [centeredIndicatorOn, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right,
    MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one,
    Set.inter_eq_left.mpr hEΩ, Set.inter_eq_right.mpr hFΩ, Set.inter_self]
  field_simp [hΩpos.ne']
  ring

/-- Exact squared norm of a centered aperture indicator. -/
theorem norm_sq_centeredIndicatorOn
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (Ω E : Set X)
    (hΩ : MeasurableSet Ω) (hΩfin : μ Ω ≠ ⊤)
    (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤)
    (hEΩ : E ⊆ Ω) (hΩpos : 0 < μ.real Ω) :
    ‖centeredIndicatorOn μ Ω E hΩ hΩfin hE hEfin‖ ^ 2 =
      μ.real E * (μ.real Ω - μ.real E) / μ.real Ω := by
  rw [← real_inner_self_eq_norm_sq,
    real_inner_centeredIndicatorOn μ Ω E E hΩ hΩfin hE hEfin hE hEfin hEΩ hEΩ hΩpos,
    Set.inter_self]
  field_simp [hΩpos.ne']

/-- Relative complements are antipodes in the centered-indicator Hilbert geometry. -/
theorem centeredIndicatorOn_sdiff_eq_neg
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (Ω E : Set X)
    (hΩ : MeasurableSet Ω) (hΩfin : μ Ω ≠ ⊤)
    (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤)
    (hEΩ : E ⊆ Ω) (hΩpos : 0 < μ.real Ω) :
    centeredIndicatorOn μ Ω (Ω \ E) hΩ hΩfin (hΩ.diff hE)
        (measure_ne_top_of_subset Set.sdiff_subset hΩfin) =
      -centeredIndicatorOn μ Ω E hΩ hΩfin hE hEfin := by
  have hcompfin : μ (Ω \ E) ≠ ⊤ := measure_ne_top_of_subset Set.sdiff_subset hΩfin
  have hmeasure : μ.real (Ω \ E) = μ.real Ω - μ.real E :=
    MeasureTheory.measureReal_sdiff hEΩ hE hΩfin
  have hratio : μ.real (Ω \ E) / μ.real Ω = 1 - μ.real E / μ.real Ω := by
    rw [hmeasure]
    field_simp [hΩpos.ne']
  have hindicator :
      indicatorConstLp 2 hΩ hΩfin (1 : ℝ) =
        indicatorConstLp 2 hE hEfin (1 : ℝ) +
          indicatorConstLp 2 (hΩ.diff hE) hcompfin (1 : ℝ) := by
    ext1
    grw [Lp.coeFn_add, indicatorConstLp_coeFn, indicatorConstLp_coeFn,
      indicatorConstLp_coeFn]
    conv_lhs => rw [← Set.union_sdiff_cancel hEΩ]
    rw [Set.indicator_union_of_disjoint Set.disjoint_sdiff_right]
    rfl
  rw [centeredIndicatorOn, centeredIndicatorOn, hratio, hindicator]
  module

/-- Symmetric-difference measure written through individual and intersection measures. -/
theorem measureReal_symmDiff_eq_sub_inter
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (E F : Set X)
    (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤)
    (hF : MeasurableSet F) (hFfin : μ F ≠ ⊤) :
    μ.real (E ∆ F) = μ.real E + μ.real F - 2 * μ.real (E ∩ F) := by
  rw [MeasureTheory.measureReal_symmDiff_eq hE hF hEfin hFfin]
  have hE_diff : E \ F = E \ (E ∩ F) := by ext x; simp
  have hF_diff : F \ E = F \ (F ∩ E) := by ext x; simp
  rw [hE_diff, hF_diff,
    MeasureTheory.measureReal_sdiff Set.inter_subset_left (hE.inter hF) hEfin,
    MeasureTheory.measureReal_sdiff Set.inter_subset_left (hF.inter hE) hFfin,
    Set.inter_comm E F]
  ring

/-- Exact squared distance in the constants quotient, expressed by symmetric difference. -/
theorem norm_sub_sq_centeredIndicatorOn
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (Ω E F : Set X)
    (hΩ : MeasurableSet Ω) (hΩfin : μ Ω ≠ ⊤)
    (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤)
    (hF : MeasurableSet F) (hFfin : μ F ≠ ⊤)
    (hEΩ : E ⊆ Ω) (hFΩ : F ⊆ Ω) (hΩpos : 0 < μ.real Ω) :
    ‖centeredIndicatorOn μ Ω E hΩ hΩfin hE hEfin -
        centeredIndicatorOn μ Ω F hΩ hΩfin hF hFfin‖ ^ 2 =
      μ.real (E ∆ F) - (μ.real E - μ.real F) ^ 2 / μ.real Ω := by
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq,
    real_inner_centeredIndicatorOn μ Ω E E hΩ hΩfin hE hEfin hE hEfin hEΩ hEΩ hΩpos,
    real_inner_centeredIndicatorOn μ Ω F F hΩ hΩfin hF hFfin hF hFfin hFΩ hFΩ hΩpos,
    real_inner_centeredIndicatorOn μ Ω E F hΩ hΩfin hE hEfin hF hFfin hEΩ hFΩ hΩpos,
    measureReal_symmDiff_eq_sub_inter μ E F hE hEfin hF hFfin]
  simp only [Set.inter_self]
  field_simp [hΩpos.ne']
  ring

/-- A centered-indicator difference is orthogonal to its aperture's constant direction. -/
theorem real_inner_centeredIndicatorOn_sub_indicatorOn_eq_zero
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (Ω E F : Set X)
    (hΩ : MeasurableSet Ω) (hΩfin : μ Ω ≠ ⊤)
    (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤)
    (hF : MeasurableSet F) (hFfin : μ F ≠ ⊤)
    (hEΩ : E ⊆ Ω) (hFΩ : F ⊆ Ω) (hΩpos : 0 < μ.real Ω) :
    inner ℝ (centeredIndicatorOn μ Ω E hΩ hΩfin hE hEfin -
      centeredIndicatorOn μ Ω F hΩ hΩfin hF hFfin)
      (indicatorConstLp 2 hΩ hΩfin (1 : ℝ)) = 0 := by
  simp only [centeredIndicatorOn, inner_sub_left,
    real_inner_smul_left,
    MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one,
    Set.inter_eq_left.mpr hEΩ, Set.inter_eq_left.mpr hFΩ, Set.inter_self]
  field_simp [hΩpos.ne']
  ring

/-- Decomposition of an indicator difference into its centered part and constant part. -/
theorem indicator_sub_indicator_sub_const_eq_centered_add
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (Ω E F : Set X)
    (hΩ : MeasurableSet Ω) (hΩfin : μ Ω ≠ ⊤)
    (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤)
    (hF : MeasurableSet F) (hFfin : μ F ≠ ⊤)
    (r : ℝ) :
    indicatorConstLp 2 hE hEfin (1 : ℝ) - indicatorConstLp 2 hF hFfin (1 : ℝ) -
      r • indicatorConstLp 2 hΩ hΩfin (1 : ℝ) =
    (centeredIndicatorOn μ Ω E hΩ hΩfin hE hEfin -
      centeredIndicatorOn μ Ω F hΩ hΩfin hF hFfin) +
      (μ.real E / μ.real Ω - μ.real F / μ.real Ω - r) •
        indicatorConstLp 2 hΩ hΩfin (1 : ℝ) := by
  rw [centeredIndicatorOn, centeredIndicatorOn]
  module

/-- Pythagorean square completion for distance from an indicator difference to a constant. -/
theorem norm_sq_indicator_sub_indicator_sub_const_eq
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (Ω E F : Set X)
    (hΩ : MeasurableSet Ω) (hΩfin : μ Ω ≠ ⊤)
    (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤)
    (hF : MeasurableSet F) (hFfin : μ F ≠ ⊤)
    (hEΩ : E ⊆ Ω) (hFΩ : F ⊆ Ω) (hΩpos : 0 < μ.real Ω)
    (r : ℝ) :
    ‖indicatorConstLp 2 hE hEfin (1 : ℝ) - indicatorConstLp 2 hF hFfin (1 : ℝ) -
        r • indicatorConstLp 2 hΩ hΩfin (1 : ℝ)‖ ^ 2 =
      ‖centeredIndicatorOn μ Ω E hΩ hΩfin hE hEfin -
          centeredIndicatorOn μ Ω F hΩ hΩfin hF hFfin‖ ^ 2 +
        μ.real Ω * (μ.real E / μ.real Ω - μ.real F / μ.real Ω - r) ^ 2 := by
  rw [indicator_sub_indicator_sub_const_eq_centered_add μ Ω E F hΩ hΩfin hE hEfin hF hFfin r,
    norm_add_sq_real]
  have horth := real_inner_centeredIndicatorOn_sub_indicatorOn_eq_zero μ Ω E F hΩ hΩfin
    hE hEfin hF hFfin hEΩ hFΩ hΩpos
  rw [real_inner_smul_right, horth, mul_zero]
  ring_nf
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hbase : ‖indicatorConstLp 2 hΩ hΩfin (1 : ℝ)‖ ^ 2 = μ.real Ω := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one,
      Set.inter_self]
  rw [hbase]
  ring

/-- Every constant shift of an indicator difference is at least as long as its centered part. -/
theorem norm_centeredIndicatorOn_sub_le_indicator_sub_indicator_sub_const
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (Ω E F : Set X)
    (hΩ : MeasurableSet Ω) (hΩfin : μ Ω ≠ ⊤)
    (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤)
    (hF : MeasurableSet F) (hFfin : μ F ≠ ⊤)
    (hEΩ : E ⊆ Ω) (hFΩ : F ⊆ Ω) (hΩpos : 0 < μ.real Ω)
    (r : ℝ) :
    ‖centeredIndicatorOn μ Ω E hΩ hΩfin hE hEfin -
        centeredIndicatorOn μ Ω F hΩ hΩfin hF hFfin‖ ≤
      ‖indicatorConstLp 2 hE hEfin (1 : ℝ) - indicatorConstLp 2 hF hFfin (1 : ℝ) -
        r • indicatorConstLp 2 hΩ hΩfin (1 : ℝ)‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  calc
    ‖centeredIndicatorOn μ Ω E hΩ hΩfin hE hEfin -
        centeredIndicatorOn μ Ω F hΩ hΩfin hF hFfin‖ *
        ‖centeredIndicatorOn μ Ω E hΩ hΩfin hE hEfin -
          centeredIndicatorOn μ Ω F hΩ hΩfin hF hFfin‖ =
        ‖centeredIndicatorOn μ Ω E hΩ hΩfin hE hEfin -
          centeredIndicatorOn μ Ω F hΩ hΩfin hF hFfin‖ ^ 2 := (pow_two _).symm
    _ ≤ ‖indicatorConstLp 2 hE hEfin (1 : ℝ) - indicatorConstLp 2 hF hFfin (1 : ℝ) -
          r • indicatorConstLp 2 hΩ hΩfin (1 : ℝ)‖ ^ 2 := by
      rw [norm_sq_indicator_sub_indicator_sub_const_eq μ Ω E F hΩ hΩfin hE hEfin hF hFfin
        hEΩ hFΩ hΩpos r]
      exact le_add_of_nonneg_right <| mul_nonneg measureReal_nonneg (sq_nonneg _)
    _ = ‖indicatorConstLp 2 hE hEfin (1 : ℝ) - indicatorConstLp 2 hF hFfin (1 : ℝ) -
          r • indicatorConstLp 2 hΩ hΩfin (1 : ℝ)‖ *
        ‖indicatorConstLp 2 hE hEfin (1 : ℝ) - indicatorConstLp 2 hF hFfin (1 : ℝ) -
          r • indicatorConstLp 2 hΩ hΩfin (1 : ℝ)‖ := pow_two _

/-- The constant selected by mean subtraction attains the quotient distance. -/
theorem norm_indicator_sub_indicator_sub_nearest_const_eq_centered
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (Ω E F : Set X)
    (hΩ : MeasurableSet Ω) (hΩfin : μ Ω ≠ ⊤)
    (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤)
    (hF : MeasurableSet F) (hFfin : μ F ≠ ⊤)
    (hEΩ : E ⊆ Ω) (hFΩ : F ⊆ Ω) (hΩpos : 0 < μ.real Ω) :
    ‖indicatorConstLp 2 hE hEfin (1 : ℝ) - indicatorConstLp 2 hF hFfin (1 : ℝ) -
        ((μ.real E - μ.real F) / μ.real Ω) • indicatorConstLp 2 hΩ hΩfin (1 : ℝ)‖ =
      ‖centeredIndicatorOn μ Ω E hΩ hΩfin hE hEfin -
        centeredIndicatorOn μ Ω F hΩ hΩfin hF hFfin‖ := by
  have hzero : μ.real E / μ.real Ω - μ.real F / μ.real Ω -
      (μ.real E - μ.real F) / μ.real Ω = 0 := by
    field_simp [hΩpos.ne']
    ring
  have hsq : ‖indicatorConstLp 2 hE hEfin (1 : ℝ) - indicatorConstLp 2 hF hFfin (1 : ℝ) -
      ((μ.real E - μ.real F) / μ.real Ω) • indicatorConstLp 2 hΩ hΩfin (1 : ℝ)‖ ^ 2 =
      ‖centeredIndicatorOn μ Ω E hΩ hΩfin hE hEfin -
        centeredIndicatorOn μ Ω F hΩ hΩfin hF hFfin‖ ^ 2 := by
    rw [norm_sq_indicator_sub_indicator_sub_const_eq μ Ω E F hΩ hΩfin hE hEfin hF hFfin
      hEΩ hFΩ hΩpos, hzero]
    ring
  nlinarith [norm_nonneg (indicatorConstLp 2 hE hEfin (1 : ℝ) -
      indicatorConstLp 2 hF hFfin (1 : ℝ) -
      ((μ.real E - μ.real F) / μ.real Ω) • indicatorConstLp 2 hΩ hΩfin (1 : ℝ)),
    norm_nonneg (centeredIndicatorOn μ Ω E hΩ hΩfin hE hEfin -
      centeredIndicatorOn μ Ω F hΩ hΩfin hF hFfin)]

/-- Exact quotient metric: centered-indicator distance is the infimum over constant shifts. -/
theorem iInf_norm_indicator_sub_indicator_sub_const_eq_centered
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (Ω E F : Set X)
    (hΩ : MeasurableSet Ω) (hΩfin : μ Ω ≠ ⊤)
    (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤)
    (hF : MeasurableSet F) (hFfin : μ F ≠ ⊤)
    (hEΩ : E ⊆ Ω) (hFΩ : F ⊆ Ω) (hΩpos : 0 < μ.real Ω) :
    (⨅ r : ℝ, ‖indicatorConstLp 2 hE hEfin (1 : ℝ) - indicatorConstLp 2 hF hFfin (1 : ℝ) -
      r • indicatorConstLp 2 hΩ hΩfin (1 : ℝ)‖) =
      ‖centeredIndicatorOn μ Ω E hΩ hΩfin hE hEfin -
        centeredIndicatorOn μ Ω F hΩ hΩfin hF hFfin‖ := by
  let f : ℝ → ℝ := fun r =>
    ‖indicatorConstLp 2 hE hEfin (1 : ℝ) - indicatorConstLp 2 hF hFfin (1 : ℝ) -
      r • indicatorConstLp 2 hΩ hΩfin (1 : ℝ)‖
  change iInf f = _
  have hbelow : BddBelow (Set.range f) :=
    ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩
  apply le_antisymm
  · calc
      iInf f ≤ f ((μ.real E - μ.real F) / μ.real Ω) := ciInf_le hbelow _
      _ = ‖centeredIndicatorOn μ Ω E hΩ hΩfin hE hEfin -
          centeredIndicatorOn μ Ω F hΩ hΩfin hF hFfin‖ := by
        exact norm_indicator_sub_indicator_sub_nearest_const_eq_centered μ Ω E F hΩ hΩfin
          hE hEfin hF hFfin hEΩ hFΩ hΩpos
  · apply le_ciInf
    intro r
    exact norm_centeredIndicatorOn_sub_le_indicator_sub_indicator_sub_const μ Ω E F hΩ hΩfin
      hE hEfin hF hFfin hEΩ hFΩ hΩpos r

end
end GaloisForLFunctions.HTGeometry

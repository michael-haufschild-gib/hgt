import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.MeasuredSets

/-!
# Density of separated products in product `L²`

This module proves, for sigma-finite measures, that algebraic tensors of `L²` functions map
to a dense subspace of the product `L²` space.  The proof is unconditional: finite-measure
rectangles form a generating semiring, their finite disjoint unions approximate measurable
sets in symmetric difference, and `Lp.induction` upgrades indicator approximation to density.
It also shows that any two dense factor maps have dense separated-product tensor image.
-/

namespace MeasureTheory

noncomputable section

open Topology
open scoped ENNReal symmDiff TensorProduct

variable {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [SigmaFinite μ] [SigmaFinite ν]

def l2SeparatedFun
    (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    α × β → ℂ :=
  fun z => f z.1 * g z.2

omit [SigmaFinite μ] [SigmaFinite ν] in
theorem l2SeparatedFun_aestronglyMeasurable
    (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    AEStronglyMeasurable (l2SeparatedFun f g) (μ.prod ν) := by
  exact
    ((Lp.aestronglyMeasurable f).aemeasurable.comp_fst.mul
      (Lp.aestronglyMeasurable g).aemeasurable.comp_snd).aestronglyMeasurable

omit [SigmaFinite μ] [SigmaFinite ν] in
theorem l2SeparatedFun_memLp
    (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    MemLp (l2SeparatedFun f g) 2 (μ.prod ν) := by
  apply
    (memLp_two_iff_integrable_sq_norm
      (l2SeparatedFun_aestronglyMeasurable f g)).2
  have hf :
      Integrable (fun x : α => ‖f x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm
      (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)
  have hg :
      Integrable (fun y : β => ‖g y‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm
      (Lp.aestronglyMeasurable g)).1 (Lp.memLp g)
  simpa only [l2SeparatedFun, norm_mul, mul_pow] using
    hf.mul_prod hg

def l2SeparatedProduct
    (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    Lp ℂ 2 (μ.prod ν) :=
  (l2SeparatedFun_memLp f g).toLp
    (l2SeparatedFun f g)

omit [SigmaFinite μ] [SigmaFinite ν] in
theorem l2SeparatedProduct_ae
    (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    l2SeparatedProduct f g
      =ᵐ[μ.prod ν] l2SeparatedFun f g :=
  (l2SeparatedFun_memLp f g).coeFn_toLp

omit [SigmaFinite μ] in
theorem l2SeparatedFun_eLpNorm
    (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    eLpNorm (l2SeparatedFun f g) 2 (μ.prod ν) =
      eLpNorm f 2 μ * eLpNorm g 2 ν := by
  apply ENNReal.rpow_left_injective
    (by norm_num : (2 : ℝ) ≠ 0)
  change
    eLpNorm (l2SeparatedFun f g) 2 (μ.prod ν) ^ (2 : ℝ) =
      (eLpNorm f 2 μ * eLpNorm g 2 ν) ^ (2 : ℝ)
  simp_rw [
    ENNReal.mul_rpow_of_nonneg _ _
      (by norm_num : (0 : ℝ) ≤ 2)]
  simp_rw [
    eLpNorm_eq_eLpNorm'
      two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofNat]
  rw [
    ← lintegral_rpow_enorm_eq_rpow_eLpNorm'
      (μ := μ.prod ν) (q := 2) (by norm_num)]
  simp only [l2SeparatedFun, enorm_mul]
  simp_rw [
    ENNReal.mul_rpow_of_nonneg _ _
      (by norm_num : (0 : ℝ) ≤ 2)]
  have hfmeas :
      AEMeasurable (fun x : α => ‖f x‖ₑ ^ (2 : ℝ)) μ := by
    fun_prop
  have hgmeas :
      AEMeasurable (fun y : β => ‖g y‖ₑ ^ (2 : ℝ)) ν := by
    fun_prop
  rw [lintegral_prod_mul hfmeas hgmeas]
  rw [
    lintegral_rpow_enorm_eq_rpow_eLpNorm'
      (μ := μ) (q := 2) (by norm_num),
    lintegral_rpow_enorm_eq_rpow_eLpNorm'
      (μ := ν) (q := 2) (by norm_num)]

omit [SigmaFinite μ] in
theorem l2SeparatedProduct_norm
    (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    ‖l2SeparatedProduct f g‖ = ‖f‖ * ‖g‖ := by
  rw [l2SeparatedProduct, Lp.norm_toLp,
    l2SeparatedFun_eLpNorm, ENNReal.toReal_mul,
    ← Lp.norm_def, ← Lp.norm_def]

def l2SeparatedProductBilinear :
    Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 ν →ₗ[ℂ]
      Lp ℂ 2 (μ.prod ν) :=
  LinearMap.mk₂ ℂ l2SeparatedProduct
    (fun f f' g => by
      apply Lp.ext
      filter_upwards [
        l2SeparatedProduct_ae (f + f') g,
        Lp.coeFn_add
          (l2SeparatedProduct f g)
          (l2SeparatedProduct f' g),
        l2SeparatedProduct_ae f g,
        l2SeparatedProduct_ae f' g,
        Measure.quasiMeasurePreserving_fst.ae_eq_comp
          (Lp.coeFn_add f f')]
        with z hsum hadd hf hf' hfactor
      rw [hsum, hadd]
      simp only [Pi.add_apply]
      rw [hf, hf']
      simp only [Function.comp_apply, Pi.add_apply] at hfactor
      simp only [l2SeparatedFun]
      rw [hfactor]
      ring)
    (fun c f g => by
      apply Lp.ext
      filter_upwards [
        l2SeparatedProduct_ae (c • f) g,
        Lp.coeFn_smul c (l2SeparatedProduct f g),
        l2SeparatedProduct_ae f g,
        Measure.quasiMeasurePreserving_fst.ae_eq_comp
          (Lp.coeFn_smul c f)]
        with z hleft hsmul hf hfactor
      rw [hleft, hsmul]
      simp only [Pi.smul_apply]
      rw [hf]
      simp only [Function.comp_apply, Pi.smul_apply] at hfactor
      simp only [l2SeparatedFun]
      rw [hfactor]
      simp only [smul_eq_mul]
      ring_nf)
    (fun f g g' => by
      apply Lp.ext
      filter_upwards [
        l2SeparatedProduct_ae f (g + g'),
        Lp.coeFn_add
          (l2SeparatedProduct f g)
          (l2SeparatedProduct f g'),
        l2SeparatedProduct_ae f g,
        l2SeparatedProduct_ae f g',
        Measure.quasiMeasurePreserving_snd.ae_eq_comp
          (Lp.coeFn_add g g')]
        with z hsum hadd hg hg' hfactor
      rw [hsum, hadd]
      simp only [Pi.add_apply]
      rw [hg, hg']
      simp only [Function.comp_apply, Pi.add_apply] at hfactor
      simp only [l2SeparatedFun]
      rw [hfactor]
      ring)
    (fun c f g => by
      apply Lp.ext
      filter_upwards [
        l2SeparatedProduct_ae f (c • g),
        Lp.coeFn_smul c (l2SeparatedProduct f g),
        l2SeparatedProduct_ae f g,
        Measure.quasiMeasurePreserving_snd.ae_eq_comp
          (Lp.coeFn_smul c g)]
        with z hleft hsmul hg hfactor
      rw [hleft, hsmul]
      simp only [Pi.smul_apply]
      rw [hg]
      simp only [Function.comp_apply, Pi.smul_apply] at hfactor
      simp only [l2SeparatedFun]
      rw [hfactor]
      simp only [smul_eq_mul]
      ring_nf)

def l2SeparatedProductContinuousBilinear :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν →L[ℂ]
      Lp ℂ 2 (μ.prod ν) :=
  l2SeparatedProductBilinear.mkContinuous₂ 1
    (fun f g => by
      change
        ‖l2SeparatedProduct f g‖ ≤
          1 * ‖f‖ * ‖g‖
      rw [l2SeparatedProduct_norm]
      simp)

omit [SigmaFinite μ] in
@[simp]
theorem l2SeparatedProductContinuousBilinear_apply
    (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    l2SeparatedProductContinuousBilinear f g =
      l2SeparatedProduct f g :=
  rfl

def l2TensorToProduct :
    (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) →ₗ[ℂ]
      Lp ℂ 2 (μ.prod ν) :=
  TensorProduct.lift l2SeparatedProductBilinear

omit [SigmaFinite μ] [SigmaFinite ν] in
@[simp]
theorem l2TensorToProduct_tmul
    (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    l2TensorToProduct (f ⊗ₜ[ℂ] g) =
      l2SeparatedProduct f g :=
  rfl

omit [SigmaFinite μ] in
theorem l2SeparatedProduct_indicatorConstLp
    {A : Set α} (hA : MeasurableSet A) (hμA : μ A ≠ ∞)
    {B : Set β} (hB : MeasurableSet B) (hνB : ν B ≠ ∞)
    (c : ℂ) :
    l2SeparatedProduct
        (indicatorConstLp 2 hA hμA c)
        (indicatorConstLp 2 hB hνB (1 : ℂ)) =
      indicatorConstLp 2 (hA.prod hB)
        (by
          rw [Measure.prod_prod]
          exact
            (ENNReal.mul_lt_top
              (lt_top_iff_ne_top.2 hμA)
              (lt_top_iff_ne_top.2 hνB)).ne)
        c := by
  apply Lp.ext
  filter_upwards [
    l2SeparatedProduct_ae
      (indicatorConstLp 2 hA hμA c)
      (indicatorConstLp 2 hB hνB (1 : ℂ)),
    indicatorConstLp_coeFn
      (p := 2) (μ := μ.prod ν)
      (hs := hA.prod hB)
      (hμs := by
        rw [Measure.prod_prod]
        exact
          (ENNReal.mul_lt_top
            (lt_top_iff_ne_top.2 hμA)
            (lt_top_iff_ne_top.2 hνB)).ne)
      (c := c),
    Measure.quasiMeasurePreserving_fst.ae_eq_comp
      (indicatorConstLp_coeFn
        (p := 2) (μ := μ) (hs := hA)
        (hμs := hμA) (c := c)),
    Measure.quasiMeasurePreserving_snd.ae_eq_comp
      (indicatorConstLp_coeFn
        (p := 2) (μ := ν) (hs := hB)
        (hμs := hνB) (c := (1 : ℂ)))]
      with z hleft hright hfirst hsecond
  rw [hleft, hright]
  simp only [Function.comp_apply] at hfirst hsecond
  simp only [l2SeparatedFun]
  rw [hfirst, hsecond]
  by_cases hzA : z.1 ∈ A <;>
    by_cases hzB : z.2 ∈ B <;>
      simp [hzA, hzB]

def measurableRectangles :
    Set (Set (α × β)) :=
  Set.image2 (· ×ˢ ·)
    {s : Set α | MeasurableSet s}
    {t : Set β | MeasurableSet t}

theorem measurableSets_isSetRing
    (γ : Type*) [MeasurableSpace γ] :
    IsSetRing {s : Set γ | MeasurableSet s} where
  empty_mem := MeasurableSet.empty
  union_mem := fun _ _ hs ht => hs.union ht
  sdiff_mem := fun _ _ hs ht => hs.diff ht

omit [MeasurableSpace α] [MeasurableSpace β] in
theorem setRingRectangles_isSetSemiring
    {C : Set (Set α)} {D : Set (Set β)}
    (hCr : IsSetRing C) (hDr : IsSetRing D) :
    IsSetSemiring (Set.image2 (· ×ˢ ·) C D) where
  empty_mem := by
    exact
      ⟨∅, hCr.empty_mem, ∅, hDr.empty_mem, by simp⟩
  inter_mem := by
    rintro _ ⟨A, hA, B, hB, rfl⟩
      _ ⟨C, hC, D, hD, rfl⟩
    refine
      ⟨A ∩ C, hCr.inter_mem hA hC,
        B ∩ D, hDr.inter_mem hB hD, ?_⟩
    ext z
    simp only [Set.mem_inter_iff, Set.mem_prod, and_and_and_comm]
  sdiff_eq_sUnion' := by
    classical
    rintro _ ⟨A, hA, B, hB, rfl⟩
      _ ⟨C, hC, D, hD, rfl⟩
    let R₁ := (A \ C) ×ˢ B
    let R₂ := (A ∩ C) ×ˢ (B \ D)
    refine ⟨{R₁, R₂}, ?_, ?_, ?_⟩
    · intro R hR
      simp only [Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff] at hR
      rcases hR with rfl | rfl
      · exact
          ⟨A \ C, hCr.sdiff_mem hA hC,
            B, hB, rfl⟩
      · exact
          ⟨A ∩ C, hCr.inter_mem hA hC,
            B \ D, hDr.sdiff_mem hB hD, rfl⟩
    · intro R hR S hS hRS
      simp only [Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff] at hR hS
      rcases hR with rfl | rfl <;>
        rcases hS with rfl | rfl
      · exact (hRS rfl).elim
      · simp only [Function.onFun, R₁, R₂]
        exact Set.disjoint_left.2 fun z hz₁ hz₂ =>
          hz₁.1.2 hz₂.1.2
      · simp only [Function.onFun, R₁, R₂]
        exact Set.disjoint_left.2 fun z hz₁ hz₂ =>
          hz₂.1.2 hz₁.1.2
      · exact (hRS rfl).elim
    · simp only [Finset.coe_insert, Finset.coe_singleton,
        Set.sUnion_insert, Set.sUnion_singleton, R₁, R₂]
      ext z
      simp only [Set.mem_sdiff, Set.mem_prod, Set.mem_union,
        Set.mem_inter_iff]
      tauto

theorem measurableRectangles_isSetSemiring :
    IsSetSemiring
      (measurableRectangles (α := α) (β := β)) :=
  setRingRectangles_isSetSemiring
    (measurableSets_isSetRing α)
    (measurableSets_isSetRing β)

def finiteMeasurableSets
    {γ : Type*} [MeasurableSpace γ]
    (ρ : Measure γ) :
    Set (Set γ) :=
  {s : Set γ | MeasurableSet s ∧ ρ s ≠ ∞}

theorem finiteMeasurableSets_isSetRing
    {γ : Type*} [MeasurableSpace γ]
    (ρ : Measure γ) :
    IsSetRing (finiteMeasurableSets ρ) where
  empty_mem := by
    simp [finiteMeasurableSets]
  union_mem := by
    rintro s t ⟨hs, hρs⟩ ⟨ht, hρt⟩
    refine ⟨hs.union ht, ?_⟩
    exact
      ((measure_union_le s t).trans_lt
        (ENNReal.add_lt_top.2
          ⟨lt_top_iff_ne_top.2 hρs,
            lt_top_iff_ne_top.2 hρt⟩)).ne
  sdiff_mem := by
    rintro s t ⟨hs, hρs⟩ ⟨ht, hρt⟩
    refine ⟨hs.diff ht, ?_⟩
    exact
      ((measure_mono Set.sdiff_subset).trans_lt
        (lt_top_iff_ne_top.2 hρs)).ne

def finiteMeasureRectangles :
    Set (Set (α × β)) :=
  Set.image2 (· ×ˢ ·)
    (finiteMeasurableSets μ)
    (finiteMeasurableSets ν)

omit [SigmaFinite μ] [SigmaFinite ν] in
theorem finiteMeasureRectangles_isSetSemiring :
    IsSetSemiring
      (finiteMeasureRectangles
        (α := α) (β := β) (μ := μ) (ν := ν)) :=
  setRingRectangles_isSetSemiring
    (finiteMeasurableSets_isSetRing μ)
    (finiteMeasurableSets_isSetRing ν)

theorem finiteMeasurableSets_isCountablySpanning
    {γ : Type*} [MeasurableSpace γ]
    (ρ : Measure γ) [SigmaFinite ρ] :
    IsCountablySpanning (finiteMeasurableSets ρ) :=
  ⟨spanningSets ρ,
    fun n =>
      ⟨measurableSet_spanningSets ρ n,
        (measure_spanningSets_lt_top ρ n).ne⟩,
    iUnion_spanningSets ρ⟩

theorem generateFrom_finiteMeasurableSets
    {γ : Type*} [mγ : MeasurableSpace γ]
    (ρ : Measure γ) [SigmaFinite ρ] :
    MeasurableSpace.generateFrom
        (finiteMeasurableSets ρ) =
      mγ := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    exact hs.1
  · intro s hs
    rw [← Set.inter_univ s, ← iUnion_spanningSets ρ,
      Set.inter_iUnion]
    apply MeasurableSet.iUnion
    intro n
    apply MeasurableSpace.measurableSet_generateFrom
    exact
      ⟨hs.inter (measurableSet_spanningSets ρ n),
        ((measure_mono Set.inter_subset_right).trans_lt
          (measure_spanningSets_lt_top ρ n)).ne⟩

theorem generateFrom_finiteMeasureRectangles :
    MeasurableSpace.generateFrom
        (finiteMeasureRectangles
          (α := α) (β := β) (μ := μ) (ν := ν)) =
      Prod.instMeasurableSpace := by
  exact
    generateFrom_eq_prod
      (generateFrom_finiteMeasurableSets μ)
      (generateFrom_finiteMeasurableSets ν)
      (finiteMeasurableSets_isCountablySpanning μ)
      (finiteMeasurableSets_isCountablySpanning ν)

theorem exists_supClosure_finiteMeasureRectangles_symmDiff_lt
    {s : Set (α × β)}
    (hs : MeasurableSet s)
    (hρs : (μ.prod ν) s ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ t ∈
        supClosure
          (finiteMeasureRectangles
            (α := α) (β := β) (μ := μ) (ν := ν)),
      (μ.prod ν) (t ∆ s) < ε := by
  let R : ℕ → Set (α × β) :=
    fun n => spanningSets μ n ×ˢ spanningSets ν n
  have hRmeas (n : ℕ) : MeasurableSet (R n) :=
    (measurableSet_spanningSets μ n).prod
      (measurableSet_spanningSets ν n)
  have hRfinite (n : ℕ) : (μ.prod ν) (R n) ≠ ∞ := by
    change
      (μ.prod ν)
          (spanningSets μ n ×ˢ spanningSets ν n) ≠ ∞
    rw [Measure.prod_prod]
    exact
      (ENNReal.mul_lt_top
        (measure_spanningSets_lt_top μ n)
        (measure_spanningSets_lt_top ν n)).ne
  have hRmono : Monotone R := by
    intro m n hmn
    exact Set.prod_mono
      (spanningSets_mono hmn)
      (spanningSets_mono hmn)
  have hRunion : ⋃ n, R n = Set.univ := by
    ext z
    constructor
    · exact fun _ => Set.mem_univ z
    · intro _
      rcases Set.mem_iUnion.1
          (show z.1 ∈ ⋃ n, spanningSets μ n by
            rw [iUnion_spanningSets μ]
            exact Set.mem_univ z.1) with
        ⟨m, hm⟩
      rcases Set.mem_iUnion.1
          (show z.2 ∈ ⋃ n, spanningSets ν n by
            rw [iUnion_spanningSets ν]
            exact Set.mem_univ z.2) with
        ⟨n, hn⟩
      refine Set.mem_iUnion.2 ⟨max m n, ?_⟩
      exact
        ⟨spanningSets_mono (Nat.le_max_left _ _) hm,
          spanningSets_mono (Nat.le_max_right _ _) hn⟩
  have hinter : ⋂ n, s \ R n = ∅ := by
    apply Set.Subset.antisymm
    · intro z hz
      have hzall := Set.mem_iInter.1 hz
      have hzunion : z ∈ ⋃ n, R n := by
        rw [hRunion]
        exact Set.mem_univ z
      rcases Set.mem_iUnion.1 hzunion with ⟨n, hzn⟩
      exact ((hzall n).2 hzn).elim
    · exact Set.empty_subset _
  have htailTendsto :
      Filter.Tendsto
        ((μ.prod ν) ∘ fun n => s \ R n)
        Filter.atTop (𝓝 0) := by
    have h :=
      tendsto_measure_iInter_atTop
        (μ := μ.prod ν)
        (s := fun n => s \ R n)
        (fun n => (hs.diff (hRmeas n)).nullMeasurableSet)
        (fun m n hmn =>
          Set.sdiff_subset_sdiff_right (hRmono hmn))
        ⟨0,
          ((measure_mono Set.sdiff_subset).trans_lt
            (lt_top_iff_ne_top.2 hρs)).ne⟩
    simpa only [hinter, measure_empty] using h
  obtain ⟨n, htail⟩ :
      ∃ n, (μ.prod ν) (s \ R n) < ε / 2 :=
    ((tendsto_order.1 htailTendsto).2
      (ε / 2) (ENNReal.half_pos hε)).exists
  let ρ : Measure (α × β) := (μ.prod ν).restrict (R n)
  letI : IsFiniteMeasure ρ :=
    ⟨by
      change
        ((μ.prod ν).restrict (R n)) Set.univ < ∞
      rw [Measure.restrict_apply_univ]
      exact lt_top_iff_ne_top.2 (hRfinite n)⟩
  have hRC :
      R n ∈
        finiteMeasureRectangles
          (α := α) (β := β) (μ := μ) (ν := ν) := by
    exact
      ⟨spanningSets μ n,
        ⟨measurableSet_spanningSets μ n,
          (measure_spanningSets_lt_top μ n).ne⟩,
        spanningSets ν n,
        ⟨measurableSet_spanningSets ν n,
          (measure_spanningSets_lt_top ν n).ne⟩,
        rfl⟩
  have hcover :
      ∃ D : Set (Set (α × β)),
        D.Countable ∧
          D ⊆
            finiteMeasureRectangles
              (α := α) (β := β) (μ := μ) (ν := ν) ∧
          ρ (⋃₀ D)ᶜ = 0 := by
    refine ⟨{R n}, Set.countable_singleton _, ?_, ?_⟩
    · simpa only [Set.singleton_subset_iff] using hRC
    · rw [Set.sUnion_singleton]
      change
        ((μ.prod ν).restrict (R n)) (R n)ᶜ = 0
      rw [Measure.restrict_apply' (hRmeas n)]
      simp
  have hhalf : 0 < ε / 2 := ENNReal.half_pos hε
  rcases
      exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring
        (μ := ρ)
        finiteMeasureRectangles_isSetSemiring
        hcover
        generateFrom_finiteMeasureRectangles.symm
        (hs.inter (hRmeas n)) hhalf with
    ⟨t, htC, ht⟩
  let u := t ∩ R n
  have huC :
      u ∈
        supClosure
          (finiteMeasureRectangles
            (α := α) (β := β) (μ := μ) (ν := ν)) := by
    exact
      finiteMeasureRectangles_isSetSemiring.isSetRing_supClosure.inter_mem
        htC (subset_supClosure hRC)
  have hlocal :
      (μ.prod ν) (u ∆ (s ∩ R n)) < ε / 2 := by
    have hset :
        u ∆ (s ∩ R n) =
          (t ∆ (s ∩ R n)) ∩ R n := by
      ext z
      simp only [u, Set.mem_symmDiff, Set.mem_inter_iff]
      tauto
    rw [hset, ← Measure.restrict_apply' (hRmeas n)]
    exact ht
  refine ⟨u, huC, ?_⟩
  calc
    (μ.prod ν) (u ∆ s) ≤
        (μ.prod ν)
          ((u ∆ (s ∩ R n)) ∪ (s \ R n)) := by
      apply measure_mono
      intro z hz
      simp only [u, Set.mem_symmDiff, Set.mem_inter_iff,
        Set.mem_union, Set.mem_sdiff] at hz ⊢
      tauto
    _ ≤
        (μ.prod ν) (u ∆ (s ∩ R n)) +
          (μ.prod ν) (s \ R n) :=
      measure_union_le _ _
    _ < ε / 2 + ε / 2 :=
      ENNReal.add_lt_add hlocal htail
    _ = ε := ENNReal.add_halves ε

omit [SigmaFinite μ] in
theorem supClosure_finiteMeasureRectangles_measurable_finite
    {t : Set (α × β)}
    (ht :
      t ∈
        supClosure
          (finiteMeasureRectangles
            (α := α) (β := β) (μ := μ) (ν := ν))) :
    MeasurableSet t ∧ (μ.prod ν) t ≠ ∞ := by
  rcases
      finiteMeasureRectangles_isSetSemiring.mem_supClosure_iff.1 ht with
    ⟨P, hP⟩
  have hpart :
      ∀ q ∈ P.parts,
        MeasurableSet q ∧ (μ.prod ν) q < ∞ := by
    intro q hq
    rcases hP hq with
      ⟨A, ⟨hA, hμA⟩, B, ⟨hB, hνB⟩, rfl⟩
    refine ⟨hA.prod hB, ?_⟩
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top
      (lt_top_iff_ne_top.2 hμA)
      (lt_top_iff_ne_top.2 hνB)
  have hparts : ⋃₀ (P.parts : Set (Set (α × β))) = t := by
    calc
      ⋃₀ (P.parts : Set (Set (α × β))) =
          P.parts.sup id :=
        (Finset.sup_id_set_eq_sUnion P.parts).symm
      _ = t := P.sup_parts
  constructor
  · rw [← hparts]
    exact
      P.parts.finite_toSet.measurableSet_sUnion
        (fun q hq => (hpart q hq).1)
  · rw [← hparts]
    have hlt :
        (μ.prod ν)
            (⋃ q ∈ (P.parts : Set (Set (α × β))), q) < ∞ :=
      measure_biUnion_lt_top
        P.parts.finite_toSet
        (fun q hq => (hpart q hq).2)
    simpa only [Set.sUnion_eq_biUnion] using hlt.ne

omit [SigmaFinite μ] in
theorem indicatorConstLp_supClosure_mem_tensorRange
    {t : Set (α × β)}
    (ht :
      t ∈
        supClosure
          (finiteMeasureRectangles
            (α := α) (β := β) (μ := μ) (ν := ν)))
    (c : ℂ) :
    indicatorConstLp 2
        (supClosure_finiteMeasureRectangles_measurable_finite
          ht).1
        (supClosure_finiteMeasureRectangles_measurable_finite
          ht).2 c ∈
      LinearMap.range
        (l2TensorToProduct
          (α := α) (β := β) (μ := μ) (ν := ν)) := by
  let S :
      Submodule ℂ (Lp ℂ 2 (μ.prod ν)) :=
    LinearMap.range
      (l2TensorToProduct
        (α := α) (β := β) (μ := μ) (ν := ν))
  rcases
      finiteMeasureRectangles_isSetSemiring.mem_supClosure_iff.1 ht with
    ⟨P, hP⟩
  have hpartMeas :
      ∀ q ∈ P.parts, MeasurableSet q := by
    intro q hq
    rcases hP hq with
      ⟨A, ⟨hA, hμA⟩, B, ⟨hB, hνB⟩, rfl⟩
    exact hA.prod hB
  have hpartFinite :
      ∀ q ∈ P.parts, (μ.prod ν) q ≠ ∞ := by
    intro q hq
    rcases hP hq with
      ⟨A, ⟨hA, hμA⟩, B, ⟨hB, hνB⟩, rfl⟩
    rw [Measure.prod_prod]
    exact
      (ENNReal.mul_lt_top
        (lt_top_iff_ne_top.2 hμA)
        (lt_top_iff_ne_top.2 hνB)).ne
  have hpartRange (q : Set (α × β)) (hq : q ∈ P.parts) :
      indicatorConstLp 2
          (hpartMeas q hq)
          (hpartFinite q hq) c ∈ S := by
    rcases hP hq with
      ⟨A, ⟨hA, hμA⟩, B, ⟨hB, hνB⟩, rfl⟩
    refine
      ⟨indicatorConstLp 2 hA hμA c ⊗ₜ[ℂ]
          indicatorConstLp 2 hB hνB (1 : ℂ), ?_⟩
    rw [l2TensorToProduct_tmul]
    exact l2SeparatedProduct_indicatorConstLp
      hA hμA hB hνB c
  have hfiniteUnion :
      ∀ Q : Finset (Set (α × β)), Q ⊆ P.parts →
        ∃ hQmeas :
            MeasurableSet (⋃₀ (Q : Set (Set (α × β)))),
          ∃ hQfinite :
              (μ.prod ν) (⋃₀ (Q : Set (Set (α × β)))) ≠ ∞,
            indicatorConstLp 2 hQmeas hQfinite c ∈ S := by
    intro Q hQP
    induction Q using Finset.induction with
    | empty =>
        refine
          ⟨by simp, by simp, ?_⟩
        simp
    | @insert q Q hq ih =>
        have hqP : q ∈ P.parts :=
          hQP (Finset.mem_insert_self q Q)
        have hQP' : Q ⊆ P.parts := by
          intro r hr
          exact hQP (Finset.mem_insert_of_mem hr)
        rcases ih hQP' with
          ⟨hQmeas, hQfinite, hQmem⟩
        have hqmeas := hpartMeas q hqP
        have hqfinite := hpartFinite q hqP
        have hdisj :
            Disjoint q (⋃₀ (Q : Set (Set (α × β)))) := by
          rw [Set.disjoint_sUnion_right]
          intro r hr
          exact P.disjoint hqP (hQP' hr) (by
            intro hqr
            subst r
            exact hq hr)
        have hUnionMeas :
            MeasurableSet
              (q ∪ ⋃₀ (Q : Set (Set (α × β)))) :=
          hqmeas.union hQmeas
        have hUnionFinite :
            (μ.prod ν)
                (q ∪ ⋃₀ (Q : Set (Set (α × β)))) ≠ ∞ := by
          exact
            ((measure_union_le q
                (⋃₀ (Q : Set (Set (α × β))))).trans_lt
              (ENNReal.add_lt_top.2
                ⟨lt_top_iff_ne_top.2 hqfinite,
                  lt_top_iff_ne_top.2 hQfinite⟩)).ne
        refine
          ⟨by
            simpa only [Finset.coe_insert,
              Set.sUnion_insert] using hUnionMeas,
            by
              simpa only [Finset.coe_insert,
                Set.sUnion_insert] using hUnionFinite,
            ?_⟩
        have hmemUnion :
            indicatorConstLp 2 hUnionMeas hUnionFinite c ∈ S := by
          rw [indicatorConstLp_disjoint_union
            hqmeas hQmeas hqfinite hQfinite hdisj c]
          exact S.add_mem (hpartRange q hqP) hQmem
        simpa only [Finset.coe_insert,
          Set.sUnion_insert] using hmemUnion
  rcases hfiniteUnion P.parts (fun _ h => h) with
    ⟨hAllMeas, hAllFinite, hAllMem⟩
  have hparts :
      ⋃₀ (P.parts : Set (Set (α × β))) = t := by
    calc
      ⋃₀ (P.parts : Set (Set (α × β))) =
          P.parts.sup id :=
        (Finset.sup_id_set_eq_sUnion P.parts).symm
      _ = t := P.sup_parts
  simpa only [S, hparts] using hAllMem

theorem indicatorConstLp_mem_tensorClosure
    (c : ℂ) {s : Set (α × β)}
    (hs : MeasurableSet s)
    (hρs : (μ.prod ν) s ≠ ∞) :
    indicatorConstLp 2 hs hρs c ∈
      (LinearMap.range
        (l2TensorToProduct
          (α := α) (β := β) (μ := μ) (ν := ν))).topologicalClosure := by
  change
    indicatorConstLp 2 hs hρs c ∈
      ((LinearMap.range
        (l2TensorToProduct
          (α := α) (β := β) (μ := μ) (ν := ν))).topologicalClosure :
        Set (Lp ℂ 2 (μ.prod ν)))
  rw [Submodule.topologicalClosure_coe]
  apply EMetric.mem_closure_iff.2
  intro ε hε
  by_cases hεtop : ε = ∞
  · refine ⟨0, SetLike.coe_mem 0, ?_⟩
    rw [hεtop]
    exact edist_lt_top _ _
  have hhalf : ε / 2 ≠ 0 :=
    (ENNReal.half_pos hε.ne').ne'
  obtain ⟨η, hηpos, hηbound⟩ :=
    exists_eLpNorm_indicator_le
      (α := α × β) (E := ℂ)
      (p := 2) (μ := μ.prod ν)
      (by norm_num) c hhalf
  rcases
      exists_supClosure_finiteMeasureRectangles_symmDiff_lt
        hs hρs (ε := (η : ℝ≥0∞))
        (ENNReal.coe_ne_zero.mpr hηpos.ne') with
    ⟨t, htC, hρt⟩
  let htData :=
    supClosure_finiteMeasureRectangles_measurable_finite htC
  refine
    ⟨indicatorConstLp 2 htData.1 htData.2 c,
      indicatorConstLp_supClosure_mem_tensorRange htC c,
      ?_⟩
  rw [edist_indicatorConstLp_eq_enorm]
  calc
    ‖indicatorConstLp 2
        (hs.symmDiff htData.1)
        (by
          rw [symmDiff_comm]
          exact (hρt.trans ENNReal.coe_lt_top).ne) c‖ₑ =
        eLpNorm ((s ∆ t).indicator fun _ => c) 2
          (μ.prod ν) := by
      rw [indicatorConstLp, Lp.enorm_toLp]
    _ ≤ ε / 2 := hηbound _ (by
      rw [symmDiff_comm]
      exact hρt.le)
    _ < ε := ENNReal.half_lt_self hε.ne' hεtop

theorem l2TensorToProduct_denseRange :
    DenseRange
      (l2TensorToProduct
        (α := α) (β := β) (μ := μ) (ν := ν)) := by
  let S :
      Submodule ℂ (Lp ℂ 2 (μ.prod ν)) :=
    LinearMap.range
      (l2TensorToProduct
        (α := α) (β := β) (μ := μ) (ν := ν))
  have hall :
      ∀ f : Lp ℂ 2 (μ.prod ν),
        f ∈ S.topologicalClosure := by
    intro f
    apply Lp.induction
      (p := 2) (μ := μ.prod ν)
      (motive := fun u => u ∈ S.topologicalClosure)
      (by norm_num)
    · intro c s hs hρs
      simpa only [Lp.simpleFunc.coe_indicatorConst, S] using
        indicatorConstLp_mem_tensorClosure
          (μ := μ) (ν := ν) c hs hρs.ne
    · intro u v hu hv huv hu' hv'
      exact S.topologicalClosure.add_mem hu' hv'
    · exact Submodule.isClosed_topologicalClosure S
  have htop : S.topologicalClosure = ⊤ :=
    eq_top_iff.mpr (fun f _ => hall f)
  rw [denseRange_iff_closure_range]
  simpa only [S, Submodule.topologicalClosure_coe,
    Submodule.top_coe, LinearMap.coe_range] using
    congrArg
      (fun U : Submodule ℂ (Lp ℂ 2 (μ.prod ν)) =>
        (U : Set (Lp ℂ 2 (μ.prod ν))))
      htop

variable {A B : Type*}
    [AddCommMonoid A] [Module ℂ A]
    [AddCommMonoid B] [Module ℂ B]

def denseFactorTensorToProduct
    (F : A →ₗ[ℂ] Lp ℂ 2 μ)
    (G : B →ₗ[ℂ] Lp ℂ 2 ν) :
    (A ⊗[ℂ] B) →ₗ[ℂ] Lp ℂ 2 (μ.prod ν) :=
  l2TensorToProduct.comp (TensorProduct.map F G)

omit [SigmaFinite μ] [SigmaFinite ν] in
@[simp]
theorem denseFactorTensorToProduct_tmul
    (F : A →ₗ[ℂ] Lp ℂ 2 μ)
    (G : B →ₗ[ℂ] Lp ℂ 2 ν)
    (a : A) (b : B) :
    denseFactorTensorToProduct F G (a ⊗ₜ[ℂ] b) =
      l2SeparatedProduct (F a) (G b) := by
  rfl

theorem denseFactorTensorToProduct_denseRange
    (F : A →ₗ[ℂ] Lp ℂ 2 μ)
    (G : B →ₗ[ℂ] Lp ℂ 2 ν)
    (hF : DenseRange F) (hG : DenseRange G) :
    DenseRange (denseFactorTensorToProduct F G) := by
  let T :
      (A ⊗[ℂ] B) →ₗ[ℂ] Lp ℂ 2 (μ.prod ν) :=
    denseFactorTensorToProduct F G
  let S : Submodule ℂ (Lp ℂ 2 (μ.prod ν)) :=
    LinearMap.range T
  have hclosed :
      IsClosed
        (S.topologicalClosure :
          Set (Lp ℂ 2 (μ.prod ν))) :=
    Submodule.isClosed_topologicalClosure S
  have hright
      (a : A) (v : Lp ℂ 2 ν) :
      l2SeparatedProduct (F a) v ∈
        S.topologicalClosure := by
    let L :
        Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 (μ.prod ν) :=
      l2SeparatedProductContinuousBilinear (F a)
    have hmaps :
        Set.MapsTo L
          (Set.range G)
          (S.topologicalClosure :
            Set (Lp ℂ 2 (μ.prod ν))) := by
      rintro _ ⟨b, rfl⟩
      apply S.le_topologicalClosure
      refine ⟨a ⊗ₜ[ℂ] b, ?_⟩
      simp only [T, denseFactorTensorToProduct_tmul,
        L, l2SeparatedProductContinuousBilinear_apply]
    have hv := hG v
    have hout := (hmaps.closure L.continuous) hv
    simpa only [L,
      l2SeparatedProductContinuousBilinear_apply,
      hclosed.closure_eq, SetLike.mem_coe] using hout
  have hsep
      (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
      l2SeparatedProduct u v ∈
        S.topologicalClosure := by
    let L :
        Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (μ.prod ν) :=
      l2SeparatedProductContinuousBilinear.flip v
    have hmaps :
        Set.MapsTo L
          (Set.range F)
          (S.topologicalClosure :
            Set (Lp ℂ 2 (μ.prod ν))) := by
      rintro _ ⟨a, rfl⟩
      simpa only [L, ContinuousLinearMap.flip_apply,
        l2SeparatedProductContinuousBilinear_apply,
        SetLike.mem_coe] using
        hright a v
    have hu := hF u
    have hout := (hmaps.closure L.continuous) hu
    simpa only [L, ContinuousLinearMap.flip_apply,
      l2SeparatedProductContinuousBilinear_apply,
      hclosed.closure_eq, SetLike.mem_coe] using hout
  have hTensor :
      ∀ x : Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν,
        l2TensorToProduct x ∈
          S.topologicalClosure := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero =>
        simp
    | tmul u v =>
        simpa only [l2TensorToProduct_tmul] using
          hsep u v
    | add x y hx hy =>
        simpa only [map_add] using
          S.topologicalClosure.add_mem hx hy
  have hRange :
      Set.range
          (l2TensorToProduct
            (α := α) (β := β) (μ := μ) (ν := ν)) ⊆
        (S.topologicalClosure :
          Set (Lp ℂ 2 (μ.prod ν))) := by
    rintro _ ⟨x, rfl⟩
    exact hTensor x
  have hall :
      ∀ y : Lp ℂ 2 (μ.prod ν),
        y ∈ S.topologicalClosure := by
    intro y
    exact
      (closure_minimal hRange hclosed)
        (l2TensorToProduct_denseRange y)
  have htop : S.topologicalClosure = ⊤ :=
    eq_top_iff.mpr (fun y _ => hall y)
  rw [denseRange_iff_closure_range]
  simpa only [T, S, Submodule.topologicalClosure_coe,
    Submodule.top_coe, LinearMap.coe_range] using
    congrArg
      (fun U : Submodule ℂ (Lp ℂ 2 (μ.prod ν)) =>
        (U : Set (Lp ℂ 2 (μ.prod ν))))
      htop

end

end MeasureTheory

import Mathlib

/-!
# Monotone quantile transport on the line

For a measurable `S ⊂ ℝ` of finite measure `L`, let `F(u) = |S ∩ (−∞, u]|` (`QuantileTransport.cdf`)
and let `G(x) = inf {u : x ≤ F(u)}` be its quantile function (`QuantileTransport.quantile`).

* `F` is monotone and `1`-Lipschitz (`cdf_sub_le`).
* On `(0, L)`, `F ∘ G = id` and `G x ≤ u ↔ x ≤ F u` (`cdf_quantile`, `quantile_le_iff`).
* `G` pushes Lebesgue measure on `(0, L)` forward to Lebesgue measure on `S`
  (`map_quantile_restrict_Ioo`).
* Since `G` inverts a `1`-Lipschitz map, it stretches distances: `|x − y| ≤ |G x − G y|`
  (`abs_sub_le_abs_quantile_sub`).

Consequently, for every nonnegative `g` and every kernel `k` that decreases with the distance,
`∫∫_{S×S} g(u) g(v) k(|u − v|) ≤ ∫∫_{(0,L)²} g(G x) g(G y) k(|x − y|)`, while
`∫_{(0,L)} φ(g(G x)) dx = ∫_S φ ∘ g` for every `φ`. For kernels that increase with the distance the
inequality reverses. In one dimension this replaces the Riesz rearrangement inequality: it moves a
nonnegative function with support of finite measure onto an interval of the same length without
decreasing any cross term against a decreasing kernel.
-/

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace QuantileTransport

/-- The distribution function `F(u) = |S ∩ (−∞, u]|`. -/
def cdf (S : Set ℝ) (u : ℝ) : ℝ := (volume (S ∩ Iic u)).toReal

/-- The quantile function `G(x) = inf {u : x ≤ F(u)}`. -/
def quantile (S : Set ℝ) (x : ℝ) : ℝ := sInf {u | x ≤ cdf S u}

variable {S : Set ℝ}

theorem volume_inter_Iic_ne_top (hS : volume S ≠ ⊤) (u : ℝ) : volume (S ∩ Iic u) ≠ ⊤ :=
  ne_top_of_le_ne_top hS (measure_mono inter_subset_left)

theorem cdf_nonneg (u : ℝ) : 0 ≤ cdf S u := ENNReal.toReal_nonneg

theorem cdf_le (hS : volume S ≠ ⊤) (u : ℝ) : cdf S u ≤ (volume S).toReal :=
  ENNReal.toReal_mono hS (measure_mono inter_subset_left)

theorem cdf_mono (hS : volume S ≠ ⊤) : Monotone (cdf S) := fun _ v huv =>
  ENNReal.toReal_mono (volume_inter_Iic_ne_top hS v)
    (measure_mono (inter_subset_inter_right _ (Iic_subset_Iic.mpr huv)))

/-- **The distribution function is `1`-Lipschitz.** -/
theorem cdf_sub_le (hS : volume S ≠ ⊤) {u v : ℝ} (huv : u ≤ v) :
    cdf S v - cdf S u ≤ v - u := by
  have hsub : S ∩ Iic v ⊆ (S ∩ Iic u) ∪ Ioc u v := by
    intro w ⟨hwS, hwv⟩
    by_cases hwu : w ≤ u
    · exact Or.inl ⟨hwS, hwu⟩
    · exact Or.inr ⟨lt_of_not_ge hwu, hwv⟩
  have h1 : volume (S ∩ Iic v) ≤ volume (S ∩ Iic u) + volume (Ioc u v) :=
    (measure_mono hsub).trans (measure_union_le _ _)
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨volume_inter_Iic_ne_top hS u, measure_Ioc_lt_top.ne⟩) h1
  rw [ENNReal.toReal_add (volume_inter_Iic_ne_top hS u) measure_Ioc_lt_top.ne, Real.volume_Ioc,
    ENNReal.toReal_ofReal (by linarith)] at h2
  unfold cdf
  linarith

theorem abs_cdf_sub_le (hS : volume S ≠ ⊤) (u v : ℝ) : |cdf S u - cdf S v| ≤ |u - v| := by
  rcases le_total u v with huv | hvu
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (cdf_mono hS huv)), abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr huv)]
    exact cdf_sub_le hS huv
  · rw [abs_of_nonneg (sub_nonneg.mpr (cdf_mono hS hvu)), abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact cdf_sub_le hS hvu

theorem continuous_cdf (hS : volume S ≠ ⊤) : Continuous (cdf S) := by
  refine (LipschitzWith.of_dist_le_mul fun u v => ?_).continuous (K := 1)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  exact abs_cdf_sub_le hS u v

theorem tendsto_cdf_atTop (hS : volume S ≠ ⊤) :
    Tendsto (cdf S) atTop (𝓝 (volume S).toReal) := by
  have h := tendsto_measure_Iic_atTop (volume.restrict S)
  simp only [Measure.restrict_apply measurableSet_Iic, Measure.restrict_apply MeasurableSet.univ,
    univ_inter] at h
  have h' : Tendsto (fun u => volume (S ∩ Iic u)) atTop (𝓝 (volume S)) := by
    simpa [inter_comm] using h
  exact (ENNReal.tendsto_toReal hS).comp h'

theorem tendsto_cdf_atBot (hSm : MeasurableSet S) (hS : volume S ≠ ⊤) :
    Tendsto (cdf S) atBot (𝓝 0) := by
  have h := tendsto_measure_iInter_atBot (μ := volume) (s := fun u : ℝ => S ∩ Iic u)
    (fun u => (hSm.inter measurableSet_Iic).nullMeasurableSet)
    (fun u v huv => inter_subset_inter_right _ (Iic_subset_Iic.mpr huv))
    ⟨0, volume_inter_Iic_ne_top hS 0⟩
  have hempty : (⋂ u : ℝ, S ∩ Iic u) = ∅ := by
    ext w
    simp only [mem_iInter, mem_inter_iff, mem_Iic, mem_empty_iff_false, iff_false, not_forall]
    exact ⟨w - 1, fun h => by linarith [h.2]⟩
  rw [hempty, measure_empty] at h
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  rw [ENNReal.toReal_zero] at this
  exact this

/-- On `(0, L)` the defining set of the quantile is closed, nonempty and bounded below. -/
theorem quantile_set_props (hSm : MeasurableSet S) (hS : volume S ≠ ⊤) {x : ℝ}
    (hx : x ∈ Ioo 0 (volume S).toReal) :
    IsClosed {u | x ≤ cdf S u} ∧ {u | x ≤ cdf S u}.Nonempty ∧ BddBelow {u | x ≤ cdf S u} := by
  refine ⟨isClosed_le continuous_const (continuous_cdf hS), ?_, ?_⟩
  · obtain ⟨u, hu⟩ := ((tendsto_cdf_atTop hS).eventually (lt_mem_nhds hx.2)).exists
    exact ⟨u, hu.le⟩
  · obtain ⟨u₀, hu₀⟩ := eventually_atBot.mp ((tendsto_cdf_atBot hSm hS).eventually
      (gt_mem_nhds hx.1))
    refine ⟨u₀, fun u hu => ?_⟩
    by_contra h
    have := hu₀ u (le_of_lt (lt_of_not_ge h))
    exact absurd hu (not_le.mpr this)

/-- **The quantile inverts the distribution function on `(0, L)`.** -/
theorem cdf_quantile (hSm : MeasurableSet S) (hS : volume S ≠ ⊤) {x : ℝ}
    (hx : x ∈ Ioo 0 (volume S).toReal) : cdf S (quantile S x) = x := by
  obtain ⟨hcl, hne, hbdd⟩ := quantile_set_props hSm hS hx
  have hmem : x ≤ cdf S (quantile S x) := hcl.csInf_mem hne hbdd
  refine le_antisymm ?_ hmem
  by_contra hlt
  push Not at hlt
  set q := quantile S x
  set ε := cdf S q - x with hε
  have hε0 : 0 < ε := by linarith
  have hlow : cdf S (q - ε / 2) < x := by
    by_contra hge
    push Not at hge
    have h2 : q ≤ q - ε / 2 := csInf_le hbdd (show q - ε / 2 ∈ {u | x ≤ cdf S u} from hge)
    linarith
  have := cdf_sub_le hS (show q - ε / 2 ≤ q by linarith)
  linarith

/-- **Galois connection.** On `(0, L)`, `G x ≤ u ↔ x ≤ F u`. -/
theorem quantile_le_iff (hSm : MeasurableSet S) (hS : volume S ≠ ⊤) {x : ℝ}
    (hx : x ∈ Ioo 0 (volume S).toReal) (u : ℝ) : quantile S x ≤ u ↔ x ≤ cdf S u := by
  obtain ⟨-, -, hbdd⟩ := quantile_set_props hSm hS hx
  constructor
  · intro h
    calc x = cdf S (quantile S x) := (cdf_quantile hSm hS hx).symm
      _ ≤ cdf S u := cdf_mono hS h
  · intro h
    exact csInf_le hbdd h

theorem monotoneOn_quantile (hSm : MeasurableSet S) (hS : volume S ≠ ⊤) :
    MonotoneOn (quantile S) (Ioo 0 (volume S).toReal) := by
  intro x hx y hy hxy
  rw [quantile_le_iff hSm hS hx]
  rw [cdf_quantile hSm hS hy]
  exact hxy

/-- **The quantile stretches distances.** -/
theorem abs_sub_le_abs_quantile_sub (hSm : MeasurableSet S) (hS : volume S ≠ ⊤) {x y : ℝ}
    (hx : x ∈ Ioo 0 (volume S).toReal) (hy : y ∈ Ioo 0 (volume S).toReal) :
    |x - y| ≤ |quantile S x - quantile S y| := by
  have h := abs_cdf_sub_le hS (quantile S x) (quantile S y)
  rwa [cdf_quantile hSm hS hx, cdf_quantile hSm hS hy] at h

theorem aemeasurable_quantile (hSm : MeasurableSet S) (hS : volume S ≠ ⊤) :
    AEMeasurable (quantile S) (volume.restrict (Ioo 0 (volume S).toReal)) :=
  aemeasurable_restrict_of_monotoneOn measurableSet_Ioo (monotoneOn_quantile hSm hS)

/-- **Quantile transport.** The quantile pushes Lebesgue measure on `(0, L)` to Lebesgue measure
on `S`. -/
theorem map_quantile_restrict_Ioo (hSm : MeasurableSet S) (hS : volume S ≠ ⊤) :
    Measure.map (quantile S) (volume.restrict (Ioo 0 (volume S).toReal)) =
      volume.restrict S := by
  haveI : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS
  haveI : IsFiniteMeasure (Measure.map (quantile S)
      (volume.restrict (Ioo 0 (volume S).toReal))) :=
    Measure.isFiniteMeasure_map _ _
  refine Measure.ext_of_Iic _ _ fun u => ?_
  rw [Measure.map_apply_of_aemeasurable (aemeasurable_quantile hSm hS) measurableSet_Iic,
    Measure.restrict_apply' measurableSet_Ioo, Measure.restrict_apply measurableSet_Iic]
  have hset : quantile S ⁻¹' Iic u ∩ Ioo 0 (volume S).toReal =
      Ioo 0 (volume S).toReal ∩ Iic (cdf S u) := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_Iic]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, (quantile_le_iff hSm hS h2 u).mp h1⟩
    · rintro ⟨h2, h1⟩
      exact ⟨(quantile_le_iff hSm hS h2 u).mpr h1, h2⟩
  rw [hset]
  have hc0 := cdf_nonneg (S := S) u
  have hcL := cdf_le hS u
  have hvol : volume (Ioo 0 (volume S).toReal ∩ Iic (cdf S u)) = ENNReal.ofReal (cdf S u) := by
    rcases eq_or_lt_of_le hcL with heq | hlt
    · have : Ioo 0 (volume S).toReal ∩ Iic (cdf S u) = Ioo 0 (volume S).toReal := by
        rw [heq]
        exact inter_eq_left.mpr (fun x hx => le_of_lt hx.2)
      rw [this, Real.volume_Ioo, heq, sub_zero]
    · have : Ioo 0 (volume S).toReal ∩ Iic (cdf S u) = Ioc 0 (cdf S u) := by
        ext x
        simp only [mem_inter_iff, mem_Ioo, mem_Iic, mem_Ioc]
        constructor
        · rintro ⟨⟨h1, -⟩, h3⟩
          exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩
          exact ⟨⟨h1, lt_of_le_of_lt h3 hlt⟩, h3⟩
      rw [this, Real.volume_Ioc, sub_zero]
  rw [hvol, cdf, ENNReal.ofReal_toReal (volume_inter_Iic_ne_top hS u), inter_comm]

/-! ## Transported integrals -/

/-- **Single integrals transport exactly.** -/
theorem integral_restrict_eq_quantile (hSm : MeasurableSet S) (hS : volume S ≠ ⊤) {f : ℝ → ℝ}
    (hf : Measurable f) :
    ∫ u in S, f u = ∫ x in Ioo 0 (volume S).toReal, f (quantile S x) := by
  rw [← map_quantile_restrict_Ioo hSm hS,
    integral_map (aemeasurable_quantile hSm hS) hf.aestronglyMeasurable]

theorem ae_prod_quantile_eq_mk (hSm : MeasurableSet S) (hS : volume S ≠ ⊤) :
    ∀ᵐ p ∂((volume.restrict (Ioo 0 (volume S).toReal)).prod
        (volume.restrict (Ioo 0 (volume S).toReal))),
      (aemeasurable_quantile hSm hS).mk _ p.1 = quantile S p.1 ∧
        (aemeasurable_quantile hSm hS).mk _ p.2 = quantile S p.2 ∧
        p.1 ∈ Ioo 0 (volume S).toReal ∧ p.2 ∈ Ioo 0 (volume S).toReal := by
  set μI := volume.restrict (Ioo 0 (volume S).toReal)
  have h := (aemeasurable_quantile hSm hS).ae_eq_mk
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := μI) (ν := μI)).ae h
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := μI) (ν := μI)).ae h
  have h3 := (Measure.quasiMeasurePreserving_fst (μ := μI) (ν := μI)).ae
    (ae_restrict_mem measurableSet_Ioo)
  have h4 := (Measure.quasiMeasurePreserving_snd (μ := μI) (ν := μI)).ae
    (ae_restrict_mem measurableSet_Ioo)
  filter_upwards [h1, h2, h3, h4] with p hp1 hp2 hp3 hp4
  exact ⟨hp1.symm, hp2.symm, hp3, hp4⟩

/-- **Pair integrals transport exactly.** -/
theorem integral_prod_restrict_eq_quantile (hSm : MeasurableSet S) (hS : volume S ≠ ⊤)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    ∫ p, f p ∂((volume.restrict S).prod (volume.restrict S)) =
      ∫ p, f (quantile S p.1, quantile S p.2) ∂((volume.restrict (Ioo 0 (volume S).toReal)).prod
        (volume.restrict (Ioo 0 (volume S).toReal))) := by
  set μI := volume.restrict (Ioo 0 (volume S).toReal)
  set hae := aemeasurable_quantile hSm hS
  have hGm := hae.measurable_mk
  have hmap : Measure.map (hae.mk _) μI = volume.restrict S := by
    rw [← Measure.map_congr hae.ae_eq_mk]
    exact map_quantile_restrict_Ioo hSm hS
  rw [← hmap, Measure.map_prod_map μI μI hGm hGm,
    integral_map_of_stronglyMeasurable (hGm.prodMap hGm) hf.stronglyMeasurable]
  refine integral_congr_ae ?_
  filter_upwards [ae_prod_quantile_eq_mk hSm hS] with p hp
  show f (hae.mk _ p.1, hae.mk _ p.2) = _
  rw [hp.1, hp.2.1]

/-- **Decreasing kernels: transport does not decrease the pair energy.** For `g ≥ 0` bounded and a
bounded kernel `k ≥ 0` that is antitone on `[0, ∞)`,
`∫∫_{S×S} g(u) g(v) k(|u−v|) ≤ ∫∫_{(0,L)²} g(G x) g(G y) k(|x−y|)`. -/
theorem integral_kernel_le_quantile (hSm : MeasurableSet S) (hS : volume S ≠ ⊤) {g k : ℝ → ℝ}
    (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) {C : ℝ} (hgC : ∀ x, g x ≤ C) (hk : Measurable k)
    (hk0 : ∀ r, 0 ≤ k r) {K : ℝ} (hkK : ∀ r, k r ≤ K) (hanti : AntitoneOn k (Ici 0)) :
    ∫ p, g p.1 * g p.2 * k |p.1 - p.2| ∂((volume.restrict S).prod (volume.restrict S)) ≤
      ∫ p, g (quantile S p.1) * g (quantile S p.2) * k |p.1 - p.2|
        ∂((volume.restrict (Ioo 0 (volume S).toReal)).prod
          (volume.restrict (Ioo 0 (volume S).toReal))) := by
  set μI := volume.restrict (Ioo 0 (volume S).toReal)
  haveI : IsFiniteMeasure μI := isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  set hae := aemeasurable_quantile hSm hS
  set Gm := hae.mk (quantile S)
  have hGm : Measurable Gm := hae.measurable_mk
  have hmeas : Measurable fun p : ℝ × ℝ => g p.1 * g p.2 * k |p.1 - p.2| :=
    ((hg.comp measurable_fst).mul (hg.comp measurable_snd)).mul
      (hk.comp (measurable_fst.sub measurable_snd).abs)
  rw [integral_prod_restrict_eq_quantile hSm hS hmeas]
  have hC0 : 0 ≤ C := (hg0 0).trans (hgC 0)
  have hbound : ∀ a b c : ℝ, ‖g a * g b * k c‖ ≤ C * C * K := by
    intro a b c
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hg0 a) (hg0 b)) (hk0 c))]
    exact mul_le_mul (mul_le_mul (hgC a) (hgC b) (hg0 b) hC0) (hkK c) (hk0 c) (mul_nonneg hC0 hC0)
  have hae_eq := ae_prod_quantile_eq_mk hSm hS
  have hL_meas : Measurable fun p : ℝ × ℝ => g (Gm p.1) * g (Gm p.2) * k |Gm p.1 - Gm p.2| :=
    ((hg.comp (hGm.comp measurable_fst)).mul (hg.comp (hGm.comp measurable_snd))).mul
      (hk.comp ((hGm.comp measurable_fst).sub (hGm.comp measurable_snd)).abs)
  have hR_meas : Measurable fun p : ℝ × ℝ => g (Gm p.1) * g (Gm p.2) * k |p.1 - p.2| :=
    ((hg.comp (hGm.comp measurable_fst)).mul (hg.comp (hGm.comp measurable_snd))).mul
      (hk.comp (measurable_fst.sub measurable_snd).abs)
  have hLi : Integrable (fun p : ℝ × ℝ => g (quantile S p.1) * g (quantile S p.2) *
      k |quantile S p.1 - quantile S p.2|) (μI.prod μI) := by
    refine (integrable_const (C * C * K)).mono' ?_ (ae_of_all _ fun p => hbound _ _ _)
    refine hL_meas.aestronglyMeasurable.congr ?_
    filter_upwards [hae_eq] with p hp
    simp only [Gm] at hp ⊢
    rw [hp.1, hp.2.1]
  have hRi : Integrable (fun p : ℝ × ℝ => g (quantile S p.1) * g (quantile S p.2) *
      k |p.1 - p.2|) (μI.prod μI) := by
    refine (integrable_const (C * C * K)).mono' ?_ (ae_of_all _ fun p => hbound _ _ _)
    refine hR_meas.aestronglyMeasurable.congr ?_
    filter_upwards [hae_eq] with p hp
    simp only [Gm] at hp ⊢
    rw [hp.1, hp.2.1]
  refine integral_mono_ae hLi hRi ?_
  filter_upwards [hae_eq] with p hp
  have hst := abs_sub_le_abs_quantile_sub hSm hS hp.2.2.1 hp.2.2.2
  have hkle : k |quantile S p.1 - quantile S p.2| ≤ k |p.1 - p.2| :=
    hanti (mem_Ici.mpr (abs_nonneg _)) (mem_Ici.mpr (abs_nonneg _)) hst
  exact mul_le_mul_of_nonneg_left hkle (mul_nonneg (hg0 _) (hg0 _))

/-- **Increasing kernels: transport does not increase the pair energy.** -/
theorem integral_quantile_le_kernel (hSm : MeasurableSet S) (hS : volume S ≠ ⊤) {g k : ℝ → ℝ}
    (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) {C : ℝ} (hgC : ∀ x, g x ≤ C) (hk : Measurable k)
    (hk0 : ∀ r, 0 ≤ k r) {K : ℝ} (hkK : ∀ r, k r ≤ K) (hmono : MonotoneOn k (Ici 0)) :
    ∫ p, g (quantile S p.1) * g (quantile S p.2) * k |p.1 - p.2|
        ∂((volume.restrict (Ioo 0 (volume S).toReal)).prod
          (volume.restrict (Ioo 0 (volume S).toReal))) ≤
      ∫ p, g p.1 * g p.2 * k |p.1 - p.2| ∂((volume.restrict S).prod (volume.restrict S)) := by
  set μI := volume.restrict (Ioo 0 (volume S).toReal)
  haveI : IsFiniteMeasure μI := isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  set hae := aemeasurable_quantile hSm hS
  set Gm := hae.mk (quantile S)
  have hGm : Measurable Gm := hae.measurable_mk
  have hmeas : Measurable fun p : ℝ × ℝ => g p.1 * g p.2 * k |p.1 - p.2| :=
    ((hg.comp measurable_fst).mul (hg.comp measurable_snd)).mul
      (hk.comp (measurable_fst.sub measurable_snd).abs)
  rw [integral_prod_restrict_eq_quantile hSm hS hmeas]
  have hC0 : 0 ≤ C := (hg0 0).trans (hgC 0)
  have hbound : ∀ a b c : ℝ, ‖g a * g b * k c‖ ≤ C * C * K := by
    intro a b c
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hg0 a) (hg0 b)) (hk0 c))]
    exact mul_le_mul (mul_le_mul (hgC a) (hgC b) (hg0 b) hC0) (hkK c) (hk0 c) (mul_nonneg hC0 hC0)
  have hae_eq := ae_prod_quantile_eq_mk hSm hS
  have hL_meas : Measurable fun p : ℝ × ℝ => g (Gm p.1) * g (Gm p.2) * k |Gm p.1 - Gm p.2| :=
    ((hg.comp (hGm.comp measurable_fst)).mul (hg.comp (hGm.comp measurable_snd))).mul
      (hk.comp ((hGm.comp measurable_fst).sub (hGm.comp measurable_snd)).abs)
  have hR_meas : Measurable fun p : ℝ × ℝ => g (Gm p.1) * g (Gm p.2) * k |p.1 - p.2| :=
    ((hg.comp (hGm.comp measurable_fst)).mul (hg.comp (hGm.comp measurable_snd))).mul
      (hk.comp (measurable_fst.sub measurable_snd).abs)
  have hLi : Integrable (fun p : ℝ × ℝ => g (quantile S p.1) * g (quantile S p.2) *
      k |quantile S p.1 - quantile S p.2|) (μI.prod μI) := by
    refine (integrable_const (C * C * K)).mono' ?_ (ae_of_all _ fun p => hbound _ _ _)
    refine hL_meas.aestronglyMeasurable.congr ?_
    filter_upwards [hae_eq] with p hp
    simp only [Gm] at hp ⊢
    rw [hp.1, hp.2.1]
  have hRi : Integrable (fun p : ℝ × ℝ => g (quantile S p.1) * g (quantile S p.2) *
      k |p.1 - p.2|) (μI.prod μI) := by
    refine (integrable_const (C * C * K)).mono' ?_ (ae_of_all _ fun p => hbound _ _ _)
    refine hR_meas.aestronglyMeasurable.congr ?_
    filter_upwards [hae_eq] with p hp
    simp only [Gm] at hp ⊢
    rw [hp.1, hp.2.1]
  refine integral_mono_ae hRi hLi ?_
  filter_upwards [hae_eq] with p hp
  have hst := abs_sub_le_abs_quantile_sub hSm hS hp.2.2.1 hp.2.2.2
  have hkle : k |p.1 - p.2| ≤ k |quantile S p.1 - quantile S p.2| :=
    hmono (mem_Ici.mpr (abs_nonneg _)) (mem_Ici.mpr (abs_nonneg _)) hst
  exact mul_le_mul_of_nonneg_left hkle (mul_nonneg (hg0 _) (hg0 _))

end QuantileTransport

end

end GaloisForLFunctions.HTGeometry

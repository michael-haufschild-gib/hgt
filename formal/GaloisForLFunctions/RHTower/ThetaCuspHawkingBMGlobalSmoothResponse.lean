import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMGlobalSobolevBootstrap
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
Local Fourier reconstructions glue to a globally smooth modular response representing the original full-forcing Hilbert-space solution.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup TemperedDistribution
open scoped ContDiff ENNReal SchwartzMap
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse GaloisForLFunctions.HTGeometry
noncomputable section

theorem exists_planarChartTest_ne_zero {z : ℂ} (hz : z ∈ {z : ℂ | 0 < z.im}) :
    ∃ g : PlanarChartTest, g.field z ≠ 0 := by
  obtain ⟨b,hb,hc,hd,_,he⟩ := exists_contDiff_tsupport_subset (n := ⊤) (isOpen_upperHalfPlaneSet.mem_nhds hz)
  have hcc : HasCompactSupport (Complex.ofRealCLM ∘ b) := hc.comp_left rfl
  have hdd : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ b) := Complex.ofRealCLM.contDiff.comp hd
  have hss : tsupport (Complex.ofRealCLM ∘ b) ⊆ {z : ℂ | 0 < z.im} := by
    apply Subset.trans _ hb
    exact closure_mono (by intro x hx; simpa using hx)
  refine ⟨⟨Complex.ofRealCLM ∘ b,hdd,hcc,hss⟩,?_⟩
  change (b z : ℂ) ≠ 0
  simp [he]

/-- Smooth representatives of all compact chart localizations glue across all modular seams.
The glued field represents the actual globally lifted scalar in planar measure. -/
theorem global_smooth_representative_of_localizations (u : Space)
    (hu : ∀ g : PlanarChartTest, ∃ r : ℂ → ℂ, ContDiff ℝ ∞ r ∧ r =ᵐ[volume] g.localValue u) :
    ∃ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {z : ℂ | 0 < z.im} ∧
      f =ᵐ[volume.restrict {z : ℂ | 0 < z.im}] (fun z : ℂ => globalLift u (ofComplex z)) := by
  classical
  choose R hR hRa using hu
  have hcross (g h : PlanarChartTest) (z : ℂ) : g.field z * R h z = h.field z * R g z := by
    have hae : (fun w : ℂ => g.field w * R h w) =ᵐ[volume]
        (fun w : ℂ => h.field w * R g w) := by
      filter_upwards [hRa g,hRa h] with w hgw hhw
      rw [hgw,hhw]
      simp only [PlanarChartTest.localValue]
      ring
    exact congrFun (Measure.eq_of_ae_eq hae (g.smooth.continuous.mul (hR h).continuous)
      (h.smooth.continuous.mul (hR g).continuous)) z
  let chosen (z : ℂ) (hz : z ∈ {z : ℂ | 0 < z.im}) : PlanarChartTest :=
    Classical.choose (exists_planarChartTest_ne_zero hz)
  have chosen_ne (z : ℂ) (hz : z ∈ {z : ℂ | 0 < z.im}) : (chosen z hz).field z ≠ 0 :=
    Classical.choose_spec (exists_planarChartTest_ne_zero hz)
  let f (z : ℂ) : ℂ := if hz : z ∈ {z : ℂ | 0 < z.im} then
    R (chosen z hz) z / (chosen z hz).field z else 0
  have hquot (z : ℂ) (g : PlanarChartTest) (hg : g.field z ≠ 0) : f z = R g z / g.field z := by
    have hz : z ∈ {z : ℂ | 0 < z.im} := g.support (subset_tsupport g.field hg)
    dsimp only [f]
    rw [dif_pos hz]
    apply (div_eq_div_iff (chosen_ne z hz) hg).mpr
    have he := hcross (chosen z hz) g z
    linear_combination -he
  have hs : ContDiffOn ℝ ∞ f {z : ℂ | 0 < z.im} := by
    intro z hz
    let g := chosen z hz
    have hg : g.field z ≠ 0 := chosen_ne z hz
    have hq : ContDiffAt ℝ ∞ (fun w : ℂ => R g w / g.field w) z := by
      simpa only [div_eq_mul_inv] using (hR g).contDiffAt.mul
        (g.smooth.contDiffAt.fun_inv hg)
    apply (hq.congr_of_eventuallyEq _).contDiffWithinAt
    filter_upwards [(isOpen_ne_fun g.smooth.continuous continuous_const).mem_nhds hg] with w hw
    exact hquot w g hw
  let U (g : PlanarChartTest) : Set ℂ := {z | g.field z ≠ 0}
  have hU (g : PlanarChartTest) : IsOpen (U g) := isOpen_ne_fun g.smooth.continuous continuous_const
  have hcover : {z : ℂ | 0 < z.im} ⊆ ⋃ g : PlanarChartTest, U g := by
    intro z hz
    obtain ⟨g,hg⟩ := exists_planarChartTest_ne_zero hz
    exact mem_iUnion.mpr ⟨g,hg⟩
  have hpatch (g : PlanarChartTest) : f =ᵐ[volume.restrict (U g)] (fun z : ℂ => globalLift u (ofComplex z)) := by
    apply (ae_restrict_iff' (hU g).measurableSet).mpr
    filter_upwards [hRa g] with z hz hg
    rw [hquot z g hg,hz]
    simp only [PlanarChartTest.localValue]
    exact mul_div_cancel_left₀ _ hg
  obtain ⟨C,hC,hcov⟩ := (HereditarilyLindelofSpace.isLindelof {z : ℂ | 0 < z.im}).elim_countable_subcover
    U hU hcover
  have he : f =ᵐ[volume.restrict (⋃ g ∈ C, U g)] (fun z : ℂ => globalLift u (ofComplex z)) :=
    (ae_restrict_biUnion_iff U hC _).mpr (fun g _ => hpatch g)
  exact ⟨f,hs,ae_restrict_of_ae_restrict_of_subset hcov he⟩

/-- The actual response has a smooth planar representative on the entire upper half-plane. -/
theorem full_response_global_planar_smooth (q : XiZeroCopy) (branch : Bool) :
    ∃ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {z : ℂ | 0 < z.im} ∧
      f =ᵐ[volume.restrict {z : ℂ | 0 < z.im}]
        (fun z => globalLift (embedding (weakResponse q branch)) (ofComplex z)) :=
  global_smooth_representative_of_localizations _ (full_response_global_local_smooth q branch)

/-- The constructed globally smooth representative of the original full-forcing response. -/
def globalResponse (q : XiZeroCopy) (branch : Bool) (z : UpperHalfPlane) : ℂ :=
  (full_response_global_planar_smooth q branch).choose (z:ℂ)

/-- The actual full-forcing response is smooth across every seam and elliptic fixed point. -/
theorem globalResponse_smooth (q : XiZeroCopy) (branch : Bool) :
    ChartSmooth (globalResponse q branch) := by
  intro z
  have hs := (full_response_global_planar_smooth q branch).choose_spec.1.contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  apply hs.congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_apply,globalResponse,ofComplex_apply_of_im_pos hw]

/-- The smooth global response is the original lifted L² solution in full invariant volume. -/
theorem globalResponse_ae_lift (q : XiZeroCopy) (branch : Bool) :
    globalResponse q branch =ᵐ[(volume : Measure UpperHalfPlane)]
      globalLift (embedding (weakResponse q branch)) := by
  have he := (full_response_global_planar_smooth q branch).choose_spec.2
  have hd := (withDensity_absolutelyContinuous
    ((volume : Measure ℂ).restrict {z : ℂ | 0 < z.im})
    (fun z => (chartDensity z : ℝ≥0∞))).ae_le he
  rw [← map_volume_chart_eq] at hd
  have hn := UpperHalfPlane.measurableEmbedding_coe.ae_map_iff.mp hd
  filter_upwards [hn] with z hz
  simpa only [ofComplex_apply,globalResponse] using hz

theorem chartSmooth_eq_of_ae_eq {f g : UpperHalfPlane → ℂ}
    (hf : ChartSmooth f) (hg : ChartSmooth g) (he : f =ᵐ[(volume : Measure UpperHalfPlane)] g) : f = g := by
  have hm : ∀ᵐ z ∂Measure.map UpperHalfPlane.coe (volume : Measure UpperHalfPlane),
      f (ofComplex z) = g (ofComplex z) :=
    UpperHalfPlane.measurableEmbedding_coe.ae_map_iff.mpr (by
      filter_upwards [he] with z hz
      simpa only [ofComplex_apply] using hz)
  rw [map_volume_chart_eq] at hm
  have hd : Measurable (fun z : ℂ => (chartDensity z : ℝ≥0∞)) := by
    unfold chartDensity
    fun_prop
  have hh := (ae_withDensity_iff hd).mp hm
  have hae : (fun z : ℂ => f (ofComplex z)) =ᵐ[volume.restrict {z : ℂ | 0 < z.im}]
      (fun z : ℂ => g (ofComplex z)) := by
    filter_upwards [hh,ae_restrict_mem isOpen_upperHalfPlaneSet.measurableSet] with z hz hy
    exact hz (by simp [chartDensity,ne_of_gt hy])
  have hc (a : UpperHalfPlane → ℂ) (ha : ChartSmooth a) :
      ContinuousOn (fun z : ℂ => a (ofComplex z)) {z : ℂ | 0 < z.im} := by
    intro z hz
    have hh := ha (ofComplex z)
    rw [ofComplex_apply_of_im_pos hz] at hh
    exact hh.continuousAt.continuousWithinAt
  have hp := Measure.eqOn_open_of_ae_eq hae isOpen_upperHalfPlaneSet (hc f hf) (hc g hg)
  funext z
  simpa only [ofComplex_apply] using hp z.im_pos

/-- The globally smooth response obeys the original modular identifications pointwise. -/
theorem globalResponse_invariant (q : XiZeroCopy) (branch : Bool) (γ : PSL2Z)
    (z : UpperHalfPlane) : globalResponse q branch (γ • z) = globalResponse q branch z := by
  apply congrFun (chartSmooth_eq_of_ae_eq ((globalResponse_smooth q branch).modular_pullback γ)
    (globalResponse_smooth q branch) ?_) z
  have ht := (measurePreserving_smul γ (volume : Measure UpperHalfPlane)).quasiMeasurePreserving.ae
    (globalResponse_ae_lift q branch)
  filter_upwards [ht,globalResponse_ae_lift q branch] with w hw he
  rw [hw,he,globalLift_invariant]

/-- The smooth, globally modular response represents the original solution in its native Hilbert space. -/
theorem globalResponse_native_ae (q : XiZeroCopy) (branch : Bool) :
    globalResponse q branch =ᵐ[measure] embedding (weakResponse q branch) := by
  have ht : globalResponse q branch =ᵐ[measure] globalLift (embedding (weakResponse q branch)) :=
    ae_restrict_of_ae (globalResponse_ae_lift q branch)
  exact ht.trans (globalLift_ae_eq (embedding (weakResponse q branch)))

end
end RHTower.D4BMModularCore

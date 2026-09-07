import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMInteriorSobolevBootstrap
import GaloisForLFunctions.HTGeometry.PlanarSobolevSmoothRepresentative
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
The actual full-forcing response has a constructed smooth representative on the open modular cell. Local Fourier reconstructions agree on overlaps and glue, and the resulting field represents the original angular class in its native measure. Smooth extension across modular seams is not asserted.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup TemperedDistribution
open scoped ContDiff ENNReal SchwartzMap
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse GaloisForLFunctions.HTGeometry
noncomputable section

/-- Each actual scalar localization has a smooth representative of its original value. -/
theorem full_response_local_smooth (q : XiZeroCopy) (minusBranch : Bool) (g : InteriorTest) :
    ∃ f : ℂ → ℂ, ContDiff ℝ ∞ f ∧
      f =ᵐ[volume] g.localValue (embedding (weakResponse q minusBranch)) := by
  obtain ⟨f,hf,he⟩ := planar_all_sobolev_smooth_representative
    (g.localVector (embedding (weakResponse q minusBranch)))
    (fun n => full_response_local_all_orders q minusBranch n g)
  exact ⟨f,hf,he.trans (g.localValue_memLp _).coeFn_toLp⟩

/-- Each original completed-gradient localization also has a smooth representative. -/
theorem full_response_gradient_local_smooth (q : XiZeroCopy) (minusBranch : Bool)
    (g : InteriorTest) (i : Fin 2) :
    ∃ f : ℂ → ℂ, ContDiff ℝ ∞ f ∧
      f =ᵐ[volume] g.localValue ((weakResponse q minusBranch : EnergySpace) i.succ) := by
  obtain ⟨f,hf,he⟩ := planar_all_sobolev_smooth_representative
    (g.localVector ((weakResponse q minusBranch : EnergySpace) i.succ))
    (fun n => full_response_gradient_all_orders q minusBranch n g i)
  exact ⟨f,hf,he.trans (g.localValue_memLp _).coeFn_toLp⟩

private theorem interior_open : IsOpen interiorChart :=
  UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ isOpen_fdo

/-- Actual compact interior tests are nonzero at every point of the open cell. -/
theorem exists_interiorTest_ne_zero {z : ℂ} (hz : z ∈ interiorChart) :
    ∃ g : InteriorTest, g.field z ≠ 0 := by
  obtain ⟨b,hb,hc,hd,_,he⟩ := exists_contDiff_tsupport_subset (n := ⊤) (interior_open.mem_nhds hz)
  have hcc : HasCompactSupport (Complex.ofRealCLM ∘ b) := hc.comp_left rfl
  have hdd : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ b) := Complex.ofRealCLM.contDiff.comp hd
  have hss : tsupport (Complex.ofRealCLM ∘ b) ⊆ interiorChart := by
    apply Subset.trans _ hb
    exact closure_mono (by intro x hx; simpa using hx)
  refine ⟨⟨Complex.ofRealCLM ∘ b,hdd,hcc,hss⟩,?_⟩
  change (b z : ℂ) ≠ 0
  simp [he]

/-- Smooth representatives of all actual compact localizations glue to one smooth
field on the open cell. Its equality to the original angular class is a.e. planar equality. -/
theorem smooth_representative_of_localizations (u : Space)
    (hu : ∀ g : InteriorTest, ∃ r : ℂ → ℂ, ContDiff ℝ ∞ r ∧ r =ᵐ[volume] g.localValue u) :
    ∃ f : ℂ → ℂ, ContDiffOn ℝ ∞ f interiorChart ∧
      f =ᵐ[volume.restrict interiorChart] (fun z : ℂ => u (ofComplex z)) := by
  classical
  choose R hR hRa using hu
  have hcross (g h : InteriorTest) (z : ℂ) : g.field z * R h z = h.field z * R g z := by
    have hae : (fun w : ℂ => g.field w * R h w) =ᵐ[volume]
        (fun w : ℂ => h.field w * R g w) := by
      filter_upwards [hRa g,hRa h] with w hgw hhw
      rw [hgw,hhw]
      simp only [InteriorTest.localValue]
      ring
    exact congrFun (Measure.eq_of_ae_eq hae (g.smooth.continuous.mul (hR h).continuous)
      (h.smooth.continuous.mul (hR g).continuous)) z
  let chosen (z : ℂ) (hz : z ∈ interiorChart) : InteriorTest :=
    Classical.choose (exists_interiorTest_ne_zero hz)
  have chosen_ne (z : ℂ) (hz : z ∈ interiorChart) : (chosen z hz).field z ≠ 0 :=
    Classical.choose_spec (exists_interiorTest_ne_zero hz)
  let f (z : ℂ) : ℂ := if hz : z ∈ interiorChart then
    R (chosen z hz) z / (chosen z hz).field z else 0
  have hquot (z : ℂ) (g : InteriorTest) (hg : g.field z ≠ 0) : f z = R g z / g.field z := by
    have hz : z ∈ interiorChart := g.support (subset_tsupport g.field hg)
    dsimp only [f]
    rw [dif_pos hz]
    apply (div_eq_div_iff (chosen_ne z hz) hg).mpr
    have he := hcross (chosen z hz) g z
    linear_combination -he
  have hs : ContDiffOn ℝ ∞ f interiorChart := by
    intro z hz
    let g := chosen z hz
    have hg : g.field z ≠ 0 := chosen_ne z hz
    have hq : ContDiffAt ℝ ∞ (fun w : ℂ => R g w / g.field w) z := by
      simpa only [div_eq_mul_inv] using (hR g).contDiffAt.mul
        (g.smooth.contDiffAt.fun_inv hg)
    apply (hq.congr_of_eventuallyEq _).contDiffWithinAt
    filter_upwards [(isOpen_ne_fun g.smooth.continuous continuous_const).mem_nhds hg] with w hw
    exact hquot w g hw
  let U (g : InteriorTest) : Set ℂ := {z | g.field z ≠ 0}
  have hU (g : InteriorTest) : IsOpen (U g) := isOpen_ne_fun g.smooth.continuous continuous_const
  have hcover : interiorChart ⊆ ⋃ g : InteriorTest, U g := by
    intro z hz
    obtain ⟨g,hg⟩ := exists_interiorTest_ne_zero hz
    exact mem_iUnion.mpr ⟨g,hg⟩
  have hpatch (g : InteriorTest) : f =ᵐ[volume.restrict (U g)] (fun z : ℂ => u (ofComplex z)) := by
    apply (ae_restrict_iff' (hU g).measurableSet).mpr
    filter_upwards [hRa g] with z hz hg
    rw [hquot z g hg,hz]
    simp only [InteriorTest.localValue]
    exact mul_div_cancel_left₀ _ hg
  obtain ⟨C,hC,hcov⟩ := (HereditarilyLindelofSpace.isLindelof interiorChart).elim_countable_subcover
    U hU hcover
  have he : f =ᵐ[volume.restrict (⋃ g ∈ C, U g)] (fun z : ℂ => u (ofComplex z)) :=
    (ae_restrict_biUnion_iff U hC _).mpr (fun g _ => hpatch g)
  exact ⟨f,hs,ae_restrict_of_ae_restrict_of_subset hcov he⟩

/-- The unique response to the complete original forcing has a constructed smooth
representative throughout the open modular cell. No regularity premise is supplied. -/
theorem full_response_interior_smooth (q : XiZeroCopy) (minusBranch : Bool) :
    ∃ f : ℂ → ℂ, ContDiffOn ℝ ∞ f interiorChart ∧
      f =ᵐ[volume.restrict interiorChart]
        (fun z : ℂ => (embedding (weakResponse q minusBranch)) (ofComplex z)) :=
  smooth_representative_of_localizations _ (full_response_local_smooth q minusBranch)

/-- Both original completed gradients have constructed smooth representatives
throughout the open modular cell. -/
theorem full_response_gradient_interior_smooth (q : XiZeroCopy) (minusBranch : Bool) (i : Fin 2) :
    ∃ f : ℂ → ℂ, ContDiffOn ℝ ∞ f interiorChart ∧
      f =ᵐ[volume.restrict interiorChart]
        (fun z : ℂ => (weakResponse q minusBranch : EnergySpace) i.succ (ofComplex z)) :=
  smooth_representative_of_localizations _ (fun g => full_response_gradient_local_smooth q minusBranch g i)

/-- Planar a.e. identification on the open cell identifies the original native
angular class: the actual modular seams have zero native measure. -/
theorem interior_representative_native_ae (u : Space) (f : ℂ → ℂ)
    (he : f =ᵐ[volume.restrict interiorChart] (fun z : ℂ => u (ofComplex z))) :
    (fun z : UpperHalfPlane => f (z:ℂ)) =ᵐ[measure] u := by
  have hp := (ae_restrict_iff' interior_open.measurableSet).mp he
  have hr : ∀ᵐ z ∂((volume : Measure ℂ).restrict cellChart),
      z ∈ interiorChart → f z = u (ofComplex z) := ae_restrict_of_ae hp
  have hd := (withDensity_absolutelyContinuous ((volume : Measure ℂ).restrict cellChart)
    (fun z => (chartDensity z : ℝ≥0∞))).ae_le hr
  rw [← map_measure_eq] at hd
  have hn := UpperHalfPlane.measurableEmbedding_coe.ae_map_iff.mp hd
  filter_upwards [hn,ae_mem_interior] with z hz hi
  have hez := hz (mem_image_of_mem UpperHalfPlane.coe hi)
  simpa only [ofComplex_apply] using hez

/-- The constructed smooth interior field represents the original full-forcing
response in its native modular L² measure, on both physical Xi branches. -/
theorem full_response_native_smooth_representative (q : XiZeroCopy) (minusBranch : Bool) :
    ∃ f : ℂ → ℂ, ContDiffOn ℝ ∞ f interiorChart ∧
      (fun z : UpperHalfPlane => f (z:ℂ)) =ᵐ[measure] embedding (weakResponse q minusBranch) := by
  obtain ⟨f,hf,he⟩ := full_response_interior_smooth q minusBranch
  exact ⟨f,hf,interior_representative_native_ae _ f he⟩

end
end RHTower.D4BMModularCore

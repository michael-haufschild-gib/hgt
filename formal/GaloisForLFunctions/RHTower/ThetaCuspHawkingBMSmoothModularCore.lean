import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSmoothModularPeriodization
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMGlobalAngularForcing
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
The full smooth modular core is dense in the invariant angular L² space. Its literal hyperbolic-frame derivatives have finite energy, proved from compact quotient support.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff
namespace RHTower.D4BMModularCore
noncomputable section

abbrev measure : Measure UpperHalfPlane := D4BMGlobalAngularResponse.angularMeasure
abbrev Space := Lp ℂ 2 measure

/-- Compact support in the actual modular quotient, expressed on its closed cell. -/
def CellCompact (f : UpperHalfPlane → ℂ) : Prop :=
  ∃ K : Set UpperHalfPlane, IsCompact K ∧ ∀ z ∈ ModularGroup.fd, z ∉ K → f z = 0

/-- All smooth modular functions with compact quotient support, represented in the actual
invariant L² space. No condition forces vanishing at the joined modular sides. -/
def smoothCore : Submodule ℂ Space where
  carrier := {v | ∃ f : UpperHalfPlane → ℂ, ChartSmooth f ∧
    (∀ γ : PSL2Z, ∀ z, f (γ • z) = f z) ∧ CellCompact f ∧
    (v : UpperHalfPlane → ℂ) =ᵐ[measure] f}
  zero_mem' := by
    refine ⟨0,fun _ => contDiffAt_const,by simp,⟨∅,isCompact_empty,by simp⟩,?_⟩
    exact Lp.coeFn_zero ℂ 2 measure
  add_mem' := by
    rintro v w ⟨f,hf,hi,⟨K,hK,hk⟩,he⟩ ⟨g,hg,hj,⟨L,hL,hl⟩,hh⟩
    refine ⟨f+g,fun z => (hf z).add (hg z),?_,⟨K∪L,hK.union hL,?_⟩,?_⟩
    · intro γ z
      simp only [Pi.add_apply,hi,hj]
    · intro z hz hn
      simp only [mem_union,not_or] at hn
      simp [hk z hz hn.1,hl z hz hn.2]
    · exact (Lp.coeFn_add v w).trans (he.add hh)
  smul_mem' := by
    rintro c v ⟨f,hf,hi,⟨K,hK,hk⟩,he⟩
    refine ⟨c • f,fun z => (hf z).const_smul c,?_,⟨K,hK,?_⟩,?_⟩
    · intro γ z
      simp only [Pi.smul_apply,hi]
    · intro z hz hn
      simp [hk z hz hn]
    · exact (Lp.coeFn_smul c v).trans (he.const_smul c)

/-- The open complex-coordinate image of the modular cell interior. -/
def interiorChart : Set ℂ := UpperHalfPlane.coe '' ModularGroup.fdo

private theorem interiorChart_open : IsOpen interiorChart :=
  UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ ModularGroup.isOpen_fdo

/-- The modular seams have zero measure in the actual angular Hilbert space. -/
theorem ae_mem_interior : ∀ᵐ z ∂measure, z ∈ ModularGroup.fdo := by
  apply (ae_restrict_iff' ModularGroup.isClosed_fd.measurableSet).2
  rw [ae_iff]
  have he : {z : UpperHalfPlane | ¬ (z ∈ ModularGroup.fd → z ∈ ModularGroup.fdo)} =
      ModularGroup.fd \ ModularGroup.fdo := by ext z; simp
  rw [he]
  exact volume_fd_diff_fdo

private theorem restricted_compact (g : ℂ → ℂ) (hg : HasCompactSupport g)
    (hs : tsupport g ⊆ interiorChart) : HasCompactSupport (fun z : UpperHalfPlane => g z) := by
  have hsub : tsupport g ⊆ Set.range UpperHalfPlane.coe :=
    hs.trans (Set.image_subset_range _ _)
  have hK := UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.isInducing.isCompact_preimage' hg hsub
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal
  · intro z hz
    exact subset_tsupport g hz
  · exact isClosed_closure.preimage UpperHalfPlane.continuous_coe

private theorem restricted_smooth (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g) :
    ChartSmooth (fun z : UpperHalfPlane => g z) := by
  intro z
  apply hg.contDiffAt.congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_apply,UpperHalfPlane.ofComplex_apply_of_im_pos hw]

private theorem restricted_memLp (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hk : HasCompactSupport g) : MemLp (fun z : UpperHalfPlane => g z) 2 measure := by
  have h := hg.continuous.memLp_of_hasCompactSupport (μ := Measure.map UpperHalfPlane.coe measure)
    (p := 2) hk
  exact UpperHalfPlane.measurableEmbedding_coe.memLp_map_measure_iff.mp h

/-- Every compact smooth interior test is represented by a member of the full modular core,
through its constructed globally smooth periodization. -/
theorem interior_test_mem_smoothCore (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hk : HasCompactSupport g) (hs : tsupport g ⊆ interiorChart) :
    (restricted_memLp g hg hk).toLp (fun z : UpperHalfPlane => g z) ∈ smoothCore := by
  let f : UpperHalfPlane → ℂ := fun z => g z
  have hf := restricted_compact g hk hs
  have hsup : Function.support f ⊆ ModularGroup.fdo := by
    intro z hz
    obtain ⟨w,hw,he⟩ := hs (subset_tsupport g hz)
    exact UpperHalfPlane.coe_injective he ▸ hw
  refine ⟨periodize f,periodize_smooth f hf (restricted_smooth g hg),
    periodize_invariant f,⟨tsupport f,hf,?_⟩,?_⟩
  · intro z hz hn
    rw [periodize_eq_on_fd f hsup z hz]
    exact image_eq_zero_of_notMem_tsupport hn
  · apply (restricted_memLp g hg hk).coeFn_toLp.trans
    filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
    exact (periodize_eq_on_fd f hsup z hz).symm

/-- The full smooth modular core is dense in the actual invariant L² space. -/
theorem smoothCore_dense : Dense (smoothCore : Set Space) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,Submodule.topologicalClosure_eq_top_iff]
  apply le_antisymm
  · intro v hv
    change v = 0
    let ν : Measure ℂ := Measure.map UpperHalfPlane.coe measure
    let V : ℂ → ℂ := fun z => v (UpperHalfPlane.ofComplex z)
    have hV : MemLp V 2 ν := by
      apply UpperHalfPlane.measurableEmbedding_coe.memLp_map_measure_iff.mpr
      simpa only [V,Function.comp_def,UpperHalfPlane.ofComplex_apply] using Lp.memLp v
    have ht : ∀ (g : ℂ → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ interiorChart →
        ∫ z, g z • V z ∂ν = 0 := by
      intro g hg hk hs
      let G : ℂ → ℂ := fun z => (g z : ℂ)
      have hG : ContDiff ℝ ∞ G := Complex.ofRealCLM.contDiff.comp hg
      have hsupport : Function.support G ⊆ Function.support g := by
        intro z hz
        simpa only [G,Function.mem_support,Complex.ofReal_ne_zero] using hz
      have hGK : HasCompactSupport G := hk.mono hsupport
      have hGS : tsupport G ⊆ interiorChart := (closure_mono hsupport).trans hs
      let t : Space := (restricted_memLp G hG hGK).toLp (fun z : UpperHalfPlane => G z)
      have hzero : inner ℂ t v = 0 :=
        (Submodule.mem_orthogonal _ _).mp hv t (interior_test_mem_smoothCore G hG hGK hGS)
      rw [L2.inner_def] at hzero
      rw [UpperHalfPlane.measurableEmbedding_coe.integral_map]
      calc
        _ = ∫ z, inner ℂ (t z) (v z) ∂measure := by
          apply integral_congr_ae
          filter_upwards [(restricted_memLp G hG hGK).coeFn_toLp] with z hz
          simp only [V,UpperHalfPlane.ofComplex_apply]
          rw [hz]
          simp [G,Complex.real_smul,mul_comm]
        _ = 0 := hzero
    have hz := interiorChart_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hV.integrable (by norm_num)).locallyIntegrable.locallyIntegrableOn _) ht
    have hz' := UpperHalfPlane.measurableEmbedding_coe.ae_map_iff.mp hz
    apply Lp.ext
    filter_upwards [hz',ae_mem_interior,Lp.coeFn_zero ℂ 2 measure] with z hzero hz h0
    rw [h0]
    simpa only [V,UpperHalfPlane.ofComplex_apply,Pi.zero_apply] using hzero ⟨z,hz,rfl⟩
  · exact bot_le

end
end RHTower.D4BMModularCore

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff
namespace RHTower.D4BMModularCore
noncomputable section

/-- The literal derivative in a hyperbolic orthonormal-frame direction: use v=1 or v=I. -/
def weightedDeriv (v : ℂ) (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  (z.im : ℂ)*fderiv ℝ (f ∘ UpperHalfPlane.ofComplex) (z:ℂ) v

/-- Real chart smoothness implies continuity on the actual upper half-plane. -/
theorem ChartSmooth.continuous {f : UpperHalfPlane → ℂ} (hf : ChartSmooth f) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have h := (hf z).continuousAt.comp UpperHalfPlane.continuous_coe.continuousAt
  simpa only [Function.comp_def,UpperHalfPlane.ofComplex_apply] using h

/-- The actual weighted derivatives of every smooth modular-core field are continuous. -/
theorem weightedDeriv_continuous (v : ℂ) (f : UpperHalfPlane → ℂ) (hf : ChartSmooth f) :
    Continuous (weightedDeriv v f) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hd : ContinuousAt (fun w : ℂ => fderiv ℝ (f ∘ UpperHalfPlane.ofComplex) w v) (z:ℂ) :=
    ((hf z).fderiv_right (m := 0) (by simp)).continuousAt.clm_apply continuousAt_const
  have hy : ContinuousAt (fun w : UpperHalfPlane => (w.im : ℂ)) z :=
    Complex.ofRealCLM.continuous.continuousAt.comp UpperHalfPlane.continuous_im.continuousAt
  exact hy.mul (hd.comp UpperHalfPlane.continuous_coe.continuousAt)

private theorem weightedDeriv_zero_off_compact (v : ℂ) (f : UpperHalfPlane → ℂ)
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hk : ∀ z ∈ ModularGroup.fd, z ∉ K → f z = 0)
    (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fdo) (hn : z ∉ K) :
    weightedDeriv v f z = 0 := by
  have he : f =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [(ModularGroup.isOpen_fdo.inter hK.isClosed.isOpen_compl).mem_nhds ⟨hz,hn⟩] with w hw
    exact hk w (ModularGroup.fdo_subset_fd hw.1) hw.2
  have hc := (UpperHalfPlane.contMDiffAt_ofComplex (n := 0) z.im_pos).continuousAt
  have he' : f ∘ UpperHalfPlane.ofComplex =ᶠ[𝓝 (z:ℂ)] (fun _ => 0) :=
    by
      change ∀ᶠ w in 𝓝 (z:ℂ), f (UpperHalfPlane.ofComplex w) = 0
      exact hc.eventually (p := fun y : UpperHalfPlane => f y = (0:ℂ))
        (by
          rw [UpperHalfPlane.ofComplex_apply]
          filter_upwards [he] with w hw
          exact hw)
  unfold weightedDeriv
  rw [he'.fderiv_eq]
  simp

/-- Compact quotient support gives actual L² membership of the scalar core field. -/
theorem core_field_memLp (f : UpperHalfPlane → ℂ) (hf : ChartSmooth f) (hk : CellCompact f) :
    MemLp f 2 measure := by
  obtain ⟨K,hK,hk⟩ := hk
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hf.continuous.continuousOn
  apply MemLp.of_bound hf.continuous.aestronglyMeasurable (max C 0)
  filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
  by_cases hn : z ∈ K
  · exact (hC z hn).trans (le_max_left _ _)
  · rw [hk z hz hn,norm_zero]
    exact le_max_right _ _

/-- Both literal orthonormal-frame derivatives of every full modular-core field belong to
its actual invariant L² space; finite energy is proved rather than supplied. -/
theorem weightedDeriv_memLp (v : ℂ) (f : UpperHalfPlane → ℂ) (hf : ChartSmooth f)
    (hk : CellCompact f) : MemLp (weightedDeriv v f) 2 measure := by
  have hd := weightedDeriv_continuous v f hf
  obtain ⟨K,hK,hk⟩ := hk
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hd.continuousOn
  apply MemLp.of_bound hd.aestronglyMeasurable (max C 0)
  filter_upwards [ae_mem_interior] with z hz
  by_cases hn : z ∈ K
  · exact (hC z hn).trans (le_max_left _ _)
  · rw [weightedDeriv_zero_off_compact v f hK hk z hz hn,norm_zero]
    exact le_max_right _ _

end
end RHTower.D4BMModularCore

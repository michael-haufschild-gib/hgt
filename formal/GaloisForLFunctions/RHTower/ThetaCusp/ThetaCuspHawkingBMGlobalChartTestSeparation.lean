import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCompactTestUnfolding
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
The admitted modular core contains a nonzero test at every point, including seams and elliptic points.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff
namespace RHTower.D4BMModularCore
noncomputable section

/-- A compact smooth planar test supported in positive height defines an actual
upper-half-plane chart test, without any modular-interior support condition. -/
def CompactChartTest.ofPlanar (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) (hk : HasCompactSupport f)
    (hs : tsupport f ⊆ {z : ℂ | 0 < z.im}) : CompactChartTest where
  field z := f (z:ℂ)
  smooth := by
    intro z
    apply hf.contDiffAt.congr_of_eventuallyEq
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply,UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  compact := by
    have hr : tsupport f ⊆ Set.range UpperHalfPlane.coe := by
      simpa only [UpperHalfPlane.range_coe] using hs
    have hc := UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.isInducing.isCompact_preimage' hk hr
    apply hc.of_isClosed_subset isClosed_closure
    apply closure_minimal
    · intro z hz
      exact subset_tsupport f hz
    · exact isClosed_closure.preimage UpperHalfPlane.continuous_coe

/-- The actual compact chart-test family contains a nonnegative test equal to one
at every upper-half-plane point, including points on either seam or fixed by elliptic elements. -/
theorem exists_compact_chart_test_at (z : UpperHalfPlane) :
    ∃ g : CompactChartTest, g.field z = 1 ∧ ∀ w, 0 ≤ (g.field w).re := by
  obtain ⟨b,hb,hc,hd,hr,he⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  let f : ℂ → ℂ := Complex.ofRealCLM ∘ b
  have hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp hd
  have hk : HasCompactSupport f := hc.comp_left rfl
  have hs : tsupport f ⊆ {w : ℂ | 0 < w.im} := by
    apply Subset.trans _ hb
    exact closure_mono (by intro w hw; simpa [f] using hw)
  refine ⟨CompactChartTest.ofPlanar f hf hk hs,?_,?_⟩
  · change (b (z:ℂ) : ℂ) = 1
    simp [he]
  · intro w
    change 0 ≤ ((b (w:ℂ) : ℂ)).re
    exact (hr (Set.mem_range_self _)).1

/-- The admitted full modular core has a nonzero test at every point. Stabilizer
multiplicity is retained by the actual periodization, rather than canceled or divided away. -/
theorem exists_periodized_core_nonzero (z : UpperHalfPlane) :
    ∃ g : CompactChartTest, 1 ≤ (g.coreField.field z).re ∧ g.coreField.field z ≠ 0 := by
  obtain ⟨g,hg,hn⟩ := exists_compact_chart_test_at z
  have hs := compact_test_orbit_summable g.field g.compact z
  have hreal := (Complex.hasSum_re hs.hasSum).summable
  have hle := hreal.le_tsum (1 : PSL2Z) (fun γ _ => hn (γ • z))
  have hp : 1 ≤ (g.coreField.field z).re := by
    change 1 ≤ (periodize g.field z).re
    simpa only [periodize,Complex.re_tsum hs,one_smul,hg,Complex.one_re] using hle
  refine ⟨g,hp,?_⟩
  intro hz
  rw [hz,Complex.zero_re] at hp
  exact (not_le_of_gt (show (0:ℝ) < 1 by norm_num)) hp

end
end RHTower.D4BMModularCore

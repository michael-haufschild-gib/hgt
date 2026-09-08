import GaloisForLFunctions.RHTower.SelbergLocalTestGreen
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Compact test transport between the upper half-plane and the complex plane

Zero extension of an actual compact continuous upper-half-plane test is globally
continuous, has compact support at positive height, and respects the ordered real
linear operations. Restriction of a supported planar test is compact and its zero
extension recovers the original test exactly.
-/

open Set Topology UpperHalfPlane
open scoped CompactlySupported
namespace GaloisForLFunctions.RHTower.SelbergUpperHalfPlaneCompactTests
noncomputable section

/-- The actual partial inverse of the upper-half-plane inclusion is continuous on its source. -/
theorem ofComplex_continuousOn : ContinuousOn ofComplex {z : ℂ | 0 < z.im} := by
  have hs : ofComplex.source = {z : ℂ | 0 < z.im} := by
    change (isOpenEmbedding_coe.toOpenPartialHomeomorph UpperHalfPlane.coe).target = _
    rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, range_coe]
  exact hs ▸ ofComplex.continuousOn

/-- Extend an actual compact upper-half-plane test by zero outside positive height. -/
def zeroExtend (g : C_c(ℍ, ℝ)) (z : ℂ) : ℝ :=
  if 0 < z.im then g (ofComplex z) else 0

/-- Zero extension retains every original upper-half-plane test value. -/
theorem zeroExtend_apply (g : C_c(ℍ, ℝ)) (z : ℍ) : zeroExtend g z = g z := by
  simp only [zeroExtend, coe_im, z.im_pos, if_true, ofComplex_apply]

/-- The zero extension has topological support in the compact image of the original support. -/
theorem zeroExtend_tsupport_subset (g : C_c(ℍ, ℝ)) :
    tsupport (zeroExtend g) ⊆ ((↑) : ℍ → ℂ) '' tsupport g := by
  apply closure_minimal _ (g.hasCompactSupport.image continuous_coe).isClosed
  intro z hz
  by_cases hy : 0 < z.im
  · refine ⟨ofComplex z, subset_tsupport g ?_, ?_⟩
    · simpa only [Function.mem_support, zeroExtend, if_pos hy] using hz
    · rw [ofComplex_apply_of_im_pos hy]
  · exact (hz (by simp only [zeroExtend, if_neg hy])).elim

/-- The complete topological support of a zero extension lies at positive height. -/
theorem zeroExtend_support (g : C_c(ℍ, ℝ)) : tsupport (zeroExtend g) ⊆ {z : ℂ | 0 < z.im} := by
  intro z hz
  obtain ⟨w, _, rfl⟩ := zeroExtend_tsupport_subset g hz
  exact w.im_pos

/-- Zero extension preserves genuine compact support. -/
theorem zeroExtend_compact (g : C_c(ℍ, ℝ)) : HasCompactSupport (zeroExtend g) :=
  (g.hasCompactSupport.image continuous_coe).of_isClosed_subset isClosed_closure
    (zeroExtend_tsupport_subset g)

/-- The zero extension is globally continuous, including at the boundary of the upper half-plane. -/
theorem zeroExtend_continuous (g : C_c(ℍ, ℝ)) : Continuous (zeroExtend g) := by
  have h : ContinuousOn (zeroExtend g) {z : ℂ | 0 < z.im} := by
    apply (g.continuous.comp_continuousOn ofComplex_continuousOn).congr
    intro z hz
    change 0 < z.im at hz
    change (if 0 < z.im then g (ofComplex z) else 0) = g (ofComplex z)
    rw [if_pos hz]
  exact h.continuous_of_tsupport_subset isOpen_upperHalfPlaneSet (zeroExtend_support g)

/-- Zero extension respects test addition. -/
theorem zeroExtend_add (g h : C_c(ℍ, ℝ)) :
    zeroExtend (g + h) = fun z => zeroExtend g z + zeroExtend h z := by
  funext z
  by_cases hz : 0 < z.im <;> simp [zeroExtend, hz]

/-- Zero extension respects real scalar multiplication. -/
theorem zeroExtend_smul (c : ℝ) (g : C_c(ℍ, ℝ)) :
    zeroExtend (c • g) = fun z => c * zeroExtend g z := by
  funext z
  by_cases hz : 0 < z.im <;> simp [zeroExtend, hz]

/-- Zero extension preserves pointwise test ordering. -/
theorem zeroExtend_mono {g h : C_c(ℍ, ℝ)} (hgh : g ≤ h) :
    ∀ z, zeroExtend g z ≤ zeroExtend h z := by
  intro z
  by_cases hz : 0 < z.im
  · simp only [zeroExtend, if_pos hz]
    exact hgh _
  · simp only [zeroExtend, if_neg hz, le_refl]

/-- A compact planar test supported at positive height restricts to a genuinely compact upper-half-plane test. -/
theorem restricted_compact {phi : ℂ → ℝ} (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) :
    HasCompactSupport (fun z : ℍ => phi z) := by
  have hK : IsCompact (ofComplex '' tsupport phi) :=
    hc.image_of_continuousOn (ofComplex_continuousOn.mono hs)
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hK.isClosed
  intro z hz
  exact ⟨(z : ℂ), subset_tsupport phi hz, ofComplex_apply z⟩

/-- Restrict an admissible planar continuous test to the actual upper half-plane. -/
def restrictCompact (phi : ℂ → ℝ) (hp : Continuous phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) : C_c(ℍ, ℝ) :=
  ⟨⟨fun z => phi z, hp.comp continuous_coe⟩, restricted_compact hc hs⟩

/-- Restriction followed by zero extension recovers the original admissible planar test exactly. -/
theorem zeroExtend_restrictCompact (phi : ℂ → ℝ) (hp : Continuous phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) : zeroExtend (restrictCompact phi hp hc hs) = phi := by
  funext z
  by_cases hz : 0 < z.im
  · change (if 0 < z.im then phi (ofComplex z : ℂ) else 0) = phi z
    rw [if_pos hz, ofComplex_apply_of_im_pos hz]
  · rw [zeroExtend, if_neg hz]
    exact (image_eq_zero_of_notMem_tsupport (fun h => hz (hs h))).symm

end
end GaloisForLFunctions.RHTower.SelbergUpperHalfPlaneCompactTests

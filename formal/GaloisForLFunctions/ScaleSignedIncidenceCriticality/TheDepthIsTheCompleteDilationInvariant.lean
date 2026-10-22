import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheSquareRootPrecisionLaw

/-!
# The depth is the complete dilation invariant

A lattice datum has two coordinates, a scale and a depth (`ScaleDepthDatum`). Rescaling the scale
and leaving the depth fixed is the field's dilation action, and this module shows the depth is its
*complete* invariant: two data lie on one orbit exactly when their depths agree
(`dilationEquiv_iff_sdDepth_eq`). Any reading that resolves the depth must therefore be constant on
orbits and separate them.

With both coordinates free the aperture certificate does neither. The dense end of the family —
scale at least twice the aperture — carries the maximal depth and satisfies the certificate for
free, so it lies in every shadow and the resolution limit returns to the trivial `½`
(`resolutionLimit_sdDepth_scaleDepthReading`), at every aperture and every coercivity level. A
single aperture cannot see the depth without a scale bound, however strong its certificate.

Both halves of the field answer this. `TheSquareRootPrecisionLaw` exhibits the scale-free quantity
the action admits — the exponential rate of the deficit, whose infimum is the depth — and
`TwoAliasingBandsDetermineTheDepth` shows the obstruction above is an artefact of using *one*
aperture: two determine the depth with no scale input at all.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The dilation action -/

/-- Two data lie on one dilation orbit: same depth, scales related by a positive factor. -/
def DilationEquiv (p q : ScaleDepthDatum) : Prop :=
  ∃ t : ℝ, 0 < t ∧ sdScale q = t * sdScale p ∧ sdDepth q = sdDepth p

/-- **The depth is the complete invariant of the dilation action.** -/
theorem dilationEquiv_iff_sdDepth_eq (p q : ScaleDepthDatum) :
    DilationEquiv p q ↔ sdDepth q = sdDepth p := by
  refine ⟨fun hd => ?_, fun h => ?_⟩
  · obtain ⟨-, -, -, h⟩ := hd
    exact h
  have hp : (0 : ℝ) < sdScale p := p.2.1
  have hq : (0 : ℝ) < sdScale q := q.2.1
  refine ⟨sdScale q / sdScale p, div_pos hq hp, ?_, h⟩
  field_simp

theorem dilationEquiv_refl (p : ScaleDepthDatum) : DilationEquiv p p :=
  (dilationEquiv_iff_sdDepth_eq p p).mpr rfl

/-- A reading resolves the depth only if it separates dilation orbits. -/
theorem sdDepth_eq_of_dilationEquiv {p q : ScaleDepthDatum} (h : DilationEquiv p q) :
    sdDepth q = sdDepth p := (dilationEquiv_iff_sdDepth_eq p q).mp h

/-! ### 2. One aperture resolves no depth -/

/-- The maximal-depth datum that satisfies the certificate for free at aperture `a`. -/
noncomputable def denseMaximalDatum (a : ℝ) (ha : 0 < a) : ScaleDepthDatum :=
  ⟨(2 * a + 1, 1 / 2), by linarith, by norm_num, le_rfl⟩

theorem sdDepth_denseMaximalDatum {a : ℝ} (ha : 0 < a) :
    sdDepth (denseMaximalDatum a ha) = 1 / 2 := rfl

theorem scaleDepthReading_denseMaximalDatum {a η : ℝ} (ha : 0 < a) (hη : 0 ≤ η) :
    scaleDepthReading a η (denseMaximalDatum a ha) :=
  scaleDepthReading_of_dense hη _ (by show 2 * a ≤ 2 * a + 1; linarith)

/-- **Depth resolution collapses without a scale bound.** At every aperture and every level, the
resolution limit of the depth on the two-coordinate family is the trivial `½`. -/
theorem resolutionLimit_sdDepth_scaleDepthReading {a η : ℝ} (ha : 0 < a) (hη : 0 ≤ η)
    {p₀ : ScaleDepthDatum} (hp₀ : scaleDepthReading a η p₀) :
    resolutionLimit sdDepth (scaleDepthReading a η) p₀ = 1 / 2 := by
  refine resolutionLimit_eq_of_mem_shadow_of_max (fun x => x.2.2.2) ?_
    (sdDepth_denseMaximalDatum ha)
  exact propext (iff_of_true (scaleDepthReading_denseMaximalDatum ha hη) hp₀)

/-- **What a resolving reading must be.** The depth is the complete dilation invariant, and the
single-aperture certificate resolves none of it. -/
theorem theDilationRequirement {a η : ℝ} (ha : 0 < a) (hη : 0 ≤ η)
    {p₀ : ScaleDepthDatum} (hp₀ : scaleDepthReading a η p₀) :
    (∀ p q : ScaleDepthDatum, DilationEquiv p q ↔ sdDepth q = sdDepth p) ∧
      resolutionLimit sdDepth (scaleDepthReading a η) p₀ = 1 / 2 :=
  ⟨dilationEquiv_iff_sdDepth_eq, resolutionLimit_sdDepth_scaleDepthReading ha hη hp₀⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality

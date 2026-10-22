import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheWallGatesOfAResolvingReading
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.CoercivityAtABoundedApertureIsStillBlind
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheNodeFaceUnitIsAReciprocalPrimePower

/-!
# The floor theorem

Every exact limit in this programme has been proved twice over: once as an upper bound, because the
invariant is bounded on the whole class, and once as a lower bound, by exhibiting a witness in the
shadow that attains the bound. The two halves are always the same two lines, and this module
replaces them by one lemma.

**The floor theorem** (`resolutionLimit_eq_of_mem_shadow_of_max`): if `I ≤ M` everywhere and some
datum of the shadow attains `M`, then the limit is `M`. That is the entire mechanism behind the
field's floors: a floor is the statement that *the fibre of the reduction realises the maximum of
the invariant*. Nothing else is involved — no property of the Weil form, no aperture, no arithmetic.

Two consequences make it a tool rather than a tidy-up.

* `resolutionLimit_eq_of_factors_of_max` — a reduction followed by any reading inherits the floor,
  because a witness in the finer shadow lies in the coarser one. Future faces need only produce a
  fibre-maximal witness; the coarsening is free.
* The field's entries become one-line instances: `resolutionLimit_width_apertureGain'` (bounded
  aperture at any coercivity level), `resolutionLimit_width_heightReading'` (bounded height),
  `resolutionLimit_nodeScale_asymptotic'` (every density reading on node sets).

The theorem also says exactly what would be needed to break a floor: not a better estimate, but a
shadow whose maximum is smaller — that is, a reading whose fibres *fail* to realise the maximum.
Each positive result of the programme (the productive seam, the trans-Nyquist level, the uniform
deficit) is of that form.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower GaloisForLFunctions.BiScaleUncertainty

set_option autoImplicit false

variable {D F O : Type*}

/-! ### 1. The theorem -/

/-- **The floor theorem.** A bounded invariant whose maximum is attained inside the shadow has that
maximum as its resolution limit. -/
theorem resolutionLimit_eq_of_mem_shadow_of_max {I : D → ℝ} {r : D → O} {d e : D} {M : ℝ}
    (hub : ∀ x : D, I x ≤ M) (he : e ∈ shadow r d) (hval : I e = M) :
    resolutionLimit I r d = M := by
  have hbdd : BddAbove (I '' shadow r d) := ⟨M, by rintro x ⟨y, -, rfl⟩; exact hub y⟩
  refine le_antisymm (csSup_le (shadow_image_nonempty I r d) ?_) ?_
  · rintro x ⟨y, -, rfl⟩
    exact hub y
  · exact hval ▸ le_csSup hbdd ⟨e, he, rfl⟩

/-- **Coarsening is free.** A witness for the floor of a reduction is a witness for every reading
of that reduction's value. -/
theorem resolutionLimit_eq_of_factors_of_max {I : D → ℝ} {f : D → F} {r : F → O} {d e : D}
    {M : ℝ} (hub : ∀ x : D, I x ≤ M) (he : f e = f d) (hval : I e = M) :
    resolutionLimit I (r ∘ f) d = M :=
  resolutionLimit_eq_of_mem_shadow_of_max hub (show r (f e) = r (f d) by rw [he]) hval

/-! ### 2. The field's entries as instances -/

/-- The bounded-aperture floor, at every coercivity level. -/
theorem resolutionLimit_width_apertureGain' {a η : ℝ} (ha : 0 < a) {Z : TemperedZeroConfig}
    (hZ : apertureGain a η Z) : resolutionLimit width (apertureGain a η) Z = 1 / 2 := by
  obtain ⟨Z', hw', hpos'⟩ := exists_width_eq_half_apertureGain ha η
  exact resolutionLimit_eq_of_mem_shadow_of_max width_le_half
    (propext (iff_of_true hpos' hZ)) hw'

/-- The bounded-height floor. -/
theorem resolutionLimit_width_heightReading' {L T : ℝ} (hL : 0 < L) :
    resolutionLimit width (heightReading T) (onLineLattice hL) = 1 / 2 :=
  resolutionLimit_eq_of_mem_shadow_of_max width_le_half
    (heightReading_isolatedPairConfig hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl T)
    (width_latticeWithPairAbove_half hL T)

/-- The node floor, for every asymptotic reading. -/
theorem resolutionLimit_nodeScale_asymptotic' {r : Set ℕ → O} (h : AsymptoticReading r) :
    resolutionLimit nodeScale r {n : ℕ | IsPrimePow n} = 1 / 2 :=
  resolutionLimit_eq_of_mem_shadow_of_max nodeScale_le_half
    (invisible_deleteNode_of_asymptoticReading h 2 _) nodeScale_deleteNode_two

/-! ### 3. What a floor is -/

/-- **A floor is fibre-maximality.** The three entries above, and every other floor of the field,
are the same statement about different reductions: the shadow of the reading contains a datum at
which the invariant is maximal. Breaking a floor means producing a reading whose shadow does not. -/
theorem aFloorIsFibreMaximality {a η : ℝ} (ha : 0 < a) {Z : TemperedZeroConfig}
    (hZ : apertureGain a η Z) {L T : ℝ} (hL : 0 < L) {r : Set ℕ → O}
    (hr : AsymptoticReading r) :
    resolutionLimit width (apertureGain a η) Z = 1 / 2 ∧
      resolutionLimit width (heightReading T) (onLineLattice hL) = 1 / 2 ∧
      resolutionLimit nodeScale r {n : ℕ | IsPrimePow n} = 1 / 2 :=
  ⟨resolutionLimit_width_apertureGain' ha hZ, resolutionLimit_width_heightReading' hL,
    resolutionLimit_nodeScale_asymptotic' hr⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality

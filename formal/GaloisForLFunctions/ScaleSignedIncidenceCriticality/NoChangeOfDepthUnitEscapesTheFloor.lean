import GaloisForLFunctions.ScaleSignedIncidenceCriticality.CoercivityAtABoundedApertureIsStillBlind
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionIntervalIsTheWholeRange

/-!
# No change of depth unit escapes the floor

Faced with a floor of `½` in the width unit, the natural move is to change the unit: measure the
depth by `δ²`, by a Hodge exponent, by `log(1/δ)`, by any reparametrisation that might turn the
trivial bound into a useful one. It cannot work, and this module says so once for all units at
once.

The reason is structural. The shadow of a bounded-aperture certificate is, in the lattice
parameters, a *product*: a constraint on the scale together with **every** depth. Any invariant
that is a monotone function of the depth is therefore read on the whole interval `[0, ½]`, and its
resolution limit is its value at the endpoint:

* `resolutionLimit_comp_width_apertureGain` — for every monotone `g`, every aperture `a` and every
  coercivity level `η`, the limit of `g ∘ width` is exactly `g(½)`;
* `resolutionFloor_comp_width_aperturePositivity` — and the floor is exactly `g(0)`;
* `resolutionInterval_comp_width_aperturePositivity` — so the interval is `[g(0), g(½)]`, which is
  proper whenever `g` is strictly monotone: the reading is vacuous in *every* non-degenerate unit
  (`theFloorIsUnitIndependent`).

With the seam computation, the coercivity levels and this, the finite-aperture face is closed under
all four natural strengthenings: more apertures, more height data, a larger gap, and a different
unit. The only remaining direction is the one the programme already identifies — crossing the
Nyquist aperture.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

variable {g : ℝ → ℝ}

/-! ### 1. Boundedness in an arbitrary monotone unit -/

theorem bddAbove_comp_width_image (hg : MonotoneOn g (Icc 0 (1 / 2)))
    (s : Set TemperedZeroConfig) : BddAbove ((g ∘ width) '' s) := by
  refine ⟨g (1 / 2), ?_⟩
  rintro x ⟨Z, -, rfl⟩
  exact hg ⟨width_nonneg Z, width_le_half Z⟩ ⟨by norm_num, le_rfl⟩ (width_le_half Z)

theorem bddBelow_comp_width_image (hg : MonotoneOn g (Icc 0 (1 / 2)))
    (s : Set TemperedZeroConfig) : BddBelow ((g ∘ width) '' s) := by
  refine ⟨g 0, ?_⟩
  rintro x ⟨Z, -, rfl⟩
  exact hg ⟨le_rfl, by norm_num⟩ ⟨width_nonneg Z, width_le_half Z⟩ (width_nonneg Z)

/-! ### 2. The limit in an arbitrary monotone unit -/

/-- **Every monotone depth unit has the trivial limit.** At every aperture and every coercivity
level, a certificate reads `g ∘ width` only up to `g(½)`. -/
theorem resolutionLimit_comp_width_apertureGain (hg : MonotoneOn g (Icc 0 (1 / 2))) {a η : ℝ}
    (ha : 0 < a) {Z : TemperedZeroConfig} (hZ : apertureGain a η Z) :
    resolutionLimit (g ∘ width) (apertureGain a η) Z = g (1 / 2) := by
  obtain ⟨Z', hw', hpos'⟩ := exists_width_eq_half_apertureGain ha η
  refine le_antisymm (csSup_le (shadow_image_nonempty (g ∘ width) (apertureGain a η) Z) ?_) ?_
  · rintro x ⟨W, -, rfl⟩
    exact hg ⟨width_nonneg W, width_le_half W⟩ ⟨by norm_num, le_rfl⟩ (width_le_half W)
  · have hmem : Z' ∈ shadow (apertureGain a η) Z := propext (iff_of_true hpos' hZ)
    calc g (1 / 2) = (g ∘ width) Z' := by simp [Function.comp, hw']
      _ ≤ resolutionLimit (g ∘ width) (apertureGain a η) Z :=
          le_csSup (bddAbove_comp_width_image hg _) ⟨Z', hmem, rfl⟩

/-- The same for bare positivity, the level-`0` case. -/
theorem resolutionLimit_comp_width_aperturePositivity (hg : MonotoneOn g (Icc 0 (1 / 2)))
    {a : ℝ} (ha : 0 < a) {Z : TemperedZeroConfig} (hZ : aperturePositivity a Z) :
    resolutionLimit (g ∘ width) (aperturePositivity a) Z = g (1 / 2) := by
  obtain ⟨Z', hw', hpos'⟩ := exists_width_eq_half_aperturePositivity ha
  refine le_antisymm (csSup_le (shadow_image_nonempty (g ∘ width) (aperturePositivity a) Z) ?_) ?_
  · rintro x ⟨W, -, rfl⟩
    exact hg ⟨width_nonneg W, width_le_half W⟩ ⟨by norm_num, le_rfl⟩ (width_le_half W)
  · have hmem : Z' ∈ shadow (aperturePositivity a) Z := propext (iff_of_true hpos' hZ)
    calc g (1 / 2) = (g ∘ width) Z' := by simp [Function.comp, hw']
      _ ≤ resolutionLimit (g ∘ width) (aperturePositivity a) Z :=
          le_csSup (bddAbove_comp_width_image hg _) ⟨Z', hmem, rfl⟩

/-! ### 3. The floor in an arbitrary monotone unit -/

/-- **And the floor is the other endpoint.** The on-line lattice shares every aperture
certificate, so the reading never bounds `g ∘ width` above `g(0)`. -/
theorem resolutionFloor_comp_width_aperturePositivity (hg : MonotoneOn g (Icc 0 (1 / 2)))
    {a : ℝ} {Z : TemperedZeroConfig} (hZ : aperturePositivity a Z) :
    resolutionFloor (g ∘ width) (aperturePositivity a) Z = g 0 := by
  refine le_antisymm ?_
    ((certifiesLower_iff_le_resolutionFloor (bddBelow_comp_width_image hg _)).mp fun W _ =>
      hg ⟨le_rfl, by norm_num⟩ ⟨width_nonneg W, width_le_half W⟩ (width_nonneg W))
  calc resolutionFloor (g ∘ width) (aperturePositivity a) Z
      ≤ (g ∘ width) (onLineLattice (by norm_num : (0 : ℝ) < 1)) :=
        csInf_le (bddBelow_comp_width_image hg _)
          ⟨_, onLineLattice_mem_shadow_aperturePositivity hZ, rfl⟩
    _ = g 0 := by simp [Function.comp, width_onLineLattice]

/-- **The interval in an arbitrary monotone unit.** -/
theorem resolutionInterval_comp_width_aperturePositivity (hg : MonotoneOn g (Icc 0 (1 / 2)))
    {a : ℝ} (ha : 0 < a) {Z : TemperedZeroConfig} (hZ : aperturePositivity a Z) :
    resolutionInterval (g ∘ width) (aperturePositivity a) Z = Icc (g 0) (g (1 / 2)) := by
  rw [resolutionInterval, resolutionFloor_comp_width_aperturePositivity hg hZ,
    resolutionLimit_comp_width_aperturePositivity hg ha hZ]

/-! ### 4. Unit independence -/

/-- **The floor is unit independent.** In any strictly monotone depth unit the interval left open
by a finite-aperture certificate is still a nondegenerate interval reaching both ends of the
possible range: no reparametrisation of the depth turns the certificate into a bound. -/
theorem theFloorIsUnitIndependent {a : ℝ} (ha : 0 < a) {Z : TemperedZeroConfig}
    (hZ : aperturePositivity a Z) (hg : StrictMonoOn g (Icc 0 (1 / 2))) :
    resolutionInterval (g ∘ width) (aperturePositivity a) Z = Icc (g 0) (g (1 / 2)) ∧
      g 0 < g (1 / 2) :=
  ⟨resolutionInterval_comp_width_aperturePositivity hg.monotoneOn ha hZ,
    hg ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩ (by norm_num)⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality

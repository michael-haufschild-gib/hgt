import GaloisForLFunctions.ScaleSignedIncidenceCriticality.CoercivityAtABoundedApertureIsStillBlind
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionIntervalIsTheWholeRange

/-!
# The approximate problem is no easier

The programme's gates concern the exact property `width = 0`. A natural hope is that the
approximate property `width ≤ ε` is cheaper: one would settle for a zero-free strip rather than the
critical line. In the admissibility calculus the hope is empty, and the failure has a sharp
threshold.

A configuration certified at aperture `a` shares that certificate both with the on-line lattice,
of width `0`, and with the depth-`½` lattice (`onLineLattice_mem_shadow_aperturePositivity`,
`exists_width_eq_half_apertureGain`). So for every `ε < ½` the two verdicts differ inside one
shadow and no bounded-aperture reading decides `width ≤ ε`
(`not_resolves_widthLe_apertureGain`), at any coercivity level; while for `ε ≥ ½` the property is
vacuously true and *every* reading decides it (`resolves_widthLe_of_half_le`). Hence
(`theApproximationThreshold`) the set of tolerances a bounded reading can decide is exactly
`[½, ∞)`.

So `½` is not only the resolution limit of the width but the exact **threshold of the decision
problem**: relaxing the target from the critical line to any strip of half-width below `½` buys
nothing at all. The same holds on the height face (`not_resolves_widthLe_heightReading`). A
mechanism must aim at the exact statement, or supply data of a different kind — mass, dilution, a
trans-Nyquist level — not a weaker target.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. Above the threshold every reading decides -/

/-- For a tolerance of at least `½` the property is vacuously true, so any reading decides it. -/
theorem resolves_widthLe_of_half_le {O : Type*} (r : TemperedZeroConfig → O) {ε : ℝ}
    (hε : 1 / 2 ≤ ε) : Resolves r (fun W => width W ≤ ε) :=
  fun _ _ _ => iff_of_true ((width_le_half _).trans hε) ((width_le_half _).trans hε)

/-! ### 2. Below the threshold none does -/

/-- **No bounded-aperture certificate decides any nontrivial tolerance.** The on-line lattice and
the depth-`½` lattice share the certificate and give opposite verdicts. -/
theorem not_resolves_widthLe_aperturePositivity {a ε : ℝ} (ha : 0 < a) (hε : 0 ≤ ε)
    (hε' : ε < 1 / 2) {Z : TemperedZeroConfig} (hZ : aperturePositivity a Z) :
    ¬ Resolves (aperturePositivity a) (fun W => width W ≤ ε) := by
  obtain ⟨Z', hw', hpos'⟩ := exists_width_eq_half_aperturePositivity ha
  intro hres
  have hmem : Z' ∈ shadow (aperturePositivity a) Z := propext (iff_of_true hpos' hZ)
  have hmemL : onLineLattice (by norm_num : (0 : ℝ) < 1) ∈ shadow (aperturePositivity a) Z :=
    onLineLattice_mem_shadow_aperturePositivity hZ
  have hline0 : width (onLineLattice (by norm_num : (0 : ℝ) < 1)) ≤ ε := by
    rw [width_onLineLattice]; exact hε
  have hZle : width Z ≤ ε := (hres Z _ hmemL).mp hline0
  have hZ'le : width Z' ≤ ε := (hres Z Z' hmem).mpr hZle
  rw [hw'] at hZ'le
  linarith

/-- **The same at every coercivity level**, for a datum inside the strip. -/
theorem not_resolves_widthLe_apertureGain {a η ε : ℝ} (ha : 0 < a) (hε' : ε < 1 / 2)
    {Z : TemperedZeroConfig} (hZ : apertureGain a η Z) (hw : width Z ≤ ε) :
    ¬ Resolves (apertureGain a η) (fun W => width W ≤ ε) := by
  obtain ⟨Z', hw', hpos'⟩ := exists_width_eq_half_apertureGain ha η
  intro hres
  have hmem : Z' ∈ shadow (apertureGain a η) Z := propext (iff_of_true hpos' hZ)
  have hZ'le : width Z' ≤ ε := (hres Z Z' hmem).mpr hw
  rw [hw'] at hZ'le
  linarith

/-- **The same on the height face.** -/
theorem not_resolves_widthLe_heightReading {L T ε : ℝ} (hL : 0 < L) (hε : 0 ≤ ε)
    (hε' : ε < 1 / 2) : ¬ Resolves (heightReading T) (fun W => width W ≤ ε) := by
  intro hres
  have hmem : latticeWithPairAbove hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl T ∈
      shadow (heightReading T) (onLineLattice hL) :=
    heightReading_isolatedPairConfig hL _ _ T
  have h0 : width (onLineLattice hL) ≤ ε := by rw [width_onLineLattice]; exact hε
  have h1 : width (latticeWithPairAbove hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl T) ≤ ε :=
    (hres (onLineLattice hL) _ hmem).mpr h0
  rw [width_latticeWithPairAbove_half hL T] at h1
  linarith

/-! ### 3. The threshold -/

/-- **The approximation threshold is `½`.** A bounded-aperture reading decides the tolerance `ε`
exactly when `ε ≥ ½`: every weaker target is as inaccessible as the critical line itself. -/
theorem theApproximationThreshold {a : ℝ} (ha : 0 < a) {Z : TemperedZeroConfig}
    (hZ : aperturePositivity a Z) :
    (∀ ε : ℝ, 1 / 2 ≤ ε → Resolves (aperturePositivity a) (fun W => width W ≤ ε)) ∧
      ∀ ε : ℝ, 0 ≤ ε → ε < 1 / 2 →
        ¬ Resolves (aperturePositivity a) (fun W => width W ≤ ε) :=
  ⟨fun _ hε => resolves_widthLe_of_half_le _ hε,
    fun _ hε hε' => not_resolves_widthLe_aperturePositivity ha hε hε' hZ⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality

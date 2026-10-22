import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheFloorTheorem
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionIntervalIsTheWholeRange

/-!
# Ordinate data is blind to the width

Every floor of the programme so far bounds a reading by *restricting* it — to an aperture, a height,
a radius, a density. This module floors a reading that is restricted in no way at all: the exact set
of ordinates of the configuration, at every height, with no truncation.

The doubled on-line lattice and the depth-`δ` off-line lattice of the same spacing have the **same
ordinates** (`ordinateSet_eq`), since both carriers project onto `{2πk/L}`. Their widths are `0`
and `δ`. So by the floor theorem

`resolutionLimit width ordinateSet = ½`  (`resolutionLimit_width_ordinateSet`),

and, because coarsening is free, the same holds for *anything computed from the ordinates*
(`resolutionLimit_width_ordinateDerived`): the counting function, the gaps and their statistics,
pair correlation, any moment of the spacing distribution, any density exponent.

This is a different kind of wall from the trans-Nyquist one. There the information was at infinity,
and the unbounded reading was faithful; here the reading is already unbounded and still certifies
nothing, because the ordinates carry no trace of the real parts. The width is a *horizontal*
invariant, and ordinate data is vertical. Any mechanism must therefore read the real parts — or the
Weil form, which couples them — and no amount of vertical statistics, however deep, can substitute.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The ordinate reading -/

/-- The **ordinate set** of a configuration: its zero heights, with no reference to real parts. -/
def ordinateSet (Z : TemperedZeroConfig) : Set ℝ := {t : ℝ | ∃ ρ ∈ Z.1.carrier, ρ.im = t}

theorem ordinateSet_onLineLattice {L : ℝ} (hL : 0 < L) :
    ordinateSet (onLineLattice hL) =
      Set.range (fun k : ℤ => (k : ℝ) * (2 * Real.pi / L)) := by
  ext t
  simp only [ordinateSet, mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨ρ, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, by simp [verticalLatticePoint]⟩
  · rintro ⟨k, rfl⟩
    exact ⟨verticalLatticePoint L 0 k, ⟨k, rfl⟩, by simp [verticalLatticePoint]⟩

theorem ordinateSet_offLineLattice {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ordinateSet (offLineLattice hL hδ hδ') =
      Set.range (fun k : ℤ => (k : ℝ) * (2 * Real.pi / L)) := by
  ext t
  simp only [ordinateSet, mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨ρ, (⟨k, rfl⟩ | ⟨k, rfl⟩), rfl⟩
    · exact ⟨k, by simp [verticalLatticePoint]⟩
    · exact ⟨k, by simp [verticalLatticePoint]⟩
  · rintro ⟨k, rfl⟩
    exact ⟨verticalLatticePoint L δ k, Or.inl ⟨k, rfl⟩, by simp [verticalLatticePoint]⟩

/-- **The two lattices have the same ordinates.** -/
theorem ordinateSet_eq {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ordinateSet (offLineLattice hL hδ hδ') = ordinateSet (onLineLattice hL) := by
  rw [ordinateSet_offLineLattice hL hδ hδ', ordinateSet_onLineLattice hL]

/-! ### 2. The floor -/

/-- **The exact ordinate set, at every height, has the trivial limit for the width.** -/
theorem resolutionLimit_width_ordinateSet {L : ℝ} (hL : 0 < L) :
    resolutionLimit width ordinateSet (onLineLattice hL) = 1 / 2 :=
  resolutionLimit_eq_of_mem_shadow_of_max width_le_half
    (ordinateSet_eq hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl)
    (width_offLineLattice hL (by norm_num) le_rfl)

/-- **And so does every quantity computed from the ordinates** — counting functions, gaps, spacing
statistics, correlations, density exponents. -/
theorem resolutionLimit_width_ordinateDerived {O : Type*} (r : Set ℝ → O) {L : ℝ} (hL : 0 < L) :
    resolutionLimit width (r ∘ ordinateSet) (onLineLattice hL) = 1 / 2 :=
  resolutionLimit_eq_of_factors_of_max width_le_half
    (ordinateSet_eq hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl)
    (width_offLineLattice hL (by norm_num) le_rfl)

/-- **No ordinate-only reading decides the critical line.** -/
theorem not_resolves_onLine_ordinateDerived {O : Type*} (r : Set ℝ → O) {L : ℝ} (hL : 0 < L) :
    ¬ Resolves (r ∘ ordinateSet) (fun W => width W = 0) := by
  intro hres
  have hmem : offLineLattice hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl ∈
      shadow (r ∘ ordinateSet) (onLineLattice hL) := by
    show r (ordinateSet _) = r (ordinateSet _)
    rw [ordinateSet_eq hL (by norm_num) le_rfl]
  have h0 : width (offLineLattice hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl) = 0 :=
    (hres (onLineLattice hL) _ hmem).mpr (width_onLineLattice hL)
  rw [width_offLineLattice hL (by norm_num) le_rfl] at h0
  norm_num at h0

/-- **The width is a horizontal invariant.** The ordinates determine nothing about it, at any
height and in any statistic, so a mechanism must read the real parts or the Weil form. -/
theorem theOrdinateWall {L : ℝ} (hL : 0 < L) :
    resolutionLimit width ordinateSet (onLineLattice hL) = 1 / 2 ∧
      ∀ (O : Type) (r : Set ℝ → O),
        resolutionLimit width (r ∘ ordinateSet) (onLineLattice hL) = 1 / 2 :=
  ⟨resolutionLimit_width_ordinateSet hL, fun _ r => resolutionLimit_width_ordinateDerived r hL⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality

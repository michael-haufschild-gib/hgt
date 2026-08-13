import GaloisForLFunctions.RHTower.WeightedEulerCarrierSetup

/-!
# The four carrier blocks attached to a rectangular quadrant carrier

The rectangle `Kc` inside the critical quadrant, its complex conjugate `Kcbar`, their union `Kt`,
the image `Kt'` of `Kt` under the functional-equation reflection `z ↦ 1 - z`, and the total carrier
`Ktot = Kt ∪ Kt'`.  All four have real parts in `[1 - b, b] ⊆ (0, 1)`, `Kt` and `Kt'` are separated
by the vertical strip `1 - a < Re < a`, and `Kc` and `Kcbar` are separated by the horizontal strip
`|Im| < c`.

* `RHTower.QuadrantCarrierData.Kc`, `.Kcbar`, `.Kt`, `.Kt'`, `.Ktot` and their basic properties.
-/

noncomputable section

open Complex Set

namespace RHTower

open GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

namespace QuadrantCarrierData

variable {f₂ : holoQuadrant →L[ℝ] ℝ} (D : QuadrantCarrierData f₂)

/-- The upper block. -/
def Kc : Set ℂ := rect D.a D.b D.c D.d

/-- The lower block, the conjugate of the upper one. -/
def Kcbar : Set ℂ := rect D.a D.b (-D.d) (-D.c)

/-- The right pair of blocks. -/
def Kt : Set ℂ := doubledRect D.a D.b D.c D.d

/-- The left pair of blocks, the reflection of the right pair. -/
def Kt' : Set ℂ := doubledRect (1 - D.b) (1 - D.a) D.c D.d

/-- The total carrier. -/
def Ktot : Set ℂ := D.Kt ∪ D.Kt'

theorem half_lt_b : 1 / 2 < D.b := lt_of_lt_of_le D.ha D.hab

theorem one_sub_b_pos : 0 < 1 - D.b := by have := D.hb; linarith

theorem one_sub_a_lt_a : 1 - D.a < D.a := by have := D.ha; linarith

theorem one_sub_b_le_a : 1 - D.b ≤ D.a := by
  have h1 := D.ha
  have h3 := D.hab
  linarith

theorem one_sub_a_le_b : 1 - D.a ≤ D.b := by
  have h1 := D.ha
  have h2 := D.hab
  linarith

theorem isCompact_Kc : IsCompact D.Kc := isCompact_rect _ _ _ _

theorem isCompact_Kcbar : IsCompact D.Kcbar := isCompact_rect _ _ _ _

theorem isCompact_Kt : IsCompact D.Kt :=
  isCompact_doubledRect _ _ D.hc.le D.hcd

theorem isCompact_Kt' : IsCompact D.Kt' :=
  isCompact_doubledRect _ _ D.hc.le D.hcd

theorem isCompact_Ktot : IsCompact D.Ktot := D.isCompact_Kt.union D.isCompact_Kt'

instance : CompactSpace D.Kc := isCompact_iff_compactSpace.mp D.isCompact_Kc
instance : CompactSpace D.Kcbar := isCompact_iff_compactSpace.mp D.isCompact_Kcbar
instance : CompactSpace D.Kt := isCompact_iff_compactSpace.mp D.isCompact_Kt
instance : CompactSpace D.Kt' := isCompact_iff_compactSpace.mp D.isCompact_Kt'
instance : CompactSpace D.Ktot := isCompact_iff_compactSpace.mp D.isCompact_Ktot

theorem Kc_subset_Kt : D.Kc ⊆ D.Kt := rect_subset_doubledRect _ _ _ _

theorem Kt_subset_Ktot : D.Kt ⊆ D.Ktot := Set.subset_union_left

theorem Kt'_subset_Ktot : D.Kt' ⊆ D.Ktot := Set.subset_union_right

theorem conj_mem_Kt {z : ℂ} (hz : z ∈ D.Kt) : (starRingEnd ℂ) z ∈ D.Kt :=
  conj_mem_doubledRect hz

theorem conj_mem_Kcbar {z : ℂ} (hz : z ∈ D.Kcbar) : (starRingEnd ℂ) z ∈ D.Kc := by
  rw [Kcbar, mem_rect] at hz
  rw [Kc, mem_rect]
  refine ⟨by simpa using hz.1, ?_, ?_⟩ <;> simp <;> linarith [hz.2.1, hz.2.2]

theorem Kc_im {z : ℂ} (hz : z ∈ D.Kc) : D.c ≤ z.im := ((mem_rect.mp hz).2).1

theorem Kcbar_im {z : ℂ} (hz : z ∈ D.Kcbar) : z.im ≤ -D.c := ((mem_rect.mp hz).2).2

theorem Kt_re {z : ℂ} (hz : z ∈ D.Kt) : D.a ≤ z.re := ((mem_doubledRect.mp hz).1).1

theorem Kt'_re {z : ℂ} (hz : z ∈ D.Kt') : z.re ≤ 1 - D.a := ((mem_doubledRect.mp hz).1).2

theorem one_sub_mem_Kt' {z : ℂ} (hz : z ∈ D.Kt) : 1 - z ∈ D.Kt' := by
  rw [Kt, mem_doubledRect] at hz
  rw [Kt', mem_doubledRect]
  refine ⟨⟨by simp; linarith [hz.1.2], by simp; linarith [hz.1.1]⟩, ?_⟩
  rcases hz.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · right
    constructor <;> simp <;> linarith
  · left
    constructor <;> simp <;> linarith

theorem Ktot_re {z : ℂ} (hz : z ∈ D.Ktot) : 1 - D.b ≤ z.re ∧ z.re ≤ D.b := by
  rcases hz with hz | hz
  · rw [Kt, mem_doubledRect] at hz
    exact ⟨le_trans D.one_sub_b_le_a hz.1.1, hz.1.2⟩
  · rw [Kt', mem_doubledRect] at hz
    exact ⟨hz.1.1, le_trans hz.1.2 D.one_sub_a_le_b⟩

theorem norm_le_of_mem_Ktot {z : ℂ} (hz : z ∈ D.Ktot) :
    ‖z‖ ≤ (|1 - D.b| + |D.b|) + (|(-D.d)| + |D.d|) := by
  refine norm_le_of_mem_rect (a := 1 - D.b) (b := D.b) (c := -D.d) (d := D.d) ?_
  rw [mem_rect]
  refine ⟨D.Ktot_re hz, ?_⟩
  have him : (-D.d ≤ z.im ∧ z.im ≤ -D.c) ∨ (D.c ≤ z.im ∧ z.im ≤ D.d) := by
    rcases hz with hz | hz
    · exact (mem_doubledRect.mp hz).2
    · exact (mem_doubledRect.mp hz).2
  rcases him with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, by linarith [D.hc, D.hcd]⟩
  · exact ⟨by linarith [D.hc, D.hcd], h2⟩

end QuadrantCarrierData

end RHTower

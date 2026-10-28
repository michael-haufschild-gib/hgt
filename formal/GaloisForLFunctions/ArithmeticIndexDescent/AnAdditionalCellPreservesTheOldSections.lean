import GaloisForLFunctions.ArithmeticIndexDescent.AShortNewCellPaysItsOwnInteraction
import GaloisForLFunctions.ArithmeticIndexDescent.TheSourceKernelEnergyBoundsTheSchurCost

/-!
# Adding a new cell without shrinking the old sections

A new cell separated from the existing arithmetic support can pay its full
mixed-source charge by choosing its own width. The old widths and the entire
old independently profiled section space stay fixed. The loss of old square
mass can be chosen arbitrarily small.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri ArithmeticElectrostatics

/-- A geometric gap permits adaptive extension of the whole old section space.
Only the new width is chosen; no mixed-form estimate or positivity is assumed. -/
theorem exists_smallCell_extension_of_gap
    {N : ℕ} (hN : 1 ≤ N) {w : ℝ} (hw0 : 0 < w)
    (hw : w ≤ fullSectionRatio * atomSpacing N) {b d ε : ℝ}
    (hd : 0 < d) (hε : 0 < ε)
    (hgap : ∀ u ∈ arithmeticSectionSupport N w, d < |u - b|) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ p : arithmeticSectionTests N w, ∀ g : realTests,
        (∀ u, δ / 2 < |u - b| → g.1 u = 0) →
        (1 - ε) * sectionMass p.1.1 + sectionMass g.1 ≤
          realWeilForm (p.1 + g) (p.1 + g) := by
  let L := Real.log N + w
  let R := |L| + |b| + 2
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨δ₀, hδ₀, hext⟩ := exists_shortCell_diagonal_extension hR hd hε b 1
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hδlt p g hgs
  have hps : ∀ u, R < |u| → p.1.1 u = 0 := by
    intro u hu
    apply arithmeticSectionTest_eq_zero_of_abs_gt p
    have hLR : L ≤ R := by
      dsimp [R]
      linarith only [le_abs_self L, abs_nonneg b]
    exact hLR.trans_lt hu
  have hpsgap : ∀ u, p.1.1 u ≠ 0 → d < |u - b| := by
    intro u hu
    apply hgap u
    by_contra hnot
    exact hu (arithmeticSectionTest_eq_zero_off_support p hnot)
  have hnew := hext δ hδ hδlt p.1 g hps hpsgap hgs
  have hold := integral_sq_le_weilPair_arithmeticSection hN hw0 hw p
  change sectionMass p.1.1 ≤ realWeilForm p.1 p.1 at hold
  linarith only [hnew, hold]

/-- Every point outside the actual compact cell union has a positive geometric gap. -/
theorem exists_arithmeticSectionSupport_gap {N : ℕ} {w b : ℝ}
    (hb : b ∉ arithmeticSectionSupport N w) :
    ∃ d : ℝ, 0 < d ∧ ∀ u ∈ arithmeticSectionSupport N w, d < |u - b| := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp
    (isCompact_arithmeticSectionSupport N w).isClosed.isOpen_compl b hb
  refine ⟨r / 2, div_pos hr (by norm_num), ?_⟩
  intro u hu
  have hfar : r ≤ |u - b| := by
    by_contra hnot
    have huB : u ∈ Metric.ball b r := by
      rw [Metric.mem_ball, Real.dist_eq]
      exact lt_of_not_ge hnot
    exact hball huB hu
  linarith only [hr, hfar]

/-- At every exterior centre, a new cell preserves any chosen fraction of the
old source floor, uniformly over the entire old and new profile spaces. -/
theorem exists_smallCell_extension
    {N : ℕ} (hN : 1 ≤ N) {w : ℝ} (hw0 : 0 < w)
    (hw : w ≤ fullSectionRatio * atomSpacing N) {b ε : ℝ}
    (hb : b ∉ arithmeticSectionSupport N w) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ p : arithmeticSectionTests N w, ∀ g : realTests,
        (∀ u, δ / 2 < |u - b| → g.1 u = 0) →
        (1 - ε) * sectionMass p.1.1 + sectionMass g.1 ≤
          realWeilForm (p.1 + g) (p.1 + g) := by
  obtain ⟨d, hd, hgap⟩ := exists_arithmeticSectionSupport_gap hb
  exact exists_smallCell_extension_of_gap hN hw0 hw hd hε hgap

/-- Half the old mass and all new mass remain after paying every mixed source term. -/
theorem exists_smallCell_extension_half
    {N : ℕ} (hN : 1 ≤ N) {w : ℝ} (hw0 : 0 < w)
    (hw : w ≤ fullSectionRatio * atomSpacing N) {b : ℝ}
    (hb : b ∉ arithmeticSectionSupport N w) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ p : arithmeticSectionTests N w, ∀ g : realTests,
        (∀ u, δ / 2 < |u - b| → g.1 u = 0) →
        (1 / 2) * sectionMass p.1.1 + sectionMass g.1 ≤
          realWeilForm (p.1 + g) (p.1 + g) := by
  simpa only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using
    exists_smallCell_extension hN hw0 hw hb (by norm_num : (0 : ℝ) < 1 / 2)

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_smallCell_extension_of_gap
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_smallCell_extension
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_smallCell_extension_half

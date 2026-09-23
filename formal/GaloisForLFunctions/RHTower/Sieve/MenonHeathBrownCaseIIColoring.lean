import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownWindowRelevantDichotomy

/-!
# Finite coloring for Menon's degree-three Case II

Every large sharp twisted interval is assigned its literal frequency cell, window-relevant
Heath--Brown box, distinguished positive factor, and the exact medium/long alternative.  The
selected ordinate is retained separately.  The signed binomial coefficient is removed with its
literal degree-three cost `2^(3 : ℕ) = 8`; no box, factor, or branch is averaged away.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Set

/-- Finite data selected from one large interval in Menon's degree-three Case II. -/
abbrev MenonHeathBrownCaseIILabel (L X cells : ℕ) :=
  Σ _cell : Fin cells,
    Σ box : HeathBrownBoxChoice L X 3,
      HeathBrownBoxFactorIndex 3 box.m × Bool

def MenonHeathBrownCaseIILabel.cell
    {L X cells : ℕ} (label : MenonHeathBrownCaseIILabel L X cells) : Fin cells :=
  label.1

def MenonHeathBrownCaseIILabel.box
    {L X cells : ℕ} (label : MenonHeathBrownCaseIILabel L X cells) :
    HeathBrownBoxChoice L X 3 :=
  label.2.1

def MenonHeathBrownCaseIILabel.factor
    {L X cells : ℕ} (label : MenonHeathBrownCaseIILabel L X cells) :
    HeathBrownBoxFactorIndex 3 label.box.m :=
  label.2.2.1

def MenonHeathBrownCaseIILabel.isLong
    {L X cells : ℕ} (label : MenonHeathBrownCaseIILabel L X cells) : Bool :=
  label.2.2.2

/-- Exact pointwise information carried by a Case-II color and its selected ordinate. -/
def IsMenonHeathBrownCaseIISelection
    (L X a cells : ℕ) (T0 t sigma tau V Δ Q y : ℝ)
    (label : MenonHeathBrownCaseIILabel L X cells) : Prop :=
  y ∈ Set.Icc
      (-V + (label.cell : ℝ) * Δ)
      (-V + ((label.cell : ℝ) + 1) * Δ) ∧
    IsHeathBrownBoxEligible L X 3 T0 t label.box ∧
    IsHeathBrownBoxWindowRelevant (a : ℝ) X 3 label.box ∧
    Q ≤ (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 8 *
      ‖heathBrownDyadicCoreProduct L X 3 label.box.m
        label.box.a label.box.b label.box.q
        ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * Complex.I)‖ ∧
    1 ≤ heathBrownBoxFactorExponent
      label.box.a label.box.b label.box.q label.factor ∧
    if label.isLong then
      (a : ℝ) ^ (1 / 8 : ℝ) ≤
          ((2 ^ heathBrownBoxFactorExponent
            label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ) ∧
        (L : ℝ) <
            ((2 ^ heathBrownBoxFactorExponent
              label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ) ∧
          (heathBrownBoxFactorKind 3 label.box.m label.factor = .zeta ∨
            heathBrownBoxFactorKind 3 label.box.m label.factor = .log)
    else
      (a : ℝ) ^ (1 / 8 : ℝ) ≤
          ((2 ^ heathBrownBoxFactorExponent
            label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ) ∧
        ((2 ^ heathBrownBoxFactorExponent
          label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ) ≤
          (L : ℝ)

/-- The Case-II label type is inhabited as soon as the frequency grid is nonempty. -/
theorem nonempty_menonHeathBrownCaseIILabel
    (L X cells : ℕ) (hcells : 0 < cells) :
    Nonempty (MenonHeathBrownCaseIILabel L X cells) := by
  let cell : Fin cells := ⟨0, hcells⟩
  let box : HeathBrownBoxChoice L X 3 :=
    Classical.choice (nonempty_heathBrownBoxChoice L X 3 (by norm_num))
  let factor : HeathBrownBoxFactorIndex 3 box.m :=
    Sum.inr (Sum.inr Unit.unit)
  exact ⟨⟨cell, box, factor, false⟩⟩

/-- Exact cardinality of the finite Case-II color type. -/
theorem card_menonHeathBrownCaseIILabel (L X cells : ℕ) :
    Fintype.card (MenonHeathBrownCaseIILabel L X cells) =
      cells * ∑ box : HeathBrownBoxChoice L X 3,
        Fintype.card (HeathBrownBoxFactorIndex 3 box.m) * 2 := by
  simp [MenonHeathBrownCaseIILabel]

/-- A degree-three color costs at most twelve factor/branch choices per literal box. -/
theorem card_menonHeathBrownCaseIILabel_le (L X cells : ℕ) :
    Fintype.card (MenonHeathBrownCaseIILabel L X cells) ≤
      cells * Fintype.card (HeathBrownBoxChoice L X 3) * 12 := by
  rw [card_menonHeathBrownCaseIILabel]
  calc
    cells * ∑ box : HeathBrownBoxChoice L X 3,
          Fintype.card (HeathBrownBoxFactorIndex 3 box.m) * 2 ≤
        cells * ∑ _box : HeathBrownBoxChoice L X 3, 12 := by
      gcongr with box
      change Fintype.card (HeathBrownBoxFactorIndex 3 (box.1 : ℕ)) * 2 ≤ 12
      rw [card_heathBrownBoxFactorIndex box.1.isLt]
      omega
    _ = cells * Fintype.card (HeathBrownBoxChoice L X 3) * 12 := by
      simp [mul_assoc]

/-- Removing the signed degree-three binomial scalar costs at most `8`. -/
theorem norm_heathBrownBoxTerm_three_le_eight_mul_core
    {L X : ℕ} (box : HeathBrownBoxChoice L X 3) (s : ℂ) :
    ‖heathBrownBoxTerm L X 3 box s‖ ≤
      8 * ‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q s‖ := by
  rw [heathBrownBoxTerm,
    norm_heathBrownDyadicTermProduct_eq_choose_mul_core]
  gcongr
  exact_mod_cast Nat.choose_le_two_pow 3 box.m

/-- Pointwise sharp-interval selection in complete finite-label form. -/
theorem exists_menonHeathBrownCaseIISelection_of_vonMangoldtTwist_Ioc_gt
    (L X a b cells : ℕ) (hXL : X < (L + 1) ^ (3 : ℕ))
    (hab : a ≤ b) (hbX : b ≤ X) (T0 t tau : ℝ) (hT0 : 1 < T0)
    (hscale : ((2 ^ (6 : ℕ) : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ))
    (ha : (64 : ℝ) ^ (8 : ℕ) ≤ (a : ℝ)) (hL : 1 ≤ L)
    (_hcut : (L : ℝ) ≤ (a : ℝ) ^ (1 / 3 : ℝ))
    {B sigma C V Δ : ℝ} (hsigma : 1 < sigma) (hC : 1 ≤ C)
    (hkernel : ∀ y : ℝ,
      ‖menonSharpIntervalMellinKernel (a : ℝ) (b : ℝ) sigma y‖ ≤
        C * (1 + y ^ (2 : ℕ))⁻¹)
    (hV : 0 ≤ V) (hΔ : 0 < Δ) (hcells : 0 < cells)
    (hgrid : 2 * V = (cells : ℝ) * Δ)
    (hthreshold : 0 <
      (B - heathBrownWindowRelevantFixedPolylogBound L X 3 (a : ℝ) sigma * C *
          (Real.pi - 2 * Real.arctan V)) /
          ((cells : ℝ) * Δ * C))
    (hlarge : B < ‖(2 * Real.pi : ℝ) •
      (∑ n ∈ Finset.Ioc a b, vonMangoldtTwist tau n)‖) :
    ∃ label : MenonHeathBrownCaseIILabel L X cells, ∃ y : ℝ,
      IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma tau V Δ
        ((B - heathBrownWindowRelevantFixedPolylogBound L X 3 (a : ℝ) sigma * C *
            (Real.pi - 2 * Real.arctan V)) /
            ((cells : ℝ) * Δ * C)) y label := by
  let Q : ℝ :=
    (B - heathBrownWindowRelevantFixedPolylogBound L X 3 (a : ℝ) sigma * C *
        (Real.pi - 2 * Real.arctan V)) /
        ((cells : ℝ) * Δ * C)
  obtain ⟨j, hj, y, hy, box, heligible, hrelevant, hbox, hfactor⟩ :=
    exists_windowRelevantBox_cell_medium_or_long_zeta_log_cutoff_of_vonMangoldtTwist_Ioc_gt
      L X a b cells hXL hab hbX T0 t tau hT0 hscale ha hL hsigma hC
        hkernel hV hΔ hcells hgrid hthreshold hlarge
  have hterm := norm_heathBrownBoxTerm_three_le_eight_mul_core box
    ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * Complex.I)
  have hcard0 : 0 ≤ (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) := by
    positivity
  have hcore : Q ≤ (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 8 *
      ‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q
        ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * Complex.I)‖ := by
    calc
      Q ≤ (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) *
          ‖heathBrownBoxTerm L X 3 box
            ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * Complex.I)‖ := by
        simpa only [Q] using hbox
      _ ≤ (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) *
          (8 * ‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q
            ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * Complex.I)‖) :=
        mul_le_mul_of_nonneg_left hterm hcard0
      _ = (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 8 *
          ‖heathBrownDyadicCoreProduct L X 3 box.m box.a box.b box.q
            ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * Complex.I)‖ := by ring
  rcases hfactor with ⟨i, hmediumLo, hmediumHi⟩ | ⟨i, hlongLo, hlong, hkind⟩
  · let label : MenonHeathBrownCaseIILabel L X cells :=
      ⟨⟨j, Finset.mem_range.mp hj⟩, box, (i : HeathBrownBoxFactorIndex 3 box.m), false⟩
    refine ⟨label, y, ?_⟩
    dsimp only [IsMenonHeathBrownCaseIISelection,
      MenonHeathBrownCaseIILabel.cell, MenonHeathBrownCaseIILabel.box,
      MenonHeathBrownCaseIILabel.factor, MenonHeathBrownCaseIILabel.isLong, label]
    exact ⟨hy, heligible, hrelevant, hcore, i.property, hmediumLo, hmediumHi⟩
  · let label : MenonHeathBrownCaseIILabel L X cells :=
      ⟨⟨j, Finset.mem_range.mp hj⟩, box, (i : HeathBrownBoxFactorIndex 3 box.m), true⟩
    refine ⟨label, y, ?_⟩
    dsimp only [IsMenonHeathBrownCaseIISelection,
      MenonHeathBrownCaseIILabel.cell, MenonHeathBrownCaseIILabel.box,
      MenonHeathBrownCaseIILabel.factor, MenonHeathBrownCaseIILabel.isLong, label]
    exact ⟨hy, heligible, hrelevant, hcore, i.property, hlongLo, hlong, hkind⟩

/-- Uniform finite coloring of a finite set of large sharp twisted intervals. -/
theorem exists_menonHeathBrownCaseIISelection_coloring
    (L X a b cells : ℕ) (hXL : X < (L + 1) ^ (3 : ℕ))
    (hab : a ≤ b) (hbX : b ≤ X) (T0 t : ℝ) (hT0 : 1 < T0)
    (hscale : ((2 ^ (6 : ℕ) : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ))
    (ha : (64 : ℝ) ^ (8 : ℕ) ≤ (a : ℝ)) (hL : 1 ≤ L)
    (hcut : (L : ℝ) ≤ (a : ℝ) ^ (1 / 3 : ℝ))
    {B sigma C V Δ : ℝ} (hsigma : 1 < sigma) (hC : 1 ≤ C)
    (hkernel : ∀ y : ℝ,
      ‖menonSharpIntervalMellinKernel (a : ℝ) (b : ℝ) sigma y‖ ≤
        C * (1 + y ^ (2 : ℕ))⁻¹)
    (hV : 0 ≤ V) (hΔ : 0 < Δ) (hcells : 0 < cells)
    (hgrid : 2 * V = (cells : ℝ) * Δ)
    (hthreshold : 0 <
      (B - heathBrownWindowRelevantFixedPolylogBound L X 3 (a : ℝ) sigma * C *
          (Real.pi - 2 * Real.arctan V)) /
          ((cells : ℝ) * Δ * C))
    (S : Finset ℕ) (tau : ℕ → ℝ)
    (hlarge : ∀ r ∈ S, B < ‖(2 * Real.pi : ℝ) •
      (∑ n ∈ Finset.Ioc a b, vonMangoldtTwist (tau r) n)‖) :
    ∃ color : ℕ → MenonHeathBrownCaseIILabel L X cells,
      ∃ selectedY : ℕ → ℝ, ∀ r ∈ S,
        IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma (tau r) V Δ
          ((B - heathBrownWindowRelevantFixedPolylogBound L X 3 (a : ℝ) sigma * C *
              (Real.pi - 2 * Real.arctan V)) /
              ((cells : ℝ) * Δ * C)) (selectedY r) (color r) := by
  classical
  have hpoint : ∀ r : ℕ, r ∈ S →
      ∃ label : MenonHeathBrownCaseIILabel L X cells, ∃ y : ℝ,
        IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma (tau r) V Δ
          ((B - heathBrownWindowRelevantFixedPolylogBound L X 3 (a : ℝ) sigma * C *
              (Real.pi - 2 * Real.arctan V)) /
              ((cells : ℝ) * Δ * C)) y label := by
    intro r hr
    exact exists_menonHeathBrownCaseIISelection_of_vonMangoldtTwist_Ioc_gt
      L X a b cells hXL hab hbX T0 t (tau r) hT0 hscale ha hL hcut hsigma hC
        hkernel hV hΔ hcells hgrid hthreshold (hlarge r hr)
  choose selected selectedY hselected using hpoint
  let fallback : MenonHeathBrownCaseIILabel L X cells :=
    Classical.choice (nonempty_menonHeathBrownCaseIILabel L X cells hcells)
  let color : ℕ → MenonHeathBrownCaseIILabel L X cells := fun r =>
    if hr : r ∈ S then selected r hr else fallback
  let ordinate : ℕ → ℝ := fun r =>
    if hr : r ∈ S then selectedY r hr else 0
  refine ⟨color, ordinate, ?_⟩
  intro r hr
  simpa only [color, ordinate, dif_pos hr] using hselected r hr

end RHTower.Sieve

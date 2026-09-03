import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownWideIntervalCellSelection
import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownCaseIIColoring

/-!
# Case-II coloring with a common wide smoothing width

Variable sharp upper endpoints share one explicit wide-kernel majorant.  Endpoint variation adds no
color; the only new source cost is the pair of literal transition-window errors.
-/

namespace RHTower.Sieve

noncomputable section

open Finset ArithmeticFunction Complex Set

/-- Pointwise wide-smoothed interval selection in the existing complete Case-II label type. -/
theorem exists_menonHeathBrownCaseIISelection_of_vonMangoldtTwist_Ioc_gt_wide
    (L X a b cells : ℕ) (hXL : X < (L + 1) ^ 3) (hab : a ≤ b)
    (T0 t tau : ℝ) (hT0 : 1 < T0)
    (hscale : ((2 ^ 6 : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ))
    (ha : (64 : ℝ) ^ 8 ≤ (a : ℝ)) (hL : 1 ≤ L)
    {H B sigma C V Δ : ℝ} (hH : 0 < H)
    (haH : 1 ≤ (a : ℝ) + H) (hbH : 1 ≤ (b : ℝ) + H)
    (hsupport : (b : ℝ) + H ≤ X) (hsigma : 1 < sigma) (hC : 1 ≤ C)
    (hkernel : ∀ y : ℝ,
      ‖menonWideIntervalMellinKernel (a : ℝ) (b : ℝ) H sigma y‖ ≤
        C * (1 + y ^ 2)⁻¹)
    (hV : 0 ≤ V) (hΔ : 0 < Δ) (hcells : 0 < cells)
    (hgrid : 2 * V = (cells : ℝ) * Δ)
    (hthreshold : 0 <
      (B - heathBrownWindowRelevantFixedPolylogBound L X 3 (a : ℝ) sigma * C *
          (Real.pi - 2 * Real.arctan V)) /
          ((cells : ℝ) * Δ * C))
    (hlarge : B +
        ((H + 1) * Real.log ((b : ℝ) + H) +
          (H + 1) * Real.log ((a : ℝ) + H)) <
      ‖∑ n ∈ Finset.Ioc a b, vonMangoldtTwist tau n‖) :
    ∃ label : MenonHeathBrownCaseIILabel L X cells, ∃ y : ℝ,
      IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma tau V Δ
        ((B - heathBrownWindowRelevantFixedPolylogBound L X 3 (a : ℝ) sigma * C *
            (Real.pi - 2 * Real.arctan V)) /
            ((cells : ℝ) * Δ * C)) y label := by
  let Q : ℝ :=
    (B - heathBrownWindowRelevantFixedPolylogBound L X 3 (a : ℝ) sigma * C *
        (Real.pi - 2 * Real.arctan V)) /
        ((cells : ℝ) * Δ * C)
  obtain ⟨j, hj, y, hy, box, heligible, hrelevant, _hedge, hbox⟩ :=
    exists_windowRelevantBox_cell_large_of_vonMangoldtTwist_Ioc_gt_wide
      L X 3 a b cells (by omega) hXL hab T0 t tau hT0
        (by simpa only [show 2 * 3 = 6 by omega] using hscale)
        hH haH hbH hsupport hsigma hC hkernel hV hΔ hcells hgrid hthreshold hlarge
  have ha1 : (1 : ℝ) < (a : ℝ) :=
    (by norm_num : (1 : ℝ) < 64 ^ 8).trans_le ha
  have hwidth := windowRelevant_heathBrownBox_coreLower_gt hrelevant
  have hdiv : (a : ℝ) / 64 <
      (groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) := by
    norm_num at hwidth ⊢
    exact hwidth
  have hedge : (a : ℝ) ^ (7 / 8 : ℝ) ≤
      (groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) :=
    (rpow_sevenEighth_le_div_sixtyFour_of_pow_eight_le ha).trans hdiv.le
  have hfactor := exists_heathBrown_three_medium_or_long_zeta_log_cutoff
    box hL ha1 hedge
  have hterm := norm_heathBrownBoxTerm_three_le_eight_mul_core box
    ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * Complex.I)
  have hcard0 : 0 ≤ (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) := by positivity
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
      ⟨⟨j, Finset.mem_range.mp hj⟩, box,
        (i : HeathBrownBoxFactorIndex 3 box.m), false⟩
    refine ⟨label, y, ?_⟩
    dsimp only [IsMenonHeathBrownCaseIISelection,
      MenonHeathBrownCaseIILabel.cell, MenonHeathBrownCaseIILabel.box,
      MenonHeathBrownCaseIILabel.factor, MenonHeathBrownCaseIILabel.isLong, label]
    exact ⟨hy, heligible, hrelevant, hcore, i.property, hmediumLo, hmediumHi⟩
  · let label : MenonHeathBrownCaseIILabel L X cells :=
      ⟨⟨j, Finset.mem_range.mp hj⟩, box,
        (i : HeathBrownBoxFactorIndex 3 box.m), true⟩
    refine ⟨label, y, ?_⟩
    dsimp only [IsMenonHeathBrownCaseIISelection,
      MenonHeathBrownCaseIILabel.cell, MenonHeathBrownCaseIILabel.box,
      MenonHeathBrownCaseIILabel.factor, MenonHeathBrownCaseIILabel.isLong, label]
    exact ⟨hy, heligible, hrelevant, hcore, i.property, hlongLo, hlong, hkind⟩

/-- One absolute derivative constant colors variable-upper sharp intervals at a common wide width.
The source upper bound `Y` is separated from the enlarged Heath--Brown cutoff `X`. -/
theorem exists_absolute_menonHeathBrownCaseIISelection_variableUpper_wide_coloring :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ (L X Y a cells : ℕ) (T0 t : ℝ)
          (H B sigma V Δ : ℝ) (S : Finset ℕ) (upper : ℕ → ℕ) (tau : ℕ → ℝ),
        X < (L + 1) ^ 3 → 1 < T0 →
        ((2 ^ 6 : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ) →
        (64 : ℝ) ^ 8 ≤ (a : ℝ) → 1 ≤ L →
        0 < H → (Y : ℝ) + H ≤ (X : ℝ) →
        1 < sigma → 0 ≤ V → 0 < Δ → 0 < cells →
        2 * V = (cells : ℝ) * Δ →
        (∀ r ∈ S, a ≤ upper r) →
        (∀ r ∈ S, upper r ≤ Y) →
        let C : ℝ := menonWideIntervalAmbientKernelMajorant C0 X H sigma
        let Q : ℝ :=
          (B - heathBrownWindowRelevantFixedPolylogBound L X 3 (a : ℝ) sigma * C *
              (Real.pi - 2 * Real.arctan V)) /
            ((cells : ℝ) * Δ * C)
        0 < Q →
        (∀ r ∈ S, B +
            ((H + 1) * Real.log (((upper r : ℕ) : ℝ) + H) +
              (H + 1) * Real.log ((a : ℝ) + H)) <
          ‖∑ n ∈ Finset.Ioc a (upper r), vonMangoldtTwist (tau r) n‖) →
        ∃ color : ℕ → MenonHeathBrownCaseIILabel L X cells,
          ∃ selectedY : ℕ → ℝ, ∀ r ∈ S,
            IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma (tau r) V Δ Q
              (selectedY r) (color r) := by
  obtain ⟨C0, hC0, hkernel⟩ := exists_menonWideIntervalAmbientKernelMajorant
  refine ⟨C0, hC0, ?_⟩
  intro L X Y a cells T0 t H B sigma V Δ S upper tau hXL hT0 hscale ha hL
    hH hYX hsigma hV hΔ hcells hgrid hupperLo hupperHi
  dsimp only
  intro hQ hlarge
  let C : ℝ := menonWideIntervalAmbientKernelMajorant C0 X H sigma
  let Q : ℝ :=
    (B - heathBrownWindowRelevantFixedPolylogBound L X 3 (a : ℝ) sigma * C *
        (Real.pi - 2 * Real.arctan V)) /
      ((cells : ℝ) * Δ * C)
  have haOne : 1 ≤ a := by
    have haReal : (1 : ℝ) ≤ (a : ℝ) := by
      calc
        (1 : ℝ) ≤ (64 : ℝ) ^ 8 := by norm_num
        _ ≤ (a : ℝ) := ha
    exact_mod_cast haReal
  have haH : 1 ≤ (a : ℝ) + H := by
    have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast haOne
    linarith
  have hpoint : ∀ r : ℕ, r ∈ S →
      ∃ label : MenonHeathBrownCaseIILabel L X cells, ∃ y : ℝ,
        IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma (tau r) V Δ Q
          y label := by
    intro r hr
    have har := hupperLo r hr
    have hrY := hupperHi r hr
    have hsupport : ((upper r : ℕ) : ℝ) + H ≤ (X : ℝ) := by
      have hrYR : ((upper r : ℕ) : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hrY
      linarith
    have hbH : 1 ≤ ((upper r : ℕ) : ℝ) + H := by
      have harR : (1 : ℝ) ≤ ((upper r : ℕ) : ℝ) := by exact_mod_cast haOne.trans har
      linarith
    have hkernelR := hkernel (X := X) (a := a) (b := upper r)
      (H := H) (sigma := sigma) haOne har hsupport hH (by linarith)
    exact exists_menonHeathBrownCaseIISelection_of_vonMangoldtTwist_Ioc_gt_wide
      L X a (upper r) cells hXL har T0 t (tau r) hT0 hscale ha hL
      hH haH hbH hsupport hsigma hkernelR.1 hkernelR.2 hV hΔ hcells hgrid
      (by simpa only [Q, C] using hQ) (hlarge r hr)
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

end

end RHTower.Sieve

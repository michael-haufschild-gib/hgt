import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownWindowRelevantCellSelection
import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownSixFactorDichotomy

/-!
# Degree-three window relevance to Menon's factor dichotomy

For `k = 3`, window relevance places the literal core above `a / 64`.  Once
`64^8 ≤ a`, this is at least `a^(7/8)`, exactly the support threshold required by Menon's
six-factor medium/long classification.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Set

/-- At the explicit degree-three threshold, the eighth-power loss absorbs the dyadic width
`64`. -/
theorem rpow_sevenEighth_le_div_sixtyFour_of_pow_eight_le
    {P : ℝ} (hP : (64 : ℝ) ^ 8 ≤ P) :
    P ^ (7 / 8 : ℝ) ≤ P / 64 := by
  have hPpos : 0 < P := (by positivity : (0 : ℝ) < 64 ^ 8).trans_le hP
  have hroot0 := Real.rpow_le_rpow
    (by positivity : (0 : ℝ) ≤ (64 : ℝ) ^ 8) hP
      (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have hroot64 : (((64 : ℝ) ^ 8) ^ (1 / 8 : ℝ)) = 64 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 64)]
    norm_num
  have hroot : (64 : ℝ) ≤ P ^ (1 / 8 : ℝ) := by
    rw [hroot64] at hroot0
    exact hroot0
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 64)]
  calc
    P ^ (7 / 8 : ℝ) * 64 ≤
        P ^ (7 / 8 : ℝ) * P ^ (1 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg hPpos.le _)
    _ = P := by
      rw [← Real.rpow_add hPpos]
      norm_num

/-- A degree-three window-relevant box above the explicit threshold satisfies Menon's exact
medium-positive-factor or long-zeta/logarithm classification. -/
theorem exists_heathBrown_three_medium_or_long_zeta_log_of_windowRelevant
    {L X : ℕ} {a : ℝ} (box : HeathBrownBoxChoice L X 3)
    (hrelevant : IsHeathBrownBoxWindowRelevant a X 3 box)
    (ha : (64 : ℝ) ^ 8 ≤ a) (hL : 1 ≤ L)
    (hcut : (L : ℝ) ≤ a ^ (1 / 3 : ℝ)) :
    (∃ i : PositiveHeathBrownBoxFactorIndex box,
        a ^ (1 / 8 : ℝ) ≤
            ((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ) ∧
          ((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ) ≤
            a ^ (1 / 3 : ℝ)) ∨
      ∃ i : PositiveHeathBrownBoxFactorIndex box,
        a ^ (1 / 3 : ℝ) <
            ((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ) ∧
          (heathBrownBoxFactorKind 3 box.m i = .zeta ∨
            heathBrownBoxFactorKind 3 box.m i = .log) := by
  have ha1 : 1 < a := (by norm_num : (1 : ℝ) < 64 ^ 8).trans_le ha
  have hwidth := windowRelevant_heathBrownBox_coreLower_gt hrelevant
  have hdiv : a / 64 <
      (groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) := by
    norm_num at hwidth ⊢
    exact hwidth
  have hedge : a ^ (7 / 8 : ℝ) ≤
      (groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) :=
    (rpow_sevenEighth_le_div_sixtyFour_of_pow_eight_le ha).trans hdiv.le
  exact exists_heathBrown_three_medium_or_long_zeta_log box hL ha1 hcut hedge

/-- Exact sharp-interval cell selection followed by the degree-three Menon factor-length
dichotomy.  The selected box remains literal, eligible, and window-relevant, and its full core
amplitude lower bound is retained in the conclusion. -/
theorem exists_windowRelevantBox_cell_medium_or_long_zeta_log_of_vonMangoldtTwist_Ioc_gt
    (L X a b cells : ℕ) (hXL : X < (L + 1) ^ 3)
    (hab : a ≤ b) (hbX : b ≤ X) (T0 t tau : ℝ) (hT0 : 1 < T0)
    (hscale : ((2 ^ 6 : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ))
    (ha : (64 : ℝ) ^ 8 ≤ (a : ℝ)) (hL : 1 ≤ L)
    (hcut : (L : ℝ) ≤ (a : ℝ) ^ (1 / 3 : ℝ))
    {B sigma C V Δ : ℝ} (hsigma : 1 < sigma) (hC : 1 ≤ C)
    (hkernel : ∀ y : ℝ,
      ‖menonSharpIntervalMellinKernel (a : ℝ) (b : ℝ) sigma y‖ ≤
        C * (1 + y ^ 2)⁻¹)
    (hV : 0 ≤ V) (hΔ : 0 < Δ) (hcells : 0 < cells)
    (hgrid : 2 * V = (cells : ℝ) * Δ)
    (hthreshold : 0 <
      (B - heathBrownWindowRelevantFixedPolylogBound L X 3 (a : ℝ) sigma * C *
          (Real.pi - 2 * Real.arctan V)) /
          ((cells : ℝ) * Δ * C))
    (hlarge : B < ‖(2 * Real.pi : ℝ) •
      (∑ n ∈ Finset.Ioc a b, vonMangoldtTwist tau n)‖) :
    ∃ j ∈ Finset.range cells,
      ∃ y ∈ Set.Icc (-V + (j : ℝ) * Δ) (-V + ((j : ℝ) + 1) * Δ),
        ∃ box : HeathBrownBoxChoice L X 3,
          IsHeathBrownBoxEligible L X 3 T0 t box ∧
          IsHeathBrownBoxWindowRelevant (a : ℝ) X 3 box ∧
          (B - heathBrownWindowRelevantFixedPolylogBound L X 3 (a : ℝ) sigma * C *
              (Real.pi - 2 * Real.arctan V)) /
              ((cells : ℝ) * Δ * C) ≤
            (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) *
              ‖heathBrownBoxTerm L X 3 box
                ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * Complex.I)‖ ∧
          ((∃ i : PositiveHeathBrownBoxFactorIndex box,
              (a : ℝ) ^ (1 / 8 : ℝ) ≤
                  ((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ) ∧
                ((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ) ≤
                  (a : ℝ) ^ (1 / 3 : ℝ)) ∨
            ∃ i : PositiveHeathBrownBoxFactorIndex box,
              (a : ℝ) ^ (1 / 3 : ℝ) <
                  ((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ) ∧
                (heathBrownBoxFactorKind 3 box.m i = .zeta ∨
                  heathBrownBoxFactorKind 3 box.m i = .log)) := by
  obtain ⟨j, hj, y, hy, box, heligible, hrelevant, _hedge, hbox⟩ :=
    exists_windowRelevantBox_cell_large_of_vonMangoldtTwist_Ioc_gt
      L X 3 a b cells (by omega) hXL hab hbX T0 t tau hT0
        (by simpa only [show 2 * 3 = 6 by omega] using hscale)
        hsigma hC hkernel hV hΔ hcells hgrid hthreshold hlarge
  exact ⟨j, hj, y, hy, box, heligible, hrelevant, hbox,
    exists_heathBrown_three_medium_or_long_zeta_log_of_windowRelevant
      box hrelevant ha hL hcut⟩

end RHTower.Sieve

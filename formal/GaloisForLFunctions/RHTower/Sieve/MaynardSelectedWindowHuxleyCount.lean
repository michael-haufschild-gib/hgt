import GaloisForLFunctions.RHTower.Sieve.HuxleyWindowDecomposition
import GaloisForLFunctions.RHTower.Sieve.MaynardWideHuxley

/-!
# Selected-cell Huxley count below the global square scale

A selected raised product can fail Huxley absorption at the full Route-T height.  Canonical
ordinate windows restore absorption.  On every window fiber the existing amplitude-normalized
Huxley theorem and order-90 fixed-polylog cancellation apply unchanged; summing fibers costs
exactly `huxleyWindowCount T W`.
-/

set_option maxRecDepth 10000

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Exact selected-cell count obtained by local Huxley absorption on ordinate windows. -/
theorem card_le_of_selected_wide_huxley_windows
    {L X K : ℕ} {c alpha delta T W : ℝ}
    (hc : 1 / 2 ≤ c) (hc0 : 0 ≤ c) (halpha : alpha ≤ 1)
    (hdelta : 0 < delta) (hT : 0 ≤ T) (hW : 0 < W)
    (label : HeathBrownSelectionLabel L X 60)
    (S : Finset ℕ) (hS : S ⊆ Finset.range K)
    (lam : ℕ → ℝ) (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, 0 ≤ lam r ∧ lam r ≤ T)
    (ell : ℕ) (hell : 0 < ell) (hell90 : ell ≤ 90)
    (hheight : W ≤ 8 * Real.pi *
      ((((groupedDyadicLower
        (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)) ^ (2 : ℕ))
    (hlarge : ∀ r ∈ S,
      ((((groupedDyadicLower
        (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)) ^ (alpha - c) ≤
        ‖(∏ i : HeathBrownSelectedFactor label, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (heathBrownSelectedKind label i))
            (heathBrownSelectedExponent label i)))
              ((c : ℂ) + (lam r : ℝ) * Complex.I)) ^ ell‖)
    (hscale :
      2 * ((Fintype.card (HeathBrownSelectedFactor label) * ell + 1 : ℕ) : ℝ) ^ (2 : ℕ) *
          heathBrownSelectedRaisedEnergy label ell *
          (1 + 256 * (Real.sqrt W +
            8 * Real.sqrt
              ((((groupedDyadicUpper
                (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)))) ≤
        ((((groupedDyadicLower
          (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)) ^ (2 * alpha)) :
    (S.card : ℝ) ≤
      (huxleyWindowCount T W : ℝ) *
        (2 * (10801 : ℝ) ^ (2 : ℕ) * maynardMontgomeryRaisedWidthConstant *
          maynardHarmonicFactor K delta *
          (1 + Real.log
            (maynardMontgomeryRaisedWidthConstant *
              ((((groupedDyadicLower
                (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)))) ^
            (2 * (Fintype.card (HeathBrownSelectedFactor label) * ell) +
              (2 ^ (2 * ((Fintype.card
                (HeathBrownSelectedFactor label) + 1) * ell)) - 1)) *
          (((groupedDyadicLower
            (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ^
            (2 - 2 * alpha)) := by
  let color : ℕ → Fin (huxleyWindowCount T W) := huxleyWindowColor T W lam
  let B : ℝ :=
    2 * (10801 : ℝ) ^ (2 : ℕ) * maynardMontgomeryRaisedWidthConstant *
      maynardHarmonicFactor K delta *
      (1 + Real.log
        (maynardMontgomeryRaisedWidthConstant *
          ((((groupedDyadicLower
            (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)))) ^
        (2 * (Fintype.card (HeathBrownSelectedFactor label) * ell) +
          (2 ^ (2 * ((Fintype.card
            (HeathBrownSelectedFactor label) + 1) * ell)) - 1)) *
      (((groupedDyadicLower
        (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ^ (2 - 2 * alpha)
  have hfibre : ∀ q : Fin (huxleyWindowCount T W),
      (((S.filter fun r => color r = q).card : ℕ) : ℝ) ≤ B := by
    intro q
    let Sf : Finset ℕ := S.filter fun r => color r = q
    have hSfS : Sf ⊆ S := Finset.filter_subset _ _
    have hSfRange : Sf ⊆ Finset.range K := hSfS.trans hS
    have hSfDiam : ∀ r ∈ Sf, ∀ s ∈ Sf, |lam s - lam r| ≤ W := by
      intro r hr s hs
      have hrS := hSfS hr
      have hsS := hSfS hs
      have hrq : color r = q := (Finset.mem_filter.mp hr).2
      have hsq : color s = q := (Finset.mem_filter.mp hs).2
      exact (abs_sub_lt_of_huxleyWindowColor_eq hW
        (hband r hrS).1 (hband r hrS).2 (hband s hsS).1 (hband s hsS).2
        (by simpa only [color] using hrq.trans hsq.symm)).le
    have hHuxley : IsMaynardSelectedHuxleyBound K c alpha delta label Sf ell := by
      unfold IsMaynardSelectedHuxleyBound
      exact huxley_heathBrown_grouped_large_values_finset_at_amplitude
        L X ell K (heathBrownSelectedKind label) (heathBrownSelectedExponent label)
        hc0 (heathBrownSelectedRaisedEnergy label ell)
        (heathBrownSelectedRaisedEnergy_nonneg label ell) le_rfl hSfRange
        hdelta hW.le hgap hSfDiam hheight
        (fun r hr => hlarge r (hSfS hr)) hscale
    simpa only [Sf, B] using
      card_le_of_selected_wide_huxley_with_fixed_polylog_raw
        hc halpha hdelta label Sf ell hell hell90 hHuxley
  have hcardCast : (S.card : ℝ) =
      ∑ q : Fin (huxleyWindowCount T W),
        (((S.filter fun r => color r = q).card : ℕ) : ℝ) := by
    exact_mod_cast card_eq_sum_color_fibres S color
  rw [hcardCast]
  calc
    (∑ q : Fin (huxleyWindowCount T W),
        (((S.filter fun r => color r = q).card : ℕ) : ℝ)) ≤
        ∑ _q : Fin (huxleyWindowCount T W), B :=
      Finset.sum_le_sum fun q _ => hfibre q
    _ = (huxleyWindowCount T W : ℝ) * B := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (huxleyWindowCount T W : ℝ) *
        (2 * (10801 : ℝ) ^ (2 : ℕ) * maynardMontgomeryRaisedWidthConstant *
          maynardHarmonicFactor K delta *
          (1 + Real.log
            (maynardMontgomeryRaisedWidthConstant *
              ((((groupedDyadicLower
                (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)))) ^
            (2 * (Fintype.card (HeathBrownSelectedFactor label) * ell) +
              (2 ^ (2 * ((Fintype.card
                (HeathBrownSelectedFactor label) + 1) * ell)) - 1)) *
          (((groupedDyadicLower
            (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ^
            (2 - 2 * alpha)) := by rfl

end RHTower.Sieve

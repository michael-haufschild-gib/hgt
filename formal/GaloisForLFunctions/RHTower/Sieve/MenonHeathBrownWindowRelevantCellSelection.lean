import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownSharpIntervalHandoff
import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownTwistedCellSelection

/-!
# Window-relevant Heath--Brown cell selection from a sharp interval

The exact half-width cutoff difference is localized without discarding its physical lower
endpoint.  A large twisted von Mangoldt interval therefore selects one frequency cell and one
literal eligible window-relevant Heath--Brown box, together with its dyadic lower-edge bound.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

/-- Mellin kernel whose values on natural arguments encode the literal interval `(a,b]`. -/
def menonSharpIntervalMellinKernel
    (a b sigma y : ℝ) : ℂ :=
  mellin (fun x : ℝ =>
      ((GaloisForLFunctions.HTGeometry.smoothWeight b (1 / 2 : ℝ) x : ℝ) : ℂ))
      ((sigma : ℂ) + (y : ℝ) * Complex.I) -
    mellin (fun x : ℝ =>
      ((GaloisForLFunctions.HTGeometry.smoothWeight a (1 / 2 : ℝ) x : ℝ) : ℂ))
      ((sigma : ℂ) + (y : ℝ) * Complex.I)

/-- The sharp interval Mellin kernel is continuous on every positive vertical line. -/
theorem continuous_menonSharpIntervalMellinKernel
    {a b sigma : ℝ} (hsigma : 0 < sigma) :
    Continuous (menonSharpIntervalMellinKernel a b sigma) := by
  exact (continuous_mellin_smoothWeight_line
      (N := b) (H := (1 / 2 : ℝ)) (by norm_num) hsigma).sub
    (continuous_mellin_smoothWeight_line
      (N := a) (H := (1 / 2 : ℝ)) (by norm_num) hsigma)

/-- The difference of the two half-width Mellin kernels retains quadratic vertical decay. -/
theorem exists_menonSharpIntervalMellinLocalizationConstant
    {a b sigma : ℝ} (ha : 0 < a) (hb : 0 < b) (hsigma : 0 < sigma) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ y : ℝ,
      ‖menonSharpIntervalMellinKernel a b sigma y‖ ≤
        C * (1 + y ^ 2)⁻¹ := by
  obtain ⟨Cb, hCb, hkernelB⟩ :=
    exists_menonMellinLocalizationConstant hb
      (by norm_num : (0 : ℝ) < 1 / 2) hsigma
  obtain ⟨Ca, hCa, hkernelA⟩ :=
    exists_menonMellinLocalizationConstant ha
      (by norm_num : (0 : ℝ) < 1 / 2) hsigma
  refine ⟨Cb + Ca, by linarith, fun y => ?_⟩
  calc
    ‖menonSharpIntervalMellinKernel a b sigma y‖ ≤
        ‖mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight b (1 / 2 : ℝ) x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ +
        ‖mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight a (1 / 2 : ℝ) x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ := by
            exact norm_sub_le _ _
    _ ≤ Cb * (1 + y ^ 2)⁻¹ + Ca * (1 + y ^ 2)⁻¹ :=
      add_le_add (hkernelB y) (hkernelA y)
    _ = (Cb + Ca) * (1 + y ^ 2)⁻¹ := by ring

/-- Exact sharp-interval localization to one frequency cell of the window-relevant aggregate.
No prefix below `a` is introduced, and the full signed aggregate is retained until cell
extraction. -/
theorem exists_windowRelevantAggregate_cell_large_of_vonMangoldtTwist_Ioc_gt
    (L X k a b cells : ℕ) (hXL : X < (L + 1) ^ k)
    (hab : a ≤ b) (hbX : b ≤ X) (T0 t tau : ℝ) (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ))
    {B sigma C V Δ : ℝ} (hsigma : 1 < sigma) (hC : 1 ≤ C)
    (hkernel : ∀ y : ℝ,
      ‖menonSharpIntervalMellinKernel (a : ℝ) (b : ℝ) sigma y‖ ≤
        C * (1 + y ^ 2)⁻¹)
    (hV : 0 ≤ V) (hΔ : 0 < Δ) (hcells : 0 < cells)
    (hgrid : 2 * V = (cells : ℝ) * Δ)
    (hlarge : B < ‖(2 * Real.pi : ℝ) •
      (∑ n ∈ Finset.Ioc a b, vonMangoldtTwist tau n)‖) :
    ∃ j ∈ Finset.range cells,
      ∃ y ∈ Set.Icc (-V + (j : ℝ) * Δ) (-V + ((j : ℝ) + 1) * Δ),
        (B - heathBrownWindowRelevantFixedPolylogBound L X k (a : ℝ) sigma * C *
            (Real.pi - 2 * Real.arctan V)) /
            ((cells : ℝ) * Δ * C) ≤
          ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (a : ℝ)
            ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * Complex.I)‖ := by
  let A : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (a : ℝ)
      ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * Complex.I)
  let W : ℝ → ℂ := menonSharpIntervalMellinKernel (a : ℝ) (b : ℝ) sigma
  let P : ℝ := heathBrownWindowRelevantFixedPolylogBound L X k (a : ℝ) sigma
  let E : ℝ := P * C * (Real.pi - 2 * Real.arctan V)
  have haR : (0 : ℝ) < (a : ℝ) := by
    have hleft : (0 : ℝ) < ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t := by
      exact mul_pos (by positivity) (Real.rpow_pos_of_pos (by linarith) _)
    exact hleft.trans_le hscale
  have haPos : 0 < a := by exact_mod_cast haR
  have hbPos : 0 < b := haPos.trans_le hab
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hbPos
  have hXNat : 1 ≤ X :=
    (Nat.succ_le_iff.mpr haPos).trans (hab.trans hbX)
  have hAbound : ∀ y : ℝ, ‖A y‖ ≤ P := fun y =>
    norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
      L X k hXNat T0 t (a : ℝ) sigma (y + tau) haR (by linarith)
  have hP : 0 ≤ P := (norm_nonneg (A 0)).trans (hAbound 0)
  have hC0 : 0 ≤ C := by linarith
  have hA : Continuous A := by
    have hshift : Continuous (fun y : ℝ => y + tau) :=
      continuous_id.add continuous_const
    exact (continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line
      L X k T0 t (a : ℝ) sigma).comp hshift
  have hW : Continuous W :=
    continuous_menonSharpIntervalMellinKernel (by linarith)
  have hintB :=
    integrable_heathBrownWindowRelevantAggregate_shift_mul_mellin_smoothWeight
      L X k hXNat T0 t (a : ℝ) tau haR hbR
        (by norm_num : (0 : ℝ) < 1 / 2) (by linarith : 0 < sigma)
  have hintA :=
    integrable_heathBrownWindowRelevantAggregate_shift_mul_mellin_smoothWeight
      L X k hXNat T0 t (a : ℝ) tau haR haR
        (by norm_num : (0 : ℝ) < 1 / 2) (by linarith : 0 < sigma)
  have hint : Integrable fun y => A y * W y := by
    have heq : (fun y => A y * W y) =
        (fun y : ℝ => A y *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight (b : ℝ)
              (1 / 2 : ℝ) x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * Complex.I)) -
        (fun y : ℝ => A y *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight (a : ℝ)
              (1 / 2 : ℝ) x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * Complex.I)) := by
      funext y
      simp only [W, menonSharpIntervalMellinKernel, Pi.sub_apply, mul_sub]
    rw [heq]
    simpa only [A] using hintB.sub hintA
  have hfull : B < ‖∫ y : ℝ, A y * W y‖ := by
    calc
      B < ‖(2 * Real.pi : ℝ) •
          (∑ n ∈ Finset.Ioc a b, vonMangoldtTwist tau n)‖ := hlarge
      _ = ‖∫ y : ℝ, A y * W y‖ := by
        congr 1
        simpa only [A, W, menonSharpIntervalMellinKernel] using
          sum_Ioc_vonMangoldtTwist_eq_integral_windowRelevantAggregate
            L X k a b hXL hab hbX T0 t tau hT0 hscale hsigma
  have hsplit : ‖∫ y : ℝ, A y * W y‖ ≤
      ‖∫ y in Set.Icc (-V) V, A y * W y‖ + E := by
    simpa only [E, P] using
      norm_integral_le_truncated_add_tail
        (g := A) (W := W) hV hP hC0 hAbound hkernel hint
  have hcentral : B - E < ‖∫ y in Set.Icc (-V) V, A y * W y‖ := by
    linarith
  have hend : -V + (cells : ℝ) * Δ = V := by linarith
  have hsetInterval :
      (∫ y in Set.Icc (-V) V, A y * W y) =
        ∫ y in (-V)..V, A y * W y := by
    rw [intervalIntegral.integral_of_le (neg_le_self hV),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hWcentral : ∀ y ∈ Set.Icc (-V) (-V + (cells : ℝ) * Δ), ‖W y‖ ≤ C := by
    intro y _hy
    have hden : 0 < 1 + y ^ 2 := by positivity
    have hinv : (1 + y ^ 2)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hden]
      nlinarith [sq_nonneg y]
    calc
      ‖W y‖ ≤ C * (1 + y ^ 2)⁻¹ := hkernel y
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left hinv hC0
      _ = C := by ring
  obtain ⟨c, hc, hcellsUpper⟩ :=
    exists_cell_max_norm_intervalIntegral_mul_le hA hW hΔ cells hWcentral
  have hsumLower : B - E ≤
      ∑ j ∈ Finset.range cells, Δ * (C * ‖A (c j)‖) := by
    apply (le_of_lt hcentral).trans
    rw [hsetInterval]
    rw [hend] at hcellsUpper
    exact hcellsUpper
  let f : ℕ → ℝ := fun j => Δ * (C * ‖A (c j)‖)
  have hf : ∀ j, 0 ≤ f j := fun j => by
    dsimp only [f]
    positivity
  have hsumNonneg : 0 ≤ ∑ j ∈ Finset.range cells, f j := by positivity
  have hsumNorm : ‖∑ j ∈ Finset.range cells, f j‖ =
      ∑ j ∈ Finset.range cells, f j := by
    rw [Real.norm_eq_abs, abs_of_nonneg hsumNonneg]
  have hrange : (Finset.range cells).Nonempty :=
    ⟨0, Finset.mem_range.mpr hcells⟩
  have hlargeSum : B - E ≤ ‖∑ j ∈ Finset.range cells, f j‖ := by
    rw [hsumNorm]
    simpa only [f] using hsumLower
  obtain ⟨j, hj, hjlarge⟩ :=
    exists_mem_card_mul_norm_ge (Finset.range cells) hrange f hlargeSum
  have hfnorm : ‖f j‖ = Δ * (C * ‖A (c j)‖) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hf j)]
  have hden : 0 < (cells : ℝ) * Δ * C := by positivity
  refine ⟨j, hj, c j, hc j (Finset.mem_range.mp hj), ?_⟩
  rw [div_le_iff₀ hden]
  calc
    B - heathBrownWindowRelevantFixedPolylogBound L X k (a : ℝ) sigma * C *
          (Real.pi - 2 * Real.arctan V) = B - E := rfl
    _ ≤ (cells : ℝ) * ‖f j‖ := by simpa using hjlarge
    _ = ‖A (c j)‖ * ((cells : ℝ) * Δ * C) := by rw [hfnorm]; ring

/-- A large sharp twisted interval selects one literal eligible window-relevant box.  The
conclusion includes the exact physical lower edge forced by relevance. -/
theorem exists_windowRelevantBox_cell_large_of_vonMangoldtTwist_Ioc_gt
    (L X k a b cells : ℕ) (hk : 0 < k) (hXL : X < (L + 1) ^ k)
    (hab : a ≤ b) (hbX : b ≤ X) (T0 t tau : ℝ) (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ))
    {B sigma C V Δ : ℝ} (hsigma : 1 < sigma) (hC : 1 ≤ C)
    (hkernel : ∀ y : ℝ,
      ‖menonSharpIntervalMellinKernel (a : ℝ) (b : ℝ) sigma y‖ ≤
        C * (1 + y ^ 2)⁻¹)
    (hV : 0 ≤ V) (hΔ : 0 < Δ) (hcells : 0 < cells)
    (hgrid : 2 * V = (cells : ℝ) * Δ)
    (hthreshold : 0 <
      (B - heathBrownWindowRelevantFixedPolylogBound L X k (a : ℝ) sigma * C *
          (Real.pi - 2 * Real.arctan V)) /
          ((cells : ℝ) * Δ * C))
    (hlarge : B < ‖(2 * Real.pi : ℝ) •
      (∑ n ∈ Finset.Ioc a b, vonMangoldtTwist tau n)‖) :
    ∃ j ∈ Finset.range cells,
      ∃ y ∈ Set.Icc (-V + (j : ℝ) * Δ) (-V + ((j : ℝ) + 1) * Δ),
        ∃ box : HeathBrownBoxChoice L X k,
          IsHeathBrownBoxEligible L X k T0 t box ∧
          IsHeathBrownBoxWindowRelevant (a : ℝ) X k box ∧
          (a : ℝ) / (2 ^ (2 * k) : ℝ) <
            (groupedDyadicLower
              (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ∧
          (B - heathBrownWindowRelevantFixedPolylogBound L X k (a : ℝ) sigma * C *
              (Real.pi - 2 * Real.arctan V)) /
              ((cells : ℝ) * Δ * C) ≤
            (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
              ‖heathBrownBoxTerm L X k box
                ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * Complex.I)‖ := by
  obtain ⟨j, hj, y, hy, hylarge⟩ :=
    exists_windowRelevantAggregate_cell_large_of_vonMangoldtTwist_Ioc_gt
      L X k a b cells hXL hab hbX T0 t tau hT0 hscale hsigma hC hkernel
        hV hΔ hcells hgrid hlarge
  obtain ⟨box, heligible, hrelevant, hbox⟩ :=
    exists_large_windowRelevant_eligible_heathBrownBox
      L X k hk T0 t (a : ℝ)
        ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * Complex.I) hthreshold hylarge
  exact ⟨j, hj, y, hy, box, heligible, hrelevant,
    windowRelevant_heathBrownBox_coreLower_gt hrelevant, hbox⟩

end RHTower.Sieve

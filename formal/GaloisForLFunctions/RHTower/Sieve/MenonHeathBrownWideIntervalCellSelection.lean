import GaloisForLFunctions.RHTower.Sieve.MenonWideIntervalUniformKernel
import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownWindowRelevantCellSelection

/-!
# Window-relevant Case-II selection from a wide-smoothed interval

This is the quantitative replacement for half-width sharp localization.  It retains the physical
lower edge, charges both smoothing transitions explicitly, and selects the same literal eligible
Heath--Brown boxes consumed by the existing Case-II receivers.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

/-- A large sharp twisted interval, after paying its two wide transition windows, selects one
frequency cell of the window-relevant aggregate. -/
theorem exists_windowRelevantAggregate_cell_large_of_vonMangoldtTwist_Ioc_gt_wide
    (L X k a b cells : ℕ) (hXL : X < (L + 1) ^ k) (hab : a ≤ b)
    (T0 t tau : ℝ) (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ))
    {H B sigma C V Δ : ℝ} (hH : 0 < H)
    (haH : 1 ≤ (a : ℝ) + H) (hbH : 1 ≤ (b : ℝ) + H)
    (hsupport : (b : ℝ) + H ≤ X) (hsigma : 1 < sigma) (hC : 1 ≤ C)
    (hkernel : ∀ y : ℝ,
      ‖menonWideIntervalMellinKernel (a : ℝ) (b : ℝ) H sigma y‖ ≤
        C * (1 + y ^ 2)⁻¹)
    (hV : 0 ≤ V) (hΔ : 0 < Δ) (hcells : 0 < cells)
    (hgrid : 2 * V = (cells : ℝ) * Δ)
    (hlarge : B +
        ((H + 1) * Real.log ((b : ℝ) + H) +
          (H + 1) * Real.log ((a : ℝ) + H)) <
      ‖∑ n ∈ Finset.Ioc a b, vonMangoldtTwist tau n‖) :
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
  let W : ℝ → ℂ := menonWideIntervalMellinKernel (a : ℝ) (b : ℝ) H sigma
  let P : ℝ := heathBrownWindowRelevantFixedPolylogBound L X k (a : ℝ) sigma
  let E : ℝ := P * C * (Real.pi - 2 * Real.arctan V)
  have haR : (0 : ℝ) < (a : ℝ) := by
    have hleft : (0 : ℝ) < ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t := by
      exact mul_pos (by positivity) (Real.rpow_pos_of_pos (by linarith) _)
    exact hleft.trans_le hscale
  have haPos : 0 < a := by exact_mod_cast haR
  have hbPos : 0 < b := haPos.trans_le hab
  have hbX : b ≤ X := by
    have hbR : (b : ℝ) ≤ (X : ℝ) := by linarith
    exact_mod_cast hbR
  have hXNat : 1 ≤ X := (Nat.succ_le_iff.mpr haPos).trans (hab.trans hbX)
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
    continuous_menonWideIntervalMellinKernel hH (by linarith)
  have hintB :=
    integrable_heathBrownWindowRelevantAggregate_shift_mul_mellin_smoothWeight
      L X k hXNat T0 t (a : ℝ) tau
        (N := (b : ℝ)) (H := H) (sigma := sigma)
        haR (by exact_mod_cast hbPos) hH (by linarith : 0 < sigma)
  have hintA :=
    integrable_heathBrownWindowRelevantAggregate_shift_mul_mellin_smoothWeight
      L X k hXNat T0 t (a : ℝ) tau
        (N := (a : ℝ)) (H := H) (sigma := sigma)
        haR haR hH (by linarith : 0 < sigma)
  have hint : Integrable fun y => A y * W y := by
    have heq : (fun y => A y * W y) =
        (fun y : ℝ => A y *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight
              (b : ℝ) H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * Complex.I)) -
        (fun y : ℝ => A y *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight
              (a : ℝ) H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * Complex.I)) := by
      funext y
      simp only [W, menonWideIntervalMellinKernel, Pi.sub_apply, mul_sub]
    rw [heq]
    simpa only [A] using hintB.sub hintA
  have hfull : B < ‖∫ y : ℝ, A y * W y‖ := by
    simpa only [A, W] using
      norm_integral_windowRelevantAggregate_wide_gt_of_vonMangoldtTwist_Ioc_gt
        L X k a b hXL hab tau T0 t hT0 hscale hH haH hbH hsupport hsigma hlarge
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

/-- Wide smoothing selects one literal eligible window-relevant box and retains its exact physical
lower edge. -/
theorem exists_windowRelevantBox_cell_large_of_vonMangoldtTwist_Ioc_gt_wide
    (L X k a b cells : ℕ) (hk : 0 < k) (hXL : X < (L + 1) ^ k)
    (hab : a ≤ b) (T0 t tau : ℝ) (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ))
    {H B sigma C V Δ : ℝ} (hH : 0 < H)
    (haH : 1 ≤ (a : ℝ) + H) (hbH : 1 ≤ (b : ℝ) + H)
    (hsupport : (b : ℝ) + H ≤ X) (hsigma : 1 < sigma) (hC : 1 ≤ C)
    (hkernel : ∀ y : ℝ,
      ‖menonWideIntervalMellinKernel (a : ℝ) (b : ℝ) H sigma y‖ ≤
        C * (1 + y ^ 2)⁻¹)
    (hV : 0 ≤ V) (hΔ : 0 < Δ) (hcells : 0 < cells)
    (hgrid : 2 * V = (cells : ℝ) * Δ)
    (hthreshold : 0 <
      (B - heathBrownWindowRelevantFixedPolylogBound L X k (a : ℝ) sigma * C *
          (Real.pi - 2 * Real.arctan V)) /
          ((cells : ℝ) * Δ * C))
    (hlarge : B +
        ((H + 1) * Real.log ((b : ℝ) + H) +
          (H + 1) * Real.log ((a : ℝ) + H)) <
      ‖∑ n ∈ Finset.Ioc a b, vonMangoldtTwist tau n‖) :
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
    exists_windowRelevantAggregate_cell_large_of_vonMangoldtTwist_Ioc_gt_wide
      L X k a b cells hXL hab T0 t tau hT0 hscale hH haH hbH hsupport
        hsigma hC hkernel hV hΔ hcells hgrid hlarge
  obtain ⟨box, heligible, hrelevant, hbox⟩ :=
    exists_large_windowRelevant_eligible_heathBrownBox
      L X k hk T0 t (a : ℝ)
        ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * Complex.I) hthreshold hylarge
  exact ⟨j, hj, y, hy, box, heligible, hrelevant,
    windowRelevant_heathBrownBox_coreLower_gt hrelevant, hbox⟩

end RHTower.Sieve

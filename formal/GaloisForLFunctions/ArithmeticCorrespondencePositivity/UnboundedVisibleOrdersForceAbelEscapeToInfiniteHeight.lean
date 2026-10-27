import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheReceiverAbelAtomsHaveTheirEffectivePoleOrder
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Unbounded effective orders force escape to infinite height

Each pole of order `m` supplies positive spectral mass at scale `e^(2m−1)`.
Unbounded orders therefore force divergence at every fixed polynomial scale.
Every compact window has finite polynomial growth, so its normalized share
vanishes. The conclusion uses the actual receiver, with no simplicity,
residue-summability, or receiver-energy premise.
-/

open Complex Set Filter Topology MeasureTheory
open RHTower GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- Unbounded effective orders force spectral mass to grow faster than every
fixed inverse power of the distance to the abscissa. -/
theorem tendsto_receiver_spectral_mass_atTop_of_unbounded_visible_order {ε : ℝ}
    (hε : 0 < ε) (hθ : 0 < zetaZeroAbscissa - ε - 1 / 2)
    (horders : ∀ N : ℕ, ∃ (ρ : ℂ) (m : ℕ), riemannZeta ρ = 0 ∧
      ρ.re = zetaZeroAbscissa ∧ ρ.re < 1 ∧ N < m ∧
      visibleTranslatedZetaOrder ε ρ = (m : ℕ∞)) (N : ℕ) :
    Tendsto (fun e : ℝ => e ^ N * ∫ y,
      ‖lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) y‖ ^ 2)
      (𝓝[>] 0) atTop := by
  obtain ⟨ρ, m, hz, hmax, hre1, hNm, horder⟩ := horders N
  have hm : 0 < m := by omega
  have hre : 1 / 2 + ε < ρ.re := by rw [hmax]; linarith
  obtain ⟨a, ha, δ, hδ, hatom⟩ := exists_receiver_pole_order_atom hε hz hmax hre hre1 hm horder
  have hlim := hatom δ hδ le_rfl (fun _ => 1) 1 continuous_const (fun _ => by norm_num)
  simp only [mul_one] at hlim
  have hA : 0 < poleMassConstant m * ‖a‖ ^ 2 :=
    mul_pos (poleMassConstant_pos (by omega)) (sq_pos_of_pos (norm_pos_iff.mpr ha))
  apply tendsto_lower_scale_mass_atTop (by omega : N < 2 * m - 1) hA hlim
  filter_upwards [self_mem_nhdsWithin] with e he
  obtain ⟨hI, hL⟩ := receiver_data_at_zeroAbscissa hε hθ he
  exact setIntegral_le_integral
    (_root_.RHTower.integrable_norm_sq_laplaceBoundary hI.ofReal hL.ofReal)
    (Eventually.of_forall fun y => sq_nonneg _)

/-- The same divergence holds for the actual diagonal Abel Gram. -/
theorem tendsto_receiver_abelGram_atTop_of_unbounded_visible_order {ε : ℝ}
    (hε : 0 < ε) (hθ : 0 < zetaZeroAbscissa - ε - 1 / 2)
    (horders : ∀ N : ℕ, ∃ (ρ : ℂ) (m : ℕ), riemannZeta ρ = 0 ∧
      ρ.re = zetaZeroAbscissa ∧ ρ.re < 1 ∧ N < m ∧
      visibleTranslatedZetaOrder ε ρ = (m : ℕ∞)) (N : ℕ) :
    Tendsto (fun e : ℝ => e ^ N *
      abelGram (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) 0 0)
      (𝓝[>] 0) atTop := by
  have h := (tendsto_receiver_spectral_mass_atTop_of_unbounded_visible_order hε hθ horders N
    ).const_mul_atTop (show 0 < (2 * Real.pi)⁻¹ by positivity)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with e he
  obtain ⟨hI, hL⟩ := receiver_data_at_zeroAbscissa hε hθ he
  rw [integral_norm_sq_lineSymbol hI hL]
  field_simp

/-- Under unbounded effective orders, every compact window loses all of its
normalized spectral mass, even if it contains multiple poles. -/
theorem tendsto_receiver_window_share_zero_of_unbounded_visible_order {ε : ℝ}
    (hε : 0 < ε) (hθ : 0 < zetaZeroAbscissa - ε - 1 / 2)
    (horders : ∀ N : ℕ, ∃ (ρ : ℂ) (m : ℕ), riemannZeta ρ = 0 ∧
      ρ.re = zetaZeroAbscissa ∧ ρ.re < 1 ∧ N < m ∧
      visibleTranslatedZetaOrder ε ρ = (m : ℕ∞)) (a b : ℝ) (hab : a ≤ b) :
    Tendsto (fun e : ℝ =>
      (∫ y in Icc a b,
        ‖lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) y‖ ^ 2) /
      (∫ y, ‖lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) y‖ ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨ρ, _, _, hmax, hre1, _, _⟩ := horders 0
  have hΘ1 : zetaZeroAbscissa < 1 := by rw [← hmax]; exact hre1
  obtain ⟨N, C, _, hC⟩ := exists_receiver_window_mass_polynomial_bound hε hθ hΘ1 a b hab
  exact tendsto_mass_share_zero_of_scaled_mass_atTop
    (Eventually.of_forall fun e => integral_nonneg fun y => sq_nonneg _) hC
    (tendsto_receiver_spectral_mass_atTop_of_unbounded_visible_order hε hθ horders N)

/-- The actual receiver has bounded effective orders on its rightmost line,
or its Abel mass escapes beyond every polynomial scale and every compact window. -/
theorem receiver_visible_order_or_infinite_height_escape {ε : ℝ}
    (hε : 0 < ε) (hθ : 0 < zetaZeroAbscissa - ε - 1 / 2) :
    (∃ M : ℕ, ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = zetaZeroAbscissa →
      visibleTranslatedZetaOrder ε ρ ≤ (M : ℕ∞)) ∨
    ((∀ N : ℕ, Tendsto (fun e : ℝ => e ^ N *
        abelGram (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) 0 0)
        (𝓝[>] 0) atTop) ∧
      ∀ a b : ℝ, a ≤ b → Tendsto (fun e : ℝ =>
        (∫ y in Icc a b,
          ‖lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) y‖ ^ 2) /
        (∫ y, ‖lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) y‖ ^ 2))
        (𝓝[>] 0) (𝓝 0)) := by
  by_cases hb : ∃ M : ℕ, ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = zetaZeroAbscissa →
      visibleTranslatedZetaOrder ε ρ ≤ (M : ℕ∞)
  · exact Or.inl hb
  · have horders : ∀ N : ℕ, ∃ (ρ : ℂ) (m : ℕ), riemannZeta ρ = 0 ∧
        ρ.re = zetaZeroAbscissa ∧ ρ.re < 1 ∧ N < m ∧
        visibleTranslatedZetaOrder ε ρ = (m : ℕ∞) := by
      push_neg at hb
      intro N
      obtain ⟨ρ, hz, hmax, hlt⟩ := hb N
      have hre1 : ρ.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hz
      have hρ1 : ρ ≠ 1 := fun h => by rw [h, one_re] at hre1; linarith
      have hs1 : ρ - (ε : ℂ) ≠ 1 := by
        intro h
        have := congrArg Complex.re h
        simp only [sub_re, ofReal_re, one_re] at this
        linarith
      have hcast := visibleTranslatedZetaOrder_eq_nat_sub (ε := ε) hρ1 hs1
      refine ⟨ρ, analyticOrderNatAt riemannZeta ρ -
        analyticOrderNatAt riemannZeta (ρ - (ε : ℂ)), hz, hmax, hre1, ?_, hcast⟩
      rw [hcast] at hlt
      exact_mod_cast hlt
    exact Or.inr ⟨tendsto_receiver_abelGram_atTop_of_unbounded_visible_order hε hθ horders,
      tendsto_receiver_window_share_zero_of_unbounded_visible_order hε hθ horders⟩

#print axioms receiver_visible_order_or_infinite_height_escape

end GaloisForLFunctions.ArithmeticCorrespondencePositivity

import GaloisForLFunctions.RHTower.ZetaTypicalLocalZeroCount
import GaloisForLFunctions.RHTower.XiLogDerivLineOneWindowLower

/-!
# Logarithmic Xi growth on the zero-free edge

Pairing each zero with its line conjugate keeps its ordinate unchanged.
The paired Poisson contribution has a width-free lower bound, so the
proved fixed-window zero count forces logarithmic growth on Re s = 1.
-/

noncomputable section
open Complex
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

/-- Keeping both members of a line-conjugate pair removes the horizontal-width loss. -/
theorem one_div_one_add_sq_le_edge_pair {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (v : ℝ) :
    1 / (1 + v ^ 2) ≤ xiLinePairRe (1 / 2) (β - 1 / 2) v := by
  have hb : 0 < 1 - β := sub_pos.mpr hβ1
  have hd1 : 0 < (1 - β) ^ 2 + v ^ 2 := by positivity
  have hd2 : 0 < β ^ 2 + v ^ 2 := by positivity
  have hβprod : 0 ≤ β * (1 - β) := mul_nonneg hβ0.le hb.le
  have he1 : (1 / 2 : ℝ) - (β - 1 / 2) = 1 - β := by ring
  have he2 : (1 / 2 : ℝ) + (β - 1 / 2) = β := by ring
  have h1 := div_le_div_of_nonneg_left hb.le hd1
    (show (1 - β) ^ 2 + v ^ 2 ≤ 1 + v ^ 2 by nlinarith only [hβ0, hβprod])
  have h2 := div_le_div_of_nonneg_left hβ0.le hd2
    (show β ^ 2 + v ^ 2 ≤ 1 + v ^ 2 by nlinarith only [hβ1, hβprod])
  rw [xiLinePairRe, he1, he2]
  calc
    _ = (1 - β) / (1 + v ^ 2) + β / (1 + v ^ 2) := by ring
    _ ≤ _ := add_le_add h1 h2

private theorem sum_copy_support_function (W : Finset XiDivisorSupport)
    (f : XiDivisorSupport → ℝ) :
    ∑ q ∈ xiCopiesOf W, f q.1 =
      ∑ ρ ∈ W, (xiSupportMultiplicity ρ : ℝ) * f ρ := by
  classical
  unfold xiCopiesOf
  rw [Finset.sum_sigma]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  change (∑ _s : Fin (xiSupportMultiplicity ρ), f ρ) = _
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- A fixed ordinate window gives an edge-field lower bound without any zero-free width. -/
theorem xi_edge_window_lower {T h : ℝ} (hh : 0 ≤ h) (hT : h ≤ T) :
    ((xiZeroCount (T + h) : ℝ) - (xiZeroCount (T - h) : ℝ)) /
        (2 * (1 + h ^ 2)) ≤ (logDeriv xi ((1 : ℂ) + (T : ℂ) * I)).re := by
  classical
  let s : ℂ := 1 + (T : ℂ) * I
  have hsre : s.re = 1 := by simp [s]
  have hsim : s.im = T := by simp [s]
  have hnonneg (q : XiZeroCopy) :
      0 ≤ xiLinePairRe (s.re - 1 / 2) ((q.1 : ℂ).re - 1 / 2)
        (s.im - (q.1 : ℂ).im) := by
    obtain ⟨hβ0, hβ1⟩ := xi_divisor_support_re_mem_open_unit q.1
    rw [hsre, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    exact (by positivity : 0 ≤ 1 / (1 + (s.im - (q.1 : ℂ).im) ^ 2)).trans
      (one_div_one_add_sq_le_edge_pair hβ0 hβ1 _)
  have hterm (ρ : XiDivisorSupport) (hρ : ρ ∈ xiSupportsWindow (T - h) (T + h)) :
      1 / (1 + h ^ 2) ≤ xiLinePairRe (1 / 2) ((ρ : ℂ).re - 1 / 2)
        (T - (ρ : ℂ).im) := by
    obtain ⟨hlo, hhi⟩ := (mem_xiSupportsWindow (sub_nonneg.mpr hT)).mp hρ
    obtain ⟨hβ0, hβ1⟩ := xi_divisor_support_re_mem_open_unit ρ
    have hv : (T - (ρ : ℂ).im) ^ 2 ≤ h ^ 2 := by
      have hp := mul_nonneg (sub_nonneg.mpr hlo.le) (sub_nonneg.mpr hhi)
      nlinarith only [hp]
    exact (div_le_div_of_nonneg_left (by norm_num)
      (by positivity : 0 < 1 + (T - (ρ : ℂ).im) ^ 2) (by linarith only [hv])).trans
        (one_div_one_add_sq_le_edge_pair hβ0 hβ1 _)
  have hsum := sum_pair_le_two_mul_re_logDeriv_xi
    (xi_ne_zero_of_one_le_re (by rw [hsre])) hnonneg
      (xiCopiesOf (xiSupportsWindow (T - h) (T + h)))
  rw [hsre, hsim, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hsum
  rw [sum_copy_support_function _ (fun ρ =>
    xiLinePairRe (1 / 2) ((ρ : ℂ).re - 1 / 2) (T - (ρ : ℂ).im))] at hsum
  have hlow := Finset.sum_le_sum (s := xiSupportsWindow (T - h) (T + h))
    (fun ρ hρ => mul_le_mul_of_nonneg_left (hterm ρ hρ)
      (show (0 : ℝ) ≤ xiSupportMultiplicity ρ by positivity))
  rw [← Finset.sum_mul, sum_mult_xiSupportsWindow (sub_nonneg.mpr hT)
    (by linarith only [hh])] at hlow
  have he : ((xiZeroCount (T + h) : ℝ) - (xiZeroCount (T - h) : ℝ)) /
      (2 * (1 + h ^ 2)) =
        (((xiZeroCount (T + h) : ℝ) - (xiZeroCount (T - h) : ℝ)) *
          (1 / (1 + h ^ 2))) / 2 := by rw [div_mul_eq_div_div]; ring
  rw [he]
  change _ ≤ (logDeriv xi s).re
  linarith only [hlow, hsum]

/-- The completed Xi field on the zero-free edge grows at least logarithmically. -/
theorem exists_xi_edge_logarithmic_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℝ, 4 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      c * Real.log T ≤ (logDeriv xi ((1 : ℂ) + (T : ℂ) * I)).re := by
  obtain ⟨h, hh, T₁, hT₁, hcount⟩ := exists_xiZeroCount_window_ge_log
  refine ⟨1 / (2 * (1 + h ^ 2)), by positivity, max T₁ h,
    hT₁.trans (le_max_left _ _), ?_⟩
  intro T hT
  have h1 : T₁ ≤ T := (le_max_left _ _).trans hT
  have h2 : h ≤ T := (le_max_right _ _).trans hT
  calc
    _ = Real.log T / (2 * (1 + h ^ 2)) := by ring
    _ ≤ ((xiZeroCount (T + h) : ℝ) - (xiZeroCount (T - h) : ℝ)) /
        (2 * (1 + h ^ 2)) := div_le_div_of_nonneg_right (hcount T h1) (by positivity)
    _ ≤ _ := xi_edge_window_lower hh.le h2

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.xi_edge_window_lower
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_xi_edge_logarithmic_lower

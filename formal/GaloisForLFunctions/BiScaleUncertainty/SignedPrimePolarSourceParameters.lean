import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Explicit logarithmic collar parameters and their source-energy scales. -/

namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

def sourceFactorialWidth (N : ℕ) : ℝ := Real.log (1+1/(4*(N : ℝ)))/3

def sourceFactorialCollar (N : ℕ) : ℝ := Real.exp (sourceFactorialWidth N)-1

def sourceFactorialCoefficient (N : ℕ) : ℝ := ((1+Real.exp (sourceFactorialWidth N))/2)^3

theorem sourceFactorialWidth_pos {N : ℕ} (hN : 1 ≤ N) : 0 < sourceFactorialWidth N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold sourceFactorialWidth
  apply div_pos _ (by norm_num)
  apply Real.log_pos
  have : 0 < 1/(4*(N : ℝ)) := by positivity
  linarith

theorem sourceFactorialCollar_pos {N : ℕ} (hN : 1 ≤ N) : 0 < sourceFactorialCollar N := by
  have he := Real.exp_lt_exp.mpr (sourceFactorialWidth_pos hN)
  rw [Real.exp_zero] at he
  exact sub_pos.mpr he

theorem exp_three_sourceFactorialWidth (N : ℕ) :
    Real.exp (3*sourceFactorialWidth N) = 1+1/(4*(N : ℝ)) := by
  unfold sourceFactorialWidth
  rw [show 3*(Real.log (1+1/(4*(N : ℝ)))/3) = Real.log (1+1/(4*(N : ℝ))) by ring,
    Real.exp_log (by positivity : 0 < 1+1/(4*(N : ℝ)))]

theorem sourceFactorialWidth_bounds {N : ℕ} (hN : 1 ≤ N) :
    1/(15*(N : ℝ)) ≤ sourceFactorialWidth N ∧ sourceFactorialWidth N ≤ 1/(12*(N : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : (0 : ℝ) < N := by linarith
  have hA : 0 < 1+1/(4*(N : ℝ)) := by positivity
  have hlo := Real.one_sub_inv_le_log_of_pos hA
  have hhi := Real.log_le_sub_one_of_pos hA
  have hid : 1-(1+1/(4*(N : ℝ)))⁻¹ = 1/(4*(N : ℝ)+1) := by
    field_simp
    ring
  rw [hid] at hlo
  have hb : 1/(5*(N : ℝ)) ≤ 1/(4*(N : ℝ)+1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  unfold sourceFactorialWidth
  constructor
  · rw [show 1/(15*(N : ℝ)) = (1/(5*(N : ℝ)))/3 by ring]
    exact div_le_div_of_nonneg_right (hb.trans hlo) (by norm_num)
  · rw [show 1/(12*(N : ℝ)) = (1/(4*(N : ℝ)))/3 by ring]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    linarith

theorem sourceFactorialWidth_le_collar (N : ℕ) :
    sourceFactorialWidth N ≤ sourceFactorialCollar N := by
  have he := Real.add_one_le_exp (sourceFactorialWidth N)
  unfold sourceFactorialCollar
  linarith

theorem exp_four_sourceFactorialWidth_le_two {N : ℕ} (hN : 1 ≤ N) :
    Real.exp (4*sourceFactorialWidth N) ≤ 2 := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hδ := sourceFactorialWidth_pos hN
  have ht : 1/(4*(N : ℝ)) ≤ 1/4 :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have ht0 : 0 ≤ 1/(4*(N : ℝ)) := by positivity
  calc
    _ ≤ Real.exp (6*sourceFactorialWidth N) := Real.exp_le_exp.mpr (by linarith)
    _ = (1+1/(4*(N : ℝ)))^2 := by
      rw [show 6*sourceFactorialWidth N = 3*sourceFactorialWidth N+3*sourceFactorialWidth N by ring,
        Real.exp_add, exp_three_sourceFactorialWidth]
      ring
    _ ≤ 2 := by nlinarith

theorem sourceFactorial_width_cost {N : ℕ} (hN : 1 ≤ N) :
    6*(N : ℝ) ≤ 1/(2*sourceFactorialWidth N) ∧ 2/sourceFactorialWidth N ≤ 30*(N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ := sourceFactorialWidth_pos hN
  obtain ⟨hlo,hhi⟩ := sourceFactorialWidth_bounds hN
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 2*sourceFactorialWidth N)).2
    have hh := (le_div_iff₀ (by positivity : 0 < 12*(N : ℝ))).mp hhi
    nlinarith
  · apply (div_le_iff₀ hδ).2
    have hh := (div_le_iff₀ (by positivity : 0 < 15*(N : ℝ))).mp hlo
    nlinarith

theorem sourceFactorial_dilated_collar_le {N : ℕ} {t : ℝ}
    (ht : t ≤ 2*sourceFactorialWidth N) :
    (1+sourceFactorialCollar N)*Real.exp t ≤ 1+1/(4*(N : ℝ)) := by
  unfold sourceFactorialCollar
  rw [show 1+(Real.exp (sourceFactorialWidth N)-1) = Real.exp (sourceFactorialWidth N) by ring,
    ← Real.exp_add, ← exp_three_sourceFactorialWidth N]
  exact Real.exp_le_exp.mpr (by linarith)

theorem sourceFactorialCoefficient_bounds {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ sourceFactorialCoefficient N ∧ sourceFactorialCoefficient N ≤ 1+1/(4*(N : ℝ)) := by
  have hδ := sourceFactorialWidth_pos hN
  have he : 1 ≤ Real.exp (sourceFactorialWidth N) := by simpa using Real.exp_le_exp.mpr hδ.le
  have hc : (Real.exp (sourceFactorialWidth N))^3 = 1+1/(4*(N : ℝ)) := by
    rw [← exp_three_sourceFactorialWidth N,
      show 3*sourceFactorialWidth N = sourceFactorialWidth N+sourceFactorialWidth N+sourceFactorialWidth N by ring,
      Real.exp_add, Real.exp_add]
    ring
  unfold sourceFactorialCoefficient
  constructor
  · calc
      (1 : ℝ) = (1 : ℝ)^3 := by norm_num
      _ ≤ _ := by gcongr; linarith
  · rw [← hc]
    gcongr
    linarith

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

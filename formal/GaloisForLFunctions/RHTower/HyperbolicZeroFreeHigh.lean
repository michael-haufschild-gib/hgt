import GaloisForLFunctions.RHTower.Sieve.ZeroFreeRegionKappaOne
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

/-!
# The hyperbolic zero-free condition at large ordinate

The condition `β(1−β)γ² ≥ 1/4` on a zero `β + iγ` of `ζ` is what lowers the unconditional
positivity threshold of the lag pole series from `13/25` to `1/2`.  It holds at every sufficiently
large ordinate: the exponent-one zero-free region gives `1 − β ≥ c/log|γ|`, the functional equation
gives the same bound for `β`, so `β(1−β) ≥ (c/log|γ|)(1 − c/log|γ|) ≥ c/(2 log|γ|)`, and
`log|γ| ≤ |γ| − 1` turns the requirement into `|γ| ≥ 1/(2c)`.

The remaining obstruction is therefore a bounded range of ordinates, where the corpus's zero-free
region supplies only an existential threshold.
-/

open Complex

namespace RHTower

noncomputable section

/-- **The hyperbolic zero-free condition holds above some ordinate.** -/
theorem exists_hyperbolic_zeroFree_high :
    ∃ T : ℝ, 3 ≤ T ∧ ∀ β γ : ℝ, T ≤ |γ| → 0 < β → β < 1 →
      riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) = 0 →
      1 / 4 ≤ β * (1 - β) * γ ^ (2 : ℕ) := by
  obtain ⟨c, T₀, hc, hT₀, hzf⟩ := Sieve.exists_zero_free_region
  refine ⟨max T₀ (max 3 (1 / (2 * c))), le_trans (le_max_left _ _) (le_max_right _ _), ?_⟩
  intro β γ hγ hβ0 hβ1 hzero
  have hγT₀ : T₀ ≤ |γ| := le_trans (le_max_left _ _) hγ
  have hγ3 : (3 : ℝ) ≤ |γ| := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hγ
  have hγc : 1 / (2 * c) ≤ |γ| := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hγ
  have hγpos : (0 : ℝ) < |γ| := by linarith
  -- `log |γ| ≥ 1`
  have hL1 : (1 : ℝ) ≤ Real.log |γ| := by
    have he : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith
    have : Real.log (Real.exp 1) < Real.log 3 :=
      Real.log_lt_log (Real.exp_pos 1) he
    rw [Real.log_exp] at this
    exact le_trans this.le (Real.log_le_log (by norm_num) hγ3)
  have hLpos : (0 : ℝ) < Real.log |γ| := by linarith
  -- upper bound from the zero-free region
  have hβup : β ≤ 1 - c / Real.log |γ| := by
    by_contra hcon
    exact hzf β γ hγT₀ hβ1.le (by linarith [not_le.mp hcon]) hzero
  -- lower bound from the functional equation
  have hβlow : c / Real.log |γ| ≤ β := by
    by_contra hcon
    have hlt : β < c / Real.log |γ| := not_le.mp hcon
    have hs0 : (0 : ℝ) < ((β : ℂ) + (γ : ℂ) * Complex.I).re := by
      simp [Complex.add_re, Complex.mul_re]
      linarith
    have hs1 : ((β : ℂ) + (γ : ℂ) * Complex.I).re < 1 := by
      simp [Complex.add_re, Complex.mul_re]
      linarith
    have hrefl : riemannZeta (1 - ((β : ℂ) + (γ : ℂ) * Complex.I)) = 0 :=
      (riemannZeta_one_sub_eq_zero_iff hs0 hs1).mpr hzero
    have hcast : (1 : ℂ) - ((β : ℂ) + (γ : ℂ) * Complex.I)
        = (((1 - β : ℝ)) : ℂ) + ((-γ : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hcast] at hrefl
    have habs : |(-γ)| = |γ| := abs_neg γ
    refine hzf (1 - β) (-γ) (by rw [habs]; exact hγT₀) (by linarith) ?_ hrefl
    rw [habs]
    linarith
  -- the two bounds force `c / log |γ| ≤ 1/2`
  have hhalf : c / Real.log |γ| ≤ 1 / 2 := by linarith
  -- minimum of `β(1−β)` on the interval
  have hprod : c / Real.log |γ| * (1 - c / Real.log |γ|) ≤ β * (1 - β) := by
    nlinarith [hβlow, hβup]
  have hprod' : c / (2 * Real.log |γ|) ≤ β * (1 - β) := by
    have hcL : 0 < c / Real.log |γ| := div_pos hc hLpos
    have hdiv : c / (2 * Real.log |γ|) = c / Real.log |γ| / 2 := by
      rw [div_div, mul_comm]
    rw [hdiv]
    nlinarith [hprod, hhalf, hcL]
  -- the ordinate is large enough
  have hlogle : Real.log |γ| ≤ |γ| := by
    have := Real.log_le_sub_one_of_pos hγpos
    linarith
  have hsq : γ ^ (2 : ℕ) = |γ| ^ (2 : ℕ) := (sq_abs γ).symm
  have hkey : Real.log |γ| / 2 ≤ c * γ ^ (2 : ℕ) := by
    rw [hsq]
    have hc2 : (0 : ℝ) < 2 * c := by linarith
    have h1 : (1 : ℝ) ≤ |γ| * (2 * c) := (div_le_iff₀ hc2).mp hγc
    have h2 : |γ| / 2 ≤ c * (|γ| * |γ|) := by nlinarith [h1, hγpos]
    nlinarith [h2, hlogle]
  have hγsq : (0 : ℝ) ≤ γ ^ (2 : ℕ) := sq_nonneg γ
  calc (1 : ℝ) / 4 ≤ c / (2 * Real.log |γ|) * γ ^ (2 : ℕ) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith : (0:ℝ) < 2 * Real.log |γ|)]
        linarith [hkey]
    _ ≤ β * (1 - β) * γ ^ (2 : ℕ) := mul_le_mul_of_nonneg_right hprod' hγsq

end

end RHTower

import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! # The small-support correction at half exterior degree -/

open Filter
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters
noncomputable section

/-- The near-pair count at half exterior degree is exponentially smaller
than the indicated binomial mass whenever its fourth-power rate is larger. -/
theorem quarter_price_of_base {c : ℝ} (hcut : 2*(3/2:ℝ)^4<16*c^4) :
    ∀ᶠ n : ℕ in atTop, 2^n*(3/2:ℝ)^(4*n) ≤
      (1/2:ℝ)*((4*n).choose (2*n):ℝ)*c^(4*n) := by
  let R : ℝ := 2*(3/2)^4
  let M : ℝ := 16*c^4
  have hm : 0<M := (show 0<R by norm_num [R]).trans hcut
  have hr : 0≤R/M := div_nonneg (by norm_num [R]) hm.le
  have hr' : R/M<1 := (div_lt_one hm).mpr hcut
  have hlim := tendsto_self_mul_const_pow_of_lt_one hr hr'
  filter_upwards [hlim.eventually_lt_const (by norm_num : (0:ℝ)<1/4),eventually_ge_atTop 2] with n hn hn₂
  have hc := Nat.four_pow_lt_mul_centralBinom (2*n) (by omega)
  rw [Nat.centralBinom_eq_two_mul_choose,show 2*(2*n)=4*n by omega] at hc
  have hcen : (16:ℝ)^n≤(2*n:ℕ)*((4*n).choose (2*n):ℝ) := by
    have h : (4:ℝ)^(2*n)≤(2*n:ℕ)*((4*n).choose (2*n):ℝ) := by exact_mod_cast hc.le
    simpa only [pow_mul,show (4:ℝ)^2=16 by norm_num] using h
  have hsmall : (4*(n:ℝ))*R^n≤M^n := by
    change (n:ℝ)*(R/M)^n<1/4 at hn
    rw [div_pow,←mul_div_assoc,div_lt_iff₀ (pow_pos hm _)] at hn
    calc
      _ = 4*((n:ℝ)*R^n) := mul_assoc ..
      _ ≤ 4*(1/4*M^n) := mul_le_mul_of_nonneg_left hn.le (by norm_num)
      _ = _ := by ring
  have ht := mul_le_mul_of_nonneg_right hcen (show 0≤(c^4)^n by positivity)
  rw [←mul_pow] at ht
  have hp : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have hcancel : R^n ≤ (1/2:ℝ)*((4*n).choose (2*n):ℝ)*(c^4)^n := by
    apply le_of_mul_le_mul_left _ (by positivity : (0:ℝ)<4*n)
    calc
      _ ≤ M^n := hsmall
      _ ≤ _ := by
        apply ht.trans_eq
        push_cast
        ring
  simpa only [pow_mul,R,mul_pow] using hcancel

#print axioms quarter_price_of_base
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters

import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! A finite lower bound for the central-binomial doubling ratio. Its exact
recurrence replaces asymptotic estimates in the factorial polar-loss bound. -/

namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

def centralBinomialDoublingRatio (N : ℕ) : ℝ :=
  (Nat.centralBinom (2*N) : ℝ)/(Nat.centralBinom N : ℝ)^2

theorem centralBinomialDoublingRatio_pos (N : ℕ) : 0 < centralBinomialDoublingRatio N := by
  have h1 : (0 : ℝ) < Nat.centralBinom N := by exact_mod_cast Nat.centralBinom_pos N
  have h2 : (0 : ℝ) < Nat.centralBinom (2*N) := by exact_mod_cast Nat.centralBinom_pos (2*N)
  exact div_pos h2 (sq_pos_of_pos h1)

private theorem cast_centralBinom_succ (N : ℕ) :
    (Nat.centralBinom (N+1) : ℝ) =
      (2*(2*(N : ℝ)+1)/((N : ℝ)+1))*(Nat.centralBinom N : ℝ) := by
  have hc : ((N : ℝ)+1)*(Nat.centralBinom (N+1) : ℝ) =
      2*(2*(N : ℝ)+1)*(Nat.centralBinom N : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ N
  calc
    _ = (2*(2*(N : ℝ)+1)*(Nat.centralBinom N : ℝ))/((N : ℝ)+1) := by
      apply (eq_div_iff (by positivity : (N : ℝ)+1 ≠ 0)).2
      nlinarith only [hc]
    _ = _ := by ring

theorem centralBinomialDoublingRatio_succ (N : ℕ) :
    centralBinomialDoublingRatio (N+1) =
      ((4*(N : ℝ)+1)*(4*(N : ℝ)+3)*((N : ℝ)+1)/(2*(2*(N : ℝ)+1)^3))*
        centralBinomialDoublingRatio N := by
  have hc : (Nat.centralBinom N : ℝ) ≠ 0 := by exact_mod_cast Nat.centralBinom_ne_zero N
  unfold centralBinomialDoublingRatio
  rw [show 2*(N+1) = (2*N+1)+1 by omega,
    cast_centralBinom_succ (2*N+1), cast_centralBinom_succ (2*N), cast_centralBinom_succ N]
  push_cast
  field_simp; ring

private theorem doubling_step_sq_lower (x : ℝ) (hx : 0 ≤ x) :
    x+2 ≤ (((4*x+1)*(4*x+3)*(x+1))/(2*(2*x+1)^3))^2*(x+1) := by
  have hd : 0 < 2*(2*x+1)^3 := by positivity
  have hp : 0 ≤ ((4*x+1)*(4*x+3)*(x+1))^2*(x+1)-(2*(2*x+1)^3)^2*(x+2) := by
    have he : ((4*x+1)*(4*x+3)*(x+1))^2*(x+1)-(2*(2*x+1)^3)^2*(x+2) =
        160*x^5+384*x^4+345*x^3+139*x^2+23*x+1 := by ring
    rw [he]
    positivity
  calc
    _ ≤ (((4*x+1)*(4*x+3)*(x+1))^2*(x+1))/(2*(2*x+1)^3)^2 :=
      (le_div_iff₀ (sq_pos_of_pos hd)).2 (by nlinarith only [hp])
    _ = _ := by rw [div_pow]; ring

/-- The ratio has square-root growth with an explicit bound at every index. -/
theorem add_one_le_centralBinomialDoublingRatio_sq (N : ℕ) :
    (N : ℝ)+1 ≤ (centralBinomialDoublingRatio N)^2 := by
  induction N with
  | zero => norm_num [centralBinomialDoublingRatio]
  | succ N ih =>
    rw [centralBinomialDoublingRatio_succ, mul_pow]
    push_cast
    calc
      _ = (N : ℝ)+2 := by ring
      _ ≤ (((4*(N : ℝ)+1)*(4*(N : ℝ)+3)*((N : ℝ)+1))/(2*(2*(N : ℝ)+1)^3))^2*
          ((N : ℝ)+1) := doubling_step_sq_lower _ (Nat.cast_nonneg N)
      _ ≤ _ := mul_le_mul_of_nonneg_left ih (sq_nonneg _)

theorem centralBinomialDoublingRatio_log (N : ℕ) :
    Real.log (centralBinomialDoublingRatio N) =
      Real.log ((4*N).choose (2*N) : ℝ)-2*Real.log ((2*N).choose N : ℝ) := by
  have h1 : (0 : ℝ) < Nat.centralBinom N := by exact_mod_cast Nat.centralBinom_pos N
  have h2 : (0 : ℝ) < Nat.centralBinom (2*N) := by exact_mod_cast Nat.centralBinom_pos (2*N)
  rw [centralBinomialDoublingRatio, Real.log_div h2.ne' (pow_ne_zero _ h1.ne'), Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  rw [Nat.centralBinom_eq_two_mul_choose (2*N), Nat.centralBinom_eq_two_mul_choose N,
    show 2*(2*N) = 4*N by omega]

theorem centralBinomialDoublingRatio_log_lower (N : ℕ) :
    Real.log ((N : ℝ)+1)/2 ≤ Real.log (centralBinomialDoublingRatio N) := by
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (N : ℝ)+1)
    (add_one_le_centralBinomialDoublingRatio_sq N)
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

private theorem doubling_step_sq_upper (x : ℝ) (hx : 0 ≤ x) :
    (((4*x+1)*(4*x+3)*(x+1))/(2*(2*x+1)^3))^2*x ≤ x+1 := by
  have hd : 0 < 2*(2*x+1)^3 := by positivity
  have hp : 0 ≤ (2*(2*x+1)^3)^2*(x+1)-((4*x+1)*(4*x+3)*(x+1))^2*x := by
    have he : (2*(2*x+1)^3)^2*(x+1)-((4*x+1)*(4*x+3)*(x+1))^2*x =
        (x+1)*(96*x^4+192*x^3+135*x^2+39*x+4) := by ring
    rw [he]
    positivity
  calc
    _ = (((4*x+1)*(4*x+3)*(x+1))^2*x)/(2*(2*x+1)^3)^2 := by rw [div_pow]; ring
    _ ≤ _ := (div_le_iff₀ (sq_pos_of_pos hd)).2 (by nlinarith only [hp])

theorem centralBinomialDoublingRatio_sq_upper (n : ℕ) :
    (centralBinomialDoublingRatio (n+1))^2 ≤ (9/4 : ℝ)*((n+1 : ℕ) : ℝ) := by
  induction n with
  | zero => norm_num [centralBinomialDoublingRatio, Nat.centralBinom, Nat.choose]
  | succ n ih =>
    rw [centralBinomialDoublingRatio_succ (n+1), mul_pow]
    calc
      _ ≤ (((4*((n+1 : ℕ) : ℝ)+1)*(4*((n+1 : ℕ) : ℝ)+3)*(((n+1 : ℕ) : ℝ)+1))/
          (2*(2*((n+1 : ℕ) : ℝ)+1)^3))^2*((9/4 : ℝ)*((n+1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ = (9/4 : ℝ)*
          ((((4*((n+1 : ℕ) : ℝ)+1)*(4*((n+1 : ℕ) : ℝ)+3)*(((n+1 : ℕ) : ℝ)+1))/
          (2*(2*((n+1 : ℕ) : ℝ)+1)^3))^2*((n+1 : ℕ) : ℝ)) := by ring
      _ ≤ (9/4 : ℝ)*(((n+1 : ℕ) : ℝ)+1) :=
        mul_le_mul_of_nonneg_left (doubling_step_sq_upper _ (Nat.cast_nonneg _)) (by norm_num)
      _ = _ := by push_cast; ring

theorem centralBinomialDoublingRatio_log_upper (n : ℕ) :
    Real.log (centralBinomialDoublingRatio (n+1)) ≤
      Real.log (n+1 : ℕ)/2+Real.log (9/4 : ℝ)/2 := by
  have hp := centralBinomialDoublingRatio_pos (n+1)
  have hlog := Real.log_le_log (sq_pos_of_pos hp) (centralBinomialDoublingRatio_sq_upper n)
  rw [Real.log_pow, Real.log_mul (by norm_num : (9/4 : ℝ) ≠ 0) (by positivity)] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

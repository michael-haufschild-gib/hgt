import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Quadratic logarithmic cost of the gapped-spin coefficient box -/
open Real
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut

/-- A width of order 3⁻ᴷ/M on M coordinates and a single displaced
field of order M cost at most a constant times M² in the logarithm. -/
theorem quadratic_box_prefactor {b : ℝ} (hb : 0 < b) :
    ∃ C > (0:ℝ), ∀ M K : ℕ, 1 ≤ M → K ≤ M →
      exp (-C*(M:ℝ)^2) ≤ (b/((M:ℝ)*3^K))^M*exp (-(9*(M:ℝ)+(2*(M:ℝ)+6)^2)/2)/(1800:ℝ)^14 := by
  let C := |log b|+log 3+14*log 1800+42
  have h₃ := log_pos (by norm_num : (1:ℝ)<3)
  have h₁₈ := log_pos (by norm_num : (1:ℝ)<1800)
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro M K hM hK
  let x : ℝ := M
  have hx : 1 ≤ x := by dsimp only [x]; exact_mod_cast hM
  have hk : (K:ℝ) ≤ x := by dsimp only [x]; exact_mod_cast hK
  have hx₀ := zero_lt_one.trans_le hx
  have hx₂ : x ≤ x^2 := by nlinarith only [mul_nonneg hx₀.le (sub_nonneg.mpr hx)]
  have hpos : 0 < b/(x*3^K) := by positivity
  apply (log_le_log_iff (exp_pos _) (div_pos (mul_pos (pow_pos hpos M) (exp_pos _)) (by positivity))).mp
  change log (exp (-C*x^2)) ≤ log ((b/(x*3^K))^M*exp (-(9*x+(2*x+6)^2)/2)/(1800:ℝ)^14)
  rw [log_exp,log_div (mul_pos (pow_pos hpos M) (exp_pos _)).ne' (by positivity),
    log_mul (pow_pos hpos M).ne' (exp_pos _).ne',log_pow,log_exp,log_pow,
    log_div hb.ne' (mul_pos hx₀ (by positivity)).ne',log_mul hx₀.ne' (by positivity),log_pow]
  change -C*x^2 ≤ x*(log b-(log x+(K:ℝ)*log 3))+(-(9*x+(2*x+6)^2)/2)-14*log 1800
  have hlog := (log_le_sub_one_of_pos hx₀).trans (sub_le_self x zero_le_one)
  have hsize : 2*x+6 ≤ 8*x := by linarith only [hx]
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 2*x+6) hsize 2
  have hlb : -(x*|log b|) ≤ x*log b := by
    simpa only [mul_neg] using mul_le_mul_of_nonneg_left (neg_abs_le (log b)) hx₀.le
  dsimp only [C]
  nlinarith only [hs,hx₂,hlb,mul_le_mul_of_nonneg_left hlog hx₀.le,
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk h₃.le) hx₀.le,
    mul_le_mul_of_nonneg_right hx₂ (abs_nonneg (log b)),
    mul_le_mul_of_nonneg_right (hx.trans hx₂) h₁₈.le,sq_nonneg x]

#print axioms quadratic_box_prefactor
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut

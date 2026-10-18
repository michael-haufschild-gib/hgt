import GaloisForLFunctions.BiScaleUncertainty.CompactAutocorrelationPolarMoment
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarFactorialPolarPacket
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Cast

/-! The factorial ramp's polar term is explicit and nonpositive. Vandermonde's
identity supplies the sign of the factorial second difference; no prime
distribution estimate or smooth-source assumption is involved. -/

open MeasureTheory Set
open scoped BigOperators CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower RHTower.ArchimedeanAnomaly
noncomputable section
set_option autoImplicit false

private theorem factorialLog_eq_log_factorial (K : ℕ) :
    floorSummatory chebyshevPsi K = Real.log (K.factorial : ℝ) := by
  rw [floorSummatory_chebyshevPsi]
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity), ih]
    ring

private theorem log_central_binomial (K : ℕ) :
    Real.log ((2*K).choose K : ℝ) =
      floorSummatory chebyshevPsi (2*K)-2*floorSummatory chebyshevPsi K := by
  have he : ((2*K).choose K : ℝ) =
      ((2*K).factorial : ℝ)/((K.factorial : ℝ)*(K.factorial : ℝ)) := by
    simpa only [two_mul] using (Nat.cast_add_choose ℝ (a := K) (b := K))
  rw [he, Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    ← factorialLog_eq_log_factorial, ← factorialLog_eq_log_factorial]
  ring

/-- The bi-null producer is the logarithmic excess of the doubled central binomial. -/
theorem chebyshevBiNullProducer_eq_log_binomial (N : ℕ) :
    chebyshevBiNullProducer N =
      Real.log ((4*N).choose (2*N) : ℝ)-2*Real.log ((2*N).choose N : ℝ) := by
  have h4 := log_central_binomial (2*N)
  rw [show 2*(2*N) = 4*N by ring] at h4
  rw [h4, log_central_binomial, chebyshevBiNullProducer]
  ring

/-- One term of Vandermonde proves the sign of the entire factorial second difference. -/
theorem chebyshevBiNullProducer_nonneg (N : ℕ) : 0 ≤ chebyshevBiNullProducer N := by
  have hc : ((2*N).choose N)^2 ≤ (4*N).choose (2*N) := by
    have hs := Finset.single_le_sum
      (f := fun j => ((2*N).choose j)^2) (s := Finset.range (2*N+1))
      (fun j _ => Nat.zero_le _) (show N ∈ Finset.range (2*N+1) by simp; omega)
    rw [Nat.sum_range_choose_sq, show 2*(2*N) = 4*N by ring] at hs
    exact hs
  have hp : (0 : ℝ) < (2*N).choose N := by
    exact_mod_cast (Nat.choose_pos (show N ≤ 2*N by omega))
  have hl := Real.log_le_log (sq_pos_of_pos hp) (show ((2*N).choose N : ℝ)^2 ≤
      ((4*N).choose (2*N) : ℝ) by exact_mod_cast hc)
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  rw [chebyshevBiNullProducer_eq_log_binomial]
  linarith

/-- Exact signed pole correction for the concrete compact ramp. -/
theorem integral_polar_autocorr_factorialRamp_eq (n : ℕ) :
    (∫ x in Ici (0 : ℝ), polarDensity x*autocorr (factorialRampSource n) x) =
      -((1+sourceFactorialCollar (n+1)/2)*harmonicCorrection (n+1)*
        chebyshevBiNullProducer (n+1))/(n+1 : ℕ) := by
  rw [integral_polar_autocorr_eq_moments]
  change (∫ u, Real.exp (u/2)*rampBiNull (sourceFactorialCollar (n+1)) (n+1) u)*
    (∫ u, Real.exp (-(u/2))*rampBiNull (sourceFactorialCollar (n+1)) (n+1) u) = _
  have hN : 1 ≤ n+1 := by omega
  have hε := sourceFactorialCollar_pos hN
  rw [integral_exp_half_rampBiNull hε, integral_exp_neg_half_rampBiNull hε hN,
    div_mul_div_comm, ← sq, Real.sq_sqrt (by positivity)]
  ring

/-- The pole lowers this ramp diagonal; it cannot be treated as a positive bonus. -/
theorem integral_polar_autocorr_factorialRamp_nonpos (n : ℕ) :
    (∫ x in Ici (0 : ℝ), polarDensity x*autocorr (factorialRampSource n) x) ≤ 0 := by
  rw [integral_polar_autocorr_factorialRamp_eq]
  have hε := (sourceFactorialCollar_pos (by omega : 1 ≤ n+1)).le
  have hH := (harmonicCorrection_bounds (by omega : 1 ≤ n+1)).1
  have hC := chebyshevBiNullProducer_nonneg (n+1)
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity)

/-- Both polar branches together have an explicit vanishing-scale envelope. -/
theorem abs_integral_polar_autocorr_factorialRamp_le (n : ℕ) :
    |∫ x in Ici (0 : ℝ), polarDensity x*autocorr (factorialRampSource n) x| ≤
      2*(5*Real.log (4*(n+1 : ℕ)+1)+1)/(n+1 : ℕ) := by
  rw [integral_polar_autocorr_eq_moments, abs_mul]
  obtain ⟨hp, hm⟩ := factorialRamp_full_moments n
  calc
    _ ≤ (2/Real.sqrt (n+1 : ℕ))*
        ((5*Real.log (4*(n+1 : ℕ)+1)+1)/Real.sqrt (n+1 : ℕ)) :=
      mul_le_mul hp hm (abs_nonneg _) (by positivity)
    _ = _ := by rw [div_mul_div_comm, ← sq, Real.sq_sqrt (by positivity)]

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

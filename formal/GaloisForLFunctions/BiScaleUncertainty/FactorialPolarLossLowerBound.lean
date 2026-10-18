import GaloisForLFunctions.BiScaleUncertainty.CentralBinomialRatioGrowth
import GaloisForLFunctions.BiScaleUncertainty.FactorialBiNullPolarSign

/-! The actual factorial polar loss has logarithmic size. The central-binomial
growth and a positive harmonic correction supply a lower bound at every index. -/

open MeasureTheory Set
open scoped BigOperators CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower RHTower.ArchimedeanAnomaly
noncomputable section
set_option autoImplicit false

theorem chebyshevBiNullProducer_log_lower (N : ℕ) :
    Real.log ((N : ℝ)+1)/2 ≤ chebyshevBiNullProducer N := by
  rw [chebyshevBiNullProducer_eq_log_binomial, ← centralBinomialDoublingRatio_log]
  exact centralBinomialDoublingRatio_log_lower N

theorem chebyshevBiNullProducer_log_upper (n : ℕ) :
    chebyshevBiNullProducer (n+1) ≤ Real.log (n+1 : ℕ)/2+Real.log (9/4 : ℝ)/2 := by
  rw [chebyshevBiNullProducer_eq_log_binomial, ← centralBinomialDoublingRatio_log]
  exact centralBinomialDoublingRatio_log_upper n

private theorem reciprocal_telescope (a : ℝ) (M : ℕ) :
    (∑ k ∈ Finset.range M, (1/(a+k)-1/(a+k+1))) = 1/a-1/(a+M) := by
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

private theorem harmonic_pair_bounds {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    (2*(N : ℝ)/(2*(N : ℝ)+1))*
        (1/(4*((N : ℝ)+k))-1/(4*((N : ℝ)+k+1))) ≤
      1/(2*((N : ℝ)+k)+1)-1/(2*((N : ℝ)+k)+2) ∧
    1/(2*((N : ℝ)+k)+1)-1/(2*((N : ℝ)+k)+2) ≤
      1/(4*((N : ℝ)+k))-1/(4*((N : ℝ)+k+1)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hbr : 0 ≤ 1/(4*((N : ℝ)+k))-1/(4*((N : ℝ)+k+1)) :=
    sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith))
  have he : 1/(2*((N : ℝ)+k)+1)-1/(2*((N : ℝ)+k)+2) =
      (2*((N : ℝ)+k)/(2*((N : ℝ)+k)+1))*
        (1/(4*((N : ℝ)+k))-1/(4*((N : ℝ)+k+1))) := by field_simp; ring
  have hlo : 2*(N : ℝ)/(2*(N : ℝ)+1) ≤ 2*((N : ℝ)+k)/(2*((N : ℝ)+k)+1) := by
    have hd : 2*((N : ℝ)+k)/(2*((N : ℝ)+k)+1)-2*(N : ℝ)/(2*(N : ℝ)+1) =
        2*(k : ℝ)/((2*((N : ℝ)+k)+1)*(2*(N : ℝ)+1)) := by field_simp; ring
    have hh : 0 ≤ 2*((N : ℝ)+k)/(2*((N : ℝ)+k)+1)-2*(N : ℝ)/(2*(N : ℝ)+1) := by
      rw [hd]
      positivity
    exact sub_nonneg.mp hh
  have hhi : 2*((N : ℝ)+k)/(2*((N : ℝ)+k)+1) ≤ 1 :=
    (div_le_iff₀ (by positivity)).2 (by linarith)
  rw [he]
  exact ⟨mul_le_mul_of_nonneg_right hlo hbr,
    by simpa only [one_mul] using mul_le_mul_of_nonneg_right hhi hbr⟩

/-- Finite telescoping bounds already determine the limiting harmonic correction. -/
theorem harmonicCorrection_bounds_sharp {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ)/(2*(N : ℝ)+1) ≤ harmonicCorrection N ∧ harmonicCorrection N ≤ 1/2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  let p : ℕ → ℝ := fun k => 1/(2*((N : ℝ)+k)+1)-1/(2*((N : ℝ)+k)+2)
  let q : ℕ → ℝ := fun k => 1/(4*((N : ℝ)+k))-1/(4*((N : ℝ)+k+1))
  have hsum : (∑ k ∈ Finset.range N, q k) = 1/(8*(N : ℝ)) := by
    calc
      _ = (1/4 : ℝ)*∑ k ∈ Finset.range N, (1/((N : ℝ)+k)-1/((N : ℝ)+k+1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        dsimp [q]
        field_simp
      _ = (1/4 : ℝ)*(1/(N : ℝ)-1/((N : ℝ)+(N : ℝ))) := by rw [reciprocal_telescope]
      _ = _ := by field_simp; ring
  have hlo : (2*(N : ℝ)/(2*(N : ℝ)+1))*(∑ k ∈ Finset.range N, q k) ≤
      ∑ k ∈ Finset.range N, p k := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => (harmonic_pair_bounds hN k).1
  have hhi : (∑ k ∈ Finset.range N, p k) ≤ ∑ k ∈ Finset.range N, q k :=
    Finset.sum_le_sum fun k _ => (harmonic_pair_bounds hN k).2
  rw [hsum] at hlo hhi
  rw [harmonicCorrection_eq_pairs]
  change (N : ℝ)/(2*(N : ℝ)+1) ≤ 4*(N : ℝ)*(∑ k ∈ Finset.range N, p k) ∧
    4*(N : ℝ)*(∑ k ∈ Finset.range N, p k) ≤ 1/2
  constructor
  · calc
      _ = 4*(N : ℝ)*((2*(N : ℝ)/(2*(N : ℝ)+1))*(1/(8*(N : ℝ)))) := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo (by positivity)
  · calc
      _ ≤ 4*(N : ℝ)*(1/(8*(N : ℝ))) := mul_le_mul_of_nonneg_left hhi (by positivity)
      _ = _ := by field_simp; ring

theorem harmonicCorrection_quarter_le {N : ℕ} (hN : 1 ≤ N) :
    (1 : ℝ)/4 ≤ harmonicCorrection N := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hb : (1 : ℝ)/4 ≤ (N : ℝ)/(2*(N : ℝ)+1) :=
    (le_div_iff₀ (by positivity)).2 (by linarith)
  exact hb.trans (harmonicCorrection_bounds_sharp hN).1

/-- Magnitude of the actual signed polar contribution of the compact ramp. -/
def factorialPolarLoss (n : ℕ) : ℝ :=
  |∫ x in Ici (0 : ℝ), polarDensity x*autocorr (factorialRampSource n) x|

theorem factorialPolarLoss_eq (n : ℕ) :
    factorialPolarLoss n =
      ((1+sourceFactorialCollar (n+1)/2)*harmonicCorrection (n+1)*
        chebyshevBiNullProducer (n+1))/(n+1 : ℕ) := by
  rw [factorialPolarLoss, abs_of_nonpos (integral_polar_autocorr_factorialRamp_nonpos n),
    integral_polar_autocorr_factorialRamp_eq, neg_div, neg_neg]

/-- A pointwise lower bound for the whole pole, with both branches retained. -/
theorem factorialPolarLoss_log_lower (n : ℕ) :
    Real.log (n+2 : ℕ)/(8*((n+1 : ℕ) : ℝ)) ≤ factorialPolarLoss n := by
  have hn : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hε := sourceFactorialCollar_pos (by omega : 1 ≤ n+1)
  have hH := harmonicCorrection_quarter_le (by omega : 1 ≤ n+1)
  have hH0 := (harmonicCorrection_bounds (by omega : 1 ≤ n+1)).1
  have hC := chebyshevBiNullProducer_log_lower (n+1)
  rw [show (((n+1 : ℕ) : ℝ)+1) = ((n+2 : ℕ) : ℝ) by push_cast; ring] at hC
  have hC0 := chebyshevBiNullProducer_nonneg (n+1)
  have hlog : 0 ≤ Real.log (n+2 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n+2 by omega))
  have hscale : (1 : ℝ) ≤ 1+sourceFactorialCollar (n+1)/2 := by linarith
  have hprod : (1/4 : ℝ)*(Real.log (n+2 : ℕ)/2) ≤
      (1+sourceFactorialCollar (n+1)/2)*harmonicCorrection (n+1)*
        chebyshevBiNullProducer (n+1) := by
    calc
      _ ≤ harmonicCorrection (n+1)*chebyshevBiNullProducer (n+1) :=
        mul_le_mul hH hC (by positivity) hH0
      _ ≤ _ := by
        simpa only [one_mul, mul_assoc] using
          mul_le_mul_of_nonneg_right hscale (mul_nonneg hH0 hC0)
  rw [factorialPolarLoss_eq]
  calc
    _ = ((1/4 : ℝ)*(Real.log (n+2 : ℕ)/2))/((n+1 : ℕ) : ℝ) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hprod hn.le

theorem factorialPolarLoss_pos (n : ℕ) : 0 < factorialPolarLoss n := by
  have hlog : 0 < Real.log (n+2 : ℕ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n+2 by omega))
  exact lt_of_lt_of_le (div_pos hlog (by positivity)) (factorialPolarLoss_log_lower n)

theorem factorialPolarLoss_scaled_lower (n : ℕ) :
    Real.log 2/8 ≤ ((n+1 : ℕ) : ℝ)*factorialPolarLoss n := by
  have hn : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hlog : Real.log 2 ≤ Real.log (n+2 : ℕ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ n+2 by omega))
  calc
    _ ≤ Real.log (n+2 : ℕ)/8 := div_le_div_of_nonneg_right hlog (by norm_num)
    _ = ((n+1 : ℕ) : ℝ)*(Real.log (n+2 : ℕ)/(8*((n+1 : ℕ) : ℝ))) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (factorialPolarLoss_log_lower n) hn.le

theorem integral_polar_autocorr_factorialRamp_neg (n : ℕ) :
    (∫ x in Ici (0 : ℝ), polarDensity x*autocorr (factorialRampSource n) x) < 0 := by
  have hp := factorialPolarLoss_pos n
  rw [factorialPolarLoss, abs_of_nonpos (integral_polar_autocorr_factorialRamp_nonpos n)] at hp
  linarith

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

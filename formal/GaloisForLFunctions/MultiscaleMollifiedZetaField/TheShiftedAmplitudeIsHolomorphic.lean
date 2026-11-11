import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheShiftedSelbergAmplitudeHasTheSameMajorant
import GaloisForLFunctions.HTGeometry.BanachTriangularExponential
import Mathlib.Analysis.Complex.Liouville

/-!
# Holomorphic shifted amplitudes with the original absolute majorant

The prime-factor formula extends the correction amplitude to an entire
function. The exponential increment bound controls every complex prime
factor by its unshifted absolute value times a small real power. On a
finite cutoff, reciprocal-logarithmic shifts have a constant majorant.
-/

open ArithmeticFunction Finset Complex
open RHTower.Sieve

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The entire prime-factor continuation of the shifted correction amplitude. -/
def complexShiftedSelbergAmplitude (n : ℕ) (z : ℂ) : ℂ :=
  if n = 0 then 0 else
    n.factorization.prod (fun p k =>
      (1 - (p : ℂ) * Complex.exp (z * (Real.log p : ℂ))) / (p : ℂ) ^ k)

/-- A complex prime numerator retains the original majorant. -/
theorem norm_shifted_prime_numerator_le {p : ℝ} (hp : 2 ≤ p) (z : ℂ) :
    ‖1 - (p : ℂ) * Complex.exp (z * (Real.log p : ℂ))‖ ≤
      (p - 1) * p ^ (2 * ‖z‖) := by
  have hp0 : 0 < p := by linarith only [hp]
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by linarith only [hp])
  let q : ℝ := Real.exp (‖z‖ * Real.log p)
  have hq : 1 ≤ q := Real.one_le_exp (mul_nonneg (norm_nonneg z) hl)
  have hinc : ‖Complex.exp (z * (Real.log p : ℂ)) - 1‖ ≤ q - 1 := by
    have hh := GaloisForLFunctions.HTGeometry.FormationDust.norm_exp_sub_one_le
      (z * (Real.log p : ℂ))
    simpa only [← Complex.exp_eq_exp_ℂ, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hl, q] using hh
  have hbase : ‖(1 : ℂ) - p‖ = p - 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith only [hp])]
    ring
  have htri : ‖1 - (p : ℂ) * Complex.exp (z * (Real.log p : ℂ))‖ ≤ p * q - 1 := by
    calc
      _ = ‖((1 : ℂ) - p) - p * (Complex.exp (z * (Real.log p : ℂ)) - 1)‖ := by congr 1; ring
      _ ≤ ‖(1 : ℂ) - p‖ + ‖(p : ℂ) * (Complex.exp (z * (Real.log p : ℂ)) - 1)‖ := norm_sub_le _ _
      _ ≤ (p - 1) + p * (q - 1) := by
        rw [hbase, norm_mul, Complex.norm_real, Real.norm_of_nonneg hp0.le]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hinc hp0.le)
      _ = p * q - 1 := by ring
  have hpq : 1 ≤ (p - 1) * q := by
    simpa only [one_mul] using mul_le_mul (show 1 ≤ p - 1 by linarith only [hp])
      hq zero_le_one (show 0 ≤ p - 1 by linarith only [hp])
  have hprod : 0 ≤ (q - 1) * ((p - 1) * q - 1) :=
    mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hpq)
  have hpower : q ^ 2 = p ^ (2 * ‖z‖) := by
    dsimp only [q]
    rw [Real.rpow_def_of_pos hp0, pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ p * q - 1 := htri
    _ ≤ (p - 1) * q ^ 2 := by nlinarith only [hprod]
    _ = _ := by rw [hpower]

private theorem norm_shifted_prime_factor_le (z : ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ‖(1 - (p : ℂ) * Complex.exp (z * (Real.log p : ℂ))) / (p : ℂ) ^ (k + 1)‖ ≤
      (p : ℝ) ^ (2 * ‖z‖) * |reciprocalMoebiusAmplitude (p ^ (k + 1))| := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [norm_div, norm_pow, Complex.norm_natCast]
  rw [← powerShiftedReciprocalAmplitude_zero, powerShiftedReciprocalAmplitude_prime_pow 0 hp]
  simp only [add_zero, Real.rpow_one, abs_div, abs_of_pos (pow_pos hp0 _)]
  have he : |1 - (p : ℝ)| = p - 1 := by
    rw [abs_of_nonpos (by linarith only [hp2])]
    ring
  rw [he]
  exact (div_le_div_of_nonneg_right (norm_shifted_prime_numerator_le hp2 z)
    (pow_nonneg hp0.le _)).trans_eq (by ring)

/-- The entire continuation agrees with the arithmetic amplitude on the real axis. -/
theorem complexShiftedSelbergAmplitude_ofReal (n : ℕ) (c : ℝ) :
    complexShiftedSelbergAmplitude n (c : ℂ) = (powerShiftedReciprocalAmplitude c n : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [complexShiftedSelbergAmplitude]
  rw [complexShiftedSelbergAmplitude, if_neg hn,
    IsMultiplicative.multiplicative_factorization (powerShiftedReciprocalAmplitude c)
      (isMultiplicative_powerShiftedReciprocalAmplitude c) hn]
  simp only [Finsupp.prod]
  change (∏ p ∈ n.factorization.support,
    (1 - (p : ℂ) * Complex.exp ((c : ℂ) * (Real.log p : ℂ))) / (p : ℂ) ^ n.factorization p) =
      Complex.ofRealHom (∏ p ∈ n.factorization.support,
        powerShiftedReciprocalAmplitude c (p ^ n.factorization p))
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)
  have hk : 1 ≤ n.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  obtain ⟨k, he⟩ : ∃ k, n.factorization p = k + 1 := ⟨n.factorization p - 1, by omega⟩
  rw [he, powerShiftedReciprocalAmplitude_prime_pow c hprime]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hexp : (p : ℝ) * Real.exp (c * Real.log p) = (p : ℝ) ^ (1 + c) := by
    rw [Real.rpow_add hp0, Real.rpow_one, Real.rpow_def_of_pos hp0]
    congr 1
    congr 1
    ring
  rw [show (c : ℂ) * (Real.log p : ℂ) = ((c * Real.log p : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_exp]
  exact_mod_cast congrArg (fun a : ℝ => (1 - a) / (p : ℝ) ^ (k + 1)) hexp

/-- The amplitude is entire, including its zero-index convention. -/
theorem differentiable_complexShiftedSelbergAmplitude (n : ℕ) :
    Differentiable ℂ (complexShiftedSelbergAmplitude n) := by
  unfold complexShiftedSelbergAmplitude Finsupp.prod
  split_ifs <;> fun_prop

/-- The real small-power majorant also controls every complex shift. -/
theorem norm_complexShiftedSelbergAmplitude_le (n : ℕ) (z : ℂ) :
    ‖complexShiftedSelbergAmplitude n z‖ ≤
      (n : ℝ) ^ (2 * ‖z‖) * |reciprocalMoebiusAmplitude n| := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [complexShiftedSelbergAmplitude]
  rw [complexShiftedSelbergAmplitude, if_neg hn.ne',
    IsMultiplicative.multiplicative_factorization reciprocalMoebiusAmplitude
      isMultiplicative_reciprocalMoebiusAmplitude hn.ne',
    ← rpowArith_apply_of_ne_zero (2 * ‖z‖) hn.ne',
    IsMultiplicative.multiplicative_factorization (rpowArith (2 * ‖z‖))
      (isMultiplicative_rpowArith _) hn.ne']
  simp only [Finsupp.prod]
  rw [norm_prod, Finset.abs_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro p hp
    exact norm_nonneg _
  · intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)
    have hk : 1 ≤ n.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    obtain ⟨k, he⟩ : ∃ k, n.factorization p = k + 1 := ⟨n.factorization p - 1, by omega⟩
    rw [he, rpowArith_apply_of_ne_zero _ (pow_ne_zero _ hprime.ne_zero)]
    refine (norm_shifted_prime_factor_le z hprime k).trans ?_
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    apply Real.rpow_le_rpow (Nat.cast_nonneg p) _ (by positivity)
    exact_mod_cast (show p ≤ p ^ (k + 1) by
      simpa only [pow_one] using Nat.pow_le_pow_right hprime.pos (show 1 ≤ k + 1 by omega))

/-- A reciprocal-logarithmic complex shift has a constant majorant on its cutoff. -/
theorem norm_complexShiftedSelbergAmplitude_log_shift_le {N : ℕ} (hN : 1 < N)
    (z : ℂ) {n : ℕ} (hn : n ≤ N) :
    ‖complexShiftedSelbergAmplitude n (z / (Real.log N : ℂ))‖ ≤
      Real.exp (2 * ‖z‖) * |reciprocalMoebiusAmplitude n| := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hl : 0 < Real.log N := Real.log_pos hN1
  refine (norm_complexShiftedSelbergAmplitude_le n (z / (Real.log N : ℂ))).trans ?_
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  calc
    _ ≤ (N : ℝ) ^ (2 * ‖z / (Real.log N : ℂ)‖) :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hn) (by positivity)
    _ = Real.exp (2 * ‖z‖) := by
      rw [Real.rpow_def_of_pos hN0, norm_div, Complex.norm_real, Real.norm_of_nonneg hl.le]
      congr 1
      field_simp [hl.ne'] <;> ring

end GaloisForLFunctions.MultiscaleMollifiedZetaField

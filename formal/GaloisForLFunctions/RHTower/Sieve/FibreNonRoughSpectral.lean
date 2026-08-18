import GaloisForLFunctions.RHTower.Sieve.FibreRamareSplit
import GaloisForLFunctions.RHTower.Sieve.ScaledFibreBridge

/-!
# The Möbius fibre mean square on the spectral side, without Turán–Kubilius

`Sieve/OmegaSpectralFibre` reaches the spectral side through the Turán–Kubilius transfer, which
writes `∑ μ ≈ (1/W) ∑ μ·ω_P` and pays the variance `∑(ω_P − W)² ≍ |I|·W` through Cauchy–Schwarz.
That square root turns a relative error `W` into `1/W`, and `W ≤ log log x + O(1)` for every
admissible prime range, so no choice of parameters makes the resulting mean square better than
`1/log log x`.

Splitting instead at the rough integers costs no square root.  The fibre sum of `μ` differs from the
fibre sum of `μ` restricted to integers with a designated prime factor by the rough count alone,
which Brun's sieve bounds by `≍ |I|/log z`, and that error enters the mean square **squared**.  The
restricted weight is still unit-bounded, so the coefficient-general fibre bridge carries it to the
spectral side unchanged.

The result is the analogue of `sum_sq_fibreSum_moebius_le_omegaSpectral` with no `1/W²` in front of
the spectral term and no variance behind it.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- The Möbius function restricted to integers carrying a designated prime factor. -/
def nonRoughMoebius (P : Finset ℕ) (n : ℕ) : ℝ :=
  if (primeFactorsIn P n).Nonempty then ((moebius n : ℤ) : ℝ) else 0

theorem abs_nonRoughMoebius_le_one (P : Finset ℕ) (n : ℕ) : |nonRoughMoebius P n| ≤ 1 := by
  rw [nonRoughMoebius]
  split
  · exact abs_moebius_real_le_one n
  · simp

/-- The restricted sum is the sum over the non-rough part of the range. -/
theorem sum_nonRoughMoebius (P S : Finset ℕ) :
    ∑ b ∈ S, nonRoughMoebius P b
      = ∑ b ∈ {b ∈ S | (primeFactorsIn P b).Nonempty}, ((moebius b : ℤ) : ℝ) := by
  classical
  rw [Finset.sum_filter]
  rfl

/-- **The rough defect of one fibre.**  The fibre sum of `μ` differs from its non-rough part by the
rough count, which Brun's sieve bounds by the same error the Ramaré split pays. -/
theorem abs_fibreSum_sub_nonRough_le {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) {z r : ℕ} (hz : 2 ≤ z)
    (hr : Even r) {lam : ℝ} (hlam : 1 ≤ lam) {a : ℕ} (ha : a ∈ outerBlock x h) :
    |∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ)
        - ∑ b ∈ innerFibre x h a, nonRoughMoebius (Nat.primesLE z) b|
      ≤ fibreRamareSieveError h z r lam := by
  classical
  have hz2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos (by linarith)
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le zero_lt_one hlam
  have hpow : (0 : ℝ) < (Real.log z) ^ lam := Real.rpow_pos_of_pos hlogz _
  have hlamr : (0 : ℝ) < lam ^ r := pow_pos hlam0 r
  set P : Finset ℕ := Nat.primesLE z with hPdef
  set t : ℕ := fibreStartIdx x a with htdef
  set L : ℕ := fibreLen x h a with hLdef
  have hfib : innerFibre x h a = Finset.Ioc t (t + L) := innerFibre_eq_Ioc hx hh ha
  -- the difference is the rough sum
  have hsplit := Finset.sum_filter_add_sum_filter_not (innerFibre x h a)
    (fun b => (primeFactorsIn P b).Nonempty) (fun b => ((moebius b : ℤ) : ℝ))
  have hdiff : ∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ)
      - ∑ b ∈ innerFibre x h a, nonRoughMoebius P b
      = ∑ b ∈ {b ∈ innerFibre x h a | ¬ (primeFactorsIn P b).Nonempty},
          ((moebius b : ℤ) : ℝ) := by
    rw [sum_nonRoughMoebius]
    linarith [hsplit]
  rw [hdiff]
  -- bound by the rough count
  have hset : {b ∈ innerFibre x h a | ¬ (primeFactorsIn P b).Nonempty}
      = {b ∈ Finset.Ioc t (t + L) | ∀ p ∈ Nat.primesLE z, ¬ p ∣ b} := by
    rw [hfib]
    refine Finset.filter_congr ?_
    intro n _
    rw [Finset.not_nonempty_iff_eq_empty, primeFactorsIn_eq_empty_iff, hPdef]
  rw [hset]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun n _ => abs_moebius_real_le_one n)) ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  refine le_trans (card_rough_Ioc_le hz (by omega) hr hlam) ?_
  have hlen : (((t + L : ℕ) : ℝ) - (t : ℝ)) = (L : ℝ) := by push_cast; ring
  rw [hlen]
  have hLle : (L : ℝ) ≤ ((⌈h⌉₊ + 1 : ℕ) : ℝ) := by
    have := fibreLen_le hx hh ha
    exact_mod_cast this
  have hc1 : (0 : ℝ) ≤ Real.exp mertensSecondLowerConst / Real.log z := by positivity
  have hc2 : (0 : ℝ)
      ≤ Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam / lam ^ r := by
    positivity
  rw [fibreRamareSieveError]
  have e1 : (L : ℝ) * (Real.exp mertensSecondLowerConst / Real.log z)
      ≤ ((⌈h⌉₊ + 1 : ℕ) : ℝ) * (Real.exp mertensSecondLowerConst / Real.log z) :=
    mul_le_mul_of_nonneg_right hLle hc1
  have e2 : (L : ℝ)
        * (Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam / lam ^ r)
      ≤ ((⌈h⌉₊ + 1 : ℕ) : ℝ)
        * (Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam / lam ^ r) :=
    mul_le_mul_of_nonneg_right hLle hc2
  linarith

/-- **The Möbius fibre mean square on the spectral side, with no Turán–Kubilius loss.**  The
spectral term carries no `1/W²`, and the sieve error appears squared. -/
theorem sum_sq_fibreSum_moebius_le_nonRough_spectral {x h : ℝ} (hx : 4 ≤ x) (hh0 : 0 ≤ h)
    (hhx : h ≤ Real.sqrt x) {z r : ℕ} (hz : 2 ≤ z) (hr : Even r) {lam : ℝ} (hlam : 1 ≤ lam) :
    ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ)) ^ 2
      ≤ 2 * (8 * Real.sqrt x
            * (∫ u : ℝ, ‖logWindowSum
                (fun n => ((nonRoughMoebius (Nat.primesLE z) n : ℝ) : ℂ))
                (fibreIndex x h) (fibreWidth x h) u‖ ^ 2)
          + 102 * 1 ^ 2 * (Real.sqrt x + 1))
        + 2 * ((outerBlock x h).card : ℝ) * (fibreRamareSieveError h z r lam) ^ 2 := by
  classical
  have hterm : ∀ a ∈ outerBlock x h,
      (∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ)) ^ 2
        ≤ 2 * (∑ b ∈ innerFibre x h a, nonRoughMoebius (Nat.primesLE z) b) ^ 2
          + 2 * (fibreRamareSieveError h z r lam) ^ 2 := by
    intro a ha
    set A : ℝ := ∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ) with hAdef
    set G : ℝ := ∑ b ∈ innerFibre x h a, nonRoughMoebius (Nat.primesLE z) b with hGdef
    have hdef := abs_fibreSum_sub_nonRough_le hx hh0 hz hr hlam ha
    rw [← hAdef, ← hGdef] at hdef
    have h0 : (0 : ℝ) ≤ fibreRamareSieveError h z r lam :=
      fibreRamareSieveError_nonneg hz hlam
    have hsq : (A - G) ^ 2 ≤ (fibreRamareSieveError h z r lam) ^ 2 := by
      nlinarith [abs_nonneg (A - G), sq_abs (A - G), hdef, h0]
    nlinarith [hsq, sq_nonneg (A - 2 * G)]
  have hstep : ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ)) ^ 2
      ≤ 2 * ∑ a ∈ outerBlock x h,
            (∑ b ∈ innerFibre x h a, nonRoughMoebius (Nat.primesLE z) b) ^ 2
        + 2 * ((outerBlock x h).card : ℝ) * (fibreRamareSieveError h z r lam) ^ 2 := by
    refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    ring
  have hbridge := sum_fibreSum_sq_le_integral_scaled (f := nonRoughMoebius (Nat.primesLE z))
    (B := 1) one_pos (fun n => abs_nonRoughMoebius_le_one _ n) hx hh0 hhx
  linarith [hstep, hbridge]

end

end RHTower.Sieve

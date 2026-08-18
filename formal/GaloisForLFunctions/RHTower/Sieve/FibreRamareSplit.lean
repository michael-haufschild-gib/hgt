import GaloisForLFunctions.RHTower.Sieve.RamareRoughBridge
import GaloisForLFunctions.RHTower.Sieve.FibreSquarefreeIngredients

/-!
# The fibre mean square through the exact Ramaré identity

The corpus's spectral chain reaches the `ω_P`-weighted polynomial through the Turán–Kubilius
transfer, which writes `∑ μ ≈ (1/W) ∑ μ·ω_P` and pays the variance `∑(ω_P − W)² ≍ |I|·W` through
Cauchy–Schwarz.  Taking that square root turns a relative error `W` into `1/W`, and since
`W ≤ log log x + O(1)` for every admissible prime range, the resulting mean square can never be
better than `1/log log x`.

Ramaré's identity is exact and needs no variance: the part of the sum carried by integers with no
designated prime factor is a rough-integer sum, bounded by Brun's sieve.  Crucially that error
enters the mean square **squared**, so a sieve density `1/log z` contributes `1/(log z)²` rather
than `1/W`.

This module performs the split at the fibre data: the fibre mean square is at most twice the mean
square of the Ramaré bilinear part plus twice the outer block times the squared sieve error.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- The uniform per-fibre Ramaré sieve error: the fundamental-lemma density at level `z` on a window
of length `⌈h⌉+1`, plus the truncation defect of Brun's pure sieve. -/
def fibreRamareSieveError (h : ℝ) (z r : ℕ) (lam : ℝ) : ℝ :=
  ((⌈h⌉₊ + 1 : ℕ) : ℝ) * (Real.exp mertensSecondLowerConst / Real.log z)
    + ((⌈h⌉₊ + 1 : ℕ) : ℝ)
        * (Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam / lam ^ r)
    + ((truncDivisors (primorial z) r).card : ℝ)

theorem fibreRamareSieveError_nonneg {h : ℝ} {z r : ℕ} (hz : 2 ≤ z) {lam : ℝ} (hlam : 1 ≤ lam) :
    0 ≤ fibreRamareSieveError h z r lam := by
  have hz2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos (by linarith)
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le zero_lt_one hlam
  have hpow : (0 : ℝ) < (Real.log z) ^ lam := Real.rpow_pos_of_pos hlogz _
  have hlamr : (0 : ℝ) < lam ^ r := pow_pos hlam0 r
  rw [fibreRamareSieveError]
  have h1 : (0 : ℝ) ≤ ((⌈h⌉₊ + 1 : ℕ) : ℝ) * (Real.exp mertensSecondLowerConst / Real.log z) := by
    positivity
  have h2 : (0 : ℝ) ≤ ((⌈h⌉₊ + 1 : ℕ) : ℝ)
      * (Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam / lam ^ r) := by
    positivity
  have h3 : (0 : ℝ) ≤ ((truncDivisors (primorial z) r).card : ℝ) := Nat.cast_nonneg _
  linarith

/-- **The Ramaré defect of one fibre.**  The fibre sum of `μ` differs from its Ramaré bilinear part
by at most the sieve error, uniformly over the outer block. -/
theorem abs_fibreSum_sub_ramare_le {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) {z r : ℕ} (hz : 2 ≤ z)
    (hr : Even r) {lam : ℝ} (hlam : 1 ≤ lam) {a : ℕ} (ha : a ∈ outerBlock x h) :
    |∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ)
        - ∑ p ∈ Nat.primesLE z, ∑ b ∈ {b ∈ innerFibre x h a | p ∣ b},
            ((moebius b : ℤ) : ℝ) / ((primeFactorsIn (Nat.primesLE z) b).card : ℝ)|
      ≤ fibreRamareSieveError h z r lam := by
  classical
  have hz2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos (by linarith)
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le zero_lt_one hlam
  have hpow : (0 : ℝ) < (Real.log z) ^ lam := Real.rpow_pos_of_pos hlogz _
  have hlamr : (0 : ℝ) < lam ^ r := pow_pos hlam0 r
  set t : ℕ := fibreStartIdx x a with htdef
  set L : ℕ := fibreLen x h a with hLdef
  have hfib : innerFibre x h a = Finset.Ioc t (t + L) := innerFibre_eq_Ioc hx hh ha
  have hbase := abs_sum_sub_ramare_Ioc_le (z := z) (a := t) (b := t + L) (r := r) hz
    (by omega) hr hlam (fun n => ((moebius n : ℤ) : ℝ)) (by norm_num)
    (fun n _ => abs_moebius_real_le_one n)
  rw [hfib]
  refine le_trans (le_of_eq_of_le ?_ hbase) ?_
  · congr 1
  · have hlen : (((t + L : ℕ) : ℝ) - (t : ℝ)) = (L : ℝ) := by push_cast; ring
    rw [hlen, one_mul]
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

/-- **The fibre mean square through the exact Ramaré identity.**  No variance and no
Cauchy–Schwarz: the sieve error enters squared. -/
theorem sum_sq_fibreSum_moebius_le_ramare_add_rough {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h)
    {z r : ℕ} (hz : 2 ≤ z) (hr : Even r) {lam : ℝ} (hlam : 1 ≤ lam) :
    ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ)) ^ 2
      ≤ 2 * ∑ a ∈ outerBlock x h,
            (∑ p ∈ Nat.primesLE z, ∑ b ∈ {b ∈ innerFibre x h a | p ∣ b},
                ((moebius b : ℤ) : ℝ) / ((primeFactorsIn (Nat.primesLE z) b).card : ℝ)) ^ 2
        + 2 * ((outerBlock x h).card : ℝ) * (fibreRamareSieveError h z r lam) ^ 2 := by
  classical
  have hterm : ∀ a ∈ outerBlock x h,
      (∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ)) ^ 2
        ≤ 2 * (∑ p ∈ Nat.primesLE z, ∑ b ∈ {b ∈ innerFibre x h a | p ∣ b},
              ((moebius b : ℤ) : ℝ) / ((primeFactorsIn (Nat.primesLE z) b).card : ℝ)) ^ 2
          + 2 * (fibreRamareSieveError h z r lam) ^ 2 := by
    intro a ha
    set A : ℝ := ∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ) with hAdef
    set R : ℝ := ∑ p ∈ Nat.primesLE z, ∑ b ∈ {b ∈ innerFibre x h a | p ∣ b},
        ((moebius b : ℤ) : ℝ) / ((primeFactorsIn (Nat.primesLE z) b).card : ℝ) with hRdef
    have hdef := abs_fibreSum_sub_ramare_le hx hh hz hr hlam ha
    rw [← hAdef, ← hRdef] at hdef
    have hsq : (A - R) ^ 2 ≤ (fibreRamareSieveError h z r lam) ^ 2 := by
      have h0 : (0 : ℝ) ≤ fibreRamareSieveError h z r lam :=
        fibreRamareSieveError_nonneg hz hlam
      have habs : |A - R| ≤ fibreRamareSieveError h z r lam := hdef
      nlinarith [abs_nonneg (A - R), sq_abs (A - R), habs, h0]
    nlinarith [hsq, sq_nonneg (A - 2 * R)]
  refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  ring

end

end RHTower.Sieve

import GaloisForLFunctions.RHTower.Sieve.UnweightedCorrelation
import GaloisForLFunctions.RHTower.Sieve.MoebiusWindowVariance

/-!
# The Möbius mean square from a correlation bound

Instantiating the unweighted reduction at `μ`.  Since `μ` is real, the Hermitian pair weight is the
plain product `μ(n)μ(n+h)`, and the diagonal is the squarefree count, so

`∑_{x < X} ‖∑_{x < n ≤ x+L} μ(n)‖² ≤ L·#{n < X+L+1 : n squarefree} + 2L(Lε + (2L+1)L)`

whenever `|∑_{n ∈ bulk} μ(n)μ(n+h)| ≤ ε` at the shifts `1 ≤ h < L`.

This is the cards' mean-square input reduced, with explicit constants, to a bound on `L-1` shifted
Möbius correlations — the statement a Chowla/Elliott-type theorem provides.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- For the real-valued `μ` the Hermitian pair weight is the plain product. -/
theorem re_moebiusC_mul_conj (n m : ℕ) :
    (moebiusC n * (starRingEnd ℂ) (moebiusC m)).re
      = ((moebius n : ℤ) : ℝ) * ((moebius m : ℤ) : ℝ) := by
  rw [moebiusC, moebiusC, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- **The Möbius mean square from a bound on the shifted correlations.** -/
theorem sum_normSq_window_moebius_le_of_correlation {X L : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hcorr : ∀ h ∈ Finset.Ico 1 L,
      |∑ n ∈ (Finset.range (X + L + 1 - h)).filter (fun n => L ≤ n ∧ n + h ≤ X),
        ((moebius n : ℤ) : ℝ) * ((moebius (n + h) : ℤ) : ℝ)| ≤ ε) :
    ∑ x ∈ Finset.range X, ‖∑ n ∈ Finset.Ioc x (x + L), moebiusC n‖ ^ (2 : ℕ)
      ≤ (L : ℝ) * (((Finset.range (X + L + 1)).filter (fun n => Squarefree n)).card : ℝ)
        + 2 * (L : ℝ) * ((L : ℝ) * ε + ((2 * L + 1 : ℕ) : ℝ) * (L : ℝ)) := by
  classical
  have hcorr' : ∀ h ∈ Finset.Ico 1 L,
      |∑ n ∈ (Finset.range (X + L + 1 - h)).filter (fun n => L ≤ n ∧ n + h ≤ X),
        (moebiusC n * (starRingEnd ℂ) (moebiusC (n + h))).re| ≤ ε := by
    intro h hh
    have hrw : ∑ n ∈ (Finset.range (X + L + 1 - h)).filter (fun n => L ≤ n ∧ n + h ≤ X),
        (moebiusC n * (starRingEnd ℂ) (moebiusC (n + h))).re
        = ∑ n ∈ (Finset.range (X + L + 1 - h)).filter (fun n => L ≤ n ∧ n + h ≤ X),
            ((moebius n : ℤ) : ℝ) * ((moebius (n + h) : ℤ) : ℝ) :=
      Finset.sum_congr rfl fun n _ => re_moebiusC_mul_conj n (n + h)
    rw [hrw]
    exact hcorr h hh
  have hbase := sum_normSq_window_le_of_unweighted (a := moebiusC) (X := X) (L := L) (ε := ε)
    hε norm_moebiusC_le_one hcorr'
  rwa [sum_normSq_moebiusC_eq_card] at hbase

/-- The complex window sum of `μ` has the real window sum as its modulus. -/
theorem normSq_sum_moebiusC_eq (t L : ℕ) :
    ‖∑ n ∈ Finset.Ioc t (t + L), moebiusC n‖ ^ (2 : ℕ)
      = (∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ)) ^ (2 : ℕ) := by
  have hre : ∑ n ∈ Finset.Ioc t (t + L), moebiusC n
      = (((∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun n _ => rfl
  rw [hre, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **The real mean square of `μ` from a correlation bound**, in the shape step 1 consumes. -/
theorem sum_sq_moebius_le_of_correlation {X L : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hcorr : ∀ h ∈ Finset.Ico 1 L,
      |∑ n ∈ (Finset.range (X + L + 1 - h)).filter (fun n => L ≤ n ∧ n + h ≤ X),
        ((moebius n : ℤ) : ℝ) * ((moebius (n + h) : ℤ) : ℝ)| ≤ ε) :
    ∑ t ∈ Finset.range X, (∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ)) ^ (2 : ℕ)
      ≤ (L : ℝ) * (((Finset.range (X + L + 1)).filter (fun n => Squarefree n)).card : ℝ)
        + 2 * (L : ℝ) * ((L : ℝ) * ε + ((2 * L + 1 : ℕ) : ℝ) * (L : ℝ)) := by
  have hbase := sum_normSq_window_moebius_le_of_correlation hε hcorr
  have hrw : ∑ x ∈ Finset.range X, ‖∑ n ∈ Finset.Ioc x (x + L), moebiusC n‖ ^ (2 : ℕ)
      = ∑ t ∈ Finset.range X, (∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ)) ^ (2 : ℕ) :=
    Finset.sum_congr rfl fun t _ => normSq_sum_moebiusC_eq t L
  rwa [hrw] at hbase

end RHTower.Sieve

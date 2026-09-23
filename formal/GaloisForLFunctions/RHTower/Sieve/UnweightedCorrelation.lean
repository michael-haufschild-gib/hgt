import GaloisForLFunctions.RHTower.Sieve.WindowKernelBulk
import GaloisForLFunctions.RHTower.Sieve.WindowShiftRange

/-!
# The variance from an unweighted correlation bound

The exact variance identity carries the kernel weights, while a citable correlation estimate bounds
the plain sum `∑_n a_n conj a_{n+h}` over the bulk.  Converting between them costs `(2L+1)L` per
shift, so a uniform bound `ε` on the bulk correlations at the shifts `1 ≤ h < L` gives

`∑_{x < X} ‖∑_{x < n ≤ x+L} a_n‖² ≤ L ∑_n ‖a_n‖² + 2L(Lε + (2L+1)L)`.

Every ingredient is proved: only `ε` has to be supplied, and it is supplied in the form the
literature states.
-/

namespace RHTower.Sieve

open Finset

/-- **The variance from a bulk correlation bound.** -/
theorem sum_normSq_window_le_of_unweighted {a : ℕ → ℂ} {X L : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (ha : ∀ n, ‖a n‖ ≤ 1)
    (hcorr : ∀ h ∈ Finset.Ico 1 L,
      |∑ n ∈ (Finset.range (X + L + 1 - h)).filter (fun n => L ≤ n ∧ n + h ≤ X),
        (a n * (starRingEnd ℂ) (a (n + h))).re| ≤ ε) :
    ∑ x ∈ Finset.range X, ‖∑ n ∈ Finset.Ioc x (x + L), a n‖ ^ (2 : ℕ)
      ≤ (L : ℝ) * ∑ n ∈ Finset.range (X + L + 1), ‖a n‖ ^ (2 : ℕ)
        + 2 * (L : ℝ) * ((L : ℝ) * ε + ((2 * L + 1 : ℕ) : ℝ) * (L : ℝ)) := by
  classical
  have hc : ∀ h n : ℕ, |(a n * (starRingEnd ℂ) (a (n + h))).re| ≤ 1 := by
    intro h n
    refine le_trans (Complex.abs_re_le_norm _) ?_
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_one₀ (ha n) (norm_nonneg _) (ha (n + h))
  rw [sum_normSq_window_eq_autocorrelation_lt a X L]
  have hdiag : ∑ n ∈ Finset.range (X + L + 1), ((windowOverlap X L n n : ℕ) : ℝ) * ‖a n‖ ^ (2 : ℕ)
      ≤ (L : ℝ) * ∑ n ∈ Finset.range (X + L + 1), ‖a n‖ ^ (2 : ℕ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    have hK : ((windowOverlap X L n n : ℕ) : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast windowOverlap_le X L n n
    exact mul_le_mul_of_nonneg_right hK (sq_nonneg _)
  have hshift : ∀ h ∈ Finset.Ico 1 L,
      ∑ n ∈ Finset.range (X + L + 1 - h), ((windowOverlap X L n (n + h) : ℕ) : ℝ)
          * (a n * (starRingEnd ℂ) (a (n + h))).re
        ≤ (L : ℝ) * ε + ((2 * L + 1 : ℕ) : ℝ) * (L : ℝ) := by
    intro h hh
    rw [Finset.mem_Ico] at hh
    have hhL : h ≤ L := by omega
    have hconv := abs_sum_kernel_sub_bulk_le (X := X) (L := L) (h := h) hhL
      (fun n => (a n * (starRingEnd ℂ) (a (n + h))).re) (hc h)
    have hbulk := hcorr h (Finset.mem_Ico.mpr ⟨hh.1, hh.2⟩)
    have hLh : ((L - h : ℕ) : ℝ) ≤ (L : ℝ) := by
      have : (L - h : ℕ) ≤ L := Nat.sub_le L h
      exact_mod_cast this
    have hLh0 : (0 : ℝ) ≤ ((L - h : ℕ) : ℝ) := Nat.cast_nonneg _
    have habs := abs_le.mp hconv
    have hmul : ((L - h : ℕ) : ℝ)
        * ∑ n ∈ (Finset.range (X + L + 1 - h)).filter (fun n => L ≤ n ∧ n + h ≤ X),
            (a n * (starRingEnd ℂ) (a (n + h))).re ≤ (L : ℝ) * ε := by
      have h1 : ∑ n ∈ (Finset.range (X + L + 1 - h)).filter (fun n => L ≤ n ∧ n + h ≤ X),
          (a n * (starRingEnd ℂ) (a (n + h))).re ≤ ε := le_trans (le_abs_self _) hbulk
      calc ((L - h : ℕ) : ℝ)
            * ∑ n ∈ (Finset.range (X + L + 1 - h)).filter (fun n => L ≤ n ∧ n + h ≤ X),
                (a n * (starRingEnd ℂ) (a (n + h))).re
          ≤ ((L - h : ℕ) : ℝ) * ε := mul_le_mul_of_nonneg_left h1 hLh0
        _ ≤ (L : ℝ) * ε := mul_le_mul_of_nonneg_right hLh hε
    linarith [habs.2, hmul]
  have hsum := Finset.sum_le_sum hshift
  rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico] at hsum
  have hcard : ((L - 1 : ℕ) : ℝ) ≤ (L : ℝ) := by
    have : (L - 1 : ℕ) ≤ L := Nat.sub_le L 1
    exact_mod_cast this
  have hnn : (0 : ℝ) ≤ (L : ℝ) * ε + ((2 * L + 1 : ℕ) : ℝ) * (L : ℝ) := by positivity
  nlinarith [hdiag, hsum, hcard, hnn]

end RHTower.Sieve

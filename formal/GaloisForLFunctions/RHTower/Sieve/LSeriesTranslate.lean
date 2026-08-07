import GaloisForLFunctions.RHTower.Sieve.TruncatedPrimeSieveMeanSquare
import GaloisForLFunctions.RHTower.Sieve.LSeriesBlockDecomposition
/-!
# Translating the frequency twists the coefficients

`L(a, σ + i(t₀+u))` is the series with coefficients `a_n n^{−it₀}` evaluated at `σ + iu`, and the twist is
unimodular.  So the mean square over an interval centred at the exceptional frequency `t₀` equals the mean square
of the twisted coefficients over an interval centred at `0`, and every estimate that sees only the moduli of the
coefficients — in particular the whole Selberg-sieve mean-square bound — applies to it verbatim, with the same
right-hand side.

This is what lets the window of the Halász dichotomy be estimated by the window mean value theorem at its own
width, rather than by the trivial size of the polynomial times the window's measure.  The gain is the square of the
`ℓ¹` mass against the sieve's mean square.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set Finset

/-- The frequency twist is unimodular. -/
theorem norm_natCast_cpow_im {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    ‖((n : ℂ)) ^ (-((t : ℝ) : ℂ) * I)‖ = 1 := by
  have hn0 : ((n : ℂ)) ≠ 0 := by
    have : n ≠ 0 := by omega
    simpa using this
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [show ((n : ℂ)) = (((n : ℝ)) : ℂ) by push_cast; ring, ← Complex.ofReal_log hnR.le]
  rw [Complex.cpow_def_of_ne_zero hn0, hlog]
  rw [show ((Real.log n : ℝ) : ℂ) * (-((t : ℝ) : ℂ) * I)
      = ((-(t * Real.log n) : ℝ) : ℂ) * I by push_cast; ring]
  rw [Complex.norm_exp_ofReal_mul_I]

/-- **Translation of the frequency is a twist of the coefficients.**  The twist is unimodular, so every bound on
the coefficients' moduli — in particular the whole Selberg-sieve mean-square estimate — applies verbatim to the
translated polynomial. -/
theorem LSeries_translate {a : ℕ → ℂ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (σ t₀ u : ℝ) :
    LSeries a ((σ : ℂ) + ((t₀ + u : ℝ) : ℂ) * I)
      = LSeries (fun n => a n * ((n : ℂ)) ^ (-((t₀ : ℝ) : ℂ) * I)) ((σ : ℂ) + (u : ℝ) * I) := by
  classical
  have hsupp' : ∀ n : ℕ, a n * ((n : ℂ)) ^ (-((t₀ : ℝ) : ℂ) * I) ≠ 0 → n ∈ s := by
    intro n hn
    refine hsupp n ?_
    intro h
    rw [h, zero_mul] at hn
    exact hn rfl
  rw [LSeries_eq_sum_term_of_support hsupp, LSeries_eq_sum_term_of_support hsupp']
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := fun h => hs0 (h ▸ hn)
  have hcn : ((n : ℂ)) ≠ 0 := by simpa using hn0
  rw [LSeries.term_def, if_neg hn0, LSeries.term_def, if_neg hn0]
  have hsplit : ((n : ℂ)) ^ ((σ : ℂ) + ((t₀ + u : ℝ) : ℂ) * I)
      = ((n : ℂ)) ^ (((t₀ : ℝ) : ℂ) * I) * ((n : ℂ)) ^ ((σ : ℂ) + (u : ℝ) * I) := by
    rw [← Complex.cpow_add _ _ hcn]
    congr 1
    push_cast
    ring
  have hinv : ((n : ℂ)) ^ (-((t₀ : ℝ) : ℂ) * I) = (((n : ℂ)) ^ (((t₀ : ℝ) : ℂ) * I))⁻¹ := by
    rw [show -((t₀ : ℝ) : ℂ) * I = -(((t₀ : ℝ) : ℂ) * I) by ring, Complex.cpow_neg]
  rw [hsplit, hinv]
  have hne : ((n : ℂ)) ^ (((t₀ : ℝ) : ℂ) * I) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hcn]
    exact Complex.exp_ne_zero _
  field_simp

/-- The twisted coefficients have the same moduli. -/
theorem norm_twist_eq {a : ℕ → ℂ} {s : Finset ℕ} (hs0 : 0 ∉ s) (t₀ : ℝ) {n : ℕ} (hn : n ∈ s) :
    ‖a n * ((n : ℂ)) ^ (-((t₀ : ℝ) : ℂ) * I)‖ = ‖a n‖ := by
  have hn0 : n ≠ 0 := fun h => hs0 (h ▸ hn)
  have hn1 : 1 ≤ n := by omega
  rw [norm_mul, norm_natCast_cpow_im hn1 t₀, mul_one]

/-- **The truncated mean square on a translated window.**  Translating the frequency twists the coefficients
without changing their moduli, so the mean square over an interval centred at `t₀` is the mean square of the
twisted coefficients over an interval centred at `0`, and every coefficient-modulus estimate transfers. -/
theorem integral_Icc_normSq_LSeries_translate {a : ℕ → ℂ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (σ t₀ : ℝ) (W : ℝ) :
    (∫ u in Set.Icc (-W) W, ‖LSeries a ((σ : ℂ) + ((t₀ + u : ℝ) : ℂ) * I)‖ ^ 2)
      = ∫ u in Set.Icc (-W) W,
          ‖LSeries (fun n => a n * ((n : ℂ)) ^ (-((t₀ : ℝ) : ℂ) * I)) ((σ : ℂ) + (u : ℝ) * I)‖ ^ 2 := by
  refine setIntegral_congr_fun measurableSet_Icc (fun u _ => ?_)
  rw [LSeries_translate hs0 hsupp σ t₀ u]

/-- **The sieve estimate on a translated window.**  The bound is the one for the untwisted coefficients: the twist
is invisible to it. -/
theorem integral_Icc_normSq_LSeries_translate_le_prime_sieve {a : ℕ → ℂ} {s : Finset ℕ}
    (hs0 : 0 ∉ s) (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (hprime : ∀ n ∈ s, a n ≠ 0 → n.Prime)
    (σ t₀ : ℝ) {W : ℝ} (hW : 0 < W) (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z)
    (hlog : 0 < Real.log Y) :
    (∫ u in Set.Icc (-W) W, ‖LSeries a ((σ : ℂ) + ((t₀ + u : ℝ) : ℂ) * I)‖ ^ 2)
      ≤ 2 * Real.pi * ((5 * W / 4) * ∑ n ∈ s,
          (2 * ((n : ℝ) * (Real.exp (1 / W) - Real.exp (-(1 / W))) + 1) / Real.log Y
            + selbergFibreError z Y + (z : ℝ))
              * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2) := by
  classical
  set ã : ℕ → ℂ := fun n => a n * ((n : ℂ)) ^ (-((t₀ : ℝ) : ℂ) * I) with hã
  have hsuppã : ∀ n : ℕ, ã n ≠ 0 → n ∈ s := by
    intro n hn
    refine hsupp n ?_
    intro h
    rw [hã] at hn
    simp only [h, zero_mul] at hn
    exact hn rfl
  have hprimeã : ∀ n ∈ s, ã n ≠ 0 → n.Prime := by
    intro n hn hne
    refine hprime n hn ?_
    intro h
    rw [hã] at hne
    simp only [h, zero_mul] at hne
    exact hne rfl
  rw [integral_Icc_normSq_LSeries_translate hs0 hsupp σ t₀ W]
  refine le_trans (integral_Icc_normSq_LSeries_le_prime_sieve hs0 hsuppã hprimeã σ hW z Y hY hYz hz
    hlog) (le_of_eq ?_)
  refine congrArg (fun x => 2 * Real.pi * ((5 * W / 4) * x)) ?_
  refine Finset.sum_congr rfl fun n hn => ?_
  congr 2
  have hn0 : n ≠ 0 := fun h => hs0 (h ▸ hn)
  have hn1 : 1 ≤ n := by omega
  rw [hã, norm_mul, norm_mul, norm_mul, norm_natCast_cpow_im hn1 t₀, mul_one]

end RHTower.Sieve
end

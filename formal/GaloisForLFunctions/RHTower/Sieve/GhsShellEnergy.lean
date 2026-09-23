import GaloisForLFunctions.RHTower.Sieve.AdaptiveGallagherBrunTitchmarsh
import GaloisForLFunctions.RHTower.Sieve.MertensIntervalShell

/-!
# The first reciprocal energy of a cofactor shell

The Dirichlet polynomial carried by a shell has coefficients `f(p) log p /(p log(x/p))`.  The
adaptive Gallagher--Brun--Titchmarsh mean square costs one `log p`, and the shell estimate `(A5)`
turns the remaining `∑_p log p/(p log²(x/p))` into `C/u`.
-/

namespace RHTower.Sieve

open Real

noncomputable section

/-- **Lemma F, equation (F1).**  The first reciprocal energy of a cofactor shell.  Lemma B supplies
the single `log p`, and `(A5)` converts it into `1/u`. -/
theorem integral_normSq_shellPoly_le {f : ℕ → ℂ} (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1)
    {T : ℝ} (hT : 2 ≤ T) {S : Finset ℕ} (hSp : ∀ p ∈ S, Nat.Prime p)
    (hST : ∀ p ∈ S, T ^ (2 : ℕ) ≤ (p : ℝ))
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hS : S ⊆ Nat.primesLE b \ Nat.primesLE a)
    {v : ℕ → ℝ} {u : ℝ} (hu : 0 < u) (hv : ∀ p ∈ S, u ≤ v p) :
    (∫ w in Set.Icc (-(T / (2 * Real.pi))) (T / (2 * Real.pi)),
        ‖logPoly (fun p : ℕ => (f p / ((v p : ℝ) : ℂ)) * ((Real.log (p : ℝ) : ℝ) : ℂ) / (p : ℂ))
          S w‖ ^ (2 : ℕ))
      ≤ 2250 * ((Real.log b - Real.log a + mertensIntervalConst) / u ^ (2 : ℕ)) := by
  classical
  refine le_trans (gallagher_bt_mean_square_coeff hT hSp hST _) ?_
  have hstep : ∑ p ∈ S, ‖f p / ((v p : ℝ) : ℂ)‖ ^ (2 : ℕ) * Real.log p / (p : ℝ)
      ≤ ∑ p ∈ S, Real.log p / ((p : ℝ) * v p ^ (2 : ℕ)) := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hpp := hSp p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
    have hvp := hv p hp
    have hv0 : (0 : ℝ) < v p := lt_of_lt_of_le hu hvp
    have hnorm : ‖f p / ((v p : ℝ) : ℂ)‖ ^ (2 : ℕ) ≤ 1 / v p ^ (2 : ℕ) := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv0, div_pow]
      have hf := hbdd p
      have hf0 := norm_nonneg (f p)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hsq : ‖f p‖ ^ (2 : ℕ) ≤ 1 := by nlinarith [hf, hf0]
      nlinarith [hsq, sq_nonneg (v p)]
    have hid : (1 / v p ^ (2 : ℕ)) * Real.log p / (p : ℝ) = Real.log p / ((p : ℝ) * v p ^ (2 : ℕ)) := by
      field_simp
    calc ‖f p / ((v p : ℝ) : ℂ)‖ ^ (2 : ℕ) * Real.log p / (p : ℝ)
        ≤ (1 / v p ^ (2 : ℕ)) * Real.log p / (p : ℝ) := by
          rw [div_le_div_iff₀ hp0 hp0]
          nlinarith [mul_le_mul_of_nonneg_right hnorm (mul_nonneg hlogp hp0.le)]
      _ = Real.log p / ((p : ℝ) * v p ^ (2 : ℕ)) := hid
  refine le_trans (mul_le_mul_of_nonneg_left hstep (by norm_num)) ?_
  exact mul_le_mul_of_nonneg_left
    (sum_log_div_prime_mul_weight_sq_le ha hab hS hu hv) (by norm_num)

end

end RHTower.Sieve

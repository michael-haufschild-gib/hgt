import GaloisForLFunctions.RHTower.Sieve.MertensIntervalShell
import GaloisForLFunctions.RHTower.Sieve.MultiplicativeLogRecursion

/-!
# The reciprocal cofactor shells

The shell sum `S_k` of the Granville--Harper--Soundararajan decomposition carries the weight
`log p / log(x/p)` on a prime range where the cofactor logarithm is between `u` and `e u`.
Summing the inner double sum trivially and applying Mertens on the shell gives the estimate that
makes the shell decomposition converge geometrically.
-/

namespace RHTower.Sieve

open Real

noncomputable section

/-- The inner double sum of the Granville--Harper--Soundararajan shell decomposition. -/
def ghsShellInner (f : ℕ → ℂ) (N p : ℕ) : ℂ :=
  ∑ q ∈ Nat.primesLE (N / p), f q * ((Real.log (q : ℝ) : ℝ) : ℂ)
    * ∑ n ∈ Finset.Icc 1 (N / (p * q)), f n

/-- The shell sum `S_k` of the cofactor decomposition. -/
def ghsShellSum (f : ℕ → ℂ) (N : ℕ) (S : Finset ℕ) : ℂ :=
  ∑ p ∈ S, f p * ((Real.log (p : ℝ) / Real.log ((N : ℝ) / p) : ℝ) : ℂ) * ghsShellInner f N p

/-- The inner double sum obeys the trivial Mertens bound. -/
theorem norm_ghsShellInner_le {f : ℕ → ℂ} (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) (N p : ℕ) :
    ‖ghsShellInner f N p‖
      ≤ ((N / p : ℕ) : ℝ) * (Real.log ((N / p : ℕ) : ℝ) + Real.log 4) := by
  classical
  rcases Nat.eq_zero_or_pos (N / p) with hNp | hNp
  · rw [ghsShellInner, hNp]
    have hempty : Nat.primesLE 0 = ∅ := by
      ext q
      simp only [Nat.mem_primesLE, Finset.notMem_empty, iff_false, not_and]
      intro hq
      have hq0 : q = 0 := by omega
      subst hq0
      exact Nat.not_prime_zero
    rw [hempty, Finset.sum_empty, norm_zero]
    norm_num
  · refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ q ∈ Nat.primesLE (N / p),
        ‖f q * ((Real.log (q : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.Icc 1 (N / (p * q)), f n‖
          ≤ ((N / p : ℕ) : ℝ) * (Real.log (q : ℝ) / (q : ℝ)) := by
      intro q hq
      have hqp := (Nat.mem_primesLE.mp hq).2
      have hqle := (Nat.mem_primesLE.mp hq).1
      have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqp.two_le
      have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
      have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg (by linarith)
      have hinner : ‖∑ n ∈ Finset.Icc 1 (N / (p * q)), f n‖ ≤ ((N / (p * q) : ℕ) : ℝ) :=
        norm_sum_Icc_le hbdd _
      have hdiv : ((N / (p * q) : ℕ) : ℝ) ≤ ((N / p : ℕ) : ℝ) / (q : ℝ) := by
        have h1 : N / (p * q) = (N / p) / q := (Nat.div_div_eq_div_mul N p q).symm
        rw [h1]
        exact Nat.cast_div_le
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogq]
      have hf := hbdd q
      have hnn : (0 : ℝ) ≤ ((N / p : ℕ) : ℝ) := Nat.cast_nonneg _
      have hstep : ‖f q‖ * Real.log q * ‖∑ n ∈ Finset.Icc 1 (N / (p * q)), f n‖
          ≤ 1 * Real.log q * (((N / p : ℕ) : ℝ) / (q : ℝ)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hf hlogq)
          (le_trans hinner hdiv) (norm_nonneg _) (by positivity)
      have hid : (1 : ℝ) * Real.log q * (((N / p : ℕ) : ℝ) / (q : ℝ))
          = ((N / p : ℕ) : ℝ) * (Real.log q / (q : ℝ)) := by
        field_simp
      linarith [hstep, hid.le, hid.ge]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hnn : (0 : ℝ) ≤ ((N / p : ℕ) : ℝ) := Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_left (mertensFirst_upper hNp) hnn

/-- **Lemma D, equation (D4).**  The trivial estimate for one reciprocal cofactor shell. -/
theorem norm_ghsShellSum_le {f : ℕ → ℂ} (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) {N : ℕ} {S : Finset ℕ}
    {u : ℝ} (hu : 0 < u) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hS : S ⊆ Nat.primesLE b \ Nat.primesLE a)
    (hv : ∀ p ∈ S, u ≤ Real.log ((N : ℝ) / (p : ℝ)))
    (hvup : ∀ p ∈ S, Real.log ((N : ℝ) / (p : ℝ)) ≤ Real.exp 1 * u) :
    ‖ghsShellSum f N S‖
      ≤ (N : ℝ) * (Real.exp 1 * u + Real.log 4)
          * ((Real.log b - Real.log a + mertensIntervalConst) / u) := by
  classical
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ p ∈ S,
      ‖f p * ((Real.log (p : ℝ) / Real.log ((N : ℝ) / (p : ℝ)) : ℝ) : ℂ) * ghsShellInner f N p‖
        ≤ (N : ℝ) * (Real.exp 1 * u + Real.log 4)
            * (Real.log (p : ℝ) / ((p : ℝ) * Real.log ((N : ℝ) / (p : ℝ)))) := by
    intro p hp
    have hpm := Finset.mem_sdiff.mp (hS hp)
    have hpp := (Nat.mem_primesLE.mp hpm.1).2
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
    have hvp := hv p hp
    have hv0 : (0 : ℝ) < Real.log ((N : ℝ) / (p : ℝ)) := lt_of_lt_of_le hu hvp
    have hvup' := hvup p hp
    have hquot : (0 : ℝ) ≤ Real.log (p : ℝ) / Real.log ((N : ℝ) / (p : ℝ)) := by positivity
    have hinner := norm_ghsShellInner_le hbdd N p
    have hnn : (0 : ℝ) ≤ ((N / p : ℕ) : ℝ) := Nat.cast_nonneg _
    have hlogNp : Real.log ((N / p : ℕ) : ℝ) ≤ Real.log ((N : ℝ) / (p : ℝ)) := by
      rcases Nat.eq_zero_or_pos (N / p) with h0 | h0
      · rw [h0]
        simpa using hv0.le
      · refine Real.log_le_log (by exact_mod_cast h0) ?_
        exact Nat.cast_div_le
    have hcast : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / (p : ℝ) := Nat.cast_div_le
    have hlogNp0 : (0 : ℝ) ≤ Real.log ((N / p : ℕ) : ℝ) := by
      rcases Nat.eq_zero_or_pos (N / p) with h0 | h0
      · rw [h0]; simp
      · exact Real.log_nonneg (by exact_mod_cast h0)
    have hinner2 : ‖ghsShellInner f N p‖ ≤ ((N : ℝ) / (p : ℝ)) * (Real.exp 1 * u + Real.log 4) := by
      refine le_trans hinner ?_
      refine mul_le_mul hcast (by linarith) (by linarith) (by positivity)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hquot]
    have hfp := hbdd p
    have hstep : ‖f p‖ * (Real.log (p : ℝ) / Real.log ((N : ℝ) / (p : ℝ))) * ‖ghsShellInner f N p‖
        ≤ 1 * (Real.log (p : ℝ) / Real.log ((N : ℝ) / (p : ℝ)))
            * (((N : ℝ) / (p : ℝ)) * (Real.exp 1 * u + Real.log 4)) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_right hfp hquot) hinner2 (norm_nonneg _)
        (by positivity)
    have hid : (1 : ℝ) * (Real.log (p : ℝ) / Real.log ((N : ℝ) / (p : ℝ)))
          * (((N : ℝ) / (p : ℝ)) * (Real.exp 1 * u + Real.log 4))
        = (N : ℝ) * (Real.exp 1 * u + Real.log 4)
            * (Real.log (p : ℝ) / ((p : ℝ) * Real.log ((N : ℝ) / (p : ℝ)))) := by
      field_simp
    linarith [hstep, hid.le, hid.ge]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hA4 := sum_log_div_prime_mul_weight_le (v := fun p : ℕ => Real.log ((N : ℝ) / (p : ℝ)))
    ha hab hS hu hv
  have hcoef : (0 : ℝ) ≤ (N : ℝ) * (Real.exp 1 * u + Real.log 4) := by
    have : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have : (0 : ℝ) ≤ Real.exp 1 * u + Real.log 4 := by positivity
    positivity
  exact mul_le_mul_of_nonneg_left hA4 hcoef

end

end RHTower.Sieve

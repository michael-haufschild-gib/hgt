import GaloisForLFunctions.RHTower.Sieve.ShortIntervalLength

/-!
# The start of the sifting range

The sieve sifts by the primes of `(P₁, h]` with `log P₁ = (log h)^a`.  As a natural number the start
is `⌈exp((log x)^{aβ})⌉`, and the rounding costs at most `log 2` in its logarithm — absorbed by
raising the exponent slightly, which is free because the admissible window for `a` is open.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The start of the sifting range. -/
def siftStart (c x : ℝ) : ℕ := ⌈Real.exp ((Real.log x) ^ c)⌉₊

/-- **The rounding costs at most `log 2`.** -/
theorem log_siftStart_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, Real.log (siftStart c x) ≤ (Real.log x) ^ c + Real.log 2 := by
  have hpow : Tendsto (fun x : ℝ => (Real.log x) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp Real.tendsto_log_atTop
  filter_upwards [hpow.eventually_ge_atTop (0 : ℝ)] with x hx
  set E : ℝ := Real.exp ((Real.log x) ^ c) with hE
  have hE1 : (1 : ℝ) ≤ E := by
    rw [hE]
    exact Real.one_le_exp hx
  have hE0 : (0 : ℝ) < E := by linarith
  have hceil : ((siftStart c x : ℕ) : ℝ) ≤ E + 1 := by
    rw [siftStart, ← hE]
    exact le_of_lt (Nat.ceil_lt_add_one hE0.le)
  have hle : E + 1 ≤ 2 * E := by linarith
  have hstart1 : (1 : ℝ) ≤ ((siftStart c x : ℕ) : ℝ) := by
    have h1 : 1 ≤ siftStart c x := by
      rw [siftStart]
      exact Nat.one_le_ceil_iff.2 hE0
    exact_mod_cast h1
  have hlog : Real.log ((siftStart c x : ℕ) : ℝ) ≤ Real.log (2 * E) :=
    Real.log_le_log (by linarith) (le_trans hceil hle)
  rw [Real.log_mul (by norm_num) (ne_of_gt hE0), hE, Real.log_exp] at hlog
  linarith [hlog]

/-- **The start of the sifting range exceeds any bound.** -/
theorem eventually_le_siftStart {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∀ᶠ x : ℝ in atTop, N ≤ siftStart c x := by
  have hpow : Tendsto (fun x : ℝ => (Real.log x) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp Real.tendsto_log_atTop
  filter_upwards [hpow.eventually_ge_atTop (Real.log N + 1)] with x hx
  have hE : ((N : ℕ) : ℝ) ≤ Real.exp ((Real.log x) ^ c) := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [Nat.cast_zero]
      exact (Real.exp_pos _).le
    · have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hlogN : Real.log (N : ℝ) ≤ (Real.log x) ^ c := by linarith
      calc ((N : ℕ) : ℝ) = Real.exp (Real.log (N : ℝ)) := (Real.exp_log hN0).symm
        _ ≤ Real.exp ((Real.log x) ^ c) := Real.exp_le_exp.2 hlogN
  rw [siftStart]
  have hchain : ((N : ℕ) : ℝ) ≤ ((⌈Real.exp ((Real.log x) ^ c)⌉₊ : ℕ) : ℝ) :=
    le_trans hE (Nat.le_ceil _)
  exact_mod_cast hchain

end

end RHTower.Sieve

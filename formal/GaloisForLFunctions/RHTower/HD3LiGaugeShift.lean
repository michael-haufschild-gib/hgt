import Mathlib

/-!
# The HD3 zero-free gauge shifts the log-defined Li coefficients

The FE-symmetric zero-free multiplier `F_c(s) = exp(c(s − 1/2)²)·ξ(s)` has exactly the same zero
divisor as `ξ` (the exponential never vanishes) and preserves the functional-equation symmetry (the
gauge is even in `s − 1/2`), yet it shifts the **log-defined** Li coefficients

`λ_n(f) = 1/(n−1)! · dⁿ/dsⁿ [s^{n−1} log f(s)]|_{s=1}`

by exactly `δλ_n = c·n²`.  So log-defined Li positivity is not a zero-divisor invariant: with `c < 0`
the shifted coefficients go negative for large `n` without moving a single zero.

The computation is exact: `s^{n−1}(s−1/2)² = s^{n+1} − s^n + s^{n−1}/4`, the `n`-th derivative kills
the last term, and `((n+1)! − n!)/(n−1)! = n²`.

## Main results

* `hd3Gauge_reflect`, `hd3_zero_iff` — the gauge is FE-symmetric and zero-free;
* `liLogCoeff_hd3Gauge` — the gauge contributes exactly `c n²`;
* `liLogCoeff_add_hd3Gauge` — hence the log-defined Li chart is not gauge invariant.
-/

namespace GaloisForLFunctions

/-- The log-defined Li coefficient functional applied to a "log" `g`. -/
noncomputable def liLogCoeff (g : ℂ → ℂ) (n : ℕ) : ℂ :=
  (1 / (Nat.factorial (n - 1) : ℂ)) * iteratedDeriv n (fun s => s ^ (n - 1) * g s) 1

/-- The HD3 zero-free FE-symmetric gauge `Q_c(s) = c (s − 1/2)²`. -/
noncomputable def hd3Gauge (c : ℂ) (s : ℂ) : ℂ := c * (s - 1 / 2) ^ (2 : ℕ)

/-- The gauge is even in `s − 1/2`, so it preserves the functional-equation symmetry. -/
theorem hd3Gauge_reflect (c s : ℂ) : hd3Gauge c (1 - s) = hd3Gauge c s := by
  rw [hd3Gauge, hd3Gauge]; ring

theorem exp_hd3Gauge_ne_zero (c s : ℂ) : Complex.exp (hd3Gauge c s) ≠ 0 := Complex.exp_ne_zero _

/-- **The gauge does not move a single zero.** -/
theorem hd3_zero_iff (c : ℂ) (f : ℂ → ℂ) (s : ℂ) :
    Complex.exp (hd3Gauge c s) * f s = 0 ↔ f s = 0 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (exp_hd3Gauge_ne_zero c s)
    · exact h'
  · intro h
    rw [h, mul_zero]

theorem factorial_succ_eq {n : ℕ} (hn : 1 ≤ n) :
    Nat.factorial (n + 1) = Nat.factorial n + n ^ (2 : ℕ) * Nat.factorial (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.factorial_succ]
  ring

/-- **The HD3 Li-coefficient gauge shift.**  The zero-free FE-symmetric gauge shifts the
log-defined Li coefficients by exactly `c n²`. -/
theorem liLogCoeff_hd3Gauge (c : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    liLogCoeff (hd3Gauge c) n = c * (n : ℂ) ^ (2 : ℕ) := by
  have hfun : (fun s : ℂ => s ^ (n - 1) * hd3Gauge c s)
      = fun s : ℂ => c * s ^ (n + 1) - c * s ^ n + (c / 4) * s ^ (n - 1) := by
    funext s
    rw [hd3Gauge]
    have h1 : n - 1 + 2 = n + 1 := by omega
    have h2 : n - 1 + 1 = n := by omega
    rw [show s ^ (n + 1) = s ^ (n - 1) * s ^ (2 : ℕ) by rw [← pow_add, h1],
      show s ^ n = s ^ (n - 1) * s by rw [← pow_succ, h2]]
    ring
  have hA : iteratedDeriv n (fun s : ℂ => c * s ^ (n + 1)) 1
      = c * (((n + 1).descFactorial n : ℕ) : ℂ) := by
    rw [iteratedDeriv_const_mul _ (by fun_prop), iteratedDeriv_pow]
    simp
  have hB : iteratedDeriv n (fun s : ℂ => c * s ^ n) 1 = c * ((n.descFactorial n : ℕ) : ℂ) := by
    rw [iteratedDeriv_const_mul _ (by fun_prop), iteratedDeriv_pow]
    simp
  have hC : iteratedDeriv n (fun s : ℂ => (c / 4) * s ^ (n - 1)) 1 = 0 := by
    rw [iteratedDeriv_const_mul _ (by fun_prop), iteratedDeriv_pow]
    have : ((n - 1).descFactorial n) = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    rw [this]
    simp
  have hc1 : ContDiffAt ℂ (n : ℕ) (fun s : ℂ => c * s ^ (n + 1)) 1 := by fun_prop
  have hc2 : ContDiffAt ℂ (n : ℕ) (fun s : ℂ => c * s ^ n) 1 := by fun_prop
  have hc3 : ContDiffAt ℂ (n : ℕ) (fun s : ℂ => (c / 4) * s ^ (n - 1)) 1 := by fun_prop
  have hc12 : ContDiffAt ℂ (n : ℕ)
      ((fun s : ℂ => c * s ^ (n + 1)) - (fun s : ℂ => c * s ^ n)) 1 := hc1.sub hc2
  have hsum : iteratedDeriv n (fun s : ℂ => c * s ^ (n + 1) - c * s ^ n + (c / 4) * s ^ (n - 1)) 1
      = c * (((n + 1).descFactorial n : ℕ) : ℂ) - c * ((n.descFactorial n : ℕ) : ℂ) + 0 := by
    rw [show (fun s : ℂ => c * s ^ (n + 1) - c * s ^ n + (c / 4) * s ^ (n - 1))
        = ((fun s : ℂ => c * s ^ (n + 1)) - (fun s : ℂ => c * s ^ n))
          + (fun s : ℂ => (c / 4) * s ^ (n - 1)) from rfl,
      iteratedDeriv_add hc12 hc3,
      iteratedDeriv_sub hc1 hc2, hA, hB, hC]
  rw [liLogCoeff, hfun, hsum]
  have hd1 : (n + 1).descFactorial n = Nat.factorial (n + 1) := by
    rw [Nat.descFactorial_eq_div (by omega)]
    have : (n + 1) - n = 1 := by omega
    rw [this]
    simp
  have hd2 : n.descFactorial n = Nat.factorial n := Nat.descFactorial_self n
  rw [hd1, hd2, factorial_succ_eq hn]
  have hfac : ((Nat.factorial (n - 1) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - 1)
  push_cast
  field_simp
  ring

/-- **The Li chart is not gauge invariant.**  Adding the HD3 gauge to the log shifts every
log-defined Li coefficient by exactly `c n²`. -/
theorem liLogCoeff_add_hd3Gauge {g : ℂ → ℂ} {n : ℕ} (hn : 1 ≤ n)
    (hg : ContDiffAt ℂ (n : ℕ) (fun s : ℂ => s ^ (n - 1) * g s) 1) (c : ℂ) :
    liLogCoeff (fun s => g s + hd3Gauge c s) n = liLogCoeff g n + c * (n : ℂ) ^ (2 : ℕ) := by
  have hsplit : (fun s : ℂ => s ^ (n - 1) * (g s + hd3Gauge c s))
      = (fun s : ℂ => s ^ (n - 1) * g s) + (fun s : ℂ => s ^ (n - 1) * hd3Gauge c s) := by
    funext s
    simp [mul_add]
  have hcd2 : ContDiffAt ℂ (n : ℕ) (fun s : ℂ => s ^ (n - 1) * hd3Gauge c s) 1 := by
    unfold hd3Gauge
    fun_prop
  rw [liLogCoeff, liLogCoeff, hsplit, iteratedDeriv_add hg hcd2, mul_add]
  congr 1
  exact liLogCoeff_hd3Gauge c hn

end GaloisForLFunctions

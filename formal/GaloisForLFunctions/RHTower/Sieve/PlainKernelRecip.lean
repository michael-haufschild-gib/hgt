import GaloisForLFunctions.RHTower.Sieve.LogPhaseKernelKuzminLandau
import GaloisForLFunctions.RHTower.Sieve.PlainKernelMass
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The log-phase kernel at a free frequency, with reciprocal decay

Choosing the Kuzmin–Landau split point at the frequency itself — `2^{J₀} ≍ t` — turns
`Sieve/LogPhaseKernelKuzminLandau.norm_sum_Icc_logPhase_le_split` into a bound whose only
`N`-dependent term decays like `N/t`:

```text
   ‖∑_{n ≤ N} n^{−it}‖  ≤  214(log₂⌈t⌉ + 1)√t + 12288√t + 12π·N/t + log₂N + 1 .
```

Its supremum over `1 ≤ t ≤ 2T` is `O(√T log T) + 12π·N` — but the `N` part is *integrable* against
`dt/t`, which is what a row mass needs and what the uniform constant `3072·N` of
`Sieve/PlainKernelMass.norm_plainKernel_le` destroys.
-/

namespace RHTower.Sieve

open Finset

/-- A dyadic bracket for a real number above one. -/
theorem exists_pow_two_bracket {t : ℝ} (ht : 1 ≤ t) :
    t ≤ (2 : ℝ) ^ (Nat.log 2 ⌈t⌉₊ + 1) ∧ (2 : ℝ) ^ (Nat.log 2 ⌈t⌉₊ + 1) ≤ 4 * t := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hceil1 : 1 ≤ ⌈t⌉₊ := Nat.one_le_ceil_iff.2 ht0
  have hlt : (⌈t⌉₊ : ℕ) < 2 ^ (Nat.log 2 ⌈t⌉₊ + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have hle : (2 : ℕ) ^ (Nat.log 2 ⌈t⌉₊) ≤ ⌈t⌉₊ :=
    Nat.pow_log_le_self 2 (by omega)
  constructor
  · have h1 : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
    have h2 : ((⌈t⌉₊ : ℕ) : ℝ) ≤ ((2 ^ (Nat.log 2 ⌈t⌉₊ + 1) : ℕ) : ℝ) := by
      exact_mod_cast hlt.le
    have h3 : ((2 ^ (Nat.log 2 ⌈t⌉₊ + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (Nat.log 2 ⌈t⌉₊ + 1) := by
      push_cast; ring
    linarith [h1, h2, h3 ▸ h2]
  · have h2 : ((2 ^ (Nat.log 2 ⌈t⌉₊) : ℕ) : ℝ) ≤ ((⌈t⌉₊ : ℕ) : ℝ) := by exact_mod_cast hle
    have h3 : ((2 ^ (Nat.log 2 ⌈t⌉₊) : ℕ) : ℝ) = (2 : ℝ) ^ (Nat.log 2 ⌈t⌉₊) := by
      push_cast; ring
    have hceil : ((⌈t⌉₊ : ℕ) : ℝ) ≤ t + 1 := by
      have := Nat.ceil_lt_add_one ht0.le
      linarith
    have hpow : (2 : ℝ) ^ (Nat.log 2 ⌈t⌉₊ + 1) = 2 * (2 : ℝ) ^ (Nat.log 2 ⌈t⌉₊) := by
      rw [pow_succ]; ring
    rw [hpow, ← h3]
    linarith

/-- **The kernel bound with reciprocal decay in the frequency.** -/
theorem norm_sum_Icc_logPhase_le_recip {M : ℕ} (hM : 1 ≤ M) {t : ℝ} (ht : 1 ≤ t) :
    ‖∑ n ∈ Finset.Icc 1 M, ((n : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ ((Nat.log 2 ⌈t⌉₊ : ℝ) + 1) * (214 * Real.sqrt t) + 12288 * Real.sqrt t
        + (12 * Real.pi * (M : ℝ) / t + ((Nat.log 2 M : ℝ) + 1)) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hsq : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨hlow, hhigh⟩ := exists_pow_two_bracket ht
  set J₀ : ℕ := Nat.log 2 ⌈t⌉₊ + 1 with hJ
  have hpow0 : (0 : ℝ) ≤ (2 : ℝ) ^ J₀ := by positivity
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hKL : 3 * t ≤ 4 * Real.pi * (2 : ℝ) ^ J₀ := by nlinarith [hlow, hpow0, hπ3]
  refine le_trans (norm_sum_Icc_logPhase_le_split hM ht0 J₀ hKL) ?_
  have hJcast : (J₀ : ℝ) = (Nat.log 2 ⌈t⌉₊ : ℝ) + 1 := by rw [hJ]; push_cast; ring
  rw [hJcast]
  have hsqt : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  have hterm : 1536 * (2 * (2 : ℝ) ^ J₀) / Real.sqrt t ≤ 12288 * Real.sqrt t := by
    rw [div_le_iff₀ hsq]
    nlinarith [hhigh, hsq, hsqt]
  linarith

/-- **The plain kernel at a free frequency.** -/
theorem norm_plainKernel_le_recip {N : ℕ} (hN : 1 ≤ N) {v : ℝ} (hv : 1 ≤ |v|) :
    ‖plainKernel N v‖
      ≤ ((Nat.log 2 ⌈|v|⌉₊ : ℝ) + 1) * (214 * Real.sqrt |v|) + 12288 * Real.sqrt |v|
        + (12 * Real.pi * (N : ℝ) / |v| + ((Nat.log 2 N : ℝ) + 1)) := by
  have hkey : ∀ w : ℝ, 1 ≤ |w| → w < 0 → ‖plainKernel N w‖
      ≤ ((Nat.log 2 ⌈|w|⌉₊ : ℝ) + 1) * (214 * Real.sqrt |w|) + 12288 * Real.sqrt |w|
        + (12 * Real.pi * (N : ℝ) / |w| + ((Nat.log 2 N : ℝ) + 1)) := by
    intro w hw hneg
    have habs : |w| = -w := abs_of_neg hneg
    have hpos : (1 : ℝ) ≤ -w := by rw [habs] at hw; exact hw
    have hbase := norm_sum_Icc_logPhase_le_recip (M := N) hN (t := -w) hpos
    rw [habs]
    refine le_trans (le_of_eq ?_) hbase
    rw [plainKernel_eq_dirichlet]
  rcases lt_or_gt_of_ne (by
    intro h
    rw [h] at hv
    norm_num at hv : v ≠ 0) with hneg | hpos
  · exact hkey v hv hneg
  · have h1 := hkey (-v) (by rwa [abs_neg]) (by linarith)
    rw [norm_plainKernel_neg, abs_neg] at h1
    exact h1

end RHTower.Sieve

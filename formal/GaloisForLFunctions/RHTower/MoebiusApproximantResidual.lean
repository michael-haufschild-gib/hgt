import GaloisForLFunctions.RHTower.MoebiusFloorSummatory
import GaloisForLFunctions.RHTower.StepFunctionCarrier

/-!
# The Möbius approximant and its residual

Every result on the Báez-Duarte lane so far has been an obstruction.  This file supplies the first
constructive input, in the discrete language of `StepFunctionCarrier`: an exact identity for the residual of
the Möbius combination of generators.

The generators are the modular sequences `g_d(n) = (n mod d)/d = n/d − ⌊n/d⌋`.  Summing against `μ(d)` and
using the corpus's `moebius_floor_summatory` (`∑_{d ≤ N} μ(d)⌊N/d⌋ = 1`, extended here to `∑_{d ≤ N} μ(d)⌊n/d⌋
= 1` for `n ≤ N`, since the terms with `d > n` vanish) gives

**`sum_moebius_modSeq` — `∑_{d ≤ N} μ(d)·g_d(n) = n·M₁(N) − 1` for `1 ≤ n ≤ N`,  `M₁(N) = ∑_{d ≤ N} μ(d)/d`.**

So the combination with coefficients `−μ(d)` reproduces the target sequence `1` on the whole range `[1,N]`
*up to* `n·M₁(N)`:

**`moebius_residual_eq` — `1 − ∑_{d ≤ N} (−μ(d))·g_d(n) = n·M₁(N)` for `1 ≤ n ≤ N`.**

Two immediate remarks.  The corpus's `abs_sum_moebius_div_le_one` gives `|M₁(N)| ≤ 1` unconditionally, so the
residual is at most `n` — free but useless.  What the construction actually needs is `M₁(N) → 0`, which is
equivalent to the prime number theorem; the corpus proves the PNT twice (`RHTower/Sieve/ChebyshevPNT.lean`
and the vendored `PNTPlus`), so that is a genuine follow-up rather than a new analytic obstacle.  Even with
it, the residual grows linearly in `n` while the weights only decay like `1/n²`, so the *undamped* Möbius
approximant does not converge — the classical remedy is a Vasyunin-type damping of the coefficients, and this
identity is the exact starting point for analysing any such choice.
-/

open Finset ArithmeticFunction

noncomputable section

namespace RHTower

/-- `moebius_floor_summatory` at an inner point: the sum may be taken over any range beyond `n`. -/
theorem moebius_floor_summatory_le {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    ∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) * ((n / d : ℕ) : ℝ) = 1 := by
  rw [← moebius_floor_summatory n hn]
  refine (Finset.sum_subset (Finset.Icc_subset_Icc_right hnN) ?_).symm
  intro d hd hdn
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hdgt : n < d := by
    by_contra hle
    exact hdn (Finset.mem_Icc.mpr ⟨hd1, by omega⟩)
  have hzero : n / d = 0 := Nat.div_eq_of_lt hdgt
  rw [hzero]
  norm_num

/-- The modular sequence is the difference of the exact and integer quotients. -/
theorem modSeq_eq_sub_floor {n d : ℕ} (hd : 1 ≤ d) :
    ((n % d : ℕ) : ℝ) / (d : ℝ) = (n : ℝ) / (d : ℝ) - ((n / d : ℕ) : ℝ) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdm := Nat.div_add_mod n d
  have hcast : ((d * (n / d) + n % d : ℕ) : ℝ) = ((n : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hdm
  push_cast at hcast
  field_simp
  linarith

/-- **The Möbius sum of the modular sequences.** -/
theorem sum_moebius_modSeq {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    ∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) * (((n % d : ℕ) : ℝ) / (d : ℝ))
      = (n : ℝ) * (∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ)) - 1 := by
  have hsplit : ∀ d ∈ Finset.Icc 1 N,
      ((moebius d : ℤ) : ℝ) * (((n % d : ℕ) : ℝ) / (d : ℝ))
        = (n : ℝ) * (((moebius d : ℤ) : ℝ) / (d : ℝ))
          - ((moebius d : ℤ) : ℝ) * ((n / d : ℕ) : ℝ) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    rw [modSeq_eq_sub_floor hd1]
    have hd0 : (d : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
      exact ne_of_gt this
    field_simp
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum,
    moebius_floor_summatory_le hn hnN]

/-- **The residual of the Möbius approximant.**  With coefficients `−μ(d)` the combination matches the
target sequence `1` on `[1,N]` up to `n·M₁(N)`. -/
theorem moebius_residual_eq {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    1 - ∑ d ∈ Finset.Icc 1 N, (-((moebius d : ℤ) : ℝ)) * (((n % d : ℕ) : ℝ) / (d : ℝ))
      = (n : ℝ) * (∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ)) := by
  have h := sum_moebius_modSeq hn hnN
  have hneg : ∑ d ∈ Finset.Icc 1 N, (-((moebius d : ℤ) : ℝ)) * (((n % d : ℕ) : ℝ) / (d : ℝ))
      = -∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) * (((n % d : ℕ) : ℝ) / (d : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  rw [hneg, h]
  ring

/-- The residual is bounded by `n`, unconditionally, from the corpus's `|M₁(N)| ≤ 1`. -/
theorem abs_moebius_residual_le {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    |1 - ∑ d ∈ Finset.Icc 1 N, (-((moebius d : ℤ) : ℝ)) * (((n % d : ℕ) : ℝ) / (d : ℝ))|
      ≤ (n : ℝ) := by
  have hN : 1 ≤ N := le_trans hn hnN
  rw [moebius_residual_eq hn hnN, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
  calc (n : ℝ) * |∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ)|
      ≤ (n : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (abs_sum_moebius_div_le_one N hN) (Nat.cast_nonneg n)
    _ = (n : ℝ) := mul_one _

end RHTower

end

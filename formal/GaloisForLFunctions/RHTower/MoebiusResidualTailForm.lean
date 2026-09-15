import GaloisForLFunctions.RHTower.TruncatedMoebiusResidual

/-!
# The residual in terms of the omitted moduli

`TruncatedMoebiusResidual` wrote the Möbius approximant's residual as `1 − F_N(n) + n·M₁(N)` and expanded
`F_N` through the truncated Möbius divisor sum.  There is a shorter exact form.  Splitting the range of
`moebius_floor_summatory` at `N` gives

`F_N(n) = 1 − ∑_{N < d ≤ n} μ(d)⌊n/d⌋`,

so the residual is

**`moebius_residual_tail_form` — `1 − ∑_{d ≤ N}(−μ(d))·g_d(n) = ∑_{N < d ≤ n} μ(d)⌊n/d⌋ + n·M₁(N)`.**

The residual is thus governed entirely by the moduli the approximant *omitted*, plus the linear Mertens term.
For `n ≤ N` the tail sum is empty and this reduces to `n·M₁(N)`, recovering the first form; no truncated
divisor sums appear.

This is the classical shape of the problem: the two terms pull in opposite directions — enlarging `N` shrinks
`M₁(N)` (the prime number theorem) but the tail sum only starts at `N`, and the trivial bound
`|∑_{N<d≤n} μ(d)⌊n/d⌋| ≤ n·log(n/N)` is far too lossy.  Making the balance work is exactly what a
Vasyunin-type damping of the coefficients is for; nothing is estimated here.
-/

open Finset ArithmeticFunction

noncomputable section

namespace RHTower

/-- **Splitting the Möbius floor summatory at `N`.** -/
theorem sum_moebius_floor_tail (n N : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) * ((n / d : ℕ) : ℝ)
      = 1 - ∑ d ∈ Finset.Ioc N n, ((moebius d : ℤ) : ℝ) * ((n / d : ℕ) : ℝ) := by
  rcases le_or_gt n N with hnN | hNn
  · have hempty : Finset.Ioc N n = ∅ := by
      rw [Finset.Ioc_eq_empty]
      omega
    rw [hempty, Finset.sum_empty, sub_zero]
    exact moebius_floor_summatory_le hn hnN
  · rcases Nat.eq_zero_or_pos N with hN0 | hN1
    · have hempty : Finset.Icc 1 N = ∅ := by
        rw [hN0]
        rw [Finset.Icc_eq_empty]
        omega
      have hfull : Finset.Ioc N n = Finset.Icc 1 n := by
        rw [hN0]
        ext d
        simp only [Finset.mem_Ioc, Finset.mem_Icc]
        omega
      rw [hempty, Finset.sum_empty, hfull, moebius_floor_summatory n hn]
      ring
    · have hunion : Finset.Icc 1 N ∪ Finset.Ioc N n = Finset.Icc 1 n := by
        ext d
        simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
        omega
      have hdisj : Disjoint (Finset.Icc 1 N) (Finset.Ioc N n) := by
        refine Finset.disjoint_left.mpr fun d hd hd' => ?_
        rw [Finset.mem_Icc] at hd
        rw [Finset.mem_Ioc] at hd'
        omega
      have hsplit : ∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ) * ((n / d : ℕ) : ℝ)
          = (∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) * ((n / d : ℕ) : ℝ))
            + ∑ d ∈ Finset.Ioc N n, ((moebius d : ℤ) : ℝ) * ((n / d : ℕ) : ℝ) := by
        rw [← hunion, Finset.sum_union hdisj]
      rw [moebius_floor_summatory n hn] at hsplit
      linarith

/-- **The residual, in terms of the omitted moduli.** -/
theorem moebius_residual_tail_form {n N : ℕ} (hn : 1 ≤ n) :
    1 - ∑ d ∈ Finset.Icc 1 N, (-((moebius d : ℤ) : ℝ)) * (((n % d : ℕ) : ℝ) / (d : ℝ))
      = (∑ d ∈ Finset.Ioc N n, ((moebius d : ℤ) : ℝ) * ((n / d : ℕ) : ℝ))
        + (n : ℝ) * (∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ)) := by
  have hgen := moebius_residual_eq_general n N
  rw [← sum_moebius_floor_eq_sum_trunc n N, sum_moebius_floor_tail n N hn] at hgen
  rw [hgen]
  ring

/-- Beyond the cutoff, the cutoff-local harmonic term cancels exactly with the
`n / d` component of the omitted floor tail.  The residual is therefore one global
harmonic Möbius sum plus the literal fractional-floor tail. -/
theorem moebius_residual_fractional_tail_form {n N : ℕ} (hn : 1 ≤ n) (hNn : N ≤ n) :
    1 - ∑ d ∈ Finset.Icc 1 N, (-((moebius d : ℤ) : ℝ)) *
        (((n % d : ℕ) : ℝ) / (d : ℝ)) =
      (∑ d ∈ Finset.Ioc N n, ((moebius d : ℤ) : ℝ) *
        (((n / d : ℕ) : ℝ) - (n : ℝ) / (d : ℝ))) +
        (n : ℝ) * ∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ) / (d : ℝ) := by
  have hunion : Finset.Icc 1 N ∪ Finset.Ioc N n = Finset.Icc 1 n := by
    ext d
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 N) (Finset.Ioc N n) := by
    refine Finset.disjoint_left.mpr fun d hdN hdTail => ?_
    rw [Finset.mem_Icc] at hdN
    rw [Finset.mem_Ioc] at hdTail
    omega
  have hsplit :
      (∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ) / (d : ℝ)) =
        (∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ)) +
          ∑ d ∈ Finset.Ioc N n, ((moebius d : ℤ) : ℝ) / (d : ℝ) := by
    rw [← hunion, Finset.sum_union hdisj]
  have htail :
      (∑ d ∈ Finset.Ioc N n, ((moebius d : ℤ) : ℝ) *
        (((n / d : ℕ) : ℝ) - (n : ℝ) / (d : ℝ))) =
        (∑ d ∈ Finset.Ioc N n, ((moebius d : ℤ) : ℝ) * ((n / d : ℕ) : ℝ)) -
          (n : ℝ) * ∑ d ∈ Finset.Ioc N n, ((moebius d : ℤ) : ℝ) / (d : ℝ) := by
    calc
      _ = ∑ d ∈ Finset.Ioc N n, (((moebius d : ℤ) : ℝ) * ((n / d : ℕ) : ℝ) -
          (n : ℝ) * (((moebius d : ℤ) : ℝ) / (d : ℝ))) := by
        apply Finset.sum_congr rfl
        intro d hd
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [moebius_residual_tail_form hn, htail, hsplit]
  ring

/-- For `n ≤ N` the tail is empty: the first form is recovered. -/
theorem moebius_residual_tail_form_of_le {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    1 - ∑ d ∈ Finset.Icc 1 N, (-((moebius d : ℤ) : ℝ)) * (((n % d : ℕ) : ℝ) / (d : ℝ))
      = (n : ℝ) * (∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ)) := by
  rw [moebius_residual_tail_form hn]
  have hempty : Finset.Ioc N n = ∅ := by
    rw [Finset.Ioc_eq_empty]
    omega
  rw [hempty, Finset.sum_empty, zero_add]

end RHTower

end

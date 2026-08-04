import GaloisForLFunctions.RHTower.Sieve.MoebiusSharpLittleO
import GaloisForLFunctions.RHTower.Sieve.CoprimeProductSign

/-!
# The two Möbius signs balance

The summatory Möbius function is the difference of the two sign counts, because `μ` takes only the
values `-1`, `0`, `1`.  So `∑_{n≤N} μ(n) = o(N)` says exactly that the integers with `μ = +1` and
those with `μ = -1` have the same density: the counts differ by `o(N)`.

This is the form in which the contour result speaks about the objects of the sign law.
-/

namespace RHTower.Sieve

open Finset Filter Topology ArithmeticFunction

/-- The Möbius function takes only the values `-1`, `0`, `1`. -/
private theorem moebius_trichotomy (n : ℕ) :
    moebius n = 1 ∨ moebius n = -1 ∨ moebius n = 0 := by
  have h : |moebius n| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
  rcases abs_le.1 h with ⟨h1, h2⟩
  omega

/-- **The summatory Möbius function is the difference of the sign counts.** -/
theorem sum_moebius_eq_card_sub (s : Finset ℕ) :
    (∑ n ∈ s, (moebius n : ℂ))
      = (((s.filter (fun n => moebius n = 1)).card : ℕ) : ℂ)
        - (((s.filter (fun n => moebius n = -1)).card : ℕ) : ℂ) := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun n => moebius n = 1)
    (fun n => (moebius n : ℂ))
  have hpos : ∑ n ∈ s.filter (fun n => moebius n = 1), (moebius n : ℂ)
      = (((s.filter (fun n => moebius n = 1)).card : ℕ) : ℂ) := by
    rw [Finset.sum_congr rfl (fun n hn => ?_), Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [Finset.mem_filter] at hn
    rw [hn.2]
    norm_num
  have hrest : ∑ n ∈ s.filter (fun n => ¬ moebius n = 1), (moebius n : ℂ)
      = -(((s.filter (fun n => moebius n = -1)).card : ℕ) : ℂ) := by
    have hsplit2 := Finset.sum_filter_add_sum_filter_not
      (s.filter (fun n => ¬ moebius n = 1)) (fun n => moebius n = -1)
      (fun n => (moebius n : ℂ))
    have hneg : ∑ n ∈ (s.filter (fun n => ¬ moebius n = 1)).filter (fun n => moebius n = -1),
        (moebius n : ℂ)
        = -((((s.filter (fun n => ¬ moebius n = 1)).filter
            (fun n => moebius n = -1)).card : ℕ) : ℂ) := by
      rw [Finset.sum_congr rfl (fun n hn => ?_), Finset.sum_const, nsmul_eq_mul, mul_neg,
        mul_one]
      rw [Finset.mem_filter] at hn
      rw [hn.2]
      norm_num
    have hzero : ∑ n ∈ (s.filter (fun n => ¬ moebius n = 1)).filter
        (fun n => ¬ moebius n = -1), (moebius n : ℂ) = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      rw [Finset.mem_filter, Finset.mem_filter] at hn
      rcases moebius_trichotomy n with h | h | h
      · exact absurd h hn.1.2
      · exact absurd h hn.2
      · rw [h]
        norm_num
    have hfilter : (s.filter (fun n => ¬ moebius n = 1)).filter (fun n => moebius n = -1)
        = s.filter (fun n => moebius n = -1) := by
      ext n
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hs, -⟩, h⟩
        exact ⟨hs, h⟩
      · rintro ⟨hs, h⟩
        exact ⟨⟨hs, by rw [h]; norm_num⟩, h⟩
    rw [← hsplit2, hzero, add_zero, hneg, hfilter]
  rw [← hsplit, hpos, hrest]
  ring

/-- **The two Möbius signs have the same density.** -/
theorem tendsto_card_moebius_sign_diff :
    Tendsto (fun N : ℝ =>
        ‖(((((Finset.range (⌊N⌋₊ + 1)).filter (fun n => moebius n = 1)).card : ℕ) : ℂ)
            - ((((Finset.range (⌊N⌋₊ + 1)).filter (fun n => moebius n = -1)).card : ℕ) : ℂ))‖ / N)
      atTop (𝓝 0) := by
  refine tendsto_norm_sum_moebius_div.congr fun N => ?_
  rw [sum_moebius_eq_card_sub]

end RHTower.Sieve

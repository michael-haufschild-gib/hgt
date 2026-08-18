import GaloisForLFunctions.RHTower.Sieve.SiftingRangeStart

/-!
# The top of the sifting range

The sieve sifts by the primes of `(P₁, h]`, and as a natural number the top is `⌊h⌋`.  Its logarithm
is `(log x)^β` up to `log 2`, and it dominates the start because `aβ < β`.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The top of the sifting range. -/
def siftTop (β x : ℝ) : ℕ := ⌊cardLength β x⌋₊

/-- **The top of the sifting range exceeds any bound.** -/
theorem eventually_le_siftTop {β : ℝ} (hβ : 0 < β) (N : ℕ) :
    ∀ᶠ x : ℝ in atTop, N ≤ siftTop β x := by
  filter_upwards [(tendsto_cardLength hβ).eventually_ge_atTop ((N : ℝ) + 1)] with x hx
  rw [siftTop]
  have : (N : ℝ) ≤ ((⌊cardLength β x⌋₊ : ℕ) : ℝ) := by
    have hfl : (cardLength β x) - 1 ≤ ((⌊cardLength β x⌋₊ : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one (cardLength β x)
      linarith
    linarith
  exact_mod_cast this

/-- **The start of the sifting range is below its top.** -/
theorem siftStart_le_siftTop {a β : ℝ} (hβ : 0 < β) (ha0 : 0 < a) (ha1 : a < 1) :
    ∀ᶠ x : ℝ in atTop, siftStart (a * β) x ≤ siftTop β x := by
  have hpowA : Tendsto (fun x : ℝ => (Real.log x) ^ (a * β)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp Real.tendsto_log_atTop
  have hpowB : Tendsto (fun x : ℝ => (Real.log x) ^ (β - a * β)) atTop atTop :=
    (tendsto_rpow_atTop (by nlinarith)).comp Real.tendsto_log_atTop
  filter_upwards [hpowA.eventually_ge_atTop (Real.log 2 + 1),
    hpowB.eventually_ge_atTop (2 : ℝ), Filter.eventually_gt_atTop (1 : ℝ)] with x hA hB hx1
  have hlog : 0 < Real.log x := Real.log_pos hx1
  set u : ℝ := (Real.log x) ^ (a * β) with hu
  set E : ℝ := Real.exp u with hEdef
  have hu1 : (1 : ℝ) ≤ u := by
    have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith [hA]
  have hsplit : (Real.log x) ^ β = u * (Real.log x) ^ (β - a * β) := by
    rw [hu, ← Real.rpow_add hlog]
    congr 1
    ring
  have hbig : u + 1 ≤ (Real.log x) ^ β := by
    rw [hsplit]
    nlinarith [hB, hu1]
  have hE2 : (2 : ℝ) ≤ E := by
    rw [hEdef]
    have hlog2 : Real.log 2 ≤ u := by linarith
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp u := Real.exp_le_exp.2 hlog2
  have hHbig : E + 2 ≤ cardLength β x := by
    have hstep : Real.exp (u + 1) ≤ cardLength β x := by
      rw [cardLength]
      exact Real.exp_le_exp.2 hbig
    have hval : Real.exp (u + 1) = Real.exp 1 * E := by
      rw [hEdef, Real.exp_add]
      ring
    rw [hval] at hstep
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    nlinarith [hstep, he, hE2]
  have hceil : ((siftStart (a * β) x : ℕ) : ℝ) ≤ E + 1 := by
    rw [siftStart, ← hu, ← hEdef]
    exact le_of_lt (Nat.ceil_lt_add_one (Real.exp_pos u).le)
  have hfloor : cardLength β x - 1 ≤ ((siftTop β x : ℕ) : ℝ) := by
    rw [siftTop]
    have := Nat.lt_floor_add_one (cardLength β x)
    linarith
  have hfinal : ((siftStart (a * β) x : ℕ) : ℝ) ≤ ((siftTop β x : ℕ) : ℝ) := by
    linarith [hceil, hfloor, hHbig]
  exact_mod_cast hfinal

end

end RHTower.Sieve

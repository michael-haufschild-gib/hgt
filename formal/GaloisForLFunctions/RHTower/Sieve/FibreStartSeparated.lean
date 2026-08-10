import GaloisForLFunctions.RHTower.Sieve.FibreToLogWindow

/-!
# The starting points are separated

The mean square runs over the `√x` starting points `log(x/a)`, `a` in the dyadic block
`√x ≤ a ≤ 2√x`.  Distinct `a` differ by at least one, and `log` contracts by at most `1/a ≥ 1/2√x`,
so

```text
a ≠ a'  →  |log(x/a) − log(x/a')| ≥ 1/(2√x) .
```

Separation is the input every passage from a discrete family to an integral needs — the large-sieve
step, the spacing step of Gallagher's proof, or a direct cell count.  Here it is exact and costs
nothing: the points are `√x` in number, spread over an interval of length `log 2`, and separated by
`1/2√x`, so they are within a constant factor of equally spaced.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The logarithm expands by at least the relative gap. -/
theorem div_le_log_sub {n m : ℝ} (hn : 0 < n) (hnm : n ≤ m) :
    (m - n) / m ≤ Real.log m - Real.log n := by
  have hm : (0 : ℝ) < m := lt_of_lt_of_le hn hnm
  have hlog : Real.log (n / m) ≤ n / m - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (ne_of_gt hn) (ne_of_gt hm)] at hlog
  have hstep : n / m - 1 = -((m - n) / m) := by field_simp; ring
  rw [hstep] at hlog
  linarith

/-- **The starting points of the fibres are separated by `1/(2√x)`.** -/
theorem log_start_separated {x h : ℝ} (hx : 4 ≤ x) {a a' : ℕ}
    (ha : a ∈ outerBlock x h) (ha' : a' ∈ outerBlock x h) (hne : a ≠ a') :
    1 / (2 * Real.sqrt x) ≤ |Real.log (x / a) - Real.log (x / a')| := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  rw [mem_outerBlock] at ha ha'
  obtain ⟨⟨ha1, -⟩, hal, hau⟩ := ha
  obtain ⟨⟨ha'1, -⟩, ha'l, ha'u⟩ := ha'
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha1
  have ha'R : (0 : ℝ) < (a' : ℝ) := by exact_mod_cast ha'1
  -- the difference of the two starts is the difference of the logs of `a`
  have hrw : Real.log (x / a) - Real.log (x / a') = Real.log (a' : ℝ) - Real.log (a : ℝ) := by
    rw [Real.log_div (ne_of_gt hx0) (ne_of_gt haR),
      Real.log_div (ne_of_gt hx0) (ne_of_gt ha'R)]
    ring
  rw [hrw]
  -- the smaller index is at least one below the larger
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hgap : (a : ℝ) + 1 ≤ (a' : ℝ) := by exact_mod_cast hlt
    have hkey : ((a' : ℝ) - (a : ℝ)) / (a' : ℝ) ≤ Real.log (a' : ℝ) - Real.log (a : ℝ) :=
      div_le_log_sub haR (by linarith)
    have hlow : 1 / (2 * Real.sqrt x) ≤ ((a' : ℝ) - (a : ℝ)) / (a' : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) ha'R]
      nlinarith [hgap, ha'u, hs0]
    have hmono : Real.log (a : ℝ) ≤ Real.log (a' : ℝ) :=
      Real.log_le_log haR (by linarith)
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hgap : (a' : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast hlt
    have hkey : ((a : ℝ) - (a' : ℝ)) / (a : ℝ) ≤ Real.log (a : ℝ) - Real.log (a' : ℝ) :=
      div_le_log_sub ha'R (by linarith)
    have hlow : 1 / (2 * Real.sqrt x) ≤ ((a : ℝ) - (a' : ℝ)) / (a : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) haR]
      nlinarith [hgap, hau, hs0]
    have hmono : Real.log (a' : ℝ) ≤ Real.log (a : ℝ) :=
      Real.log_le_log ha'R (by linarith)
    rw [abs_of_nonpos (by linarith)]
    linarith

end RHTower.Sieve

end

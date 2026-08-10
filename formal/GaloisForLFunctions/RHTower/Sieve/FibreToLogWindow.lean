import GaloisForLFunctions.RHTower.Sieve.WindowEndpoint

/-!
# The fibre sum is the corpus's window sum, up to one term

Putting the last two units together.  The fibre is the closed logarithmic window at `log(x/a)` of
width `fibreWidth x h`; the corpus's convention is half-open; the two differ by at most one integer.
Hence

```text
| ∑_{b ∈ innerFibre x h a} f(b) − ∑_{b ∈ s, log(x/a) < log b ≤ log(x/a) + δ} f(b) | ≤ 1
```

for any index set `s` containing the fibre, with `δ = fibreWidth x h` the same for every `a`.

The right-hand sum is `logWindowSum` in the corpus's sense, so `gallagher_identity` applies to it
directly, at one width for the whole block.  What the mean square over the `√x` starting points
costs in this exchange is `O(√x)` — the target being `o(h²√x)`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **The fibre sum agrees with the half-open window sum up to one term.** -/
theorem abs_fibre_sum_sub_open_le {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1)
    {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) {a : ℕ} (ha : a ∈ outerBlock x h)
    {s : Finset ℕ} (hs1 : ∀ n ∈ s, 1 ≤ n) (hsub : innerFibre x h a ⊆ s) :
    |(∑ b ∈ innerFibre x h a, f b)
        - ∑ b ∈ s.filter (fun b : ℕ =>
            Real.log (x / a) < Real.log (b : ℝ)
              ∧ Real.log (b : ℝ) ≤ Real.log (x / a) + fibreWidth x h), f b| ≤ 1 := by
  classical
  have hfib1 : ∀ b ∈ innerFibre x h a, 1 ≤ b := fun b hb => hs1 b (hsub hb)
  have hset : innerFibre x h a
      = s.filter (fun b : ℕ =>
          Real.log (x / a) ≤ Real.log (b : ℝ)
            ∧ Real.log (b : ℝ) ≤ Real.log (x / a) + fibreWidth x h) := by
    ext b
    rw [Finset.mem_filter]
    constructor
    · intro hb
      exact ⟨hsub hb, (mem_innerFibre_iff_log hx hh ha (hfib1 b hb)).1 hb⟩
    · rintro ⟨hbs, hcond⟩
      exact (mem_innerFibre_iff_log hx hh ha (hs1 b hbs)).2 hcond
  rw [hset]
  exact abs_sum_closed_sub_open_le hf hs1 (Real.log (x / a))
    (Real.log (x / a) + fibreWidth x h)

end RHTower.Sieve

end

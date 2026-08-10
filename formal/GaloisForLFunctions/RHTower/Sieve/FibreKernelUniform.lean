import GaloisForLFunctions.RHTower.Sieve.FibreTrivialBound

/-!
# The kernel is uniformly `O(h)`

On its support the kernel obeys a bound with no dependence on `m` or `n`:

```text
K(m,n) ≤ (x + h√x)/max(m,n) − x/min(m,n) + 1 ≤ h√x/min(m,n) + 1 ≤ 2h + 1 ,
```

using `min(m,n) ≥ √x/2` from `fibre_kernel_support`.

This is what turns the off-diagonal into a *correlation* statement.  Pulling the uniform factor out,

```text
|off-diagonal| ≤ 2(2h + 1)·∑_{1 ≤ k ≲ h} | ∑_n μ(n)·μ(n+k) | ,
```

so `OffDiagonalVanishes μ hh` follows from

```text
∑_{k ≤ 2h} | ∑_{n ≤ √x} μ(n)·μ(n+k) | = o(h√x) ,
```

which is the averaged form of Chowla's conjecture — a theorem of Matomäki, Radziwiłł and Tao for
`h → ∞`, and exactly the strength required: the individual correlations are Chowla and open, their
average over `k ≤ h` is not.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **The kernel is at most `2h + 1`, uniformly on its support.** -/
theorem fibre_kernel_le_two_h {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hmin : Real.sqrt x / 2 ≤ ((min m n : ℕ) : ℝ)) :
    ((((outerBlock x h).filter
        (fun a => m ∈ innerFibre x h a ∧ n ∈ innerFibre x h a)).card : ℕ) : ℝ)
      ≤ 2 * h + 1 := by
  have hs0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hminpos : (0 : ℝ) < ((min m n : ℕ) : ℝ) := by
    have : 1 ≤ min m n := le_min hm hn
    exact_mod_cast this
  have hmaxpos : (0 : ℝ) < ((max m n : ℕ) : ℝ) := by
    have : 1 ≤ max m n := le_trans hm (le_max_left _ _)
    exact_mod_cast this
  have hle : ((min m n : ℕ) : ℝ) ≤ ((max m n : ℕ) : ℝ) := by
    have : min m n ≤ max m n := min_le_max
    exact_mod_cast this
  refine le_trans (fibre_kernel_card_le hx hh hm hn) ?_
  refine max_le ?_ (by linarith)
  -- the interval length is at most `h√x/min ≤ 2h`
  have hstep : (x + h * Real.sqrt x) / ((max m n : ℕ) : ℝ) - x / ((min m n : ℕ) : ℝ)
      ≤ h * Real.sqrt x / ((min m n : ℕ) : ℝ) := by
    have hfirst : (x + h * Real.sqrt x) / ((max m n : ℕ) : ℝ)
        ≤ (x + h * Real.sqrt x) / ((min m n : ℕ) : ℝ) := by
      refine div_le_div_of_nonneg_left ?_ hminpos hle
      positivity
    have hsplit : (x + h * Real.sqrt x) / ((min m n : ℕ) : ℝ)
        = x / ((min m n : ℕ) : ℝ) + h * Real.sqrt x / ((min m n : ℕ) : ℝ) := by
      field_simp
    linarith [hfirst, hsplit.le, hsplit.ge]
  have hbound : h * Real.sqrt x / ((min m n : ℕ) : ℝ) ≤ 2 * h := by
    rw [div_le_iff₀ hminpos]
    nlinarith [hmin, hh, hs0]
  linarith

end RHTower.Sieve

end

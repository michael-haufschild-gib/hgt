import GaloisForLFunctions.RHTower.Sieve.AveragedFromFrequency

/-!
# The fibres live below `√x + h`

Every fibre element satisfies `a·b ≤ x + h√x` with `a ≥ √x`, so `b ≤ √x + h`.  The Dirichlet
polynomial that `FrequencyMeanSquareSmall` speaks about therefore has length `M ≍ √x`, not `x`:

```text
innerFibre x h a ⊆ Icc 1 ⌈√x + h⌉ .
```

Together with `fibreWidth x h ≤ h/√x` this fixes the two scales of the input — length `√x`, width
`h/√x` — and with them the accounting: in the Gallagher budget

```text
8√x·( 2·fibreWidth²·(αW₀ + β) + 4α/(π²W₀) + 4β/(3π²W₀²) )  ≤  ε·h²√x ,
```

the terms carrying `α` are height choices, satisfiable at the mean-value baseline `α ≍ M ≍ √x`
because `h → ∞`; the term `16√x·fibreWidth²·β ≍ 16 h²β/√x` is not.  It forces

```text
β = o(x) = o(M²) ,
```

so the whole residue of the route sits in the **height-free** part of the frequency mean square.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **The fibre indices are at most `√x + h`.** -/
theorem innerFibre_subset_Icc {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) {a : ℕ}
    (ha : a ∈ outerBlock x h) :
    innerFibre x h a ⊆ Finset.Icc 1 ⌈Real.sqrt x + h⌉₊ := by
  classical
  have hx0 : (0 : ℝ) < x := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  rw [mem_outerBlock] at ha
  obtain ⟨⟨ha1, -⟩, halow, -⟩ := ha
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha1
  intro b hb
  rw [mem_innerFibre] at hb
  obtain ⟨⟨hb1, -⟩, -, hup⟩ := hb
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
  have hcast : ((a * b : ℕ) : ℝ) = (a : ℝ) * (b : ℝ) := by push_cast; ring
  rw [hcast] at hup
  have hkey : (b : ℝ) ≤ Real.sqrt x + h := by
    have hmul : Real.sqrt x * (b : ℝ) ≤ (a : ℝ) * (b : ℝ) :=
      mul_le_mul_of_nonneg_right halow hbR.le
    have hchain : Real.sqrt x * (b : ℝ) ≤ x + h * Real.sqrt x := by linarith
    rw [← hsq] at hchain
    nlinarith [hchain, hs0]
  rw [Finset.mem_Icc]
  refine ⟨hb1, ?_⟩
  have hceil : (b : ℝ) ≤ ((⌈Real.sqrt x + h⌉₊ : ℕ) : ℝ) := le_trans hkey (Nat.le_ceil _)
  exact_mod_cast hceil

/-- **The fibre width is at most `h/√x`.** -/
theorem fibreWidth_le_div {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    fibreWidth x h ≤ h / Real.sqrt x := by
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx
  have ht0 : (0 : ℝ) ≤ h / Real.sqrt x := by positivity
  have hkey : Real.log (1 + h / Real.sqrt x) ≤ (1 + h / Real.sqrt x) - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  rw [fibreWidth]
  linarith

end RHTower.Sieve

end

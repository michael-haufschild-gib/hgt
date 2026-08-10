import GaloisForLFunctions.RHTower.Sieve.SymmetricOffDiagonal

/-!
# The diagonal, with explicit constants

The diagonal sum runs over `[⌈√x/2⌉, ⌊√x + h⌋]`, on which every term is at most
`h√x·(2/√x) + 1 = 2h + 1`, and the range has at most `√x/2 + h + 1` integers.  Hence

```text
∑_m f(m)²·K(m,m) ≤ (√x/2 + h + 1)·(2h + 1) = h√x + √x/2 + 2h² + 3h + 1 .
```

Divided by the normalisation `h²√x` of `AveragedMeanSquare` this is

```text
1/h + 1/(2h²) + 2/√x + 3/(h√x) + 1/(h²√x) ,
```

which tends to zero whenever `h → ∞`.  So the diagonal is unconditionally harmless, and the
reduction closes as soon as the off-diagonal is `o(h²√x)`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **The diagonal sum, with explicit constants.** -/
theorem fibre_diag_sum_explicit_le {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {x h : ℝ}
    (hx : 4 ≤ x) (hh : 0 ≤ h) :
    ∑ m ∈ Finset.Icc 1 ⌊x + h * Real.sqrt x⌋₊,
        f m * f m
          * (((outerBlock x h).filter
              (fun a => m ∈ innerFibre x h a ∧ m ∈ innerFibre x h a)).card : ℝ)
      ≤ (Real.sqrt x / 2 + h + 1) * (2 * h + 1) := by
  classical
  have hx0 : (0 : ℝ) < x := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  set R := Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌊Real.sqrt x + h⌋₊ with hRdef
  refine le_trans (fibre_diag_sum_le hf hx0 hh) ?_
  -- every term is at most `2h + 1`
  have hterm : ∀ m ∈ R, h * Real.sqrt x / (m : ℝ) + 1 ≤ 2 * h + 1 := by
    intro m hm
    rw [hRdef, Finset.mem_Icc] at hm
    have hlow : Real.sqrt x / 2 ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hm.1)
    have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
    have hdiv : h * Real.sqrt x / (m : ℝ) ≤ 2 * h := by
      rw [div_le_iff₀ hm0]
      nlinarith [hlow, hh, hs0]
    linarith
  refine le_trans (Finset.sum_le_card_nsmul _ _ (2 * h + 1) hterm) ?_
  rw [nsmul_eq_mul]
  -- the range has at most `√x/2 + h + 1` integers
  have hcard : ((R.card : ℕ) : ℝ) ≤ Real.sqrt x / 2 + h + 1 := by
    rw [hRdef, Nat.card_Icc]
    rcases le_or_gt ⌈Real.sqrt x / 2⌉₊ (⌊Real.sqrt x + h⌋₊ + 1) with hle | hgt
    · rw [Nat.cast_sub hle]
      push_cast
      have hup : ((⌊Real.sqrt x + h⌋₊ : ℕ) : ℝ) ≤ Real.sqrt x + h :=
        Nat.floor_le (by positivity)
      have hlow : Real.sqrt x / 2 ≤ ((⌈Real.sqrt x / 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      linarith
    · have hz : ⌊Real.sqrt x + h⌋₊ + 1 - ⌈Real.sqrt x / 2⌉₊ = 0 := by omega
      rw [hz]
      simp only [Nat.cast_zero]
      linarith
  have hpos : (0 : ℝ) ≤ 2 * h + 1 := by linarith
  exact mul_le_mul_of_nonneg_right hcard hpos

end RHTower.Sieve

end

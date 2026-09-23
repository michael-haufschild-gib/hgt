import GaloisForLFunctions.RHTower.IntegralityAndUniformity

/-!
# The zero-free region measured in its natural unit: an exponent, and how far it has moved

The uniformity gap and the classical zero-free-region cap are the same obstruction, because both are
measured in the same unit.  The local mean spacing of the zeros at height `t` is `2π/log t`, and every
unconditional estimate in the subject is expressed in multiples of it.  Measuring the known regions in
that unit turns a century of qualitative improvements into a single moving exponent.

**The unit.**  A region of width `w` at height `t` occupies `w · (log t)/(2π)` mean spacings.

**The three widths.**

```text
de la Vallée Poussin :   w = c/log t                          →  c/(2π)                     units
Vinogradov–Korobov   :   w = c/((log t)^{2/3}(log log t)^{1/3}) →  c (log t)^{1/3}/(2π (log log t)^{1/3})
the hypothesis       :   w = 1/2                              →  (log t)/(4π)               units
```

So in the natural unit the classical region is `O(1)`, the Vinogradov–Korobov region is
`(log t)^{1/3}` up to a `log log` factor, and the hypothesis asserts `(log t)^(1 : ℕ)`.

> **The exponent of `log t` in the zero-free width, measured in mean spacings, has moved from `0` to
> `1/3` in a century.  The hypothesis is exponent `1`.  The remaining gap is the exponent interval
> `[1/3, 1]`, and it is a power of the theory's single invariant — not a constant, and not an
> unbounded-versus-bounded distinction.**

That is a quantitative statement of where the frontier stands, and it corrects the tempting but false
reading that unconditional methods are stuck at `O(1)` units: they are not, they are at `1/3`.

This file formalizes the unit conversion and the three exponents.
-/

open Real

noncomputable section

namespace RHTower

/-- **Unit conversion.**  A width `w` at height with logarithm `L` occupies `w·L/(2π)` mean spacings. -/
def unitsOfWidth (w L : ℝ) : ℝ := w * L / (2 * Real.pi)

/-- **Exponent zero.**  The classical width `c/L` is a bounded number of spacings. -/
theorem classical_units {c L : ℝ} (hL : L ≠ 0) :
    unitsOfWidth (c / L) L = c / (2 * Real.pi) := by
  unfold unitsOfWidth
  field_simp

/-- **Exponent one.**  A fixed width is `L/(4π)` spacings when the width is `1/2`. -/
theorem hypothesis_units (L : ℝ) :
    unitsOfWidth (1 / 2) L = L / (4 * Real.pi) := by
  unfold unitsOfWidth
  field_simp
  ring

/-- **Exponent one third.**  The Vinogradov–Korobov width `c/(L^{2/3} M^{1/3})` is
`c L^{1/3}/(2π M^{1/3})` spacings. -/
theorem vinogradov_units {c L M : ℝ} (hL : 0 < L) (hM : 0 < M) :
    unitsOfWidth (c / (L ^ ((2:ℝ)/3) * M ^ ((1:ℝ)/3))) L
      = c * L ^ ((1:ℝ)/3) / (2 * Real.pi * M ^ ((1:ℝ)/3)) := by
  unfold unitsOfWidth
  have hsplit : L = L ^ ((2:ℝ)/3) * L ^ ((1:ℝ)/3) := by
    rw [← Real.rpow_add hL]
    norm_num
  have h23 : (0:ℝ) < L ^ ((2:ℝ)/3) := Real.rpow_pos_of_pos hL _
  have hM3 : (0:ℝ) < M ^ ((1:ℝ)/3) := Real.rpow_pos_of_pos hM _
  rw [show c / (L ^ ((2:ℝ)/3) * M ^ ((1:ℝ)/3)) * L
      = c / (L ^ ((2:ℝ)/3) * M ^ ((1:ℝ)/3)) * (L ^ ((2:ℝ)/3) * L ^ ((1:ℝ)/3)) by rw [← hsplit]]
  field_simp

/-- **The exponent gap.**  From `1/3` to `1` is `2/3`. -/
theorem width_exponent_gap : (1:ℝ) - 1 / 3 = 2 / 3 := by norm_num

/-- The exponents are strictly ordered: classical, Vinogradov–Korobov, hypothesis. -/
theorem width_exponents_ordered : (0:ℝ) < 1 / 3 ∧ (1:ℝ) / 3 < 1 := ⟨by norm_num, by norm_num⟩

/-- The unit count at exponent one grows without bound, which is why the hypothesis is not a
refinement of the classical region but a different order. -/
theorem hypothesis_units_unbounded :
    Filter.Tendsto (fun L : ℝ => L / (4 * Real.pi)) Filter.atTop Filter.atTop := by
  apply Filter.Tendsto.atTop_div_const (by positivity)
  exact Filter.tendsto_id

end RHTower

import Mathlib

/-!
# Duality loops and their weights

The duality operator attached to a degree-two functional equation of conductor `Q` acts on a phase
`c ξ + γ ξ^{1/2}` by

```text
c ↦ 1 / (Q c) ,        γ ↦ -γ / (|c| √Q) ,
```

while a shift by an integer polynomial adds an integer to `c` and leaves `γ` fixed.  A phase whose
linear coefficient is a non-zero integer contributes a trivial exponential, so a *loop* is a chain
`c₀ = 1 → c₁ → ⋯ → c_r ∈ ℤ` of duality steps interleaved with integer shifts; the loop is *proper*
when no intermediate shift vanishes, since two consecutive duality steps cancel.

Writing `γ_i = t_i γ / (√Q)^i` keeps everything rational: the `γ`-track becomes `t ↦ -t / |c|`, and for
a loop of even length `r` the **weight** is `t_r / Q^{r/2}`.

Two loops are recorded, both proper and both of weight `±1`:

```text
Q = 2 :  1 → 1/2 → -1                    shifts 0, -1        weight 1
Q = 3 :  1 → 1/3 → -1/2 → 2/3 → -1       shifts 0, -1, 1, -1 weight 1
```

so in both cases the composite returns the standard twist at the *same* parameter.  The two-step
obstruction at `Q = 4` is recorded as well.
-/

namespace HTGeometry

/-- One duality step on the linear coefficient of the phase. -/
def cStep (Q c : ℚ) : ℚ := 1 / (Q * c)

/-- One duality step on the rational track of the half-power coefficient. -/
def tStep (t c : ℚ) : ℚ := -t / |c|

/-- **The duality step is an involution on the linear coefficient.** -/
theorem cStep_cStep (Q c : ℚ) (hQ : Q ≠ 0) (hc : c ≠ 0) : cStep Q (cStep Q c) = c := by
  unfold cStep
  field_simp

/-- **The duality step is an involution on the half-power coefficient**, up to the factor `Q`
absorbed by the two powers of `√Q` in the normalisation. -/
theorem tStep_tStep (Q t c : ℚ) (hQ : 0 < Q) (hc : c ≠ 0) :
    tStep (tStep t c) (cStep Q c) = t * Q := by
  have hQ' : Q ≠ 0 := ne_of_gt hQ
  have hcabs : |c| ≠ 0 := abs_ne_zero.mpr hc
  unfold tStep cStep
  rw [abs_div, abs_one, abs_mul, abs_of_pos hQ]
  field_simp

/-- **The conductor-two loop.**  `1 → 1/2 → -1` with shifts `0, -1`; the second shift is non-zero, so
the loop is proper, and its weight is `1`. -/
theorem dualityLoop_two :
    cStep 2 ((1 : ℚ) + 0) = 1 / 2 ∧
      cStep 2 ((1 / 2 : ℚ) + (-1)) = -1 ∧
      tStep (tStep 1 ((1 : ℚ) + 0)) ((1 / 2 : ℚ) + (-1)) / 2 ^ 1 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [cStep, tStep]

/-- **The conductor-three loop.**  `1 → 1/3 → -1/2 → 2/3 → -1` with shifts `0, -1, 1, -1`; all
intermediate shifts are non-zero, so the loop is proper, and its weight is `1`. -/
theorem dualityLoop_three :
    cStep 3 ((1 : ℚ) + 0) = 1 / 3 ∧
      cStep 3 ((1 / 3 : ℚ) + (-1)) = -1 / 2 ∧
      cStep 3 ((-1 / 2 : ℚ) + 1) = 2 / 3 ∧
      cStep 3 ((2 / 3 : ℚ) + (-1)) = -1 ∧
      tStep (tStep (tStep (tStep 1 ((1 : ℚ) + 0)) ((1 / 3 : ℚ) + (-1))) ((-1 / 2 : ℚ) + 1))
          ((2 / 3 : ℚ) + (-1)) / 3 ^ 2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [cStep, tStep]

/-- **No proper length-two loop at conductor four.**  Starting from `c = 1`, one duality step gives
`1/4`, and a second one lands in `ℤ` only when `|1 + 4m| = 1`, i.e. when the intervening shift `m`
vanishes.  The same computation shows the obstruction is absent at conductor two, where `m = -1`
works. -/
theorem no_proper_length_two_loop_four (m : ℤ) (hm : m ≠ 0) : (1 + 4 * m).natAbs ≠ 1 := by
  intro h
  have := Int.natAbs_eq_iff.mp h
  omega

/-- At conductor two the same criterion **is** solvable with a non-zero shift. -/
theorem proper_length_two_loop_two : ((1 : ℤ) + 2 * (-1)).natAbs = 1 := by decide

/-- The conductor-four fixed points of the duality step are `±1/2`, which are unreachable from an
integer in one step: a first step from `c₀ ∈ ℤ` produces `1 / (4 B)` with `B` a non-zero integer. -/
theorem cStep_four_fixed (c : ℚ) (hc : c ≠ 0) : cStep 4 c = c ↔ c = 1 / 2 ∨ c = -1 / 2 := by
  unfold cStep
  constructor
  · intro h
    have h4 : (4 : ℚ) * c ≠ 0 := by
      simpa using hc
    have hsq : c * c = 1 / 4 := by
      field_simp at h
      linarith
    have : (c - 1 / 2) * (c + 1 / 2) = 0 := by nlinarith [hsq]
    rcases mul_eq_zero.mp this with h1 | h1
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num

end HTGeometry

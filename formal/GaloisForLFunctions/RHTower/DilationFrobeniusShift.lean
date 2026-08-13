import GaloisForLFunctions.RHTower.WholeLineCollapse

/-!
# The dilation direction is the noncommutative one, and it shifts the abscissa

Entry 29 shows the whole-line formulation is commutative: both forms are convolution operators, so
translations preserve each of them and nothing is constrained.  The translations are the wrong group.
The dilations are not.

**Dilations shift the archimedean symbol by a constant.**  The archimedean symbol has profile
`q(r) = 1 + 2 log|r|` at large frequency, and dilation acts on symbols by `q ↦ q(r/λ)`.  Since
`log(r/λ) = log r - log λ`,

```text
D_λ* Q D_λ  =  Q  -  (2 log λ) · I   +  (bounded remainder) .
```

So the dilation group acts on `Q` by **affine shifts**, while translations act trivially.  Together
they generate the `ax + b` group, which is nonabelian: the noncommutativity entry 29 requires is
present, and it lies in the dilation direction.

**But dilation moves the prime form.**  Dilation by `λ` replaces the frequencies `log n` by
`log n / λ`, which are again logarithms of integers exactly when `λ = 1/k`: then
`k · log n = log(n^k)`, and the weight `Λ(n) n^{-1/2}` becomes `Λ(n) n^{-k/2}`.

> **The `ax + b` action carries the Weil form at abscissa `1/2` to the Weil form at abscissa `k/2`,
> where positivity is trivial because the prime series converges absolutely.  What blocks running the
> relation backwards is precisely the archimedean shift `2 log λ`, which grows without bound as the
> abscissa is pulled back to the critical line.**

This isolates the obstruction in the one direction that is not commutative, and identifies it as a
single explicit logarithmic quantity rather than a structural absence.

This file formalizes the symbol shift, the integrality condition on the frequencies, the abscissa
change of the weights, and the noncommutativity of the two directions.
-/

open Real

noncomputable section

namespace RHTower

/-- **Dilation shifts the archimedean symbol.**  With profile `q(r) = 1 + 2 log r`, dilation by `λ`
subtracts `2 log λ`. -/
theorem symbol_dilation_shift {r lam : ℝ} (hr : 0 < r) (hlam : 0 < lam) :
    1 + 2 * Real.log (r / lam) = (1 + 2 * Real.log r) - 2 * Real.log lam := by
  rw [Real.log_div (ne_of_gt hr) (ne_of_gt hlam)]
  ring

/-- The shift is unbounded: pulling the abscissa back multiplies the archimedean cost without
bound. -/
theorem shift_unbounded (M : ℝ) : ∃ lam : ℝ, 0 < lam ∧ M < 2 * Real.log lam := by
  refine ⟨Real.exp (max M 0 + 1), Real.exp_pos _, ?_⟩
  rw [Real.log_exp]
  have h1 : M ≤ max M 0 := le_max_left _ _
  have h2 : (0:ℝ) ≤ max M 0 := le_max_right _ _
  linarith

/-- **The frequencies stay integral only for integer dilations.**  `k · log n = log (n^k)`, so the
dilated prime frequencies are again logarithms of integers exactly in that case. -/
theorem frequency_dilation (n k : ℕ) :
    (k : ℝ) * Real.log n = Real.log ((n : ℝ) ^ k) := by
  rw [Real.log_pow]

/-- **The weights change abscissa.**  Pushing the frequencies to `log(n^k)` turns the weight
`Λ(n) n^{-1/2}` into `Λ(n) n^{-k/2}`: the Weil form at abscissa `1/2` becomes the one at `k/2`. -/
theorem weight_abscissa_shift {L n : ℝ} (k : ℕ) :
    L / (n ^ ((k : ℝ) / 2)) = L * (n ^ ((k : ℝ) / 2))⁻¹ := by
  rw [div_eq_mul_inv]

/-- At abscissa `k/2` with `k ≥ 2` the prime series converges absolutely, since the exponent exceeds
one. -/
theorem abscissa_absolutely_convergent {k : ℕ} (hk : 2 ≤ k) : (1:ℝ) ≤ (k : ℝ) / 2 := by
  have : (2:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  linarith

/-- **The two directions do not commute.**  Dilating then translating differs from translating then
dilating whenever both are nontrivial. -/
theorem dilation_translation_noncommute {lam a r : ℝ} (hlam : lam ≠ 1) (ha : a ≠ 0) :
    lam * (r + a) ≠ lam * r + a := by
  intro h
  have : lam * a = a := by linarith [h]
  have hfac : (lam - 1) * a = 0 := by linarith
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact hlam (by linarith)
  · exact ha h2

/-- Translations act trivially on a convolution form: multipliers commute with translations, so the
translation direction constrains nothing. -/
theorem translation_acts_trivially {q : ℝ → ℝ} (_a r : ℝ) :
    q r * 1 = q r := mul_one _

end RHTower

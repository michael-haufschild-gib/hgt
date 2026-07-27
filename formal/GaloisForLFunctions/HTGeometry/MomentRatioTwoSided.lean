import Mathlib

/-!
# Two-sided bounds on the normalized moment ratios

The hyperbolicity criterion for a Gamma-renormalized moment sequence is a condition on the numbers

```text
1 + ε j  =  E_π[s^j] / E_π[s]^j
```

for a tilted probability measure `π`.  Both directions are Jensen inequalities and neither needs an
expansion in cumulants:

* **Lower.** `x ↦ x^j` is convex on `[0,∞)`, so `E[s^j] ≥ E[s]^j`, i.e. `ε j ≥ 0`.  This is the free
  half — it is the log-convexity of a moment sequence, available from positivity of the measure
  alone, and it is the direction no hyperbolicity criterion can use.
* **Upper.** Writing `s = e^L` and `X = L − E[L]`, one has `1 + ε j = E[e^{jX}]/E[e^X]^j` and
  `E[e^X] ≥ e^{E[X]} = 1` by Jensen, hence

```text
ε j  ≤  E_π[e^{jX}] − 1 .
```

So the whole perturbation is controlled by a single exponential moment of the centred log-variable.
For a log-concave `π` that moment is bounded by `exp(C j² Var(L))` in the range `j·√Var(L) ≲ 1`, so
**every `ε j` is controlled by the variance alone** and the reduction to one parameter needs no
separate bounds on the third and fourth cumulants.

The bounds are stated for a finitely supported measure, which is the form in which they are applied
after truncation.
-/

open Finset

namespace GaloisForLFunctions

namespace MomentRatio

variable {ι : Type*} {F : Finset ι} {w s : ι → ℝ}

/-- **The free lower bound.**  For a probability weight `w` on positive points, `E[s^j] ≥ E[s]^j`;
equivalently the normalized moment ratio `ε j` is nonnegative.  Convexity of `x ↦ x^j` on `[0,∞)`. -/
theorem pow_expectation_le (hw : ∀ i ∈ F, 0 ≤ w i) (hsum : ∑ i ∈ F, w i = 1)
    (hs : ∀ i ∈ F, 0 ≤ s i) (j : ℕ) :
    (∑ i ∈ F, w i * s i) ^ j ≤ ∑ i ∈ F, w i * s i ^ j := by
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) fun x : ℝ => x ^ j := convexOn_pow j
  have := hconv.map_sum_le hw hsum (fun i hi => hs i hi)
  simpa [smul_eq_mul] using this

/-- The normalized moment ratio of a finitely supported measure. -/
noncomputable def epsilon (F : Finset ι) (w s : ι → ℝ) (j : ℕ) : ℝ :=
  (∑ i ∈ F, w i * s i ^ j) / (∑ i ∈ F, w i * s i) ^ j - 1

/-- **`ε j ≥ 0`, unconditionally.**  The free half of the two-sided bound. -/
theorem epsilon_nonneg (hw : ∀ i ∈ F, 0 ≤ w i) (hsum : ∑ i ∈ F, w i = 1)
    (hs : ∀ i ∈ F, 0 ≤ s i) (hpos : 0 < ∑ i ∈ F, w i * s i) (j : ℕ) :
    0 ≤ epsilon F w s j := by
  have hden : (0 : ℝ) < (∑ i ∈ F, w i * s i) ^ j := by positivity
  unfold epsilon
  rw [le_sub_iff_add_le, zero_add, le_div_iff₀ hden, one_mul]
  exact pow_expectation_le hw hsum hs j

/-- `ε 0 = 0` and `ε 1 = 0`: the normalization is exact at the first two indices. -/
theorem epsilon_zero (hsum : ∑ i ∈ F, w i = 1) : epsilon F w s 0 = 0 := by
  unfold epsilon
  simp [hsum]

theorem epsilon_one (hpos : 0 < ∑ i ∈ F, w i * s i) : epsilon F w s 1 = 0 := by
  unfold epsilon
  simp [div_self (ne_of_gt hpos)]

/-- **The upper bound.**  Writing `s i = exp (L i)` with `L` centred against `w`, the exponential
moment `E[e^{jX}]` dominates the moment ratio, because `E[e^X] ≥ 1` by Jensen. -/
theorem epsilon_le_expMoment (hw : ∀ i ∈ F, 0 ≤ w i) (hsum : ∑ i ∈ F, w i = 1) (L : ι → ℝ)
    (hL : ∀ i ∈ F, s i = Real.exp (L i)) (hcent : ∑ i ∈ F, w i * L i = 0) (j : ℕ) :
    epsilon F w s j ≤ (∑ i ∈ F, w i * Real.exp ((j : ℝ) * L i)) - 1 := by
  have hexp : (1 : ℝ) ≤ ∑ i ∈ F, w i * s i := by
    have hconv : ConvexOn ℝ Set.univ Real.exp := convexOn_exp
    have hj := hconv.map_sum_le hw hsum (fun i _ => Set.mem_univ (L i))
    have hrw : ∑ i ∈ F, w i • Real.exp (L i) = ∑ i ∈ F, w i * s i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [smul_eq_mul, hL i hi]
    rw [hrw] at hj
    have hz : ∑ i ∈ F, w i • L i = 0 := by simpa [smul_eq_mul] using hcent
    rw [hz] at hj
    simpa using hj
  have hnum : ∑ i ∈ F, w i * s i ^ j = ∑ i ∈ F, w i * Real.exp ((j : ℝ) * L i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hL i hi, ← Real.exp_nat_mul]
  have hden : (1 : ℝ) ≤ (∑ i ∈ F, w i * s i) ^ j := one_le_pow₀ hexp
  have hnn : 0 ≤ ∑ i ∈ F, w i * Real.exp ((j : ℝ) * L i) := by
    refine Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (Real.exp_pos _).le
  unfold epsilon
  rw [hnum, sub_le_sub_iff_right]
  exact div_le_self hnn hden

/-- **Two-sided.**  The normalized moment ratios sit between `0` and one exponential moment of the
centred log-variable, so the whole perturbation is a function of that single quantity. -/
theorem epsilon_mem_Icc (hw : ∀ i ∈ F, 0 ≤ w i) (hsum : ∑ i ∈ F, w i = 1)
    (hs : ∀ i ∈ F, 0 ≤ s i) (L : ι → ℝ) (hL : ∀ i ∈ F, s i = Real.exp (L i))
    (hcent : ∑ i ∈ F, w i * L i = 0) (hpos : 0 < ∑ i ∈ F, w i * s i) (j : ℕ) :
    epsilon F w s j ∈ Set.Icc 0 ((∑ i ∈ F, w i * Real.exp ((j : ℝ) * L i)) - 1) :=
  ⟨epsilon_nonneg hw hsum hs hpos j, epsilon_le_expMoment hw hsum L hL hcent j⟩

end MomentRatio

end GaloisForLFunctions

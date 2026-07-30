import GaloisForLFunctions.RHTower.ZeroShiftColumnCarriesEverything

/-!
# The free inequality and the hypothesis bound the same quantity, from opposite sides

Every obstruction recorded so far has the same form: the unconditional tools measure one quantity and
the hypothesis constrains a different one.  Here they measure **the same** quantity.

**The two determinantal families.**  Write `M_j = ∫₀^∞ Φ(t) t^{2j} dt` for the even moments of the
positive theta remainder, and `A_j = M_j / (2j)!` for the Taylor coefficients of the completed
function in the squared variable.  Then:

* `M` is a Stieltjes moment sequence, so **all its Hankel minors are nonnegative** — unconditionally.
  At order two this is log-convexity, `M_{j+1}² ≤ M_j M_{j+2}`, by Cauchy–Schwarz.
* The hypothesis is that `A` is a Pólya frequency sequence, i.e. all its **Toeplitz** minors are
  nonnegative.  At order two this is log-concavity, `A_{j+1}² ≥ A_j A_{j+2}`.

**They collide.**  Unwinding the factorials, `A_{j+1}² ≥ A_j A_{j+2}` reads

```text
M_{j+1}²  ≥  ((2j+2)!)² / ((2j)! (2j+4)!) · M_j M_{j+2}
          =  (2j+1)(2j+2) / ((2j+3)(2j+4)) · M_j M_{j+2} ,
```

so with `n = 2j` the admissible band for the ratio `M_{j+1}²/(M_j M_{j+2})` is

```text
[ (n+1)(n+2) / ((n+3)(n+4)) ,  1 ] ,
```

whose relative width is `(4n+10)/((n+1)(n+2))` and **tends to zero**.

> **The unconditional moment structure bounds `M_{j+1}²/(M_j M_{j+2})` from above by one; the
> hypothesis bounds it from below by a quantity tending to one.  The two sides pinch.  This is the
> first place where a free inequality and the hypothesis constrain the same scalar, so the hypothesis
> is not measuring an invisible direction here — it is measuring the *defect* in an inequality that
> is already known to hold.**

The atlas's standing dichotomy — free tools measure area, the hypothesis constrains codimension — does
not apply to this pair.

This file formalizes the factorial identity, the window ratio and its width, the vanishing of the
width, and the free half: log-convexity of a moment sequence of a positive discrete measure, by
Cauchy–Schwarz.
-/

open Filter Topology Finset

noncomputable section

namespace RHTower

/-- **The factorial identity.**  `(n+3)(n+4)·((n+2)!)² = (n+1)(n+2)·n!·(n+4)!`. -/
theorem window_factorial (n : ℕ) :
    (n + 3) * (n + 4) * ((n + 2).factorial) ^ 2
      = (n + 1) * (n + 2) * n.factorial * (n + 4).factorial := by
  simp only [Nat.factorial_succ]
  ring

/-- The window ratio: the factor by which the hypothesis lowers the free upper bound. -/
def windowRatio (n : ℕ) : ℝ := ((n : ℝ) + 1) * ((n : ℝ) + 2) / (((n : ℝ) + 3) * ((n : ℝ) + 4))

theorem windowRatio_pos (n : ℕ) : 0 < windowRatio n := by
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  unfold windowRatio
  positivity

/-- **The window is nontrivial.**  The lower end is strictly below the free upper end. -/
theorem windowRatio_lt_one (n : ℕ) : windowRatio n < 1 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  unfold windowRatio
  rw [div_lt_one (by positivity)]
  nlinarith

/-- **The width.**  The relative width of the band is `(4n+10)/((n+1)(n+2))`. -/
theorem window_width (n : ℕ) :
    1 / windowRatio n - 1 = (4 * (n : ℝ) + 10) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  unfold windowRatio
  rw [one_div_div]
  field_simp
  ring

/-- **The band closes.**  The window ratio tends to one, so the two bounds pinch. -/
theorem windowRatio_tendsto_one : Tendsto windowRatio atTop (𝓝 1) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / ((n : ℝ) + 3)) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => (1 + 1 / (n : ℝ)) / (1 + 3 / (n : ℝ))) atTop (𝓝 1) := by
      have hz : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hcast
      have hz3 : Tendsto (fun n : ℕ => (3 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hcast
      have hnum : Tendsto (fun n : ℕ => 1 + (1 : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.add hz
      have hden : Tendsto (fun n : ℕ => 1 + (3 : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.add hz3
      have hdiv := hnum.div hden one_ne_zero
      rw [div_one] at hdiv
      refine hdiv.congr fun n => ?_
      simp only [Pi.div_apply]
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    field_simp
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 2) / ((n : ℝ) + 4)) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => (1 + 2 / (n : ℝ)) / (1 + 4 / (n : ℝ))) atTop (𝓝 1) := by
      have hz : Tendsto (fun n : ℕ => (2 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hcast
      have hz4 : Tendsto (fun n : ℕ => (4 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hcast
      have hnum : Tendsto (fun n : ℕ => 1 + (2 : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.add hz
      have hden : Tendsto (fun n : ℕ => 1 + (4 : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.add hz4
      have hdiv := hnum.div hden one_ne_zero
      rw [div_one] at hdiv
      refine hdiv.congr fun n => ?_
      simp only [Pi.div_apply]
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    field_simp
  have := h1.mul h2
  simp only [one_mul] at this
  refine this.congr fun n => ?_
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  unfold windowRatio
  field_simp

/-- **The free half.**  A moment sequence of a positive measure is log-convex: this is
Cauchy–Schwarz applied to `u^{j/2}` against `u^{(j+2)/2}` in the weighted space. -/
theorem moment_logConvex {ι : Type*} (s : Finset ι) (w u : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hu : ∀ i ∈ s, 0 ≤ u i) (j : ℕ) :
    (∑ i ∈ s, w i * u i ^ (j + 1)) ^ 2
      ≤ (∑ i ∈ s, w i * u i ^ j) * (∑ i ∈ s, w i * u i ^ (j + 2)) := by
  have key := Finset.sum_mul_sq_le_sq_mul_sq s
      (fun i => Real.sqrt (w i * u i ^ j)) (fun i => Real.sqrt (w i * u i ^ (j + 2)))
  have hcross : ∀ i ∈ s,
      Real.sqrt (w i * u i ^ j) * Real.sqrt (w i * u i ^ (j + 2)) = w i * u i ^ (j + 1) := by
    intro i hi
    have hwi := hw i hi
    have hui := hu i hi
    rw [← Real.sqrt_mul (by positivity)]
    have : w i * u i ^ j * (w i * u i ^ (j + 2)) = (w i * u i ^ (j + 1)) ^ 2 := by ring
    rw [this, Real.sqrt_sq (by positivity)]
  have hsq1 : ∀ i ∈ s, Real.sqrt (w i * u i ^ j) ^ 2 = w i * u i ^ j := by
    intro i hi
    exact Real.sq_sqrt (by have := hw i hi; have := hu i hi; positivity)
  have hsq2 : ∀ i ∈ s, Real.sqrt (w i * u i ^ (j + 2)) ^ 2 = w i * u i ^ (j + 2) := by
    intro i hi
    exact Real.sq_sqrt (by have := hw i hi; have := hu i hi; positivity)
  rw [Finset.sum_congr rfl hcross, Finset.sum_congr rfl hsq1,
    Finset.sum_congr rfl hsq2] at key
  exact key

/-- **The collision, stated.**  If the free bound holds with value `F` and the hypothesis demands the
lower bound `windowRatio n · F`, then the admissible set for the middle quantity is a genuine
interval, and its two ends approach each other. -/
theorem window_nonempty {F : ℝ} (hF : 0 < F) (n : ℕ) :
    windowRatio n * F < F := by
  have := windowRatio_lt_one n
  nlinarith

/-- The gap between the two bounds is the free value times the width, and it vanishes relatively. -/
theorem window_gap {F : ℝ} (n : ℕ) :
    F - windowRatio n * F = (1 - windowRatio n) * F := by ring

end RHTower

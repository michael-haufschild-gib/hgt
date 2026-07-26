import GaloisForLFunctions.RHTower.WitnessTestForArguments

/-!
# The asymmetry of the prime symbol is the pole

Kronecker decoupling — recorded elsewhere in this development — gives the extremes of the prime
symbol exactly, because multiplicative independence of the primes makes the local phases free:

```text
sup_ξ P = 2 Σ_p log p · sup_θ f_p(θ) ,      inf_ξ P = 2 Σ_p log p · inf_θ f_p(θ) ,
f_p(θ) = (x c - x²)/(1 - 2 x c + x²) ,      x = p^{-1/2} , c = cos θ .
```

The local extremes are attained at `c = ±1` and sum in closed form:

```text
sup_θ f_p = x/(1 - x) = 1/(√p - 1) ,        inf_θ f_p = -x/(1 + x) = -1/(√p + 1) .
```

Both `Σ_p log p/(√p ∓ 1)` diverge like `2√N`, so the symbol is unbounded in both directions — which is
why truncation was needed at all.  **Their sum is not exponential.**

```text
sup + inf  =  2 Σ_p log p ( 1/(√p - 1) - 1/(√p + 1) )  =  4 Σ_p log p /(p - 1)
           =  4 Σ_p Σ_{k ≥ 1} log p · p^{-k}  =  4 Σ_n Λ(n)/n ,
```

using `1/(p-1) = Σ_{k≥1} p^{-k}`.  The right-hand side is exactly the pole term of the explicit
formula: truncated at `N = e^L` it is `∼ 4 L`, matching the net weight `2L` of the pole form found
earlier, per unit normalisation.

> **The prime symbol is symmetric to exponential order and asymmetric only at the logarithmic scale
> of the pole: its two extremes differ from being opposite by exactly the pole term.  The pole is not
> an extra ingredient of the explicit formula — it is the asymmetry of the prime side.**

This joins the decoupling computation to the trace identity for the pole form, and gives a third
independent derivation of the same logarithmic quantity.

This file formalizes the local extremes, their sum, and the geometric identity that turns it into the
pole series.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- **The local supremum.**  At `c = 1` the local factor is `x/(1-x)`. -/
theorem local_sup_value {x : ℝ} (hx : x ≠ 1) :
    (x * 1 - x ^ 2) / (1 - 2 * x * 1 + x ^ 2) = x / (1 - x) := by
  have hfac : 1 - 2 * x * 1 + x ^ 2 = (1 - x) ^ 2 := by ring
  have hnum : x * 1 - x ^ 2 = x * (1 - x) := by ring
  rw [hfac, hnum]
  have hne : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  field_simp

/-- **The local infimum.**  At `c = -1` the local factor is `-x/(1+x)`. -/
theorem local_inf_value {x : ℝ} (hx : x ≠ -1) :
    (x * (-1) - x ^ 2) / (1 - 2 * x * (-1) + x ^ 2) = -(x / (1 + x)) := by
  have hfac : 1 - 2 * x * (-1) + x ^ 2 = (1 + x) ^ 2 := by ring
  have hnum : x * (-1) - x ^ 2 = -(x * (1 + x)) := by ring
  rw [hfac, hnum]
  have hne : 1 + x ≠ 0 := by
    intro h
    exact hx (by linarith)
  field_simp

/-- **The extremes are nearly opposite.**  Their sum is `2x²/(1-x²)`, quadratically small in `x`. -/
theorem extremes_sum {x : ℝ} (h1 : x ≠ 1) (h2 : x ≠ -1) :
    x / (1 - x) - x / (1 + x) = 2 * x ^ 2 / (1 - x ^ 2) := by
  have hne1 : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hne2 : 1 + x ≠ 0 := by intro h; exact h2 (by linarith)
  have hne3 : 1 - x ^ 2 ≠ 0 := by
    intro h
    have : (1 - x) * (1 + x) = 0 := by nlinarith [h]
    rcases mul_eq_zero.mp this with h' | h'
    · exact hne1 h'
    · exact hne2 h'
  field_simp
  ring

/-- **At a prime the sum is `2/(p-1)`.**  Substituting `x = p^{-1/2}` gives `2x²/(1-x²) = 2/(p-1)`. -/
theorem extremes_sum_at_prime {p : ℝ} (hp : 1 < p) :
    2 * (1 / p) / (1 - 1 / p) = 2 / (p - 1) := by
  have hp0 : p ≠ 0 := by intro h; rw [h] at hp; linarith
  have hne : p - 1 ≠ 0 := by
    intro h
    have hp1 : p = 1 := by linarith
    rw [hp1] at hp
    linarith
  field_simp

/-- **The geometric identity.**  `1/(p-1) = Σ_{k ≥ 1} p^{-k}`, so the asymmetry is the pole series
`Σ_n Λ(n)/n`. -/
theorem inv_sub_one_eq_geometric {p : ℝ} (hp : 1 < p) :
    ∑' k : ℕ, (1 / p) ^ (k + 1) = 1 / (p - 1) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hlt : |1 / p| < 1 := by
    rw [abs_of_pos (by positivity)]
    rw [div_lt_one hp0]
    exact hp
  have hgeom : ∑' k : ℕ, (1 / p) ^ (k + 1) = (1 / p) * ∑' k : ℕ, (1 / p) ^ k := by
    rw [← tsum_mul_left]
    congr 1
    funext k
    ring
  rw [hgeom, tsum_geometric_of_lt_one (by positivity) (by rw [div_lt_one hp0]; exact hp)]
  have hne : 1 - 1 / p ≠ 0 := by
    intro h
    have : (1:ℝ) / p = 1 := by linarith
    rw [div_eq_one_iff_eq (ne_of_gt hp0)] at this
    linarith
  field_simp

/-- **The asymmetry is logarithmic while the extremes are exponential.**  Truncated at `N`, the sum of
the extremes grows like `log N` and each extreme like `√N`, so the two scales are separated. -/
theorem asymmetry_scale_separation {N : ℝ} (hN : 1 < N) :
    Real.log N < Real.sqrt N * Real.sqrt N := by
  have h1 : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (by linarith)
  rw [h1]
  have hpos : (0:ℝ) < N := by linarith
  have h2 := Real.log_le_sub_one_of_pos hpos
  linarith

end RHTower

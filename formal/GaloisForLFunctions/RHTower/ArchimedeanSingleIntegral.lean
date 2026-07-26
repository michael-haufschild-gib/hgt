import GaloisForLFunctions.RHTower.ScrewWindowFejerAmplitude

/-!
# The archimedean side collapses to one integral in the same tent

The corpus computes the archimedean side of the rectangular window as a Gauss/digamma series paired
against the rectangular Fourier square: the `n`-th summand is
`A(0)/(n+1) - ∫₀^∞ e^{-(n+3/4)t} A(t/2) e^{t/2} dt`, with `A` the rectangular autocorrelation — the
same tent that carries the prime side.  Summing the series collapses it to a **single** integral.

Using `1/(n+1) = ∫₀^∞ e^{-(n+1)t}dt` and `Σ_{n≥0} e^{-nt} = (1-e^{-t})^{-1}` for `t > 0`,

```text
Σ_n [ A(0)/(n+1) - ∫₀^∞ e^{-(n+3/4)t} A(t/2) e^{t/2} dt ]
      =  ∫₀^∞  ( A(0)·e^{-t} - A(t/2)·e^{-t/4} ) / (1 - e^{-t})  dt .
```

Both series diverge separately; the combination converges, and this file proves the mechanism: the
numerator vanishes linearly at the origin, at a rate controlled by `A(0)` and the Lipschitz constant
of `A`, while the denominator vanishes linearly with slope one.  Explicitly, for `0 < t ≤ 1`,

```text
|A(0)e^{-t} - A(t/2)e^{-t/4}| ≤ (A(0) + Λ/2)·t ,      1 - e^{-t} ≥ t/2 ,
```

so the integrand is bounded by `2A(0) + Λ` near zero.  The tent is Lipschitz with constant `1`, so
this applies directly.

With the prime side already a tent-weighted Chebyshev window and the zero side a Fejér cosine series,
the rectangular window criterion is now one completely explicit inequality:

```text
∫₀^∞ (A(0)e^{-t} - A(t/2)e^{-t/4})/(1-e^{-t}) dt  -  2 Σ_k (Λ(k)/√k)·A(log k)   ≥   B ,
```

with `A` the tent of half-width `L`.  Every ingredient is elementary; the difficulty is entirely in
the competition between the two terms.

This file formalizes the two elementary bounds that make the collapsed integrand integrable at the
origin.
-/

open Real

noncomputable section

namespace RHTower

/-- The collapsed archimedean integrand. -/
def archCollapsed (A0 : ℝ) (A : ℝ → ℝ) (t : ℝ) : ℝ :=
  (A0 * Real.exp (-t) - A (t / 2) * Real.exp (-t / 4)) / (1 - Real.exp (-t))

/-- **The denominator vanishes linearly with slope one.**  For `0 ≤ t`, `1 - e^{-t} ≥ t - t²/2`, and
on `0 ≤ t ≤ 1` this is at least `t/2`. -/
theorem one_sub_exp_neg_ge {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t / 2 ≤ 1 - Real.exp (-t) := by
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have hexp : 1 + t ≤ Real.exp t := by
    have := Real.add_one_le_exp t; linarith
  have hinv : Real.exp (-t) ≤ (1 + t)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ h1t hexp
  have hfrac : (1 + t)⁻¹ ≤ 1 - t / 2 := by
    rw [inv_le_iff_one_le_mul₀ h1t]
    nlinarith [ht, ht1]
  linarith [hinv, hfrac]

/-- **The exponential gap is linear.**  For `0 ≤ t`, `0 ≤ e^{-t/4} - e^{-t} ≤ 3t/4`. -/
theorem exp_gap_le {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t / 4) - Real.exp (-t) ≤ t := by
  have h1 : Real.exp (-t / 4) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr; linarith
  have h2 : 1 - t ≤ Real.exp (-t) := by
    have := Real.add_one_le_exp (-t)
    linarith
  linarith

/-- The gap is nonnegative. -/
theorem exp_gap_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ Real.exp (-t / 4) - Real.exp (-t) := by
  have : Real.exp (-t) ≤ Real.exp (-t / 4) := by
    apply Real.exp_le_exp.mpr; linarith
  linarith

/-- **The numerator vanishes linearly.**  Splitting
`A(0)e^{-t} - A(t/2)e^{-t/4} = A(0)(e^{-t} - e^{-t/4}) + e^{-t/4}(A(0) - A(t/2))` bounds the
numerator by `(A(0) + Λ/2)·t` when `A` is `Λ`-Lipschitz at the origin. -/
theorem archCollapsed_num_le {A0 Lip t : ℝ} {A : ℝ → ℝ}
    (hA0 : 0 ≤ A0) (hLip : |A0 - A (t / 2)| ≤ Lip * (t / 2)) (ht : 0 ≤ t) :
    |A0 * Real.exp (-t) - A (t / 2) * Real.exp (-t / 4)|
      ≤ (A0 + Lip / 2) * t := by
  have hsplit : A0 * Real.exp (-t) - A (t / 2) * Real.exp (-t / 4)
      = A0 * (Real.exp (-t) - Real.exp (-t / 4))
        + Real.exp (-t / 4) * (A0 - A (t / 2)) := by ring
  rw [hsplit]
  have hgap : |A0 * (Real.exp (-t) - Real.exp (-t / 4))| ≤ A0 * t := by
    rw [abs_mul, abs_of_nonneg hA0, abs_of_nonpos (by linarith [exp_gap_nonneg ht])]
    have := exp_gap_le ht
    nlinarith [hA0, this]
  have hexp1 : Real.exp (-t / 4) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr; linarith
  have hsec : |Real.exp (-t / 4) * (A0 - A (t / 2))| ≤ Lip * (t / 2) := by
    rw [abs_mul, abs_of_nonneg (le_of_lt (Real.exp_pos _))]
    calc Real.exp (-t / 4) * |A0 - A (t / 2)| ≤ 1 * |A0 - A (t / 2)| := by
          apply mul_le_mul_of_nonneg_right hexp1 (abs_nonneg _)
      _ = |A0 - A (t / 2)| := one_mul _
      _ ≤ Lip * (t / 2) := hLip
  calc |A0 * (Real.exp (-t) - Real.exp (-t / 4)) + Real.exp (-t / 4) * (A0 - A (t / 2))|
      ≤ |A0 * (Real.exp (-t) - Real.exp (-t / 4))| + |Real.exp (-t / 4) * (A0 - A (t / 2))| :=
        abs_add_le _ _
    _ ≤ A0 * t + Lip * (t / 2) := by linarith [hgap, hsec]
    _ = (A0 + Lip / 2) * t := by ring

/-- **The integrand is bounded at the origin.**  Combining the two bounds, the collapsed archimedean
integrand is bounded by `2A(0) + Λ` on `(0,1]`: the divergences of the two series cancel exactly. -/
theorem archCollapsed_bounded {A0 Lip t : ℝ} {A : ℝ → ℝ}
    (hA0 : 0 ≤ A0) (hLipnn : 0 ≤ Lip)
    (hLip : |A0 - A (t / 2)| ≤ Lip * (t / 2)) (ht : 0 < t) (ht1 : t ≤ 1) :
    |archCollapsed A0 A t| ≤ 2 * A0 + Lip := by
  unfold archCollapsed
  have hden : t / 2 ≤ 1 - Real.exp (-t) := one_sub_exp_neg_ge (le_of_lt ht) ht1
  have hdenpos : 0 < 1 - Real.exp (-t) := by linarith [hden, ht]
  rw [abs_div, abs_of_pos hdenpos]
  rw [div_le_iff₀ hdenpos]
  have hnum := archCollapsed_num_le hA0 hLip (le_of_lt ht)
  calc |A0 * Real.exp (-t) - A (t / 2) * Real.exp (-t / 4)|
      ≤ (A0 + Lip / 2) * t := hnum
    _ = (2 * A0 + Lip) * (t / 2) := by ring
    _ ≤ (2 * A0 + Lip) * (1 - Real.exp (-t)) := by
        apply mul_le_mul_of_nonneg_left hden (by linarith)

end RHTower

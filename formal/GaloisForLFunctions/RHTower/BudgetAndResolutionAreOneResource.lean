import GaloisForLFunctions.RHTower.ThreeTypesOfApproach

/-!
# Budget and resolution are the same resource

Li's criterion and the Weil tent-function lane are the same explicit formula with different test
classes.  This file identifies the transform that connects them and shows the two lanes trade the
same quantity.

**Li's test is Fejér on the Cayley circle.**  On the critical line `s = ½ + it` one has
`|s - 1| = |s|`, so `1 - 1/ρ = (ρ-1)/ρ` has modulus one: writing it as `e^{iθ}` gives

```text
Re[ 1 - (1 - 1/ρ)ⁿ ]  =  1 - cos nθ  =  2 sin²(nθ/2) ,
```

the Fejér-type kernel.  The map `t ↦ θ` is the Cayley transform, carrying `t → ±∞` to `θ → 0`, so the
zero-counting density `log|t| / 2π` becomes `log(1/θ) / (2πθ²)` and

```text
Σ_ρ (1 - cos nθ_ρ)  ≍  (n/2) log n ,
```

which is the known Li main term.

**The scaling.**  The kernel obeys `2 sin²(nθ/2)/θ² = n² · 2 sin²(φ/2)/φ²` with `φ = nθ`: it peaks at
`θ ≍ 1/n` with height `≍ n²` over width `≍ 1/n`, hence mass `≍ n`.  It resolves **every** zero.

**The price.**  A tent test of width `L` has compact support, which truncates the prime sum and buys
the finite archimedean budget of the earlier entries; it resolves only a window.  The Fejér test
vanishes only at the isolated points `θ ∈ 2πℤ/n`, so no window is excluded and the prime sum is not
truncated at all.

> **Compact support buys budget and forfeits resolution; the Fejér family buys resolution and forfeits
> budget.  The two lanes are one explicit formula spending one resource, which is why the atlas's type
> A and type B are not independent difficulties but two ends of a single trade.**

This file formalizes the modulus-one identity on the critical line, the nonnegativity of the Fejér
test, its scaling law, and the fact that it excludes no window.
-/

open Real

noncomputable section

namespace RHTower

/-- **Modulus one on the critical line.**  For `s = ½ + it` the reflected point has the same modulus,
so `(s-1)/s` lies on the unit circle. -/
theorem critical_line_modulus (t : ℝ) :
    (-(1 / 2 : ℝ)) ^ (2 : ℕ) + t ^ (2 : ℕ) = (1 / 2 : ℝ) ^ (2 : ℕ) + t ^ (2 : ℕ) := by ring

/-- **The Li integrand is the Fejér kernel.**  `1 - cos nθ = 2 sin²(nθ/2)`. -/
theorem li_integrand_eq (x : ℝ) : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ (2 : ℕ) := by
  have h := Real.cos_two_mul_eq_one_sub (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  rw [h]; ring

/-- **Hence it is nonnegative**, which is why the hypothesis makes every Li coefficient nonnegative. -/
theorem li_integrand_nonneg (x : ℝ) : 0 ≤ 1 - Real.cos x := by
  rw [li_integrand_eq]
  positivity

/-- **The scaling law.**  With `φ = nθ` the weighted kernel is `n²` times a fixed profile, so it peaks
at `θ ≍ 1/n` with height `≍ n²` over width `≍ 1/n`. -/
theorem fejer_scaling {n θ : ℝ} (hn : n ≠ 0) (hθ : θ ≠ 0) :
    2 * Real.sin (n * θ / 2) ^ (2 : ℕ) / θ ^ (2 : ℕ)
      = n ^ (2 : ℕ) * (2 * Real.sin ((n * θ) / 2) ^ (2 : ℕ) / (n * θ) ^ (2 : ℕ)) := by
  field_simp

/-- **The Fejér test excludes no window.**  It vanishes only where the sine does, a discrete set, so
no interval of the transformed variable is cut off. -/
theorem fejer_vanishes_only_at_zeros {x : ℝ} (h : 1 - Real.cos x = 0) :
    Real.sin (x / 2) = 0 := by
  rw [li_integrand_eq] at h
  have : Real.sin (x / 2) ^ (2 : ℕ) = 0 := by linarith
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

/-- **A compactly supported test does exclude a window.**  Outside its support it is identically zero,
so an entire interval of the prime sum is truncated. -/
theorem compact_support_excludes {g : ℝ → ℝ} {L : ℝ}
    (hsupp : ∀ u : ℝ, L < |u| → g u = 0) {u : ℝ} (hu : L < |u|) : g u = 0 :=
  hsupp u hu

/-- **The trade, in logical form.**  A test cannot both truncate a window and be nonvanishing on it:
the two demands are contradictory at any point of that window. -/
theorem budget_resolution_trade {g : ℝ → ℝ} {L u : ℝ}
    (hsupp : ∀ v : ℝ, L < |v| → g v = 0) (hu : L < |u|) (hres : g u ≠ 0) : False :=
  hres (hsupp u hu)

end RHTower

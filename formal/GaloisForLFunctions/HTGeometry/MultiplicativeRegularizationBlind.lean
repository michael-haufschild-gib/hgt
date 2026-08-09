import Mathlib

/-!
# A convergent multiplicative regularization sees only the leading asymptotic

Let a divergent quantity have the expansion

```text
f L  =  A · L^{k+1}  +  B · L^k  +  r L ,        r L / L^k → 0 ,
```

and regularize it multiplicatively, `f L ↦ c L · f L`.  If the normalizer is chosen so that
`c L · L^{k+1}` converges — which is forced if `c L · f L` is to converge to a nonzero limit, since
the leading term must be exactly compensated — then

```text
c L · f L  →  A · δ ,        δ = lim c L · L^{k+1} .
```

**The subleading coefficient `B` never appears in the limit, and neither does the remainder.**  So a
multiplicative regularization that converges is determined by the leading asymptotic alone.

This is the mechanism behind an obstruction that shows up repeatedly in Hankel-type prime-side Grams.
There the entries are `∑_{n≤N} w(n)·log^{i+j} n` with `∑_{n≤N} w(n) = log N + O(1)`, so
`A_{i+j} = 1/(i+j+1)` and the arithmetic lives entirely in `B` and beyond.  Any multiplicative
normalization that renders the Gram finite therefore returns the same arithmetic-free limit — for the
Mertens weight, the Hilbert matrix — regardless of which normalizer is used and regardless of whether
it preserves positivity.  Retaining the arithmetic requires a *subtractive* regularization, which is
exactly the operation that does not inherit positivity from the finite apertures.
-/

open Filter Topology

namespace GaloisForLFunctions

namespace MultiplicativeRegularization

/-- **A convergent multiplicative regularization is blind to everything below the leading term.**
The limit is `A · δ`, with no dependence on the subleading coefficient `B` or on the remainder. -/
theorem tendsto_mul_regularized {k : ℕ} (A B δ : ℝ) (c r : ℝ → ℝ)
    (hr : Tendsto (fun L : ℝ => r L / L ^ k) atTop (𝓝 0))
    (hc : Tendsto (fun L : ℝ => c L * L ^ (k + 1)) atTop (𝓝 δ)) :
    Tendsto (fun L : ℝ => c L * (A * L ^ (k + 1) + B * L ^ k + r L)) atTop (𝓝 (A * δ)) := by
  have hinv : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  -- leading term
  have h1 : Tendsto (fun L : ℝ => c L * (A * L ^ (k + 1))) atTop (𝓝 (A * δ)) := by
    have := hc.const_mul A
    refine this.congr fun L => ?_
    ring
  -- subleading term
  have h2 : Tendsto (fun L : ℝ => c L * (B * L ^ k)) atTop (𝓝 0) := by
    have hprod : Tendsto (fun L : ℝ => (c L * L ^ (k + 1)) * (B * L⁻¹)) atTop (𝓝 (δ * (B * 0))) :=
      hc.mul (hinv.const_mul B)
    rw [mul_zero, mul_zero] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    field_simp
    ring
  -- remainder
  have h3 : Tendsto (fun L : ℝ => c L * r L) atTop (𝓝 0) := by
    have hprod : Tendsto
        (fun L : ℝ => (c L * L ^ (k + 1)) * ((r L / L ^ k) * L⁻¹)) atTop (𝓝 (δ * (0 * 0))) :=
      hc.mul (hr.mul hinv)
    rw [mul_zero, mul_zero] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    have hLk : (L : ℝ) ^ k ≠ 0 := by positivity
    field_simp
    ring
  have hsum := (h1.add h2).add h3
  rw [add_zero, add_zero] at hsum
  refine hsum.congr fun L => ?_
  ring

/-- **Independence of the subleading data, stated as such.**  Two expansions with the same leading
coefficient and any subleading coefficients give the same regularized limit. -/
theorem mul_regularized_indep_subleading {k : ℕ} (A B B' δ : ℝ) (c r r' : ℝ → ℝ)
    (hr : Tendsto (fun L : ℝ => r L / L ^ k) atTop (𝓝 0))
    (hr' : Tendsto (fun L : ℝ => r' L / L ^ k) atTop (𝓝 0))
    (hc : Tendsto (fun L : ℝ => c L * L ^ (k + 1)) atTop (𝓝 δ)) :
    Tendsto (fun L : ℝ => c L * (A * L ^ (k + 1) + B * L ^ k + r L)) atTop (𝓝 (A * δ))
      ∧ Tendsto (fun L : ℝ => c L * (A * L ^ (k + 1) + B' * L ^ k + r' L)) atTop (𝓝 (A * δ)) :=
  ⟨tendsto_mul_regularized A B δ c r hr hc, tendsto_mul_regularized A B' δ c r' hr' hc⟩

end MultiplicativeRegularization

end GaloisForLFunctions

namespace GaloisForLFunctions

namespace MultiplicativeRegularization

/-- **The compensation is forced.**  If the regularized product converges and the leading
coefficient is nonzero, then the normalizer's leading compensation converges — to the limit
divided by the leading coefficient.  No compensation hypothesis is assumed; it is derived. -/
theorem tendsto_normalizer_of_tendsto_mul_regularized {k : ℕ} (A B ℓ : ℝ) (c r : ℝ → ℝ)
    (hA : A ≠ 0)
    (hr : Tendsto (fun L : ℝ => r L / L ^ k) atTop (𝓝 0))
    (hcH : Tendsto (fun L : ℝ => c L * (A * L ^ (k + 1) + B * L ^ k + r L)) atTop (𝓝 ℓ)) :
    Tendsto (fun L : ℝ => c L * L ^ (k + 1)) atTop (𝓝 (ℓ / A)) := by
  have hinv : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hshape :
      Tendsto (fun L : ℝ => (A * L ^ (k + 1) + B * L ^ k + r L) / L ^ (k + 1)) atTop (𝓝 A) := by
    have hsum :
        Tendsto (fun L : ℝ => A + B * L⁻¹ + (r L / L ^ k) * L⁻¹) atTop
          (𝓝 (A + B * 0 + 0 * 0)) :=
      ((tendsto_const_nhds.add (hinv.const_mul B)).add (hr.mul hinv))
    rw [mul_zero, add_zero, zero_mul, add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    have hLk : (L : ℝ) ^ k ≠ 0 := by positivity
    have hLk1 : (L : ℝ) ^ (k + 1) ≠ 0 := by positivity
    field_simp
    ring
  have hshape_ne : ∀ᶠ L : ℝ in atTop,
      (A * L ^ (k + 1) + B * L ^ k + r L) / L ^ (k + 1) ≠ 0 :=
    hshape.eventually_ne hA
  have hquot :
      Tendsto (fun L : ℝ =>
        (c L * (A * L ^ (k + 1) + B * L ^ k + r L)) *
          ((A * L ^ (k + 1) + B * L ^ k + r L) / L ^ (k + 1))⁻¹) atTop (𝓝 (ℓ * A⁻¹)) :=
    hcH.mul (hshape.inv₀ hA)
  rw [div_eq_mul_inv]
  refine hquot.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ), hshape_ne] with L hL hne
  have hLk1 : (L : ℝ) ^ (k + 1) ≠ 0 := by positivity
  have hH : A * L ^ (k + 1) + B * L ^ k + r L ≠ 0 := by
    intro h0
    exact hne (by rw [h0, zero_div])
  field_simp

/-- **Cross-system blindness, derived form.**  Two expansions with the same nonzero leading
coefficient and one common normalizer have identical regularized limits as soon as one of them
converges: the compensation extracted from the first forces the second's limit.  This is the
abstract engine behind the Beurling cross-system blindness of multiplicative regularization. -/
theorem tendsto_mul_regularized_cross_system {k : ℕ} (A B B' ℓ : ℝ) (c r r' : ℝ → ℝ)
    (hA : A ≠ 0)
    (hr : Tendsto (fun L : ℝ => r L / L ^ k) atTop (𝓝 0))
    (hr' : Tendsto (fun L : ℝ => r' L / L ^ k) atTop (𝓝 0))
    (hcH : Tendsto (fun L : ℝ => c L * (A * L ^ (k + 1) + B * L ^ k + r L)) atTop (𝓝 ℓ)) :
    Tendsto (fun L : ℝ => c L * (A * L ^ (k + 1) + B' * L ^ k + r' L)) atTop (𝓝 ℓ) := by
  have hδ := tendsto_normalizer_of_tendsto_mul_regularized A B ℓ c r hA hr hcH
  have h := tendsto_mul_regularized A B' (ℓ / A) c r' hr' hδ
  rwa [mul_div_cancel₀ ℓ hA] at h

end MultiplicativeRegularization

end GaloisForLFunctions

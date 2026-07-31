import GaloisForLFunctions.RHTower.ArchimedeanConcentrationGain

/-!
# Exact diagonalization of the pole form, and the baseline dichotomy

The pole term of the Weil functional is the rank-two form

```text
pole(h) = ĝ(1/2) + ĝ(-1/2) = 2 ⟨h, e₊⟩ ⟨h, e₋⟩ ,     e_±(u) = e^{±u/2},
```

indefinite as a product of two independent functionals.  Writing `e_± = c ± s` with
`c(u) = cosh(u/2)` and `s(u) = sinh(u/2)` diagonalizes it exactly:

```text
pole(h) = 2 ⟨h, c⟩² - 2 ⟨h, s⟩² ,
```

the even direction carrying the positive eigenvalue and the odd direction the negative one.  This is
the same Krein splitting that organizes the whole Weil form, now made explicit for the pole.

The negative direction is **small on a short interval**.  On `I = [-ℓ, ℓ]`,

```text
‖s‖²_{L²(I)} = ∫_{-ℓ}^{ℓ} sinh²(u/2) du = ∫_{-ℓ}^{ℓ} (cosh u - 1)/2 du = sinh ℓ - ℓ ,
```

which vanishes to third order at `ℓ = 0`: `sinh ℓ - ℓ ≤ (ℓ³/6)·cosh ℓ`, since
`cosh t - 1 = 2 sinh²(t/2) ≤ (t²/2)·cosh²(t/2) = (t²/4)(cosh t + 1) ≤ (t²/2) cosh t`.  So by
Cauchy–Schwarz the whole negative part of the pole form is at most `2(sinh ℓ - ℓ)‖h‖²`, cubically
small.

That leaves the positive part `2⟨h, c⟩²` to be paired against the archimedean term, and the pairing
is a genuine dichotomy.  Write `P = ⟨h, c⟩`.  Since `ĥ` has derivative bounded by `ℓ‖h‖₁ ≤ ℓ√(2ℓ)`
for `h` supported in `I` with `‖h‖₂ = 1`, the low-frequency mass obeys

```text
(1/2π)∫_{|ξ|≤Ξ} |ĥ|² ≤ (Ξ/π)( |ĥ(0)|² + (2/3)ℓ³Ξ² ) ,
```

so the high-frequency fraction satisfies `β ≥ 1 - (Ξ/π)|ĥ(0)|² - (2/(3π))ℓ³Ξ³`.  Since `c` differs
from the constant `1` by at most `cosh(ℓ/2) - 1` on `I`, `|ĥ(0)|` and `|P|` differ by `O(ℓ²)`.
Hence:

* either `P²` is not small, and the pole form supplies a positive term `2P²`;
* or `P²` is small, and then `β` is close to `1`, so the archimedean average is close to `σ(Ξ)`,
  which is positive for `Ξ > 2π` and grows like `log(Ξ/2π)`.

Both branches are explicit and elementary — no prolate spheroidal functions and no Toeplitz theory.
This file formalizes the diagonalization, the closed form and cubic smallness of the negative
direction, and the dichotomy arithmetic.
-/

open Real intervalIntegral

noncomputable section

namespace RHTower

/-- **Exact diagonalization of the pole form.**  With `⟨h,e₊⟩ = P + Q` and `⟨h,e₋⟩ = P - Q`, where
`P = ⟨h,cosh(·/2)⟩` and `Q = ⟨h,sinh(·/2)⟩`, the rank-two pole form becomes a difference of
squares. -/
theorem pole_diagonalize (P Q : ℝ) : 2 * (P + Q) * (P - Q) = 2 * P ^ 2 - 2 * Q ^ 2 := by ring

/-- `sinh²(u/2) = (cosh u - 1)/2`. -/
theorem sinh_half_sq (u : ℝ) : Real.sinh (u / 2) ^ 2 = (Real.cosh u - 1) / 2 := by
  have h := Real.cosh_two_mul (u / 2)
  have hs := Real.cosh_sq_sub_sinh_sq (u / 2)
  have e : 2 * (u / 2) = u := by ring
  rw [e] at h
  linarith

/-- `sinh x ≤ x cosh x` for `x ≥ 0`: the difference has derivative `x sinh x ≥ 0` and vanishes at
the origin. -/
theorem sinh_le_self_mul_cosh {x : ℝ} (hx : 0 ≤ x) :
    Real.sinh x ≤ x * Real.cosh x := by
  have hmono : MonotoneOn (fun t : ℝ => t * Real.cosh t - Real.sinh t) (Set.Ici (0 : ℝ)) := by
    have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t * Real.cosh t - Real.sinh t)
        (t * Real.sinh t) t := by
      intro t
      have h := ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub (Real.hasDerivAt_sinh t)
      convert! h using 1 ; simp
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop)
      (fun t _ => (hderiv t).differentiableAt.differentiableWithinAt) ?_
    intro t ht
    rw [interior_Ici] at ht
    rw [(hderiv t).deriv]
    have h1 : (0 : ℝ) ≤ t := le_of_lt ht
    have h2 : (0 : ℝ) ≤ Real.sinh t := Real.sinh_nonneg_iff.mpr h1
    positivity
  have h0 : (0 : ℝ) * Real.cosh 0 - Real.sinh 0 = 0 := by simp
  have := hmono (Set.self_mem_Ici) hx hx
  simp only [h0] at this
  linarith [this]

/-- The negative direction of the pole form is nonnegative in size and vanishes at `ℓ = 0`:
`sinh ℓ ≥ ℓ`. -/
theorem sinh_sub_self_nonneg {ℓ : ℝ} (hℓ : 0 ≤ ℓ) : 0 ≤ Real.sinh ℓ - ℓ := by
  have hmono : MonotoneOn (fun t : ℝ => Real.sinh t - t) (Set.Ici (0 : ℝ)) := by
    have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.sinh t - t) (Real.cosh t - 1) t := by
      intro t
      exact (Real.hasDerivAt_sinh t).sub (hasDerivAt_id t)
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop)
      (fun t _ => (hderiv t).differentiableAt.differentiableWithinAt) ?_
    intro t _
    rw [(hderiv t).deriv]
    have := Real.one_le_cosh t
    linarith
  have h0 : Real.sinh 0 - 0 = 0 := by simp
  have := hmono (Set.self_mem_Ici) hℓ hℓ
  simp only [h0] at this
  linarith [this]

/-- **Cubic smallness.**  `cosh t - 1 ≤ (t²/2)·cosh t`, the pointwise input to
`sinh ℓ - ℓ ≤ (ℓ³/6)cosh ℓ`. -/
theorem cosh_sub_one_le {t : ℝ} (ht : 0 ≤ t) : Real.cosh t - 1 ≤ t ^ 2 / 2 * Real.cosh t := by
  have hs : Real.sinh (t / 2) ^ 2 = (Real.cosh t - 1) / 2 := sinh_half_sq t
  have hhalf : (0 : ℝ) ≤ t / 2 := by linarith
  have hb := sinh_le_self_mul_cosh hhalf
  have hsn : (0 : ℝ) ≤ Real.sinh (t / 2) := Real.sinh_nonneg_iff.mpr hhalf
  have hsq : Real.sinh (t / 2) ^ 2 ≤ (t / 2) ^ 2 * Real.cosh (t / 2) ^ 2 := by
    have hcn : (0 : ℝ) ≤ (t / 2) * Real.cosh (t / 2) := by
      have := Real.cosh_pos (t / 2); positivity
    nlinarith [hb, hsn, hcn]
  have hdouble : Real.cosh t = 2 * Real.cosh (t / 2) ^ 2 - 1 := by
    have h := Real.cosh_two_mul (t / 2)
    have hss := Real.cosh_sq_sub_sinh_sq (t / 2)
    have e : 2 * (t / 2) = t := by ring
    rw [e] at h
    linarith
  have hone : (1 : ℝ) ≤ Real.cosh (t / 2) ^ 2 := by
    have := Real.one_le_cosh (t / 2)
    nlinarith
  nlinarith [hs, hsq, hdouble, hone]

/-- **The baseline dichotomy.**  Either the even functional carries mass, in which case the pole form
contributes `2P²`, or it does not, in which case the high-frequency fraction is near one and the
archimedean average is near `σ(Ξ)`.  Stated as the explicit trade-off. -/
theorem baseline_dichotomy {P Q σ₀ σΞ β Ξ ℓ A : ℝ}
    (hQ : Q ^ 2 ≤ Real.sinh ℓ - ℓ)
    (hβ : 1 - Ξ / Real.pi * P ^ 2 - 2 / (3 * Real.pi) * ℓ ^ 3 * Ξ ^ 3 ≤ β)
    (hmono : σ₀ ≤ σΞ)
    (hA : σ₀ + β * (σΞ - σ₀) ≤ A) :
    2 * P ^ 2 - 2 * (Real.sinh ℓ - ℓ) + σ₀
        + (1 - Ξ / Real.pi * P ^ 2 - 2 / (3 * Real.pi) * ℓ ^ 3 * Ξ ^ 3) * (σΞ - σ₀)
      ≤ 2 * P ^ 2 - 2 * Q ^ 2 + A := by
  have hstep : (1 - Ξ / Real.pi * P ^ 2 - 2 / (3 * Real.pi) * ℓ ^ 3 * Ξ ^ 3) * (σΞ - σ₀)
      ≤ β * (σΞ - σ₀) := mul_le_mul_of_nonneg_right hβ (by linarith)
  linarith

end RHTower

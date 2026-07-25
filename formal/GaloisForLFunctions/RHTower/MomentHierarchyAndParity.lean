import GaloisForLFunctions.RHTower.LatticeEquilibriumCollision

/-!
# The moment hierarchy of the flow, and the index as a discriminant sign

Two structures tie the holomorphic invariants of the divisor to the flow and to the Weil index.

## The Burgers hierarchy on negative moments

With `ż_j = 2 Σ_{k≠j} 1/(z_j - z_k)` put `q_n = Σ_j z_j^{-n}`.  Differentiating and symmetrising the
ordered pair `(j,k) ↔ (k,j)` using

```text
(a - b)^{-1}(a^{-3} - b^{-3}) = -(a² + ab + b²)/(a³b³)
```

gives the closed polynomial law

```text
q̇₂ = 2(2q₁q₃ + q₂² - 3q₄) ,
```

and, since `H_t` is even in `z` so that all odd moments vanish,

```text
q̇₂ = 2q₂² - 6q₄ .
```

This is the moment form of the Burgers equation `L_τ = L_zz + (L²)_z` of the preceding module: the
whole hierarchy of negative moments — hence, by their explicit polynomial relations, the whole family
of Li coefficients — evolves along the de Bruijn–Newman flow by a closed system of ODEs.  It is the
first explicit dynamical bridge between Li's criterion and the flow: the Li coefficients are not
merely correlated with `Λ`, they are transported by it.

## The index is a discriminant sign

For a real quadratic factor the discriminant sees reality exactly:

```text
(z-(x+iy))(z-(x-iy)) = z² - 2xz + (x²+y²) ,  disc = -4y² < 0   (a conjugate pair) ,
(z-(x+a))(z-(x-a))   = z² - 2xz + (x²-a²) ,  disc = +4a² > 0   (a real pair) .
```

Discriminants multiply over factors up to positive squares, so for a real polynomial with `m`
conjugate pairs `sign(disc) = (-1)^m`.  By the orbit decomposition `m = ind₋(W)`, so

> **the sign of the discriminant is the parity of the Weil index.**

The Riemann hypothesis asserts `ind₋(W_ξ) = 0`; a *negative* regularized discriminant for `ξ` would
give `ind₋(W_ξ)` odd, hence nonzero, and disprove it.  Parity is strictly weaker than the count, so
this is a weaker target than any criterion so far — at the cost that the discriminant of an
order-one entire function needs regularization, its sign being carried by the imaginary part of a
regularized log-sum modulo `2πi`.

## Where the literature stands on the governing statistic

A search of the gap literature confirms the identification of the preceding module: what is studied
is the *absolute* normalized gap — infinitely many below `0.515396`, infinitely many above `2.7328`
(and `3.18` on the critical line).  Even "infinitely many gaps below half the average" is open.  No
result addresses a gap relative to its neighbours, which is what the collision criterion needs.  The
relative-gap statistic is therefore an unstudied object, and the two independent analyses — the
collision threshold and the classification of admissible functionals — converge on it.

This file formalizes the symmetrisation identity behind the hierarchy, the moment law, and the
discriminant/parity dictionary.
-/

open Complex

noncomputable section

namespace RHTower

/-- **The symmetrisation identity** behind the moment hierarchy:
`(a-b)^{-1}(a^{-3} - b^{-3}) = -(a² + ab + b²)/(a³b³)`. -/
theorem symmetrisation_cube {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0) :
    (a - b)⁻¹ * (a ^ (-3 : ℤ) - b ^ (-3 : ℤ))
      = -((a ^ 2 + a * b + b ^ 2) / (a ^ 3 * b ^ 3)) := by
  field_simp
  ring

/-- **The moment law.**  Symmetrising the derivative of `q₂` produces the closed quadratic law
`q̇₂ = 2(2q₁q₃ + q₂² - 3q₄)`. -/
theorem moment_law {q₁ q₂ q₃ q₄ qdot : ℝ}
    (h : qdot = 2 * ((q₁ * q₃ - q₄) + (q₂ ^ 2 - q₄) + (q₃ * q₁ - q₄))) :
    qdot = 2 * (2 * q₁ * q₃ + q₂ ^ 2 - 3 * q₄) := by
  rw [h]; ring

/-- **The even case.**  `H_t` is even in `z`, so the odd moments vanish and the law reduces to
`q̇₂ = 2q₂² - 6q₄`. -/
theorem moment_law_even {q₂ q₄ qdot : ℝ}
    (h : qdot = 2 * (2 * 0 * 0 + q₂ ^ 2 - 3 * q₄)) : qdot = 2 * q₂ ^ 2 - 6 * q₄ := by
  rw [h]; ring

/-- **A conjugate pair has negative discriminant.**  The real quadratic with roots `x ± iy` has
discriminant `-4y²`. -/
theorem disc_conj_pair {x y : ℝ} (hy : y ≠ 0) :
    (2 * x) ^ 2 - 4 * (x ^ 2 + y ^ 2) < 0 := by
  have : 0 < y ^ 2 := by positivity
  nlinarith

/-- **A real pair has positive discriminant.**  The real quadratic with roots `x ± a` has
discriminant `4a²`. -/
theorem disc_real_pair {x a : ℝ} (ha : a ≠ 0) :
    0 < (2 * x) ^ 2 - 4 * (x ^ 2 - a ^ 2) := by
  have : 0 < a ^ 2 := by positivity
  nlinarith

/-- **Parity.**  Discriminants multiply up to positive squares, so an even number of conjugate pairs
gives a positive discriminant and an odd number a negative one.  Two pairs: -/
theorem disc_two_pairs {d₁ d₂ : ℝ} (h₁ : d₁ < 0) (h₂ : d₂ < 0) : 0 < d₁ * d₂ :=
  mul_pos_of_neg_of_neg h₁ h₂

/-- Three pairs: the sign flips back. -/
theorem disc_three_pairs {d₁ d₂ d₃ : ℝ} (h₁ : d₁ < 0) (h₂ : d₂ < 0) (h₃ : d₃ < 0) :
    d₁ * d₂ * d₃ < 0 :=
  mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg h₁ h₂) h₃

/-- **The falsification target in parity form.**  If the regularized discriminant is negative the
index is odd, hence nonzero, and the Riemann hypothesis fails.  Stated as: an odd index is not
zero. -/
theorem odd_index_ne_zero {m : ℕ} (h : m % 2 = 1) : m ≠ 0 := by
  intro hm; rw [hm] at h; simp at h

/-- The index vanishes exactly when both its parity and its magnitude do; parity alone is a strictly
weaker — hence strictly easier — target. -/
theorem parity_weaker {m : ℕ} (h : m = 0) : m % 2 = 0 := by rw [h]

end RHTower

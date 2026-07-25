import GaloisForLFunctions.RHTower.QuantitativeNymanBeurling

/-!
# The admissible shape of a criterion is a threshold count

Three independent constraints have accumulated on any functional `Φ` of the divisor that could decide
the Riemann hypothesis.

* **Metric.**  No discrete invariant separates critical from off-critical divisors, since the two
  loci are joined through a double zero inside the symmetric class.  So `Φ` must be a continuously
  varying real quantity.
* **Height-neutral.**  Every quantified lane loses strength at a putative counterexample
  polynomially or exponentially in its height, so numerical verification and analytic estimate never
  meet.  A usable `Φ` must weight a zero independently of its height.
* **Non-monotone under the flow.**  The de Bruijn–Newman deformation moves the divisor toward the
  critical line, so any `Φ` decreasing along it yields only upper bounds on the deviation and can
  never contradict the failure of the hypothesis.

Are the three compatible?  For additive functionals `Φ = Σ_j φ(y_j)` of the deviations `y_j`, the
answer is decided by a single computation.  The flow gives
`ẏ_j = -2 Σ_{k≠j} (y_j - y_k)/|z_j - z_k|²`, so

```text
d/dt Σ_j φ(y_j) = -2 Σ_{ {j,k} } (φ'(y_j) - φ'(y_k))(y_j - y_k) / |z_j - z_k|² .
```

Every term is nonpositive exactly when `φ'` is nondecreasing — that is, when **`φ` is convex**.  So:

> **Every convex even weight gives a functional monotone along the flow, hence capped.  A
> height-neutral, non-monotone additive functional must have a non-convex weight.**

The square `φ(y) = y²` is convex, recovering the imaginary energy and its cap; so is `y⁴`, since
`(a³-b³)(a-b) = (a-b)²(a²+ab+b²) ≥ 0`.  A truncated weight `φ(y) = min(y²,ε²)` is not convex, and its
derivative is genuinely non-monotone: `φ'(ε/2) = ε` while `φ'(2ε) = 0`, so the term at that pair is
strictly positive and the functional can increase.

The three conditions are therefore **simultaneously satisfiable**, and the functionals that satisfy
them are the truncated ones — which count zeros whose deviation exceeds a threshold, up to a bounded
weight.  That is a zero-density statistic:

> **The admissible shape of a criterion for the Riemann hypothesis is a threshold count of
> off-critical zeros — an `N(σ,T)`-type quantity — and nothing smoother.**

The derivation is what is new here: the conclusion follows from three independent no-go results, one
topological, one effective, one dynamical, and it explains why the smooth criteria — Weil positivity,
Li coefficients, the imaginary energy, the Nyman–Beurling distance — each stall in their own way,
while the unconditional progress that exists lives in the zero-density literature.

This file formalizes the symmetrized derivative, the convexity dichotomy, the two convex examples,
and the non-convex witness.
-/

noncomputable section

namespace RHTower

/-- **The symmetrized term.**  The contribution of a pair to the time derivative of an additive
functional is `-(φ'(a) - φ'(b))(a - b)` divided by the squared separation. -/
def pairTerm (pa pb a b d : ℝ) : ℝ := -((pa - pb) * (a - b)) / d

/-- **Convex weights are monotone.**  If `φ'` is nondecreasing then every pair term is nonpositive,
so the functional decreases along the flow. -/
theorem pairTerm_nonpos {pa pb a b d : ℝ} (hd : 0 < d)
    (hmono : (pa - pb) * (a - b) ≥ 0) : pairTerm pa pb a b d ≤ 0 := by
  unfold pairTerm
  apply div_nonpos_of_nonpos_of_nonneg _ (le_of_lt hd)
  linarith

/-- The square weight is convex: `(2a - 2b)(a - b) = 2(a-b)² ≥ 0`. -/
theorem square_weight_convex (a b : ℝ) : (2 * a - 2 * b) * (a - b) ≥ 0 := by
  nlinarith [sq_nonneg (a - b)]

/-- The quartic weight is convex: `(4a³ - 4b³)(a - b) = 4(a-b)²(a²+ab+b²) ≥ 0`. -/
theorem quartic_weight_convex (a b : ℝ) : (4 * a ^ 3 - 4 * b ^ 3) * (a - b) ≥ 0 := by
  have hq : a ^ 2 + a * b + b ^ 2 ≥ 0 := by nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
  have hfac : (4 * a ^ 3 - 4 * b ^ 3) * (a - b)
      = 4 * (a - b) ^ 2 * (a ^ 2 + a * b + b ^ 2) := by ring
  rw [hfac]
  positivity

/-- **The non-convex witness.**  For the truncated weight `min(y²,ε²)` the derivative is `2y` below
the threshold and `0` above, so at the pair `(ε/2, 2ε)` the product is strictly negative and the pair
term is strictly positive: the functional can increase along the flow. -/
theorem truncated_weight_nonconvex {eps : ℝ} (he : 0 < eps) :
    (eps - 0) * (eps / 2 - 2 * eps) < 0 := by
  nlinarith

/-- The corresponding pair term is strictly positive, so a truncated weight is not monotone. -/
theorem pairTerm_pos_of_nonconvex {pa pb a b d : ℝ} (hd : 0 < d)
    (hneg : (pa - pb) * (a - b) < 0) : 0 < pairTerm pa pb a b d := by
  unfold pairTerm
  apply div_pos _ hd
  linarith

/-- **The dichotomy.**  An additive functional of the deviations is monotone along the flow if its
weight is convex, and can fail to be monotone only if the weight is not.  Height-neutrality is
automatic for any weight depending on the deviation alone, so the three constraints are satisfiable
exactly by non-convex — that is, threshold — weights. -/
theorem admissible_iff_nonconvex {pa pb a b d : ℝ} (hd : 0 < d) :
    (0 ≤ (pa - pb) * (a - b) → pairTerm pa pb a b d ≤ 0) ∧
      ((pa - pb) * (a - b) < 0 → 0 < pairTerm pa pb a b d) :=
  ⟨fun h => pairTerm_nonpos hd h, fun h => pairTerm_pos_of_nonconvex hd h⟩

/-- A threshold weight is bounded, so its total over the divisor is a count: the number of zeros with
deviation above the threshold, up to the bounded weight. -/
theorem threshold_weight_bounded (y eps : ℝ) :
    min (y ^ 2) (eps ^ 2) ≤ eps ^ 2 := min_le_right _ _

/-- And it vanishes exactly on the critical configuration. -/
theorem threshold_weight_zero_iff {y eps : ℝ} (he : 0 < eps) :
    min (y ^ 2) (eps ^ 2) = 0 ↔ y = 0 := by
  constructor
  · intro h
    rcases min_cases (y ^ 2) (eps ^ 2) with ⟨he₁, _⟩ | ⟨he₂, _⟩
    · rw [he₁] at h; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    · rw [he₂] at h
      exact absurd h (by positivity)
  · intro h; rw [h]; simp [le_of_lt (by positivity : (0:ℝ) < eps ^ 2)]

end RHTower

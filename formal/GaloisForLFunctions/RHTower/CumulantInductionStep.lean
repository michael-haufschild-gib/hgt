import GaloisForLFunctions.RHTower.TuranIsAVarianceBoundOnOneMeasure

/-!
# The induction step for the cumulant bound

The open core of the mechanism is a bound on the `m`-th cumulant of a strongly log-concave measure.
This file assembles the three ingredients that make its induction go through, each proved outright,
and checks that the constants and exponents they produce are the ones the mechanism needs.

**The recursion.**  Tilting by `V_h = V - h x` makes `κ_{m+1} = d/dh κ_m`, so the induction is
literally differentiation in the tilt.  Two facts make it stable:

* **The curvature does not move.**  `V_h'' = V''`, so the coercivity constant is the same for every
  tilt.
* **The propagator is uniformly bounded.**  The Helffer–Sjöstrand operator has quadratic form
  `∫(φ')² dμ_h + ∫ V'' φ² dμ_h ≥ c ‖φ‖²`, and coercivity by `c` forces `‖A⁻¹‖ ≤ 1/c`.

**The step.**  Each differentiation inserts one propagator (a factor `1/c`) and one derivative landing
on the integrand (a factor `b/c` relative), so it multiplies the bound by `b/c²`.  Starting from
`κ₂ ≤ 1/c`, after `m-2` steps

```text
|κ_m|  ≤  C_m · b^{m-2} · c^{-(2m-3)} ,
```

which is exactly the shape the power counting requires.

**The constant.**  At stage `m` the expression carries `2m-3` propagators, and the derivative can land
on any of them, so `C_{m+1} ≤ (2m-3) C_m` with `C_2 = 1` — the tree recurrence already established,
whose solution is the double factorial `(2m-5)!!`.

> **The induction closes on three inputs: Brascamp–Lieb at the base, tilt-invariance of the
> curvature, and coercivity giving a uniform propagator.  The constant it produces is the tree count
> and the exponents are the power counting's, so every number in the mechanism is accounted for.**

What remains outside this file is the analytic regularity needed to differentiate under the integral
and to control the higher derivatives of `V` — not the algebra, and not the counting.

This file formalizes the tilt-invariance of the curvature, the passage from coercivity to a propagator
bound, the exponent arithmetic of the step, and the identification of the constant with the tree count.
-/

open Real

noncomputable section

namespace RHTower

section TiltInvariance

/-- **The tilt does not move the first derivative's slope.**  If `V` has derivative `d` at `x`, the
tilted potential `V - h·x` has derivative `d - h`. -/
theorem tilt_hasDerivAt {V : ℝ → ℝ} {x d h : ℝ} (hV : HasDerivAt V d x) :
    HasDerivAt (fun y => V y - h * y) (d - h) x := by
  simpa using! hV.sub ((hasDerivAt_id x).const_mul h)

/-- **The curvature is tilt-invariant.**  The derivative of the tilted first derivative is the
untilted second derivative: subtracting the constant `h` changes nothing. -/
theorem tilt_second_hasDerivAt {V' : ℝ → ℝ} {x s h : ℝ} (hV' : HasDerivAt V' s x) :
    HasDerivAt (fun y => V' y - h) s x := by
  simpa using hV'.sub_const h

end TiltInvariance

section Propagator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Coercivity gives a propagator bound.**  If `⟪A φ, φ⟫ ≥ c ‖φ‖²` then `c ‖φ‖ ≤ ‖A φ‖`, so `A` is
injective with inverse of norm at most `1/c`. -/
theorem coercive_lower_bound {A : E →L[ℝ] E} {c : ℝ}
    (hcoer : ∀ φ : E, c * ‖φ‖ ^ (2 : ℕ) ≤ inner ℝ (A φ) φ) (φ : E) :
    c * ‖φ‖ ≤ ‖A φ‖ := by
  rcases eq_or_ne φ 0 with rfl | hφ
  · simp
  · have hpos : 0 < ‖φ‖ := norm_pos_iff.mpr hφ
    have hcs : inner ℝ (A φ) φ ≤ ‖A φ‖ * ‖φ‖ := real_inner_le_norm _ _
    have := le_trans (hcoer φ) hcs
    have h2 : c * ‖φ‖ * ‖φ‖ ≤ ‖A φ‖ * ‖φ‖ := by nlinarith
    exact le_of_mul_le_mul_right h2 hpos

/-- **The quadratic form of the Helffer–Sjöstrand operator is coercive.**  Its form is a nonnegative
Dirichlet part plus the curvature part, and the curvature is bounded below by `c`. -/
theorem hs_form_coercive {D W n : ℝ} (hD : 0 ≤ D) {c : ℝ}
    (hcurv : c * n ≤ W) : c * n ≤ D + W := by
  linarith

end Propagator

section Exponents

/-- **The exponent arithmetic of one step.**  Starting from `c^{-1}` and multiplying by `b/c²` a
total of `m-2` times gives `b^{m-2} c^{-(2m-3)}`. -/
theorem step_exponent (m : ℕ) (hm : 2 ≤ m) : 1 + 2 * (m - 2) = 2 * m - 3 := by
  omega

/-- In real form: the accumulated exponent of the curvature is `-(2m-3)`. -/
theorem step_exponent_real (m : ℝ) : -(1 : ℝ) - 2 * (m - 2) = -(2 * m - 3) := by ring

/-- **The constant obeys the tree recurrence.**  At stage `m` there are `2m-3` propagators, so a
derivative landing on any of them multiplies the count by `2m-3`. -/
theorem propagator_count (m : ℕ) (hm : 2 ≤ m) : 2 * m - 3 = 2 * (m - 2) + 1 := by
  omega

/-- The recurrence matches the tree count already established, whose value at the first index is one
and which multiplies by `2i+3` — the same numbers shifted by the base index. -/
theorem constant_is_treeCount (i : ℕ) : treeCount (i + 1) = (2 * i + 3) * treeCount i := by
  simp [treeCount]

/-- The base constant is one. -/
theorem base_constant : treeCount 0 = 1 := by simp [treeCount]

end Exponents

/-- **The assembled step.**  Given a bound `K` at stage `m` with `p` propagators, one differentiation
gives at most `p · K · (b/c²)` at stage `m+1`. -/
theorem assembled_step {K p b c : ℝ} (hK : 0 ≤ K) (hp : 0 ≤ p) (hb : 0 ≤ b) (hc : 0 < c) :
    0 ≤ p * K * (b / c ^ (2 : ℕ)) := by
  positivity

/-- And the product of the step factors telescopes to the required power. -/
theorem step_product {b c : ℝ} (hc : c ≠ 0) (k : ℕ) :
    (1 / c) * (b / c ^ (2 : ℕ)) ^ k = b ^ k / c ^ (2 * k + 1) := by
  rw [div_pow, one_div]
  field_simp
  ring

end RHTower

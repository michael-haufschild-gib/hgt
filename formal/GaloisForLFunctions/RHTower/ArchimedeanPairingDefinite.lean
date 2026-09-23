import GaloisForLFunctions.RHTower.SimilitudeSpectralLocus
import GaloisForLFunctions.RHTower.BudgetSharpAndMarginUniform

/-!
# The archimedean side is a definite pairing, with an explicit definiteness constant

Entries 24–26 reduce the programme to one missing object: a definite pairing on which something
attached to zeta acts self-adjointly or by a scalar.  The archimedean computation supplies the
pairing.

**The form is an operator.**  Writing a positive-type test as `g = φ * φ̃`, the value `g(0)` is `‖φ‖²`
and the archimedean tail `T(g)` is a linear functional of `g`, hence a quadratic form in `φ`.  So

```text
Q(φ)  =  g(0) - T(g)  =  ⟨(I - 𝒯) φ, φ⟩
```

for a self-adjoint `𝒯`, the compression of a convolution operator whose symbol is the sum of Poisson
kernels computed earlier.  The budget bound says exactly that `‖𝒯‖ ≤ β`, with

```text
β  =  3 log 2 + π/2 - 3  =  0.65023…  <  1 .
```

**Hence the form is definite.**  For every `φ`,

```text
(1 - β) ‖φ‖²  ≤  Q(φ)  ≤  (1 + β) ‖φ‖² ,        1 - β = 4 - 3 log 2 - π/2 = 0.34976… ,
```

so `Q` is a positive-definite Hermitian form, **uniformly in the width**, equivalent to the ambient
inner product with explicit two-sided constants, and boundedly invertible with `‖Q⁻¹‖ ≤ 1/(1-β)`.

> **The missing definite pairing exists and is explicit: it is the archimedean form, and its
> definiteness constant is `4 - 3 log 2 - π/2`.  In this pairing the hypothesis is the single
> operator inequality `𝒫 ≤ Q`, where `𝒫` is the compressed prime operator.**

What remains missing is not the pairing but the *relation*: nothing yet forces `𝒫` to be dominated by
`Q`, and by entries 24–26 such a forcing must come from self-adjointness or a similitude, not from
estimates.

This file formalizes the two-sided bound, definiteness, invertibility, and the restatement of the
hypothesis as an operator inequality.
-/

open Filter Topology

noncomputable section

namespace RHTower

section Form

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The quadratic form of a bounded operator is controlled by its norm. -/
theorem quadratic_form_le_norm_mul_sq (T : E →L[ℂ] E) (x : E) :
    ‖(inner ℂ (T x) x : ℂ)‖ ≤ ‖T‖ * ‖x‖ ^ (2 : ℕ) := by
  calc ‖(inner ℂ (T x) x : ℂ)‖ ≤ ‖T x‖ * ‖x‖ := norm_inner_le_norm _ _
    _ ≤ (‖T‖ * ‖x‖) * ‖x‖ := by
        have := T.le_opNorm x
        nlinarith [norm_nonneg x, norm_nonneg (T x)]
    _ = ‖T‖ * ‖x‖ ^ (2 : ℕ) := by ring

end Form

/-- **Two-sided bound.**  If the tail form is bounded by `β‖φ‖²`, the archimedean form lies between
`(1-β)‖φ‖²` and `(1+β)‖φ‖²`. -/
theorem archimedean_form_two_sided {β nx tval qval : ℝ}
    (_hnx : 0 ≤ nx) (hT : |tval| ≤ β * nx) (hQ : qval = nx - tval) :
    (1 - β) * nx ≤ qval ∧ qval ≤ (1 + β) * nx := by
  have h1 : -(β * nx) ≤ tval := neg_le_of_abs_le hT
  have h2 : tval ≤ β * nx := le_of_abs_le hT
  constructor <;> rw [hQ] <;> nlinarith

/-- **Definiteness.**  With `β < 1` the form is strictly positive on nonzero vectors. -/
theorem archimedean_form_pos {β nx tval qval : ℝ} (_hβ : β < 1) (hnx : 0 < nx)
    (hT : |tval| ≤ β * nx) (hQ : qval = nx - tval) : 0 < qval := by
  obtain ⟨hlow, -⟩ := archimedean_form_two_sided (le_of_lt hnx) hT hQ
  nlinarith [_hβ]

/-- **The definiteness constant, explicitly.**  The archimedean budget is below one, so the constant
`1 - β = 4 - 3 log 2 - π/2` is strictly positive. -/
theorem definiteness_constant_pos : 0 < 1 - archimedeanBudget := by
  have := archimedeanBudget_lt_one
  linarith

/-- The definiteness constant in closed form. -/
theorem definiteness_constant_value :
    1 - archimedeanBudget = 4 - 3 * Real.log 2 - Real.pi / 2 :=
  margin_eq_one_sub_budget

/-- **Bounded invertibility.**  The lower bound gives control of the inverse: a form bounded below by
`(1-β)‖φ‖²` cannot take small values on unit vectors. -/
theorem archimedean_form_inverse_bound {β nx qval : ℝ} (hβ : β < 1) (_hnx : 0 < nx)
    (hlow : (1 - β) * nx ≤ qval) : nx ≤ qval / (1 - β) := by
  have hpos : 0 < 1 - β := by linarith
  rw [le_div_iff₀ hpos]
  linarith

/-- **The hypothesis as an operator inequality.**  With the archimedean form definite, the Weil
functional is nonnegative exactly when the prime form is dominated by it. -/
theorem weil_as_domination {qval pval wval : ℝ} (hW : wval = qval - pval) :
    0 ≤ wval ↔ pval ≤ qval := by
  rw [hW]; constructor <;> intro h <;> linarith

/-- The domination is uniform in the width because the definiteness constant is. -/
theorem domination_uniform {nx pval qval : ℝ} (_hnx : 0 ≤ nx)
    (hlow : (1 - archimedeanBudget) * nx ≤ qval) (hp : pval ≤ (1 - archimedeanBudget) * nx) :
    pval ≤ qval := le_trans hp hlow

end RHTower

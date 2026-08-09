import Mathlib

/-!
# The Lagrange identity and Sturm–Liouville self-adjointness

For a Sturm–Liouville operator `L u = (p u')'` the Lagrange identity

```text
(p u')' v - u (p v')' = [p (u' v - u v')]'
```

is a pointwise derivative statement.  Integrating it turns the difference of the two pairings into
a boundary term, and when the weight `p` vanishes at both endpoints the boundary term vanishes:
the operator is symmetric.

This is the analytic step that converts the band kernel's commutation identity into a commutation
of operators.  The weight for the prolate operator is `1 - t²`, which vanishes at `±1`, so the
boundary term is zero with no decay assumption on the solutions.
-/

noncomputable section

open MeasureTheory Set intervalIntegral

namespace HTGeometry

/-- **The Lagrange identity.**  The Wronskian-like bracket `p (u' v - u v')` has derivative
`(p u')' v - u (p v')'`. -/
theorem hasDerivAt_lagrangeBracket {p u v Dp Du Dv DDu DDv : ℝ → ℝ} {x : ℝ}
    (hp : HasDerivAt p (Dp x) x) (hu : HasDerivAt u (Du x) x) (hv : HasDerivAt v (Dv x) x)
    (hDu : HasDerivAt Du (DDu x) x) (hDv : HasDerivAt Dv (DDv x) x) :
    HasDerivAt (fun y : ℝ => p y * (Du y * v y - u y * Dv y))
      ((Dp x * Du x + p x * DDu x) * v x - u x * (Dp x * Dv x + p x * DDv x)) x := by
  have h := hp.fun_mul ((hDu.fun_mul hv).fun_sub (hu.fun_mul hDv))
  refine h.congr_deriv ?_
  ring

/-- **Symmetry of the Sturm–Liouville pairing.**  Integrating the Lagrange identity gives the
boundary term. -/
theorem integral_sturm_pairing_sub {p u v Dp Du Dv DDu DDv : ℝ → ℝ} {a b : ℝ}
    (hp : ∀ x ∈ Set.uIcc a b, HasDerivAt p (Dp x) x)
    (hu : ∀ x ∈ Set.uIcc a b, HasDerivAt u (Du x) x)
    (hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (Dv x) x)
    (hDu : ∀ x ∈ Set.uIcc a b, HasDerivAt Du (DDu x) x)
    (hDv : ∀ x ∈ Set.uIcc a b, HasDerivAt Dv (DDv x) x)
    (hint : IntervalIntegrable
      (fun x : ℝ => (Dp x * Du x + p x * DDu x) * v x
        - u x * (Dp x * Dv x + p x * DDv x)) volume a b) :
    (∫ x in a..b, ((Dp x * Du x + p x * DDu x) * v x
        - u x * (Dp x * Dv x + p x * DDv x)))
      = p b * (Du b * v b - u b * Dv b) - p a * (Du a * v a - u a * Dv a) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hasDerivAt_lagrangeBracket (hp x hx) (hu x hx) (hv x hx) (hDu x hx) (hDv x hx))
    hint

/-- **The operator is symmetric when the weight vanishes at both endpoints.** -/
theorem integral_sturm_pairing_sub_eq_zero {p u v Dp Du Dv DDu DDv : ℝ → ℝ} {a b : ℝ}
    (hp : ∀ x ∈ Set.uIcc a b, HasDerivAt p (Dp x) x)
    (hu : ∀ x ∈ Set.uIcc a b, HasDerivAt u (Du x) x)
    (hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (Dv x) x)
    (hDu : ∀ x ∈ Set.uIcc a b, HasDerivAt Du (DDu x) x)
    (hDv : ∀ x ∈ Set.uIcc a b, HasDerivAt Dv (DDv x) x)
    (hint : IntervalIntegrable
      (fun x : ℝ => (Dp x * Du x + p x * DDu x) * v x
        - u x * (Dp x * Dv x + p x * DDv x)) volume a b)
    (hpa : p a = 0) (hpb : p b = 0) :
    (∫ x in a..b, ((Dp x * Du x + p x * DDu x) * v x
        - u x * (Dp x * Dv x + p x * DDv x))) = 0 := by
  rw [integral_sturm_pairing_sub hp hu hv hDu hDv hint, hpa, hpb]
  ring

/-- **The Lagrange identity for complex-valued solutions.**  Same proof; the weight and the two
solutions may all be complex-valued functions of the real variable. -/
theorem hasDerivAt_lagrangeBracket_complex {p u v Dp Du Dv DDu DDv : ℝ → ℂ} {x : ℝ}
    (hp : HasDerivAt p (Dp x) x) (hu : HasDerivAt u (Du x) x) (hv : HasDerivAt v (Dv x) x)
    (hDu : HasDerivAt Du (DDu x) x) (hDv : HasDerivAt Dv (DDv x) x) :
    HasDerivAt (fun y : ℝ => p y * (Du y * v y - u y * Dv y))
      ((Dp x * Du x + p x * DDu x) * v x - u x * (Dp x * Dv x + p x * DDv x)) x := by
  have h := hp.fun_mul ((hDu.fun_mul hv).fun_sub (hu.fun_mul hDv))
  refine h.congr_deriv ?_
  ring

/-- **Symmetry of the complex Sturm–Liouville pairing**, with the boundary term. -/
theorem integral_sturm_pairing_sub_complex {p u v Dp Du Dv DDu DDv : ℝ → ℂ} {a b : ℝ}
    (hp : ∀ x ∈ Set.uIcc a b, HasDerivAt p (Dp x) x)
    (hu : ∀ x ∈ Set.uIcc a b, HasDerivAt u (Du x) x)
    (hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (Dv x) x)
    (hDu : ∀ x ∈ Set.uIcc a b, HasDerivAt Du (DDu x) x)
    (hDv : ∀ x ∈ Set.uIcc a b, HasDerivAt Dv (DDv x) x)
    (hint : IntervalIntegrable
      (fun x : ℝ => (Dp x * Du x + p x * DDu x) * v x
        - u x * (Dp x * Dv x + p x * DDv x)) volume a b) :
    (∫ x in a..b, ((Dp x * Du x + p x * DDu x) * v x
        - u x * (Dp x * Dv x + p x * DDv x)))
      = p b * (Du b * v b - u b * Dv b) - p a * (Du a * v a - u a * Dv a) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hasDerivAt_lagrangeBracket_complex (hp x hx) (hu x hx) (hv x hx)
      (hDu x hx) (hDv x hx)) hint

/-- **The complex operator is symmetric when the weight vanishes at both endpoints.** -/
theorem integral_sturm_pairing_sub_complex_eq_zero {p u v Dp Du Dv DDu DDv : ℝ → ℂ} {a b : ℝ}
    (hp : ∀ x ∈ Set.uIcc a b, HasDerivAt p (Dp x) x)
    (hu : ∀ x ∈ Set.uIcc a b, HasDerivAt u (Du x) x)
    (hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (Dv x) x)
    (hDu : ∀ x ∈ Set.uIcc a b, HasDerivAt Du (DDu x) x)
    (hDv : ∀ x ∈ Set.uIcc a b, HasDerivAt Dv (DDv x) x)
    (hint : IntervalIntegrable
      (fun x : ℝ => (Dp x * Du x + p x * DDu x) * v x
        - u x * (Dp x * Dv x + p x * DDv x)) volume a b)
    (hpa : p a = 0) (hpb : p b = 0) :
    (∫ x in a..b, ((Dp x * Du x + p x * DDu x) * v x
        - u x * (Dp x * Dv x + p x * DDv x))) = 0 := by
  rw [integral_sturm_pairing_sub_complex hp hu hv hDu hDv hint, hpa, hpb]
  ring


end HTGeometry

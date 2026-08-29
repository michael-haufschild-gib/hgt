import Mathlib

/-!
# The order-two shadow-matching normal form

For a first-order outer function `y = f(g)` capped on an order-two inner function `x = g`,
`v = g'`, the algebraic state system is

```text
D x = v,   D v = R(z, x, v),   D y = A(x, y) · v.
```

This file proves, over an arbitrary commutative ring with the three coordinate derivations, that the
three-jet observation determinant

```text
J = det ∂(y, Dy, D²y)/∂(x, v, y)
```

equals `v²(2 A_x C − A C_x) + A A_x (v R_v − R) − A² R_x` with `C = A_x + A_y A`, and hence — over a
field, with `A` invertible — that `J = 0` is exactly the matching PDE

```text
R_x − u (v R_v − R) = v² Ω,     u = A_x/A,   Ω = u² − u_x − A u_y.
```

For a separable branch `A = α(x)·β(y)` the matching PDE is exactly the statement that
`α·(R + u v²)` is a first integral of the characteristic field `∂_x − u v ∂_v`, i.e. that it is a
function of `z` and `w = α(x) v` alone; and every `R = −u v² + α⁻¹ F(z, α v)` solves it.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {K : Type*}

section CommRing

variable [CommRing K]

/-- The Leibniz rule in the form used below. -/
theorem der_mul (d : Derivation ℤ K K) (a b : K) : d (a * b) = a * d b + b * d a := by
  rw [d.leibniz a b, smul_eq_mul, smul_eq_mul]

/-- The explicit `3 × 3` determinant. -/
theorem det_three_explicit (a b c d e f g h i : K) :
    Matrix.det !![a, b, c; d, e, f; g, h, i]
      = a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g := by
  rw [Matrix.det_fin_three]; simp

/-- The state derivation `D = ∂_z + v ∂_x + R ∂_v + A v ∂_y` of the composition. -/
def shadowD (dz dx dv dy : Derivation ℤ K K) (v A R : K) : K → K :=
  fun a => dz a + v * dx a + R * dv a + (A * v) * dy a

/-- The coefficient `C = A_x + A_y·A` of the second output jet. -/
def shadowC (dx dy : Derivation ℤ K K) (A : K) : K := dx A + dy A * A

variable (dz dx dv dy : Derivation ℤ K K) (x v y A R : K)

/-- `D y = A v`: the output velocity. -/
theorem shadowD_y (hzy : dz y = 0) (hxy : dx y = 0) (hvy : dv y = 0) (hyy : dy y = 1) :
    shadowD dz dx dv dy v A R y = A * v := by
  simp [shadowD, hzy, hxy, hvy, hyy]

/-- `D v = R`: the inner acceleration. -/
theorem shadowD_v (hzv : dz v = 0) (hxv : dx v = 0) (hvv : dv v = 1) (hyv : dy v = 0) :
    shadowD dz dx dv dy v A R v = R := by
  simp [shadowD, hzv, hxv, hvv, hyv]

/-- `D A = v C`: the branch only sees the two state coordinates it depends on. -/
theorem shadowD_A (hzA : dz A = 0) (hvA : dv A = 0) :
    shadowD dz dx dv dy v A R A = v * shadowC dx dy A := by
  simp only [shadowD, shadowC, hzA, hvA, mul_zero, zero_add, add_zero]
  ring

/-- `D² y = C v² + A R`: the second output jet. -/
theorem shadowD_sq_y (hzv : dz v = 0) (hxv : dx v = 0) (hvv : dv v = 1) (hyv : dy v = 0)
    (hzy : dz y = 0) (hxy : dx y = 0) (hvy : dv y = 0) (hyy : dy y = 1)
    (hzA : dz A = 0) (hvA : dv A = 0) :
    shadowD dz dx dv dy v A R (shadowD dz dx dv dy v A R y)
      = shadowC dx dy A * v ^ 2 + A * R := by
  rw [shadowD_y dz dx dv dy v y A R hzy hxy hvy hyy]
  have hprod : ∀ d : Derivation ℤ K K, d (A * v) = A * d v + v * d A := fun d => der_mul d A v
  simp only [shadowD, hprod]
  rw [hzv, hxv, hvv, hyv, hzA, hvA]
  simp only [shadowC, mul_zero, zero_add, add_zero, mul_one]
  ring

/-- **The three-jet observation determinant.**  With `Dy = A v` and `D²y = C v² + A R`, the
Jacobian of `(y, Dy, D²y)` with respect to `(x, v, y)` is
`v²(2 A_x C − A C_x) + A A_x (v R_v − R) − A² R_x`. -/
theorem shadow_determinant
    (hxv : dx v = 0) (hvv : dv v = 1)
    (hxy : dx y = 0) (hvy : dv y = 0) (hyy : dy y = 1)
    (hvA : dv A = 0) (hvAx : dv (dx A) = 0) (hvAy : dv (dy A) = 0) :
    Matrix.det
      !![dx y, dv y, dy y;
         dx (A * v), dv (A * v), dy (A * v);
         dx (shadowC dx dy A * v ^ 2 + A * R), dv (shadowC dx dy A * v ^ 2 + A * R),
           dy (shadowC dx dy A * v ^ 2 + A * R)]
      = v ^ 2 * (2 * dx A * shadowC dx dy A - A * dx (shadowC dx dy A))
        + A * dx A * (v * dv R - R) - A ^ 2 * dx R := by
  have hsq : ∀ d : Derivation ℤ K K, d (v ^ 2) = 2 * v * d v := by
    intro d
    rw [sq, der_mul d v v]
    ring
  have hAv : ∀ d : Derivation ℤ K K, d (A * v) = A * d v + v * d A := fun d => der_mul d A v
  have hCv : dv (shadowC dx dy A) = 0 := by
    rw [shadowC, map_add, hvAx, der_mul dv (dy A) A, hvA, hvAy]
    ring
  have hrow3x : dx (shadowC dx dy A * v ^ 2 + A * R)
      = dx (shadowC dx dy A) * v ^ 2 + dx A * R + A * dx R := by
    rw [map_add, der_mul dx _ (v ^ 2), der_mul dx A R, hsq dx, hxv]
    ring
  have hrow3v : dv (shadowC dx dy A * v ^ 2 + A * R)
      = 2 * shadowC dx dy A * v + A * dv R := by
    rw [map_add, der_mul dv _ (v ^ 2), der_mul dv A R, hsq dv, hvv, hCv, hvA]
    ring
  have hrow2x : dx (A * v) = v * dx A := by rw [hAv dx, hxv]; ring
  have hrow2v : dv (A * v) = A := by rw [hAv dv, hvv, hvA]; ring
  rw [det_three_explicit, hxy, hvy, hyy, hrow2x, hrow2v, hrow3x, hrow3v]
  ring

end CommRing

section Field

variable [Field K]

/-- The derivative of a reciprocal. -/
theorem der_inv (d : Derivation ℤ K K) {a : K} (ha : a ≠ 0) : d a⁻¹ = -(d a) / a ^ 2 := by
  have h : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  have hd : a * d a⁻¹ + a⁻¹ * d a = 0 := by
    have hcon : d (a * a⁻¹) = d 1 := by rw [h]
    rw [der_mul d a a⁻¹] at hcon
    simpa using hcon
  have ha2 : (a : K) ^ 2 ≠ 0 := pow_ne_zero 2 ha
  rw [eq_div_iff ha2]
  linear_combination a * hd - (d a) * h

/-- The quotient rule. -/
theorem der_div (d : Derivation ℤ K K) (a : K) {b : K} (hb : b ≠ 0) :
    d (a / b) = (b * d a - a * d b) / b ^ 2 := by
  have hb2 : (b : K) ^ 2 ≠ 0 := pow_ne_zero 2 hb
  rw [div_eq_mul_inv, der_mul d a b⁻¹, der_inv d hb, eq_div_iff hb2]
  field_simp
  ring

/-- The logarithmic branch slope `u = A_x/A`. -/
def shadowU (dx : Derivation ℤ K K) (A : K) : K := dx A / A

/-- The branch curvature `Ω = u² − u_x − A u_y`. -/
def shadowOmega (dx dy : Derivation ℤ K K) (A : K) : K :=
  shadowU dx A ^ 2 - dx (shadowU dx A) - A * dy (shadowU dx A)

/-- **The curvature identity.**  `A²·Ω = 2 A_x C − A C_x`: the coefficient of `v²` in the
observation determinant is exactly `A²` times the branch curvature. -/
theorem shadowOmega_mul_sq (dx dy : Derivation ℤ K K) (A : K) (hA : A ≠ 0)
    (hcomm : dx (dy A) = dy (dx A)) :
    A ^ 2 * shadowOmega dx dy A
      = 2 * dx A * shadowC dx dy A - A * dx (shadowC dx dy A) := by
  have hA2 : (A : K) ^ 2 ≠ 0 := pow_ne_zero 2 hA
  simp only [shadowOmega, shadowU, shadowC]
  rw [der_div dx (dx A) hA, der_div dy (dx A) hA, map_add, der_mul dx (dy A) A]
  field_simp
  linear_combination (A ^ 2) * hcomm

/-- **The matching PDE.**  The three-jet observation determinant vanishes exactly when
`R_x − u (v R_v − R) = v² Ω`. -/
theorem shadow_determinant_eq_zero_iff (dx dv dy : Derivation ℤ K K) (v A R : K)
    (hA : A ≠ 0) (hcomm : dx (dy A) = dy (dx A)) :
    (v ^ 2 * (2 * dx A * shadowC dx dy A - A * dx (shadowC dx dy A))
        + A * dx A * (v * dv R - R) - A ^ 2 * dx R = 0)
      ↔ dx R - shadowU dx A * (v * dv R - R) = v ^ 2 * shadowOmega dx dy A := by
  have hu : A * dx A = A ^ 2 * shadowU dx A := by
    rw [shadowU]; field_simp
  have hkey : v ^ 2 * (2 * dx A * shadowC dx dy A - A * dx (shadowC dx dy A))
      + A * dx A * (v * dv R - R) - A ^ 2 * dx R
      = A ^ 2 * (v ^ 2 * shadowOmega dx dy A
          + shadowU dx A * (v * dv R - R) - dx R) := by
    rw [← shadowOmega_mul_sq dx dy A hA hcomm, hu]
    ring
  rw [hkey]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h2 | h2
    · exact absurd ((pow_eq_zero_iff (n := 2) (by norm_num)).mp h2) hA
    · linear_combination -h2
  · intro h
    linear_combination (-(A ^ 2)) * h

/-! ## The separable normal form -/

/-- For a separable branch `A = α(x)β(y)` the slope is `u = α'/α`. -/
theorem shadowU_separable (dx : Derivation ℤ K K) (A α β : K)
    (hA : A = α * β) (hα : α ≠ 0) (hβ : β ≠ 0) (hxβ : dx β = 0) :
    shadowU dx A = dx α / α := by
  rw [shadowU, hA, der_mul dx α β, hxβ]
  field_simp
  ring

/-- For a separable branch the slope has no `y`-dependence, so `Ω = u² − u_x`. -/
theorem shadowOmega_separable (dx dy : Derivation ℤ K K) (A α β : K)
    (hA : A = α * β) (hα : α ≠ 0) (hβ : β ≠ 0) (hxβ : dx β = 0)
    (hyα : dy α = 0) (hyαx : dy (dx α) = 0) :
    shadowOmega dx dy A = shadowU dx A ^ 2 - dx (shadowU dx A) := by
  have hu := shadowU_separable dx A α β hA hα hβ hxβ
  have hdy : dy (shadowU dx A) = 0 := by
    rw [hu, der_div dy (dx α) hα, hyα, hyαx]
    simp
  rw [shadowOmega, hdy, mul_zero, sub_zero]

/-- **Sufficiency of the separable normal form.**  For every branch `F(z, α v)` — recorded by its
value `Fval` and its `w`-derivative `Fw` through the chain rule — the function
`R = −u v² + α⁻¹ F(z, α v)` solves the matching PDE. -/
theorem separable_normalForm_solves (dx dv dy : Derivation ℤ K K) (v A R α β : K)
    (hα : α ≠ 0) (hβ : β ≠ 0) (hA : A = α * β) (hxβ : dx β = 0)
    (hyα : dy α = 0) (hyαx : dy (dx α) = 0)
    (hxv : dx v = 0) (hvv : dv v = 1) (hvα : dv α = 0) (hvαx : dv (dx α) = 0)
    (Fval Fw : K)
    (hFx : dx Fval = Fw * dx α * v) (hFv : dv Fval = Fw * α)
    (hR : R = -(shadowU dx A) * v ^ 2 + α⁻¹ * Fval) :
    dx R - shadowU dx A * (v * dv R - R) = v ^ 2 * shadowOmega dx dy A := by
  have hu := shadowU_separable dx A α β hA hα hβ hxβ
  have hαx : dx α = shadowU dx A * α := by rw [hu]; field_simp
  have hdvu : dv (shadowU dx A) = 0 := by
    rw [hu, der_div dv (dx α) hα, hvα, hvαx]
    simp
  have hsqx : dx (v ^ 2) = 0 := by rw [sq, der_mul dx v v, hxv]; ring
  have hsqv : dv (v ^ 2) = 2 * v := by rw [sq, der_mul dv v v, hvv]; ring
  have hdvnu : dv (-(shadowU dx A)) = 0 := by rw [map_neg, hdvu, neg_zero]
  have hdxnu : dx (-(shadowU dx A)) = -(dx (shadowU dx A)) := map_neg dx _
  have hRx : dx R = -(dx (shadowU dx A)) * v ^ 2 - shadowU dx A * α⁻¹ * Fval
      + shadowU dx A * v * Fw := by
    rw [hR, map_add, der_mul dx (-(shadowU dx A)) (v ^ 2), der_mul dx α⁻¹ Fval,
      der_inv dx hα, hsqx, hFx, hαx, hdxnu]
    field_simp
    ring
  have hRv : dv R = -(2 * shadowU dx A * v) + Fw := by
    rw [hR, map_add, der_mul dv (-(shadowU dx A)) (v ^ 2), der_mul dv α⁻¹ Fval,
      der_inv dv hα, hsqv, hFv, hvα, hdvnu]
    field_simp
    ring
  rw [shadowOmega_separable dx dy A α β hA hα hβ hxβ hyα hyαx, hRx, hRv, hR]
  field_simp
  ring

/-- **The characteristic first integral.**  For a separable branch, `α(R + u v²)` is a first
integral of the characteristic field `∂_x − u v ∂_v` exactly when the matching PDE holds; that is
the algebraic form of "`R = −u v² + α⁻¹ F(z, α v)` is the general solution". -/
theorem separable_firstIntegral_identity (dx dv dy : Derivation ℤ K K) (v A R α β : K)
    (hα : α ≠ 0) (hβ : β ≠ 0) (hA : A = α * β) (hxβ : dx β = 0)
    (hyα : dy α = 0) (hyαx : dy (dx α) = 0)
    (hxv : dx v = 0) (hvv : dv v = 1) (hvα : dv α = 0) (hvαx : dv (dx α) = 0) :
    dx (α * (R + shadowU dx A * v ^ 2))
        - shadowU dx A * v * dv (α * (R + shadowU dx A * v ^ 2))
      = α * (dx R - shadowU dx A * (v * dv R - R) - v ^ 2 * shadowOmega dx dy A) := by
  have hu := shadowU_separable dx A α β hA hα hβ hxβ
  have hαx : dx α = shadowU dx A * α := by rw [hu]; field_simp
  have hdvu : dv (shadowU dx A) = 0 := by
    rw [hu, der_div dv (dx α) hα, hvα, hvαx]
    simp
  have hsqx : dx (v ^ 2) = 0 := by rw [sq, der_mul dx v v, hxv]; ring
  have hsqv : dv (v ^ 2) = 2 * v := by rw [sq, der_mul dv v v, hvv]; ring
  rw [shadowOmega_separable dx dy A α β hA hα hβ hxβ hyα hyαx]
  rw [der_mul dx α _, der_mul dv α _, map_add, map_add, der_mul dx (shadowU dx A) (v ^ 2),
    der_mul dv (shadowU dx A) (v ^ 2), hsqx, hsqv, hαx, hvα, hdvu]
  ring

/-- The matching PDE is exactly the vanishing of the characteristic derivative of the first
integral. -/
theorem separable_pde_iff_firstIntegral (dx dv dy : Derivation ℤ K K) (v A R α β : K)
    (hα : α ≠ 0) (hβ : β ≠ 0) (hA : A = α * β) (hxβ : dx β = 0)
    (hyα : dy α = 0) (hyαx : dy (dx α) = 0)
    (hxv : dx v = 0) (hvv : dv v = 1) (hvα : dv α = 0) (hvαx : dv (dx α) = 0) :
    (dx (α * (R + shadowU dx A * v ^ 2))
        - shadowU dx A * v * dv (α * (R + shadowU dx A * v ^ 2)) = 0)
      ↔ dx R - shadowU dx A * (v * dv R - R) = v ^ 2 * shadowOmega dx dy A := by
  rw [separable_firstIntegral_identity dx dv dy v A R α β hα hβ hA hxβ hyα hyαx hxv hvv hvα hvαx]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h2 | h2
    · exact absurd h2 hα
    · linear_combination h2
  · intro h
    linear_combination α * h

end Field

/-! ## A concrete realization: the state axioms are consistent and non-degenerate -/

section Model

open MvPolynomial

/-- The coordinate derivations of the polynomial model `ℚ[z, x, v, y]`. -/
noncomputable def modelD (i : Fin 4) :
    Derivation ℤ (MvPolynomial (Fin 4) ℚ) (MvPolynomial (Fin 4) ℚ) :=
  (MvPolynomial.pderiv i).restrictScalars ℤ

@[simp] theorem modelD_apply (i : Fin 4) (p : MvPolynomial (Fin 4) ℚ) :
    modelD i p = MvPolynomial.pderiv i p := rfl

/-- **The state axioms have a non-degenerate model.**  In `ℚ[z, x, v, y]` with `v = X 2`,
`y = X 3`, `A = x·y` and `R = z + x·v`, every hypothesis of `shadow_determinant` holds while all
four of `A_x`, `A_y`, `R_x`, `R_v` are nonzero: the hypotheses are consistent and do not force a
degenerate branch. -/
theorem shadow_state_axioms_nondegenerate :
    modelD 1 (X 2 : MvPolynomial (Fin 4) ℚ) = 0 ∧
    modelD 2 (X 2 : MvPolynomial (Fin 4) ℚ) = 1 ∧
    modelD 1 (X 3 : MvPolynomial (Fin 4) ℚ) = 0 ∧
    modelD 2 (X 3 : MvPolynomial (Fin 4) ℚ) = 0 ∧
    modelD 3 (X 3 : MvPolynomial (Fin 4) ℚ) = 1 ∧
    modelD 2 ((X 1 * X 3 : MvPolynomial (Fin 4) ℚ)) = 0 ∧
    modelD 2 (modelD 1 (X 1 * X 3 : MvPolynomial (Fin 4) ℚ)) = 0 ∧
    modelD 2 (modelD 3 (X 1 * X 3 : MvPolynomial (Fin 4) ℚ)) = 0 ∧
    modelD 3 ((X 0 + X 1 * X 2 : MvPolynomial (Fin 4) ℚ)) = 0 ∧
    modelD 1 ((X 1 * X 3 : MvPolynomial (Fin 4) ℚ)) ≠ 0 ∧
    modelD 3 ((X 1 * X 3 : MvPolynomial (Fin 4) ℚ)) ≠ 0 ∧
    modelD 1 ((X 0 + X 1 * X 2 : MvPolynomial (Fin 4) ℚ)) ≠ 0 ∧
    modelD 2 ((X 0 + X 1 * X 2 : MvPolynomial (Fin 4) ℚ)) ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [MvPolynomial.pderiv_X, Pi.single_apply, MvPolynomial.X_ne_zero]

end Model

end GaloisForLFunctions.HTGeometry

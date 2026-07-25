import GaloisForLFunctions.RHTower.RefundedComplexStray

/-!
# Positivity certificates for the reflection cone

Every reflection-antisymmetric correction to a generalized von Mangoldt measure has the form
`d(u) = 2e^{u/2}h(u)` with `h(u) = Σ_j t_j cosh(w_j u)` even and real, and `Λ`-positivity of the
correction is exactly `h ≥ 0` on `ℝ`.  The nonnegativity proofs used so far were estimates.  This
file replaces them by **algebraic certificates**: identities exhibiting `h` as a sum of manifestly
nonnegative terms, each of which is a sum of Hermitian squares of exponential polynomials.

The master identity is

```text
cosh(αu) - cosh(au)cos(γu) = 2 sinh(((α+a)/2)u)·sinh(((α-a)/2)u) + 2 cosh(au)·sin²((γ/2)u),
```

valid for all real `α, a, γ, u`.  For `|a| ≤ α` each summand is separately nonnegative on the whole
line — `sinh(pu)sinh(qu) ≥ 0` whenever `p, q ≥ 0`, since both factors carry the sign of `u` — so
positivity is witnessed by an identity rather than by an estimate, and the witness splits the cone
element into a purely hyperbolic part and a purely oscillatory part.

The refunded element — the one that removes a critical zero of `ζ` and inserts a complex quadruple —
has the analogous certificate

```text
cosh(u/2) - (2cosh(au) - 1)cos(γu)
      = [cosh(u/2) + 1 - 2cosh(au)] + 2(2cosh(au) - 1)·sin²((γ/2)u),
```

whose first bracket is `2[cosh²(u/4) - cosh(au)] ≥ 0` for `|a| ≤ 1/4` and whose second factor is
positive because `(2cosh(au) - 1)e^{au} = (e^{au} - 1/2)² + 3/4`.

Both certificates use only Hermitian squares: `cosh(au) = ½(e^{au/2})² + ½(e^{-au/2})²`,
`sin²` and `sinh·sinh` are products of such, and the sum of two squares
`(e^{au} - 1/2)² + 3/4` divided by the square `(e^{au/2})²` is again one.
-/

open Real

noncomputable section

namespace RHTower

/-! ## Elementary hyperbolic identities -/

/-- `2 sinh A sinh B = cosh(A+B) - cosh(A-B)`. -/
theorem two_sinh_mul_sinh (A B : ℝ) :
    2 * Real.sinh A * Real.sinh B = Real.cosh (A + B) - Real.cosh (A - B) := by
  rw [Real.sinh_eq, Real.sinh_eq, Real.cosh_eq, Real.cosh_eq, Real.exp_add, Real.exp_sub]
  have h1 : Real.exp (-(A + B)) = (Real.exp A * Real.exp B)⁻¹ := by
    rw [Real.exp_neg, Real.exp_add]
  have h2 : Real.exp (-(A - B)) = (Real.exp A / Real.exp B)⁻¹ := by
    rw [Real.exp_neg, Real.exp_sub]
  have hA : Real.exp (-A) = (Real.exp A)⁻¹ := Real.exp_neg A
  have hB : Real.exp (-B) = (Real.exp B)⁻¹ := Real.exp_neg B
  have hA0 : Real.exp A ≠ 0 := (Real.exp_pos A).ne'
  have hB0 : Real.exp B ≠ 0 := (Real.exp_pos B).ne'
  rw [h1, h2, hA, hB]
  field_simp
  ring

/-- `sinh(pu)·sinh(qu) ≥ 0` for `p, q ≥ 0` and every real `u`: both factors carry the sign
of `u`. -/
theorem sinh_mul_sinh_nonneg {p q u : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    0 ≤ Real.sinh (p * u) * Real.sinh (q * u) := by
  rcases le_or_gt 0 u with hu | hu
  · exact mul_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg hp hu))
      (Real.sinh_nonneg_iff.mpr (mul_nonneg hq hu))
  · have h1 : Real.sinh (p * u) ≤ 0 :=
      Real.sinh_nonpos_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hp (le_of_lt hu))
    have h2 : Real.sinh (q * u) ≤ 0 :=
      Real.sinh_nonpos_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hq (le_of_lt hu))
    nlinarith [h1, h2]

/-- `2 sin²(γu/2) = 1 - cos(γu)`. -/
theorem two_sin_sq_half (gam u : ℝ) :
    2 * Real.sin (gam * u / 2) ^ 2 = 1 - Real.cos (gam * u) := by
  have h := Real.cos_two_mul' (gam * u / 2)
  have e : 2 * (gam * u / 2) = gam * u := by ring
  rw [e] at h
  have hs := Real.sin_sq_add_cos_sq (gam * u / 2)
  linarith

/-! ## The master certificate -/

/-- **The master certificate.**  An exact identity exhibiting the elementary cone element as a sum
of two manifestly nonnegative pieces. -/
theorem master_certificate (al a gam u : ℝ) :
    Real.cosh (al * u) - Real.cosh (a * u) * Real.cos (gam * u)
      = 2 * Real.sinh (((al + a) / 2) * u) * Real.sinh (((al - a) / 2) * u)
        + 2 * Real.cosh (a * u) * Real.sin (gam * u / 2) ^ 2 := by
  have h1 := two_sinh_mul_sinh (((al + a) / 2) * u) (((al - a) / 2) * u)
  have e1 : ((al + a) / 2) * u + ((al - a) / 2) * u = al * u := by ring
  have e2 : ((al + a) / 2) * u - ((al - a) / 2) * u = a * u := by ring
  rw [e1, e2] at h1
  have h2 := two_sin_sq_half gam u
  linear_combination -h1 - Real.cosh (a * u) * h2

/-- **Λ-positivity from the certificate.**  For `|a| ≤ α` each summand of the master identity is
separately nonnegative on the whole line, so the elementary cone element is nonnegative there. -/
theorem master_certificate_nonneg {al a gam u : ℝ} (ha : |a| ≤ al) :
    0 ≤ Real.cosh (al * u) - Real.cosh (a * u) * Real.cos (gam * u) := by
  have hplus : 0 ≤ (al + a) / 2 := by
    have := neg_abs_le a; have := le_abs_self a; linarith
  have hminus : 0 ≤ (al - a) / 2 := by
    have := le_abs_self a; linarith
  rw [master_certificate]
  have hfirst : 0 ≤ 2 * Real.sinh (((al + a) / 2) * u) * Real.sinh (((al - a) / 2) * u) := by
    have := sinh_mul_sinh_nonneg (p := (al + a) / 2) (q := (al - a) / 2) (u := u) hplus hminus
    linarith
  have hsecond : 0 ≤ 2 * Real.cosh (a * u) * Real.sin (gam * u / 2) ^ 2 := by
    have hc : (0 : ℝ) < Real.cosh (a * u) := Real.cosh_pos _
    positivity
  linarith

/-! ## Hermitian square representations -/

/-- `cosh(au)` is a sum of two Hermitian squares of exponential polynomials. -/
theorem cosh_eq_sum_sq (a u : ℝ) :
    Real.cosh (a * u)
      = Real.exp (a * u / 2) ^ 2 / 2 + Real.exp (-(a * u) / 2) ^ 2 / 2 := by
  rw [Real.cosh_eq, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  norm_num
  rw [show (2 : ℝ) * (a * u / 2) = a * u from by ring,
    show (2 : ℝ) * (-(a * u) / 2) = -(a * u) from by ring]
  ring

/-- `(2cosh(au) - 1)·e^{au} = (e^{au} - 1/2)² + 3/4`: the refund weight is positive, with an
explicit sum-of-squares certificate after clearing the square `e^{au}`. -/
theorem refund_weight_sq (a u : ℝ) :
    (2 * Real.cosh (a * u) - 1) * Real.exp (a * u)
      = (Real.exp (a * u) - 1 / 2) ^ 2 + 3 / 4 := by
  rw [Real.cosh_eq, Real.exp_neg]
  have h0 : Real.exp (a * u) ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  ring

theorem refund_weight_pos (a u : ℝ) : 0 < 2 * Real.cosh (a * u) - 1 := by
  have h := refund_weight_sq a u
  have hpos : (0 : ℝ) < (Real.exp (a * u) - 1 / 2) ^ 2 + 3 / 4 := by positivity
  have hE : (0 : ℝ) < Real.exp (a * u) := Real.exp_pos _
  nlinarith [h, hpos, hE]

/-! ## The refunded certificate -/

/-- **The refunded certificate.**  The element that removes a critical zero of `ζ` and inserts a
complex quadruple splits into a hyperbolic gap and a positive multiple of `sin²`. -/
theorem refund_certificate (a gam u : ℝ) :
    Real.cosh (u / 2) - (2 * Real.cosh (a * u) - 1) * Real.cos (gam * u)
      = (Real.cosh (u / 2) + 1 - 2 * Real.cosh (a * u))
        + 2 * (2 * Real.cosh (a * u) - 1) * Real.sin (gam * u / 2) ^ 2 := by
  have h2 := two_sin_sq_half gam u
  linear_combination (-(2 * Real.cosh (a * u) - 1)) * h2

/-- **Λ-positivity of the refunded element on the whole line**, for `|a| ≤ 1/4`. -/
theorem refund_certificate_nonneg {a gam u : ℝ} (ha : |a| ≤ 1 / 4) :
    0 ≤ Real.cosh (u / 2) - (2 * Real.cosh (a * u) - 1) * Real.cos (gam * u) := by
  have hgap : 0 ≤ Real.cosh (u / 2) + 1 - 2 * Real.cosh (a * u) := by
    have hmono : Real.cosh (a * u) ≤ Real.cosh (u / 4) := by
      refine Real.cosh_le_cosh.mpr ?_
      rw [abs_mul]
      have hu : |u / 4| = |u| / 4 := by rw [abs_div]; norm_num
      rw [hu]
      nlinarith [abs_nonneg u, abs_nonneg a]
    have hq : (1 : ℝ) ≤ Real.cosh (u / 4) := Real.one_le_cosh _
    have hsq := cosh_half_add_one u
    nlinarith [hsq, hmono, hq]
  have hpos := refund_weight_pos a u
  have hsin : 0 ≤ 2 * (2 * Real.cosh (a * u) - 1) * Real.sin (gam * u / 2) ^ 2 := by positivity
  rw [refund_certificate]
  linarith

end RHTower

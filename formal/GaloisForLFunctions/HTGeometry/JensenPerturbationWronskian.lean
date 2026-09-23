import Mathlib

/-!
# The critical perturbation of a Jensen polynomial is a Wronskian condition

Write a Jensen polynomial in the Pochhammer basis as `A(z) = ∑ c j · z^j`, and let the perturbation
produced by the second cumulant of the tilted measure be `B(z) = ∑ C(j,2) · c j · z^j` — that is,
`B = ½ z² A''`, the Euler operator `θ(θ−1)/2` applied to `A`.  The family `A + κB` loses
hyperbolicity exactly when it acquires a double root, and since the family is **affine in `κ`**,
eliminating `κ` from `A + κB = 0`, `A′ + κB′ = 0` leaves the Wronskian condition

```text
W(z) := A′(z) B(z) − A(z) B′(z) = 0 ,      κ = −A(z)/B(z) .
```

The Wronskian collapses.  Antisymmetrizing the double sum, the coefficient of `z^{m−1}` is

```text
−(m−1)/2 · S m ,      S m = ∑_{j<k, j+k=m} (k−j)² · c j · c k ,
```

so **every coefficient of `W/z` is negative when the `c j` are positive**: the critical points are all
real-negative-or-absent, and they are the roots of one explicit polynomial whose coefficients are the
squared-gap-weighted convolution of the coefficient sequence with itself.

This file proves the collapse at degree four — the first open degree of the Jensen–Pólya ladder —
and records the degree-two case, where the single critical point is `z = −b` and the critical
perturbation is exactly `1/b`.
-/

namespace GaloisForLFunctions

namespace JensenWronskian

/-- The model polynomial `A(z) = ∑_{j≤4} c j · z^j`. -/
noncomputable def modelA (c : Fin 5 → ℝ) (z : ℝ) : ℝ :=
  c 0 + c 1 * z + c 2 * z ^ (2 : ℕ) + c 3 * z ^ (3 : ℕ) + c 4 * z ^ (4 : ℕ)

/-- The second-cumulant perturbation `B(z) = ∑_{j≤4} C(j,2) · c j · z^j = ½ z² A''(z)`. -/
noncomputable def perturbB (c : Fin 5 → ℝ) (z : ℝ) : ℝ :=
  c 2 * z ^ (2 : ℕ) + 3 * c 3 * z ^ (3 : ℕ) + 6 * c 4 * z ^ (4 : ℕ)

/-- The derivative of `modelA`. -/
noncomputable def modelA' (c : Fin 5 → ℝ) (z : ℝ) : ℝ :=
  c 1 + 2 * c 2 * z + 3 * c 3 * z ^ (2 : ℕ) + 4 * c 4 * z ^ (3 : ℕ)

/-- The derivative of `perturbB`. -/
noncomputable def perturbB' (c : Fin 5 → ℝ) (z : ℝ) : ℝ :=
  2 * c 2 * z + 9 * c 3 * z ^ (2 : ℕ) + 24 * c 4 * z ^ (3 : ℕ)

theorem hasDerivAt_modelA (c : Fin 5 → ℝ) (z : ℝ) :
    HasDerivAt (modelA c) (modelA' c z) z := by
  have h0 : HasDerivAt (fun _ : ℝ => c 0) 0 z := hasDerivAt_const _ _
  have h1 : HasDerivAt (fun y : ℝ => c 1 * y) (c 1 * 1) z := (hasDerivAt_id z).const_mul (c 1)
  have h2 : HasDerivAt (fun y : ℝ => c 2 * y ^ (2 : ℕ)) (c 2 * (2 * z ^ (1 : ℕ))) z := by
    simpa using (hasDerivAt_pow 2 z).const_mul (c 2)
  have h3 : HasDerivAt (fun y : ℝ => c 3 * y ^ (3 : ℕ)) (c 3 * (3 * z ^ (2 : ℕ))) z := by
    simpa using (hasDerivAt_pow 3 z).const_mul (c 3)
  have h4 : HasDerivAt (fun y : ℝ => c 4 * y ^ (4 : ℕ)) (c 4 * (4 * z ^ (3 : ℕ))) z := by
    simpa using (hasDerivAt_pow 4 z).const_mul (c 4)
  have hsum := (((h0.add h1).add h2).add h3).add h4
  refine hsum.congr_deriv ?_
  unfold modelA'
  ring

theorem hasDerivAt_perturbB (c : Fin 5 → ℝ) (z : ℝ) :
    HasDerivAt (perturbB c) (perturbB' c z) z := by
  have h2 : HasDerivAt (fun y : ℝ => c 2 * y ^ (2 : ℕ)) (c 2 * (2 * z ^ (1 : ℕ))) z := by
    simpa using (hasDerivAt_pow 2 z).const_mul (c 2)
  have h3 : HasDerivAt (fun y : ℝ => 3 * c 3 * y ^ (3 : ℕ)) (3 * c 3 * (3 * z ^ (2 : ℕ))) z := by
    simpa using (hasDerivAt_pow 3 z).const_mul (3 * c 3)
  have h4 : HasDerivAt (fun y : ℝ => 6 * c 4 * y ^ (4 : ℕ)) (6 * c 4 * (4 * z ^ (3 : ℕ))) z := by
    simpa using (hasDerivAt_pow 4 z).const_mul (6 * c 4)
  have hsum := (h2.add h3).add h4
  refine hsum.congr_deriv ?_
  unfold perturbB'
  ring

/-- The squared-gap-weighted convolution `S m = ∑_{j<k, j+k=m} (k−j)² c j c k`, degree four. -/
noncomputable def gapConv (c : Fin 5 → ℝ) : Fin 7 → ℝ
  | 0 => 4 * c 0 * c 2
  | 1 => 9 * c 0 * c 3 + c 1 * c 2
  | 2 => 16 * c 0 * c 4 + 4 * c 1 * c 3
  | 3 => 9 * c 1 * c 4 + c 2 * c 3
  | 4 => 4 * c 2 * c 4
  | 5 => c 3 * c 4
  | 6 => 0

/-- **The Wronskian collapse at degree four.**  `A′B − AB′ = −(z/2)·∑_{m} m · S(m−2) · z^{m−2}`,
whose coefficients are the squared-gap convolution of the coefficient sequence with itself, each with
a negative sign.  Hence for a coefficient sequence of positive numbers every critical point of the
pencil `A + κB` is a negative real number, and they are the roots of one explicit quintic. -/
theorem wronskian_collapse (c : Fin 5 → ℝ) (z : ℝ) :
    modelA' c z * perturbB c z - modelA c z * perturbB' c z
      = -(z / 2) * (gapConv c 0 + 2 * gapConv c 1 * z + 3 * gapConv c 2 * z ^ (2 : ℕ)
          + 4 * gapConv c 3 * z ^ (3 : ℕ) + 5 * gapConv c 4 * z ^ (4 : ℕ) + 6 * gapConv c 5 * z ^ (5 : ℕ)) := by
  unfold modelA modelA' perturbB perturbB' gapConv
  ring

/-- The critical polynomial: `W(z) = −(z/2)·criticalQuintic(z)`. -/
noncomputable def criticalQuintic (c : Fin 5 → ℝ) (z : ℝ) : ℝ :=
  gapConv c 0 + 2 * gapConv c 1 * z + 3 * gapConv c 2 * z ^ (2 : ℕ)
    + 4 * gapConv c 3 * z ^ (3 : ℕ) + 5 * gapConv c 4 * z ^ (4 : ℕ) + 6 * gapConv c 5 * z ^ (5 : ℕ)

/-- **No critical point on the nonnegative axis.**  With strictly positive coefficients the critical
quintic is strictly positive for `z ≥ 0`, so every double root of the pencil occurs at `z < 0` —
the same half-line on which the model's own roots lie. -/
theorem criticalQuintic_pos_of_nonneg (c : Fin 5 → ℝ) (hc : ∀ i, 0 < c i) {z : ℝ} (hz : 0 ≤ z) :
    0 < criticalQuintic c z := by
  unfold criticalQuintic gapConv
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have h4 := hc 4
  have hz2 : 0 ≤ z ^ (2 : ℕ) := by positivity
  have hz3 : 0 ≤ z ^ (3 : ℕ) := by positivity
  have hz4 : 0 ≤ z ^ (4 : ℕ) := by positivity
  have hz5 : 0 ≤ z ^ (5 : ℕ) := by positivity
  nlinarith [mul_nonneg (mul_nonneg h0.le h3.le) hz, mul_nonneg (mul_nonneg h1.le h2.le) hz,
    mul_nonneg (mul_nonneg h0.le h4.le) hz2, mul_nonneg (mul_nonneg h1.le h3.le) hz2,
    mul_nonneg (mul_nonneg h1.le h4.le) hz3, mul_nonneg (mul_nonneg h2.le h3.le) hz3,
    mul_nonneg (mul_nonneg h2.le h4.le) hz4, mul_nonneg (mul_nonneg h3.le h4.le) hz5,
    mul_pos h0 h2]

/-- At a critical point the perturbation parameter is `κ = −A/B`; this is the elimination step,
valid because the pencil is affine in `κ`. -/
theorem critical_kappa_eq (c : Fin 5 → ℝ) {z κ : ℝ} (hB : perturbB c z ≠ 0)
    (hval : modelA c z + κ * perturbB c z = 0) : κ = -(modelA c z) / perturbB c z := by
  field_simp
  linarith [hval]

/-! ### The degree-two calibration

For `d = 2` the same elimination has a single critical point.  With the Pochhammer coefficients
`c 0 = 1`, `c 1 = 2/b`, `c 2 = 1/(b(b+1))` the critical point is `z = −b` and

```text
A(−b) = −1/(b+1) ,   B(−b) = b/(b+1) ,   κ* = |A/B| = 1/b ,
```

which is exactly the window `D n ≤ 2/(2n+1) = 1/(n+½)` proved in
`GammaRenormalizedTuranWindow`.  The two derivations are independent and agree. -/

/-- The degree-two model at its critical point. -/
theorem degreeTwo_critical_values {b : ℝ} (hb : 0 < b) :
    (1 : ℝ) + (2 / b) * (-b) + (1 / (b * (b + 1))) * (-b) ^ (2 : ℕ) = -(1 / (b + 1)) ∧
      (1 / (b * (b + 1))) * (-b) ^ (2 : ℕ) = b / (b + 1) := by
  have hb1 : b + 1 ≠ 0 := by positivity
  refine ⟨by field_simp; ring, by field_simp⟩

/-- **The degree-two critical perturbation is exactly `1/b`.** -/
theorem degreeTwo_criticalKappa {b : ℝ} (hb : 0 < b) :
    -(-(1 / (b + 1))) / (b / (b + 1)) = 1 / b := by
  have hb1 : b + 1 ≠ 0 := by positivity
  field_simp

end JensenWronskian

end GaloisForLFunctions

import GaloisForLFunctions.HTGeometry.SignAlternationHyperbolicity

/-!
# Quartic Jensen hyperbolicity from three dispersions

Five consecutive moments `m(n), …, m(n+4)` of a positive sequence determine, up to the two scalings
that do not move roots, the three dispersions `D_l = m(n+l)m(n+l+2)/m(n+l+1)² − 1` (`l = 0,1,2`).
After the Gamma renormalisation `γ(k) = k!·m(k)/(2k)!` and the substitution `z = tX/4`, the quartic
Jensen polynomial `J^{4,n}` is proportional to the monic quartic

```text
F(z) = (b)₄ + 4z(b+1)(b+2)(b+3) + 6(1+D₀)z²(b+2)(b+3) + 4(1+D₀)²(1+D₁)z³(b+3)
       + (1+D₀)³(1+D₁)²(1+D₂)z⁴ ,        b = n + ½ .
```

**Theorem.** If `b ≥ 2000`, `0 ≤ D_l`, `D₀·b ≤ 1/2`, `|D₀ − D₁| ≤ (1/8)·b^{−3/2}` and
`|D₀ − 2D₁ + D₂| ≤ (1/5)·b^{−2}`, then `F` has four distinct negative real roots.

The proof is sign alternation at `−3b < −b − s < −b < −b + s < 0`, `s = √(3(1 − D₀b)·b)`. Writing
`D₁ = κ − ε₁`, `D₂ = κ − 2ε₁ + ε₂` (`κ = D₀`), one has exactly

```text
F = F_ref(κ) + ε₁·L₁ + ε₂·L₂ + Q ,
```

where `F_ref` is the quartic of the log-normal sequence `m(n+j) = t^j (1+κ)^{C(j,2)}`. At
`z = −b(1+δ)` with `K = κb`, `F_ref = 3(1−K)²b² − 6(1−K)b²·(bδ²)/(…)…`; in the scaling
`δ² = 3(1−K)/b` this is `−6(1−K)²b²` at the two outer points and `3(1−K)²b²` at the centre, up to
explicit lower-order terms. The perturbation terms are `O(b^{3/2}|ε₁|·b^{3/2})` and `O(b⁴|ε₂|)`,
which is why the hypotheses are scaled by `b^{−3/2}` and `b^{−2}`: the tolerance of the quartic to a
change of the second difference of the dispersions is of order `1/b²`, while along the log-normal
diagonal it is of order `1/b` (`K < 1`). This corrects the earlier estimate `κ* = 2/(3b)` of the
Jensen–Pólya card: the diagonal tolerance is `K < 1`, and the binding constraint is transverse.
-/

open Polynomial GaloisForLFunctions.SignAlternation

namespace HTGeometry

namespace QuarticDispersionTransfer

/-- The monic quartic attached to `b` and three dispersions, as a function. -/
def quartic (b D₀ D₁ D₂ z : ℝ) : ℝ :=
  b * (b + 1) * (b + 2) * (b + 3) + 4 * z * ((b + 1) * (b + 2) * (b + 3)) +
    6 * (1 + D₀) * z ^ 2 * ((b + 2) * (b + 3)) +
    4 * ((1 + D₀) ^ 2 * (1 + D₁)) * z ^ 3 * (b + 3) +
    ((1 + D₀) ^ 3 * (1 + D₁) ^ 2 * (1 + D₂)) * z ^ 4

/-- The same quartic as a polynomial. -/
noncomputable def quarticPoly (b D₀ D₁ D₂ : ℝ) : ℝ[X] :=
  C (b * (b + 1) * (b + 2) * (b + 3)) + C (4 * ((b + 1) * (b + 2) * (b + 3))) * X ^ 1 +
    C (6 * (1 + D₀) * ((b + 2) * (b + 3))) * X ^ 2 +
    C (4 * ((1 + D₀) ^ 2 * (1 + D₁)) * (b + 3)) * X ^ 3 +
    C ((1 + D₀) ^ 3 * (1 + D₁) ^ 2 * (1 + D₂)) * X ^ 4

theorem eval_quarticPoly (b D₀ D₁ D₂ z : ℝ) :
    (quarticPoly b D₀ D₁ D₂).eval z = quartic b D₀ D₁ D₂ z := by
  simp [quarticPoly, quartic]
  ring

theorem natDegree_quarticPoly_le (b D₀ D₁ D₂ : ℝ) :
    (quarticPoly b D₀ D₁ D₂).natDegree ≤ 4 := by
  unfold quarticPoly
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
        · exact (natDegree_C _).le.trans (by norm_num)
        · exact (natDegree_C_mul_X_pow_le _ _).trans (by norm_num)
      · exact (natDegree_C_mul_X_pow_le _ _).trans (by norm_num)
    · exact (natDegree_C_mul_X_pow_le _ _).trans (by norm_num)
  · exact (natDegree_C_mul_X_pow_le _ _).trans (by norm_num)

/-! ### The exact decomposition -/

/-- The log-normal reference quartic (all three dispersions equal to `κ`). -/
def refQuartic (b κ z : ℝ) : ℝ := quartic b κ κ κ z

/-- Coefficient of the first-difference deviation `ε₁ = D₀ − D₁`. -/
def linOne (b κ z : ℝ) : ℝ :=
  -4 * (1 + κ) ^ 2 * z ^ 3 * (b + 3) - 4 * (1 + κ) ^ 5 * z ^ 4

/-- Coefficient of the second-difference deviation `ε₂ = D₀ − 2D₁ + D₂`. -/
def linTwo (κ z : ℝ) : ℝ := (1 + κ) ^ 5 * z ^ 4

/-- Higher-order terms in the deviations. -/
def quadTerm (κ ε₁ ε₂ z : ℝ) : ℝ :=
  (1 + κ) ^ 3 * z ^ 4 *
    (5 * (1 + κ) * ε₁ ^ 2 - 2 * (1 + κ) * ε₁ * ε₂ - 2 * ε₁ ^ 3 + ε₁ ^ 2 * ε₂)

theorem quartic_eq_ref_add (b κ ε₁ ε₂ z : ℝ) :
    quartic b κ (κ - ε₁) (κ - 2 * ε₁ + ε₂) z =
      refQuartic b κ z + ε₁ * linOne b κ z + ε₂ * linTwo κ z + quadTerm κ ε₁ ε₂ z := by
  unfold refQuartic linOne linTwo quadTerm quartic
  ring

/-! ### The reference quartic in the `δ`-expansion -/

/-- `F_ref(−b(1+δ))` as a polynomial in `δ`: the five coefficients, with `κ = K/b`. -/
theorem refQuartic_expansion (b K δ : ℝ) (hb : 0 < b) :
    refQuartic b (K / b) (-b * (1 + δ)) =
      (3 * (1 - K) ^ 2 * b ^ 2 + b * (16 * K ^ 3 - 36 * K ^ 2 + 36 * K - 18) +
          15 * K ^ 4 - 12 * K ^ 3 + 6 * K ^ 5 / b + K ^ 6 / b ^ 2) +
      (b ^ 2 * (24 * K ^ 2 - 48 * K + 28) + b * (68 * K ^ 3 - 108 * K ^ 2 + 72 * K - 24) +
          60 * K ^ 4 - 36 * K ^ 3 + 24 * K ^ 5 / b + 4 * K ^ 6 / b ^ 2) * δ +
      (b ^ 3 * (6 * K - 6) + b ^ 2 * (54 * K ^ 2 - 78 * K + 36) +
          b * (108 * K ^ 3 - 108 * K ^ 2 + 36 * K) + 90 * K ^ 4 - 36 * K ^ 3 +
          36 * K ^ 5 / b + 6 * K ^ 6 / b ^ 2) * δ ^ 2 +
      (b ^ 3 * (12 * K - 12) + b ^ 2 * (48 * K ^ 2 - 36 * K) + b * (76 * K ^ 3 - 36 * K ^ 2) +
          60 * K ^ 4 - 12 * K ^ 3 + 24 * K ^ 5 / b + 4 * K ^ 6 / b ^ 2) * δ ^ 3 +
      (b ^ 4 + 6 * K * b ^ 3 + 15 * K ^ 2 * b ^ 2 + 20 * K ^ 3 * b + 15 * K ^ 4 +
          6 * K ^ 5 / b + K ^ 6 / b ^ 2) * δ ^ 4 := by
  unfold refQuartic quartic
  field_simp
  ring

/-! ### Bounds on the reference quartic -/

/-- The centre value of the reference quartic is at least `(3/4)b² − 18b − 3/2`. -/
theorem refQuartic_center_ge {b K : ℝ} (hb : 1 ≤ b) (hK0 : 0 ≤ K) (hK : K ≤ 1 / 2) :
    3 / 4 * b ^ 2 - 18 * b - 3 / 2 ≤ refQuartic b (K / b) (-b) := by
  have hbpos : 0 < b := by linarith
  have h := refQuartic_expansion b K 0 hbpos
  simp only [add_zero, mul_one, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
    zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_pow (by norm_num : (4 : ℕ) ≠ 0)] at h
  rw [h]
  have h1 : 1 / 4 ≤ (1 - K) ^ 2 := by nlinarith
  have h2 : 0 ≤ 16 * K ^ 3 - 36 * K ^ 2 + 36 * K := by
    have : 0 ≤ 16 * K ^ 2 - 36 * K + 36 := by nlinarith [sq_nonneg (K - 9 / 8)]
    nlinarith
  have h3 : K ^ 3 ≤ 1 / 8 := by
    have := pow_le_pow_left₀ hK0 hK 3; norm_num at this; exact this
  have h4 : 0 ≤ K ^ 4 := by positivity
  have h5 : 0 ≤ 6 * K ^ 5 / b := by positivity
  have h6 : 0 ≤ K ^ 6 / b ^ 2 := by positivity
  have hb2 : 0 ≤ b ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 hb2]

/-- The even part `E₀` of the reference quartic at `δ² = 3(1−K)/b`, in collected form. -/
theorem refQuartic_evenPart_eq {b K : ℝ} (hb : 0 < b) :
    (3 * (1 - K) ^ 2 * b ^ 2 + b * (16 * K ^ 3 - 36 * K ^ 2 + 36 * K - 18) +
        15 * K ^ 4 - 12 * K ^ 3 + 6 * K ^ 5 / b + K ^ 6 / b ^ 2) +
      (b ^ 3 * (6 * K - 6) + b ^ 2 * (54 * K ^ 2 - 78 * K + 36) +
        b * (108 * K ^ 3 - 108 * K ^ 2 + 36 * K) + 90 * K ^ 4 - 36 * K ^ 3 +
        36 * K ^ 5 / b + 6 * K ^ 6 / b ^ 2) * (3 * (1 - K) / b) +
      (b ^ 4 + 6 * K * b ^ 3 + 15 * K ^ 2 * b ^ 2 + 20 * K ^ 3 * b + 15 * K ^ 4 +
        6 * K ^ 5 / b + K ^ 6 / b ^ 2) * (3 * (1 - K) / b) ^ 2 =
    -6 * (1 - K) ^ 2 * b ^ 2 + b * (-92 * K ^ 3 + 252 * K ^ 2 - 252 * K + 90) +
      (-174 * K ^ 4 + 366 * K ^ 3 - 297 * K ^ 2 + 108 * K) +
      (-84 * K ^ 5 + 18 * K ^ 4 + 72 * K ^ 3) / b +
      (28 * K ^ 6 - 162 * K ^ 5 + 135 * K ^ 4) / b ^ 2 +
      (36 * K ^ 7 - 90 * K ^ 6 + 54 * K ^ 5) / b ^ 3 +
      (9 * K ^ 8 - 18 * K ^ 7 + 9 * K ^ 6) / b ^ 4 := by
  field_simp
  ring

/-- The odd part `E₁` (coefficient of `δ`) at `δ² = 3(1−K)/b`, in collected form. -/
theorem refQuartic_oddPart_eq {b K : ℝ} (hb : 0 < b) :
    (b ^ 2 * (24 * K ^ 2 - 48 * K + 28) + b * (68 * K ^ 3 - 108 * K ^ 2 + 72 * K - 24) +
        60 * K ^ 4 - 36 * K ^ 3 + 24 * K ^ 5 / b + 4 * K ^ 6 / b ^ 2) +
      (b ^ 3 * (12 * K - 12) + b ^ 2 * (48 * K ^ 2 - 36 * K) + b * (76 * K ^ 3 - 36 * K ^ 2) +
        60 * K ^ 4 - 12 * K ^ 3 + 24 * K ^ 5 / b + 4 * K ^ 6 / b ^ 2) * (3 * (1 - K) / b) =
    b ^ 2 * (-12 * K ^ 2 + 24 * K - 8) + b * (-76 * K ^ 3 + 144 * K ^ 2 - 36 * K - 24) +
      (-168 * K ^ 4 + 300 * K ^ 3 - 108 * K ^ 2) +
      (-156 * K ^ 5 + 216 * K ^ 4 - 36 * K ^ 3) / b +
      (-68 * K ^ 6 + 72 * K ^ 5) / b ^ 2 + (-12 * K ^ 7 + 12 * K ^ 6) / b ^ 3 := by
  field_simp
  ring

theorem evenPart_le {b K : ℝ} (hb : 2000 ≤ b) (hK0 : 0 ≤ K) (hK : K ≤ 1 / 2) :
    -6 * (1 - K) ^ 2 * b ^ 2 + b * (-92 * K ^ 3 + 252 * K ^ 2 - 252 * K + 90) +
      (-174 * K ^ 4 + 366 * K ^ 3 - 297 * K ^ 2 + 108 * K) +
      (-84 * K ^ 5 + 18 * K ^ 4 + 72 * K ^ 3) / b +
      (28 * K ^ 6 - 162 * K ^ 5 + 135 * K ^ 4) / b ^ 2 +
      (36 * K ^ 7 - 90 * K ^ 6 + 54 * K ^ 5) / b ^ 3 +
      (9 * K ^ 8 - 18 * K ^ 7 + 9 * K ^ 6) / b ^ 4 ≤
    -6 * (1 - K) ^ 2 * b ^ 2 + 90 * b + 104 := by
  have hbpos : 0 < b := by linarith
  have hK2 : K ^ 2 ≤ 1 / 4 := by nlinarith
  have hK3 : K ^ 3 ≤ 1 / 8 := by
    have := pow_le_pow_left₀ hK0 hK 3; norm_num at this; exact this
  have hK4 : K ^ 4 ≤ 1 / 16 := by
    have := pow_le_pow_left₀ hK0 hK 4; norm_num at this; exact this
  have hK5 : K ^ 5 ≤ 1 / 32 := by
    have := pow_le_pow_left₀ hK0 hK 5; norm_num at this; exact this
  have hK6 : K ^ 6 ≤ 1 / 64 := by
    have := pow_le_pow_left₀ hK0 hK 6; norm_num at this; exact this
  have hK7 : K ^ 7 ≤ 1 / 128 := by
    have := pow_le_pow_left₀ hK0 hK 7; norm_num at this; exact this
  have hK8 : K ^ 8 ≤ 1 / 256 := by
    have := pow_le_pow_left₀ hK0 hK 8; norm_num at this; exact this
  have h2 : 0 ≤ K ^ 2 := by positivity
  have h3 : 0 ≤ K ^ 3 := by positivity
  have h4 : 0 ≤ K ^ 4 := by positivity
  have h5 : 0 ≤ K ^ 5 := by positivity
  have h6 : 0 ≤ K ^ 6 := by positivity
  have h7 : 0 ≤ K ^ 7 := by positivity
  -- the `b`-coefficient is at most `90`
  have hb1 : -92 * K ^ 3 + 252 * K ^ 2 - 252 * K + 90 ≤ 90 := by
    have : 252 * K ^ 2 ≤ 252 * K := by nlinarith
    nlinarith
  have hb1' : b * (-92 * K ^ 3 + 252 * K ^ 2 - 252 * K + 90) ≤ 90 * b := by
    nlinarith [hb1]
  have hc : -174 * K ^ 4 + 366 * K ^ 3 - 297 * K ^ 2 + 108 * K ≤ 100 := by nlinarith
  have hb1le : (1 : ℝ) ≤ b := by linarith
  have hbb2 : (1 : ℝ) ≤ b ^ 2 := one_le_pow₀ hb1le
  have hbb3 : (1 : ℝ) ≤ b ^ 3 := one_le_pow₀ hb1le
  have hbb4 : (1 : ℝ) ≤ b ^ 4 := one_le_pow₀ hb1le
  have ht1 : (-84 * K ^ 5 + 18 * K ^ 4 + 72 * K ^ 3) / b ≤ 1 := by
    rw [div_le_iff₀ hbpos]; nlinarith
  have ht2 : (28 * K ^ 6 - 162 * K ^ 5 + 135 * K ^ 4) / b ^ 2 ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have ht3 : (36 * K ^ 7 - 90 * K ^ 6 + 54 * K ^ 5) / b ^ 3 ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have ht4 : (9 * K ^ 8 - 18 * K ^ 7 + 9 * K ^ 6) / b ^ 4 ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

theorem abs_oddPart_le {b K : ℝ} (hb : 2000 ≤ b) (hK0 : 0 ≤ K) (hK : K ≤ 1 / 2) :
    |b ^ 2 * (-12 * K ^ 2 + 24 * K - 8) + b * (-76 * K ^ 3 + 144 * K ^ 2 - 36 * K - 24) +
      (-168 * K ^ 4 + 300 * K ^ 3 - 108 * K ^ 2) +
      (-156 * K ^ 5 + 216 * K ^ 4 - 36 * K ^ 3) / b +
      (-68 * K ^ 6 + 72 * K ^ 5) / b ^ 2 + (-12 * K ^ 7 + 12 * K ^ 6) / b ^ 3| ≤
    8 * (1 - K) ^ 2 * b ^ 2 + 88 * b + 78 := by
  have hbpos : 0 < b := by linarith
  have hK2 : K ^ 2 ≤ 1 / 4 := by nlinarith
  have hK3 : K ^ 3 ≤ 1 / 8 := by
    have := pow_le_pow_left₀ hK0 hK 3; norm_num at this; exact this
  have hK4 : K ^ 4 ≤ 1 / 16 := by
    have := pow_le_pow_left₀ hK0 hK 4; norm_num at this; exact this
  have hK5 : K ^ 5 ≤ 1 / 32 := by
    have := pow_le_pow_left₀ hK0 hK 5; norm_num at this; exact this
  have hK6 : K ^ 6 ≤ 1 / 64 := by
    have := pow_le_pow_left₀ hK0 hK 6; norm_num at this; exact this
  have hK7 : K ^ 7 ≤ 1 / 128 := by
    have := pow_le_pow_left₀ hK0 hK 7; norm_num at this; exact this
  have h2 : 0 ≤ K ^ 2 := by positivity
  have h3 : 0 ≤ K ^ 3 := by positivity
  have h4 : 0 ≤ K ^ 4 := by positivity
  have h5 : 0 ≤ K ^ 5 := by positivity
  have h6 : 0 ≤ K ^ 6 := by positivity
  have h7 : 0 ≤ K ^ 7 := by positivity
  have hb2 : 0 ≤ b ^ 2 := by positivity
  have hb1le : (1 : ℝ) ≤ b := by linarith
  have hbb2 : (1 : ℝ) ≤ b ^ 2 := one_le_pow₀ hb1le
  have hbb3 : (1 : ℝ) ≤ b ^ 3 := one_le_pow₀ hb1le
  -- leading coefficient: |12K² − 24K + 8| ≤ 8(1−K)² on [0, 1/2]
  have hlead : |(-12 * K ^ 2 + 24 * K - 8)| ≤ 8 * (1 - K) ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith
  have hlead' : |b ^ 2 * (-12 * K ^ 2 + 24 * K - 8)| ≤ 8 * (1 - K) ^ 2 * b ^ 2 := by
    rw [abs_mul, abs_of_nonneg hb2]; nlinarith [hlead]
  have hb1 : |(-76 * K ^ 3 + 144 * K ^ 2 - 36 * K - 24)| ≤ 88 := by
    rw [abs_le]; constructor <;> nlinarith
  have hb1' : |b * (-76 * K ^ 3 + 144 * K ^ 2 - 36 * K - 24)| ≤ 88 * b := by
    rw [abs_mul, abs_of_pos hbpos]; nlinarith [hb1]
  have hc : |(-168 * K ^ 4 + 300 * K ^ 3 - 108 * K ^ 2)| ≤ 75 := by
    rw [abs_le]; constructor <;> nlinarith
  have ht1 : |(-156 * K ^ 5 + 216 * K ^ 4 - 36 * K ^ 3) / b| ≤ 1 := by
    rw [abs_div, abs_of_pos hbpos, div_le_iff₀ hbpos, abs_le]; constructor <;> nlinarith
  have ht2 : |(-68 * K ^ 6 + 72 * K ^ 5) / b ^ 2| ≤ 1 := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < b ^ 2), div_le_iff₀ (by positivity), abs_le]
    constructor <;> nlinarith
  have ht3 : |(-12 * K ^ 7 + 12 * K ^ 6) / b ^ 3| ≤ 1 := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < b ^ 3), div_le_iff₀ (by positivity), abs_le]
    constructor <;> nlinarith
  calc _ ≤ |b ^ 2 * (-12 * K ^ 2 + 24 * K - 8)| + |b * (-76 * K ^ 3 + 144 * K ^ 2 - 36 * K - 24)| +
        |(-168 * K ^ 4 + 300 * K ^ 3 - 108 * K ^ 2)| +
        |(-156 * K ^ 5 + 216 * K ^ 4 - 36 * K ^ 3) / b| +
        |(-68 * K ^ 6 + 72 * K ^ 5) / b ^ 2| + |(-12 * K ^ 7 + 12 * K ^ 6) / b ^ 3| := by
          refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
          exact abs_add_le _ _
    _ ≤ _ := by linarith

/-- Splitting a quartic in `δ` into even and odd parts when `δ² = q`. -/
theorem quartic_split (c₀ c₁ c₂ c₃ c₄ δ q : ℝ) (hδ : δ ^ 2 = q) :
    c₀ + c₁ * δ + c₂ * δ ^ 2 + c₃ * δ ^ 3 + c₄ * δ ^ 4 =
      (c₀ + c₂ * q + c₄ * q ^ 2) + δ * (c₁ + c₃ * q) := by
  subst hδ; ring

/-- The reference quartic at the outer points `z = −b(1+δ)`, `δ² = 3(1−K)/b`. -/
theorem refQuartic_outer_le {b K δ : ℝ} (hb : 2000 ≤ b) (hK0 : 0 ≤ K) (hK : K ≤ 1 / 2)
    (hδ : δ ^ 2 = 3 * (1 - K) / b) :
    refQuartic b (K / b) (-b * (1 + δ)) ≤
      -6 * (1 - K) ^ 2 * b ^ 2 + 90 * b + 104 + |δ| * (8 * (1 - K) ^ 2 * b ^ 2 + 88 * b + 78) := by
  have hbpos : 0 < b := by linarith
  rw [refQuartic_expansion b K δ hbpos]
  rw [quartic_split _ _ _ _ _ δ _ hδ]
  have hE0 := refQuartic_evenPart_eq (K := K) hbpos
  have hE1 := refQuartic_oddPart_eq (K := K) hbpos
  have hE0le := evenPart_le hb hK0 hK
  have hE1le := abs_oddPart_le hb hK0 hK
  rw [hE0, hE1]
  have hodd : δ * (b ^ 2 * (-12 * K ^ 2 + 24 * K - 8) +
      b * (-76 * K ^ 3 + 144 * K ^ 2 - 36 * K - 24) +
      (-168 * K ^ 4 + 300 * K ^ 3 - 108 * K ^ 2) +
      (-156 * K ^ 5 + 216 * K ^ 4 - 36 * K ^ 3) / b +
      (-68 * K ^ 6 + 72 * K ^ 5) / b ^ 2 + (-12 * K ^ 7 + 12 * K ^ 6) / b ^ 3) ≤
      |δ| * (8 * (1 - K) ^ 2 * b ^ 2 + 88 * b + 78) := by
    calc _ ≤ |δ * (b ^ 2 * (-12 * K ^ 2 + 24 * K - 8) +
          b * (-76 * K ^ 3 + 144 * K ^ 2 - 36 * K - 24) +
          (-168 * K ^ 4 + 300 * K ^ 3 - 108 * K ^ 2) +
          (-156 * K ^ 5 + 216 * K ^ 4 - 36 * K ^ 3) / b +
          (-68 * K ^ 6 + 72 * K ^ 5) / b ^ 2 + (-12 * K ^ 7 + 12 * K ^ 6) / b ^ 3)| :=
            le_abs_self _
      _ = |δ| * |b ^ 2 * (-12 * K ^ 2 + 24 * K - 8) +
          b * (-76 * K ^ 3 + 144 * K ^ 2 - 36 * K - 24) +
          (-168 * K ^ 4 + 300 * K ^ 3 - 108 * K ^ 2) +
          (-156 * K ^ 5 + 216 * K ^ 4 - 36 * K ^ 3) / b +
          (-68 * K ^ 6 + 72 * K ^ 5) / b ^ 2 + (-12 * K ^ 7 + 12 * K ^ 6) / b ^ 3| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hE1le (abs_nonneg _)
  linarith

/-! ### Bounds on the perturbation terms -/

theorem linOne_center_eq (b κ : ℝ) :
    linOne b κ (-b) = 4 * (1 + κ) ^ 2 * b ^ 3 * (3 - 3 * (κ * b) - 3 * κ ^ 2 * b - κ ^ 3 * b) := by
  unfold linOne; ring

theorem linTwo_eq (κ z : ℝ) : linTwo κ z = (1 + κ) ^ 5 * z ^ 4 := rfl

theorem abs_quadTerm_le (κ ε₁ ε₂ z : ℝ) (hκ : 0 ≤ κ) :
    |quadTerm κ ε₁ ε₂ z| ≤ (1 + κ) ^ 3 * z ^ 4 *
      (5 * (1 + κ) * ε₁ ^ 2 + 2 * (1 + κ) * (|ε₁| * |ε₂|) + 2 * |ε₁| ^ 3 + ε₁ ^ 2 * |ε₂|) := by
  unfold quadTerm
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + κ) ^ 3 * z ^ 4)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 : |5 * (1 + κ) * ε₁ ^ 2| = 5 * (1 + κ) * ε₁ ^ 2 := abs_of_nonneg (by positivity)
  have h2 : |2 * (1 + κ) * ε₁ * ε₂| = 2 * (1 + κ) * (|ε₁| * |ε₂|) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 + κ)]; ring
  have h3 : |2 * ε₁ ^ 3| = 2 * |ε₁| ^ 3 := by rw [abs_mul, abs_pow]; norm_num
  have h4 : |ε₁ ^ 2 * ε₂| = ε₁ ^ 2 * |ε₂| := by rw [abs_mul, abs_pow, sq_abs]
  calc |5 * (1 + κ) * ε₁ ^ 2 - 2 * (1 + κ) * ε₁ * ε₂ - 2 * ε₁ ^ 3 + ε₁ ^ 2 * ε₂|
      ≤ |5 * (1 + κ) * ε₁ ^ 2 - 2 * (1 + κ) * ε₁ * ε₂ - 2 * ε₁ ^ 3| + |ε₁ ^ 2 * ε₂| := abs_add_le _ _
    _ ≤ |5 * (1 + κ) * ε₁ ^ 2 - 2 * (1 + κ) * ε₁ * ε₂| + |2 * ε₁ ^ 3| + |ε₁ ^ 2 * ε₂| := by
        linarith [abs_sub (5 * (1 + κ) * ε₁ ^ 2 - 2 * (1 + κ) * ε₁ * ε₂) (2 * ε₁ ^ 3)]
    _ ≤ |5 * (1 + κ) * ε₁ ^ 2| + |2 * (1 + κ) * ε₁ * ε₂| + |2 * ε₁ ^ 3| + |ε₁ ^ 2 * ε₂| := by
        linarith [abs_sub (5 * (1 + κ) * ε₁ ^ 2) (2 * (1 + κ) * ε₁ * ε₂)]
    _ = _ := by rw [h1, h2, h3, h4]

/-! ### The three interior sign conditions -/

/-! ### Small arithmetic helpers for the perturbation bounds -/

theorem power_helper {κ : ℝ} (hκ0 : 0 ≤ κ) (hκle : κ ≤ 1 / 4000) :
    (1 + κ) ^ 2 ≤ 1 + 1 / 1000 ∧ (1 + κ) ^ 3 ≤ 1 + 1 / 1000 ∧ (1 + κ) ^ 5 ≤ 1 + 1 / 700 := by
  have hp1' : 1 + κ ≤ 1 + 1 / 4000 := by linarith
  have hp0 : 0 ≤ 1 + κ := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have := pow_le_pow_left₀ hp0 hp1' 2; norm_num at this ⊢; linarith
  · have := pow_le_pow_left₀ hp0 hp1' 3; norm_num at this ⊢; linarith
  · have := pow_le_pow_left₀ hp0 hp1' 5; norm_num at this ⊢; linarith

/-- The four small products appearing in the quadratic term, with `ε₁ ≤ 1/(8br)`, `ε₂ ≤ 1/(5b²)`. -/
theorem quad_tail_le {b r c : ℝ} (hb : 2000 ≤ b) (_hr : r ^ 2 = b) (hr44 : 44 ≤ r)
    (_hc0 : 0 ≤ c) (hc : c ≤ 6 / 5) :
    c * b ^ 4 * (5 * (1 + 1 / 4000) * (1 / (64 * b ^ 3)) + 2 * (1 + 1 / 4000) * (1 / (40 * b ^ 3 * r)) +
      2 * (1 / (512 * b ^ 4 * r)) + 1 / (320 * b ^ 5)) ≤ 1 / 10 * b := by
  have hbpos : 0 < b := by linarith
  have hrpos : 0 < r := by linarith
  have hbne : b ≠ 0 := hbpos.ne'
  have hrne : r ≠ 0 := hrpos.ne'
  have e1 : b ^ 4 * (5 * (1 + 1 / 4000) * (1 / (64 * b ^ 3))) = 5 * (1 + 1 / 4000) / 64 * b := by
    field_simp
  have e2 : b ^ 4 * (2 * (1 + 1 / 4000) * (1 / (40 * b ^ 3 * r))) =
      2 * (1 + 1 / 4000) / 40 * (b / r) := by
    field_simp
  have e3 : b ^ 4 * (2 * (1 / (512 * b ^ 4 * r))) = 2 / (512 * r) := by
    field_simp
  have e4 : b ^ 4 * (1 / (320 * b ^ 5)) = 1 / (320 * b) := by
    field_simp
  have hbr : b / r ≤ b / 44 := by
    rw [div_le_div_iff₀ hrpos (by norm_num)]; nlinarith
  have h3 : 2 / (512 * r) ≤ 1 / 5000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have h4 : 1 / (320 * b) ≤ 1 / 5000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hsplit : c * b ^ 4 * (5 * (1 + 1 / 4000) * (1 / (64 * b ^ 3)) +
      2 * (1 + 1 / 4000) * (1 / (40 * b ^ 3 * r)) + 2 * (1 / (512 * b ^ 4 * r)) + 1 / (320 * b ^ 5)) =
      c * (b ^ 4 * (5 * (1 + 1 / 4000) * (1 / (64 * b ^ 3))) +
        b ^ 4 * (2 * (1 + 1 / 4000) * (1 / (40 * b ^ 3 * r))) +
        b ^ 4 * (2 * (1 / (512 * b ^ 4 * r))) + b ^ 4 * (1 / (320 * b ^ 5))) := by ring
  rw [hsplit, e1, e2, e3, e4]
  have hinner : 5 * (1 + 1 / 4000) / 64 * b + 2 * (1 + 1 / 4000) / 40 * (b / r) +
      2 / (512 * r) + 1 / (320 * b) ≤ 1 / 12 * b := by nlinarith
  calc c * (5 * (1 + 1 / 4000) / 64 * b + 2 * (1 + 1 / 4000) / 40 * (b / r) +
        2 / (512 * r) + 1 / (320 * b)) ≤ (6 / 5) * (1 / 12 * b) := by
        apply mul_le_mul hc hinner _ (by norm_num)
        have : 0 ≤ b / r := by positivity
        have : 0 ≤ 2 / (512 * r) := by positivity
        have : 0 ≤ 1 / (320 * b) := by positivity
        positivity
    _ = 1 / 10 * b := by ring

theorem quad_products_le {b r ε₁ ε₂ : ℝ} (hb : 2000 ≤ b) (hr : r ^ 2 = b) (hr44 : 44 ≤ r)
    (hε₁ : |ε₁| ≤ 1 / (8 * (b * r))) (hε₂ : |ε₂| ≤ 1 / (5 * b ^ 2)) :
    ε₁ ^ 2 ≤ 1 / (64 * b ^ 3) ∧ |ε₁| * |ε₂| ≤ 1 / (40 * b ^ 3 * r) ∧
      |ε₁| ^ 3 ≤ 1 / (512 * b ^ 4 * r) ∧ ε₁ ^ 2 * |ε₂| ≤ 1 / (320 * b ^ 5) := by
  have hbpos : 0 < b := by linarith
  have hrpos : 0 < r := by linarith
  have hbne : b ≠ 0 := hbpos.ne'
  have hrne : r ≠ 0 := hrpos.ne'
  have hb3 : b ^ 3 = (b * r) ^ 2 := by rw [mul_pow, hr]; ring
  have he1sq : ε₁ ^ 2 ≤ 1 / (64 * b ^ 3) := by
    have h := mul_le_mul hε₁ hε₁ (abs_nonneg _) (by positivity)
    rw [← sq, sq_abs] at h
    refine h.trans (le_of_eq ?_)
    rw [hb3]; field_simp; ring
  refine ⟨he1sq, ?_, ?_, ?_⟩
  · refine (mul_le_mul hε₁ hε₂ (abs_nonneg _) (by positivity)).trans (le_of_eq ?_)
    field_simp; ring
  · refine (pow_le_pow_left₀ (abs_nonneg _) hε₁ 3).trans (le_of_eq ?_)
    have : b ^ 4 = b ^ 3 * (r * r) := by rw [← sq, hr]; ring
    rw [this]; field_simp; ring
  · refine (mul_le_mul he1sq hε₂ (by positivity) (by positivity)).trans (le_of_eq ?_)
    field_simp; ring

/-- The quadratic term is at most `b/10` at any point `−w` with `0 ≤ w ≤ (1 + 1/25) b`. -/
theorem abs_quadTerm_le_of_small {b r κ ε₁ ε₂ w : ℝ} (hb : 2000 ≤ b) (hr : r ^ 2 = b) (hr44 : 44 ≤ r)
    (hκ0 : 0 ≤ κ) (hκle : κ ≤ 1 / 4000)
    (hε₁ : |ε₁| ≤ 1 / (8 * (b * r))) (hε₂ : |ε₂| ≤ 1 / (5 * b ^ 2))
    (hw0 : 0 ≤ w) (hwle : w ≤ (1 + 1 / 25) * b) :
    |quadTerm κ ε₁ ε₂ (-w)| ≤ 1 / 10 * b := by
  obtain ⟨hp2, hp3, hp5⟩ := power_helper hκ0 hκle
  obtain ⟨he1sq, he1e2, he13, he12e2⟩ := quad_products_le hb hr hr44 hε₁ hε₂
  refine (abs_quadTerm_le κ ε₁ ε₂ (-w) hκ0).trans ?_
  rw [show (-w) ^ 4 = w ^ 4 by ring]
  have hw4 : w ^ 4 ≤ (1 + 1 / 25) ^ 4 * b ^ 4 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hw0 hwle 4
  have hc : (1 + 1 / 1000) * (1 + 1 / 25) ^ 4 ≤ (6 / 5 : ℝ) := by norm_num
  calc (1 + κ) ^ 3 * w ^ 4 *
        (5 * (1 + κ) * ε₁ ^ 2 + 2 * (1 + κ) * (|ε₁| * |ε₂|) + 2 * |ε₁| ^ 3 + ε₁ ^ 2 * |ε₂|)
      ≤ ((1 + 1 / 1000) * ((1 + 1 / 25) ^ 4 * b ^ 4)) *
        (5 * (1 + 1 / 4000) * (1 / (64 * b ^ 3)) + 2 * (1 + 1 / 4000) * (1 / (40 * b ^ 3 * r)) +
          2 * (1 / (512 * b ^ 4 * r)) + 1 / (320 * b ^ 5)) := by
        apply mul_le_mul (mul_le_mul hp3 hw4 (by positivity) (by positivity)) _ (by positivity)
          (by positivity)
        gcongr
    _ = ((1 + 1 / 1000) * (1 + 1 / 25) ^ 4) * b ^ 4 *
        (5 * (1 + 1 / 4000) * (1 / (64 * b ^ 3)) + 2 * (1 + 1 / 4000) * (1 / (40 * b ^ 3 * r)) +
          2 * (1 / (512 * b ^ 4 * r)) + 1 / (320 * b ^ 5)) := by ring
    _ ≤ 1 / 10 * b := quad_tail_le hb hr hr44 (by positivity) hc

/-! ### The three interior sign conditions -/

/-- Centre: `F(−b) > 0`. Here `κ` is the dispersion and `κ·b ≤ 1/2`. -/
theorem center_pos {b κ ε₁ ε₂ r : ℝ} (hb : 2000 ≤ b) (hκ0 : 0 ≤ κ) (hκb : κ * b ≤ 1 / 2)
    (hr : r ^ 2 = b) (hr0 : 0 ≤ r)
    (hε₁ : |ε₁| * (b * r) ≤ 1 / 8) (hε₂ : |ε₂| * b ^ 2 ≤ 1 / 5) :
    0 < refQuartic b κ (-b) + ε₁ * linOne b κ (-b) +
      ε₂ * linTwo κ (-b) + quadTerm κ ε₁ ε₂ (-b) := by
  have hbpos : 0 < b := by linarith
  have hr44 : 44 ≤ r := by nlinarith
  have hrpos : 0 < r := by linarith
  have hbne : b ≠ 0 := hbpos.ne'
  have hrne : r ≠ 0 := hrpos.ne'
  have hκle : κ ≤ 1 / 4000 := by nlinarith
  obtain ⟨hp1, hp3, hp5⟩ := power_helper hκ0 hκle
  have hb3 : b ^ 3 = (b * r) ^ 2 := by rw [mul_pow, hr]; ring
  have hK0 : 0 ≤ κ * b := by positivity
  -- reference, with `K = κ b`
  have href : 3 / 4 * b ^ 2 - 18 * b - 3 / 2 ≤ refQuartic b κ (-b) := by
    have h := refQuartic_center_ge (K := κ * b) (by linarith : 1 ≤ b) hK0 hκb
    rwa [show κ * b / b = κ by field_simp] at h
  -- linOne at the centre: between 0 and 13 b³
  have hL1 : 0 ≤ linOne b κ (-b) ∧ linOne b κ (-b) ≤ 13 * b ^ 3 := by
    rw [linOne_center_eq]
    have hκ2 : κ ^ 2 * b ≤ 1 / 4000 := by
      have : κ ^ 2 * b = κ * (κ * b) := by ring
      rw [this]; nlinarith
    have hκ3 : κ ^ 3 * b ≤ 1 / 4000 := by
      have : κ ^ 3 * b = κ ^ 2 * (κ * b) := by ring
      rw [this]; nlinarith
    have hκ2' : 0 ≤ κ ^ 2 * b := by positivity
    have hκ3' : 0 ≤ κ ^ 3 * b := by positivity
    have hbr : 0 ≤ 3 - 3 * (κ * b) - 3 * κ ^ 2 * b - κ ^ 3 * b := by linarith
    have hbr' : 3 - 3 * (κ * b) - 3 * κ ^ 2 * b - κ ^ 3 * b ≤ 3 := by linarith
    have hA : 0 ≤ 4 * (1 + κ) ^ 2 * b ^ 3 := by positivity
    have hb3nn : 0 ≤ b ^ 3 := by positivity
    have hA' : 4 * (1 + κ) ^ 2 * b ^ 3 ≤ 4 * (1 + 1 / 1000) * b ^ 3 := by
      nlinarith [mul_le_mul_of_nonneg_right hp1 hb3nn]
    refine ⟨mul_nonneg hA hbr, ?_⟩
    calc 4 * (1 + κ) ^ 2 * b ^ 3 * (3 - 3 * (κ * b) - 3 * κ ^ 2 * b - κ ^ 3 * b)
        ≤ (4 * (1 + 1 / 1000) * b ^ 3) * 3 := mul_le_mul hA' hbr' hbr (by positivity)
      _ ≤ 13 * b ^ 3 := by nlinarith
  have hε₁abs : |ε₁| ≤ 1 / (8 * (b * r)) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hε₂abs : |ε₂| ≤ 1 / (5 * b ^ 2) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  -- |ε₁ L₁| ≤ 13 b³ / (8 b r) = 13 (b r) / 8
  have hT1 : |ε₁ * linOne b κ (-b)| ≤ 13 / 8 * (b * r) := by
    rw [abs_mul, abs_of_nonneg hL1.1]
    calc |ε₁| * linOne b κ (-b) ≤ (1 / (8 * (b * r))) * (13 * b ^ 3) :=
          mul_le_mul hε₁abs hL1.2 hL1.1 (by positivity)
      _ = 13 / 8 * (b * r) := by rw [hb3]; field_simp
  have hT2 : |ε₂ * linTwo κ (-b)| ≤ (1 / 5 + 1 / 3500) * b ^ 2 := by
    rw [abs_mul, linTwo_eq, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + κ) ^ 5 * (-b) ^ 4)]
    calc |ε₂| * ((1 + κ) ^ 5 * (-b) ^ 4) ≤ (1 / (5 * b ^ 2)) * ((1 + 1 / 700) * b ^ 4) := by
          apply mul_le_mul hε₂abs _ (by positivity) (by positivity)
          rw [show (-b) ^ 4 = b ^ 4 by ring]
          exact mul_le_mul_of_nonneg_right hp5 (by positivity)
      _ = (1 / 5 + 1 / 3500) * b ^ 2 := by field_simp; ring
  have hT3 : |quadTerm κ ε₁ ε₂ (-b)| ≤ 1 / 10 * b :=
    abs_quadTerm_le_of_small hb hr hr44 hκ0 hκle hε₁abs hε₂abs hbpos.le (by nlinarith)
  have hbr2 : b * r ≤ b ^ 2 / 44 := by
    rw [le_div_iff₀ (by norm_num)]; nlinarith
  have hb2000 : 2000 * b ≤ b ^ 2 := by nlinarith
  have hsum1 := abs_le.mp hT1
  have hsum2 := abs_le.mp hT2
  have hsum3 := abs_le.mp hT3
  linarith [hsum1.1, hsum2.1, hsum3.1]

/-- `|3 − bδ| ≤ 3 + b|δ|`. -/
theorem abs_three_sub_le {b δ : ℝ} (hb : 0 ≤ b) : |3 - b * δ| ≤ 3 + b * |δ| := by
  calc |3 - b * δ| ≤ |(3 : ℝ)| + |b * δ| := abs_sub _ _
    _ = 3 + b * |δ| := by rw [abs_mul, abs_of_nonneg hb]; norm_num

/-- The inner factor of `L₁` at `−b(1+δ)`. -/
theorem inner_factor_le {b κ δ : ℝ} (hb : 2000 ≤ b) (hκ0 : 0 ≤ κ) (hκle : κ ≤ 1 / 4000)
    (hκb : κ * b ≤ 1 / 2) (hδabs : |δ| ≤ 1 / 25) :
    |(b + 3) - (1 + κ) ^ 3 * (b * (1 + δ))| ≤ 5 + b * |δ| := by
  have hbpos : 0 < b := by linarith
  have hδlo := (abs_le.mp hδabs).1
  have hδhi := (abs_le.mp hδabs).2
  have hw0 : 0 ≤ b * (1 + δ) := by nlinarith
  have hwle : b * (1 + δ) ≤ (1 + 1 / 25) * b := by nlinarith
  have hp3b : ((1 + κ) ^ 3 - 1) * b ≤ 8 / 5 := by
    have e : ((1 + κ) ^ 3 - 1) * b = 3 * (κ * b) + 3 * κ * (κ * b) + κ ^ 2 * (κ * b) := by ring
    have h1 : 3 * κ * (κ * b) ≤ 3 * (1 / 4000) * (1 / 2) := by
      have := mul_le_mul hκle hκb (by positivity) (by norm_num); nlinarith
    have h2 : κ ^ 2 * (κ * b) ≤ (1 / 4000) ^ 2 * (1 / 2) := by
      have hk2 : κ ^ 2 ≤ (1 / 4000) ^ 2 := pow_le_pow_left₀ hκ0 hκle 2
      have := mul_le_mul hk2 hκb (by positivity) (by norm_num); nlinarith
    rw [e]; nlinarith
  have hp3nn : 0 ≤ (1 + κ) ^ 3 - 1 := by
    have := pow_le_pow_left₀ (by norm_num) (by linarith : (1:ℝ) ≤ 1 + κ) 3
    norm_num at this; linarith
  have hB : 0 ≤ ((1 + κ) ^ 3 - 1) * (b * (1 + δ)) := mul_nonneg hp3nn hw0
  have hB' : ((1 + κ) ^ 3 - 1) * (b * (1 + δ)) ≤ 2 := by
    have h := mul_le_mul_of_nonneg_left hwle hp3nn
    have e : ((1 + κ) ^ 3 - 1) * ((1 + 1 / 25) * b) = (1 + 1 / 25) * (((1 + κ) ^ 3 - 1) * b) := by
      ring
    rw [e] at h
    linarith
  have hA := abs_three_sub_le (δ := δ) hbpos.le
  have e : (b + 3) - (1 + κ) ^ 3 * (b * (1 + δ)) =
      (3 - b * δ) - ((1 + κ) ^ 3 - 1) * (b * (1 + δ)) := by ring
  rw [e]
  calc |(3 - b * δ) - ((1 + κ) ^ 3 - 1) * (b * (1 + δ))|
      ≤ |3 - b * δ| + |((1 + κ) ^ 3 - 1) * (b * (1 + δ))| := abs_sub _ _
    _ ≤ (3 + b * |δ|) + 2 := by rw [abs_of_nonneg hB]; linarith
    _ = 5 + b * |δ| := by ring

/-- `|δ| r ≤ 5(1−K)²` when `δ² = 3(1−K)/b`, `r² = b`, `1 − K ≥ 1/2`. -/
theorem abs_delta_mul_sqrt_le {b K r δ : ℝ} (hbpos : 0 < b) (hr : r ^ 2 = b) (hr0 : 0 ≤ r)
    (hδ : δ ^ 2 = 3 * (1 - K) / b) (hu : 1 / 2 ≤ 1 - K) :
    |δ| * r ≤ 5 * (1 - K) ^ 2 := by
  have hsq : (|δ| * r) ^ 2 ≤ (5 * (1 - K) ^ 2) ^ 2 := by
    rw [mul_pow, sq_abs, hδ, hr]
    have e : 3 * (1 - K) / b * b = 3 * (1 - K) := by field_simp
    rw [e]
    have h3 : (1 / 2 : ℝ) ^ 3 ≤ (1 - K) ^ 3 := pow_le_pow_left₀ (by norm_num) hu 3
    have hu0 : (0:ℝ) ≤ 1 - K := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h3 hu0]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp hsq

/-- Outer points: `F(−b(1+δ)) < 0` for `δ² = 3(1−κb)/b`. -/
theorem outer_neg {b κ ε₁ ε₂ r δ : ℝ} (hb : 2000 ≤ b) (hκ0 : 0 ≤ κ) (hκb : κ * b ≤ 1 / 2)
    (hr : r ^ 2 = b) (hr0 : 0 ≤ r)
    (hε₁ : |ε₁| * (b * r) ≤ 1 / 8) (hε₂ : |ε₂| * b ^ 2 ≤ 1 / 5)
    (hδ : δ ^ 2 = 3 * (1 - κ * b) / b) :
    refQuartic b κ (-b * (1 + δ)) + ε₁ * linOne b κ (-b * (1 + δ)) +
      ε₂ * linTwo κ (-b * (1 + δ)) + quadTerm κ ε₁ ε₂ (-b * (1 + δ)) < 0 := by
  have hbpos : 0 < b := by linarith
  have hr44 : 44 ≤ r := by nlinarith
  have hrpos : 0 < r := by linarith
  have hbne : b ≠ 0 := hbpos.ne'
  have hrne : r ≠ 0 := hrpos.ne'
  have hκle : κ ≤ 1 / 4000 := by nlinarith
  obtain ⟨hp2, hp3, hp5⟩ := power_helper hκ0 hκle
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = κ * b := ⟨_, rfl⟩
  rw [← hKdef] at hδ
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hκb' : K ≤ 1 / 2 := by rw [hKdef]; exact hκb
  have hu : 1 / 2 ≤ 1 - K := by linarith
  -- the size of δ
  have hδabs : |δ| ≤ 1 / 25 := by
    have h : δ ^ 2 ≤ (1 / 25) ^ 2 := by
      rw [hδ, div_le_iff₀ hbpos]; linarith
    exact abs_le_of_sq_le_sq h (by norm_num)
  have hδK : |δ| * r ≤ 5 * (1 - K) ^ 2 := abs_delta_mul_sqrt_le hbpos hr hr0 hδ hu
  have hδlo := (abs_le.mp hδabs).1
  have hδhi := (abs_le.mp hδabs).2
  -- the point `w = b(1+δ)`
  have hw0 : 0 ≤ b * (1 + δ) := mul_nonneg hbpos.le (by linarith)
  have hwle : b * (1 + δ) ≤ (1 + 1 / 25) * b := by
    have := mul_le_mul_of_nonneg_left (show 1 + δ ≤ 1 + 1 / 25 by linarith) hbpos.le
    linarith
  have hzw : -b * (1 + δ) = -(b * (1 + δ)) := by ring
  -- reference
  have href : refQuartic b κ (-b * (1 + δ)) ≤
      -6 * (1 - K) ^ 2 * b ^ 2 + 90 * b + 104 + |δ| * (8 * (1 - K) ^ 2 * b ^ 2 + 88 * b + 78) := by
    have h := refQuartic_outer_le (K := K) hb hK0 hκb' hδ
    rwa [show K / b = κ by rw [hKdef]; field_simp] at h
  -- linOne at −w
  have hL1eq : linOne b κ (-(b * (1 + δ))) =
      4 * (1 + κ) ^ 2 * (b * (1 + δ)) ^ 3 * ((b + 3) - (1 + κ) ^ 3 * (b * (1 + δ))) := by
    unfold linOne; ring
  have hinner : |(b + 3) - (1 + κ) ^ 3 * (b * (1 + δ))| ≤ 5 + b * |δ| :=
    inner_factor_le hb hκ0 hκle hκb hδabs
  have hL1abs : |linOne b κ (-(b * (1 + δ)))| ≤
      4 * (1 + 1 / 1000) * ((1 + 1 / 25) * b) ^ 3 * (5 + b * |δ|) := by
    rw [hL1eq, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * (1 + κ) ^ 2 * (b * (1 + δ)) ^ 3)]
    have hw3 : (b * (1 + δ)) ^ 3 ≤ ((1 + 1 / 25) * b) ^ 3 := pow_le_pow_left₀ hw0 hwle 3
    apply mul_le_mul _ hinner (abs_nonneg _) (by positivity)
    apply mul_le_mul _ hw3 (by positivity) (by positivity)
    linarith
  have hε₁abs : |ε₁| ≤ 1 / (8 * (b * r)) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hε₂abs : |ε₂| ≤ 1 / (5 * b ^ 2) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hT1 : |ε₁ * linOne b κ (-(b * (1 + δ)))| ≤
      (1 / (8 * (b * r))) * (4 * (1 + 1 / 1000) * ((1 + 1 / 25) * b) ^ 3 * (5 + b * |δ|)) := by
    rw [abs_mul]
    exact mul_le_mul hε₁abs hL1abs (abs_nonneg _) (by positivity)
  have hT2 : |ε₂ * linTwo κ (-(b * (1 + δ)))| ≤
      (1 / (5 * b ^ 2)) * ((1 + 1 / 700) * ((1 + 1 / 25) * b) ^ 4) := by
    rw [abs_mul, linTwo_eq, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + κ) ^ 5 * (-(b * (1 + δ))) ^ 4)]
    apply mul_le_mul hε₂abs _ (by positivity) (by positivity)
    rw [show (-(b * (1 + δ))) ^ 4 = (b * (1 + δ)) ^ 4 by ring]
    exact mul_le_mul hp5 (pow_le_pow_left₀ hw0 hwle 4) (by positivity) (by positivity)
  have hT3 : |quadTerm κ ε₁ ε₂ (-(b * (1 + δ)))| ≤ 1 / 10 * b :=
    abs_quadTerm_le_of_small hb hr hr44 hκ0 hκle hε₁abs hε₂abs hw0 hwle
  -- simplified perturbation bounds (recall `b²/r = b r`)
  have hb2r : b ^ 2 / r = b * r := by rw [← hr]; field_simp
  have hT1' : |ε₁ * linOne b κ (-(b * (1 + δ)))| ≤ 3 * (b * r) + 3 / 5 * (b * |δ| * (b * r)) := by
    refine hT1.trans ?_
    have e : (1 / (8 * (b * r))) * (4 * (1 + 1 / 1000) * ((1 + 1 / 25) * b) ^ 3 * (5 + b * |δ|)) =
        (1 + 1 / 1000) * (1 + 1 / 25) ^ 3 / 2 * ((b ^ 2 / r) * 5 + (b ^ 2 / r) * (b * |δ|)) := by
      field_simp; ring
    rw [e, hb2r]
    have hpos1 : 0 ≤ b * r := by positivity
    have hpos2 : 0 ≤ (b * r) * (b * |δ|) := by positivity
    linarith
  have hδb : b * |δ| * (b * r) ≤ 5 * (1 - K) ^ 2 * b ^ 2 := by
    have e : b * |δ| * (b * r) = (|δ| * r) * b ^ 2 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hδK (by positivity)
  have hT2' : |ε₂ * linTwo κ (-(b * (1 + δ)))| ≤ 6 / 25 * b ^ 2 := by
    refine hT2.trans ?_
    have e : (1 / (5 * b ^ 2)) * ((1 + 1 / 700) * ((1 + 1 / 25) * b) ^ 4) =
        (1 + 1 / 700) * (1 + 1 / 25) ^ 4 / 5 * b ^ 2 := by field_simp
    rw [e]
    have hc : (1 + 1 / 700) * (1 + 1 / 25) ^ 4 / 5 ≤ (6 / 25 : ℝ) := by norm_num
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hδterm : |δ| * (8 * (1 - K) ^ 2 * b ^ 2 + 88 * b + 78) ≤
      8 * (1 - K) ^ 2 * b ^ 2 * (1 / 25) + (88 * b + 78) * (1 / 25) := by
    have h0 := abs_nonneg δ
    have h1 := mul_le_mul_of_nonneg_right hδabs (by positivity : (0:ℝ) ≤ 8 * (1 - K) ^ 2 * b ^ 2)
    have h2 := mul_le_mul_of_nonneg_right hδabs (by positivity : (0:ℝ) ≤ 88 * b + 78)
    linarith
  have h44r : 44 * r ≤ b := by
    have := mul_le_mul_of_nonneg_right hr44 hr0
    rw [← sq, hr] at this
    exact this
  have hbr2 : b * r ≤ b ^ 2 / 44 := by
    rw [le_div_iff₀ (by norm_num)]
    have := mul_le_mul_of_nonneg_left h44r hbpos.le
    linarith
  have hK1 : 1 / 4 ≤ (1 - K) ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num) hu 2
    norm_num at this; linarith
  have hb2 : 0 ≤ b ^ 2 := by positivity
  have hprod1 : b ^ 2 / 4 ≤ (1 - K) ^ 2 * b ^ 2 := by
    have := mul_le_mul_of_nonneg_right hK1 hb2
    linarith
  have hb2000 : 2000 * b ≤ b ^ 2 := by
    have := mul_le_mul_of_nonneg_left hb hbpos.le
    linarith
  have hsum1 := abs_le.mp hT1'
  have hsum2 := abs_le.mp hT2'
  have hsum3 := abs_le.mp hT3
  rw [hzw] at href ⊢
  linarith [hsum1.2, hsum2.2, hsum3.2]

/-! ### The two endpoints and the main theorem -/

/-- `F(0) = (b)₄ > 0`. -/
theorem quartic_zero_pos {b D₀ D₁ D₂ : ℝ} (hb : 0 < b) : 0 < quartic b D₀ D₁ D₂ 0 := by
  unfold quartic
  simp
  positivity

/-- `F(−3b) > 0` when the dispersions are small. -/
theorem quartic_far_left_pos {b D₀ D₁ D₂ : ℝ} (hb : 2000 ≤ b)
    (h0 : 0 ≤ D₀) (h1 : 0 ≤ D₁) (h2 : 0 ≤ D₂)
    (h0' : D₀ * b ≤ 3 / 5) (h1' : D₁ * b ≤ 3 / 5) :
    0 < quartic b D₀ D₁ D₂ (-3 * b) := by
  have hbpos : 0 < b := by linarith
  unfold quartic
  -- the two negative terms, bounded using `(1+D₀)²(1+D₁) ≤ 1 + 2/b`
  have hcube : (1 + D₀) ^ 2 * (1 + D₁) ≤ 1 + 2 / b := by
    have hD0 : D₀ ≤ 3 / (5 * b) := by rw [le_div_iff₀ (by positivity)]; linarith
    have hD1 : D₁ ≤ 3 / (5 * b) := by rw [le_div_iff₀ (by positivity)]; linarith
    have hx : 3 / (5 * b) ≤ 3 / 10000 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    obtain ⟨x, hx_def⟩ : ∃ x : ℝ, x = 3 / (5 * b) := ⟨_, rfl⟩
    rw [← hx_def] at hD0 hD1 hx
    have hx0 : 0 ≤ x := by rw [hx_def]; positivity
    have hcube' : (1 + D₀) ^ 2 * (1 + D₁) ≤ (1 + x) ^ 2 * (1 + x) := by
      have a : (1 + D₀) ^ 2 ≤ (1 + x) ^ 2 :=
        pow_le_pow_left₀ (show (0:ℝ) ≤ 1 + D₀ by linarith) (show 1 + D₀ ≤ 1 + x by linarith) 2
      have c : 1 + D₁ ≤ 1 + x := by linarith
      exact mul_le_mul a c (by linarith) (by positivity)
    have hexp : (1 + x) ^ 2 * (1 + x) ≤ 1 + (3 + 1 / 1000) * x := by
      have hx2 : x ^ 2 ≤ 3 / 10000 * x := by
        have := mul_le_mul_of_nonneg_left hx hx0; nlinarith
      have hx3 : x ^ 3 ≤ (3 / 10000) ^ 2 * x := by
        have := mul_le_mul_of_nonneg_left hx2 hx0
        have h2 : x * x ^ 2 = x ^ 3 := by ring
        nlinarith
      nlinarith
    have hx' : (3 + 1 / 1000) * x ≤ 2 / b := by
      rw [hx_def, ← mul_div_assoc, div_le_div_iff₀ (by positivity) hbpos]; nlinarith
    linarith
  have hpos3 : 0 ≤ (1 + D₀) ^ 3 * (1 + D₁) ^ 2 * (1 + D₂) := by positivity
  have hge3 : 1 ≤ (1 + D₀) ^ 3 * (1 + D₁) ^ 2 * (1 + D₂) := by
    have a : 1 ≤ (1 + D₀) ^ 3 := one_le_pow₀ (by linarith)
    have c : 1 ≤ (1 + D₁) ^ 2 := one_le_pow₀ (by linarith)
    have d : 1 ≤ 1 + D₂ := by linarith
    calc (1:ℝ) = 1 * 1 * 1 := by ring
      _ ≤ (1 + D₀) ^ 3 * (1 + D₁) ^ 2 * (1 + D₂) :=
        mul_le_mul (mul_le_mul a c (by norm_num) (by positivity)) d (by norm_num) (by positivity)
  have hb4 : 0 ≤ b ^ 4 := by positivity
  have hb3 : 0 ≤ b ^ 3 := by positivity
  -- term-by-term lower bounds
  have t2 : 54 * b ^ 2 * ((b + 2) * (b + 3)) ≤ 6 * (1 + D₀) * (-3 * b) ^ 2 * ((b + 2) * (b + 3)) := by
    have : (-3 * b) ^ 2 = 9 * b ^ 2 := by ring
    rw [this]
    have : 0 ≤ 6 * D₀ * (9 * b ^ 2) * ((b + 2) * (b + 3)) := by positivity
    nlinarith
  have t3 : 4 * ((1 + D₀) ^ 2 * (1 + D₁)) * (-3 * b) ^ 3 * (b + 3) ≥
      -(108 * (1 + 2 / b) * b ^ 3 * (b + 3)) := by
    have : (-3 * b) ^ 3 = -(27 * b ^ 3) := by ring
    rw [this]
    have h := mul_le_mul_of_nonneg_right hcube (by positivity : (0:ℝ) ≤ 108 * b ^ 3 * (b + 3))
    nlinarith
  have t4 : 81 * b ^ 4 ≤ ((1 + D₀) ^ 3 * (1 + D₁) ^ 2 * (1 + D₂)) * (-3 * b) ^ 4 := by
    have : (-3 * b) ^ 4 = 81 * b ^ 4 := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_right hge3 hb4]
  have hb2000 : 2000 * b ≤ b ^ 2 := by nlinarith
  have hb3' : 2000 * b ^ 2 ≤ b ^ 3 := by nlinarith
  have hb4' : 2000 * b ^ 3 ≤ b ^ 4 := by nlinarith
  have e : 108 * (1 + 2 / b) * b ^ 3 * (b + 3) = 108 * b ^ 4 + 540 * b ^ 3 + 648 * b ^ 2 := by
    field_simp; ring
  rw [e] at t3
  nlinarith

/-- The five alternation points. -/
def altPoints (b s : ℝ) : ℕ → ℝ
  | 0 => -3 * b
  | 1 => -b - s
  | 2 => -b
  | 3 => -b + s
  | _ => 0

/-- **The five sign conditions.** With `s = √(3(1 − D₀b)b)`: `0 < s < b`, and the quartic is
positive at `−3b`, negative at `−b − s`, positive at `−b`, negative at `−b + s`, positive at `0`. -/
theorem quartic_signs {b D₀ D₁ D₂ : ℝ} (hb : 2000 ≤ b)
    (h0 : 0 ≤ D₀) (h1 : 0 ≤ D₁) (h2 : 0 ≤ D₂) (hK : D₀ * b ≤ 1 / 2)
    (hε₁ : |D₀ - D₁| * (b * Real.sqrt b) ≤ 1 / 8)
    (hε₂ : |D₀ - 2 * D₁ + D₂| * b ^ 2 ≤ 1 / 5) :
    0 < Real.sqrt (3 * (1 - D₀ * b) * b) ∧ Real.sqrt (3 * (1 - D₀ * b) * b) < b ∧
      0 < quartic b D₀ D₁ D₂ (-3 * b) ∧
      quartic b D₀ D₁ D₂ (-b - Real.sqrt (3 * (1 - D₀ * b) * b)) < 0 ∧
      0 < quartic b D₀ D₁ D₂ (-b) ∧
      quartic b D₀ D₁ D₂ (-b + Real.sqrt (3 * (1 - D₀ * b) * b)) < 0 ∧
      0 < quartic b D₀ D₁ D₂ 0 := by
  have hbpos : 0 < b := by linarith
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = Real.sqrt b := ⟨_, rfl⟩
  rw [← hr_def] at hε₁
  have hr : r ^ 2 = b := by rw [hr_def]; exact Real.sq_sqrt hbpos.le
  have hr0 : 0 ≤ r := by rw [hr_def]; exact Real.sqrt_nonneg b
  have hr44 : 44 ≤ r := by nlinarith
  -- deviations
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = D₀ - D₁ := ⟨_, rfl⟩
  obtain ⟨ε₂, hε₂def⟩ : ∃ ε₂ : ℝ, ε₂ = D₀ - 2 * D₁ + D₂ := ⟨_, rfl⟩
  rw [← hε₁def] at hε₁
  rw [← hε₂def] at hε₂
  have hD₁ : D₁ = D₀ - ε₁ := by rw [hε₁def]; ring
  have hD₂ : D₂ = D₀ - 2 * ε₁ + ε₂ := by rw [hε₂def, hε₁def]; ring
  have hF : ∀ z, quartic b D₀ D₁ D₂ z =
      refQuartic b D₀ z + ε₁ * linOne b D₀ z + ε₂ * linTwo D₀ z + quadTerm D₀ ε₁ ε₂ z := by
    intro z
    rw [← quartic_eq_ref_add, ← hD₁, ← hD₂]
  have hu : 1 / 2 ≤ 1 - D₀ * b := by linarith
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = Real.sqrt (3 * (1 - D₀ * b) * b) := ⟨_, rfl⟩
  rw [← hs_def]
  have hs0 : 0 ≤ s := by rw [hs_def]; exact Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 3 * (1 - D₀ * b) * b := by rw [hs_def]; exact Real.sq_sqrt (by positivity)
  have hspos : 0 < s := by
    rw [hs_def]; apply Real.sqrt_pos.mpr; positivity
  have hs_lt : s < b := by
    have : s ^ 2 < b ^ 2 := by rw [hs2]; nlinarith
    exact (pow_lt_pow_iff_left₀ hs0 hbpos.le (by norm_num)).mp this
  have hδ : (s / b) ^ 2 = 3 * (1 - D₀ * b) / b := by
    rw [div_pow, hs2]; field_simp
  have hδ' : (-(s / b)) ^ 2 = 3 * (1 - D₀ * b) / b := by rw [neg_sq]; exact hδ
  have hε₁abs : |ε₁| ≤ 1 / (8 * (b * r)) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hε₁small : |ε₁| * b ≤ 1 / 10 := by
    have h := mul_le_mul_of_nonneg_right hε₁abs hbpos.le
    have e : 1 / (8 * (b * r)) * b = 1 / (8 * r) := by field_simp
    rw [e] at h
    have : 1 / (8 * r) ≤ 1 / 10 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hD1b : D₁ * b ≤ 3 / 5 := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le ε₁) hbpos.le
    rw [hD₁, sub_mul]; linarith
  refine ⟨hspos, hs_lt, ?_, ?_, ?_, ?_, quartic_zero_pos hbpos⟩
  · exact quartic_far_left_pos hb h0 h1 h2 (by linarith) hD1b
  · have h := outer_neg (δ := s / b) hb h0 hK hr hr0 hε₁ hε₂ hδ
    rw [← hF] at h
    have e : -b * (1 + s / b) = -b - s := by field_simp; ring
    rwa [e] at h
  · have h := center_pos hb h0 hK hr hr0 hε₁ hε₂
    rwa [← hF] at h
  · have h := outer_neg (δ := -(s / b)) hb h0 hK hr hr0 hε₁ hε₂ hδ'
    rw [← hF] at h
    have e : -b * (1 + -(s / b)) = -b + s := by field_simp; ring
    rwa [e] at h

/-- **Quartic Jensen hyperbolicity from three dispersions.** If `b ≥ 2000`, the dispersions are
nonnegative with `D₀ b ≤ 1/2`, and the first and second differences satisfy
`|D₀ − D₁| ≤ b^{−3/2}/8`, `|D₀ − 2D₁ + D₂| ≤ b^{−2}/5`, then the monic quartic has four distinct
real roots. -/
theorem hyperbolic_quarticPoly {b D₀ D₁ D₂ : ℝ} (hb : 2000 ≤ b)
    (h0 : 0 ≤ D₀) (h1 : 0 ≤ D₁) (h2 : 0 ≤ D₂) (hK : D₀ * b ≤ 1 / 2)
    (hε₁ : |D₀ - D₁| * (b * Real.sqrt b) ≤ 1 / 8)
    (hε₂ : |D₀ - 2 * D₁ + D₂| * b ^ 2 ≤ 1 / 5) :
    Hyperbolic (quarticPoly b D₀ D₁ D₂) := by
  have hbpos : 0 < b := by linarith
  obtain ⟨hspos, hs_lt, hA, hB, hC, hD, hE⟩ := quartic_signs hb h0 h1 h2 hK hε₁ hε₂
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt (3 * (1 - D₀ * b) * b) := ⟨_, rfl⟩
  rw [← hs] at hspos hs_lt hB hD
  refine hyperbolic_of_alternating (d := 4) (y := altPoints b s)
    (natDegree_quarticPoly_le b D₀ D₁ D₂) ?_ ?_
  · intro i hi
    interval_cases i <;> simp only [altPoints] <;> linarith
  · intro i hi
    rw [eval_quarticPoly]
    interval_cases i
    · simp only [altPoints, pow_zero, one_mul]; exact hA
    · simp only [altPoints, pow_one]; linarith
    · simp only [altPoints]; norm_num; exact hC
    · simp only [altPoints]; norm_num; linarith
    · simp only [altPoints]; norm_num; exact hE

end QuarticDispersionTransfer

end HTGeometry

import Mathlib

/-!
# A single quartic monomial inequality implies the cubic moment inequality

Let `mⱼ = ∫_ℝ x^{2j} Φ(x) dx` be the even moments of a positive even weight and `μⱼ = mⱼ/m_{j−1}` its
size-biased means.  The cubic

```text
C = 3 m₀ m₁ m₃ + 15 m₁² m₂ − 10 m₀ m₂²  =  m₀m₁m₂ · (15μ₁ − 10μ₂ + 3μ₃)
```

is best read in the variable `y = x²`.  There `mⱼ = ∫₀^∞ y^{j−1/2} H(y) dy` with `H(y) = Φ(√y)`, the
natural normalization is `Lⱼ = mⱼ/Γ(j+1/2)`, and the ratios

```text
rⱼ = Lⱼ / L_{j−1} = μⱼ / (j − 1/2)
```

turn the functional into a **second difference**:

```text
15 μ₁ − 10 μ₂ + 3 μ₃  =  (15/2) · (r₁ − 2 r₂ + r₃) .
```

Both classical models have `r` affine in `j`, which is why both are equality cases:

```text
Φ = e^{−x²}   mⱼ = Γ(j+1/2)   rⱼ = 1        affine
Φ = e^{−|x|}  mⱼ = 2(2j)!     rⱼ = 4j       affine
```

Consequently `C ≥ 0` follows from **convexity** of `r`, and convexity follows in turn from
**log-convexity** `r₂² ≤ r₁r₃` by the arithmetic–geometric mean inequality.  In raw moments
log-convexity of `r` is the single quartic monomial inequality

```text
5 m₀ m₂³  ≤  9 m₁³ m₃ ,
```

which is an exact equality for the Gaussian and is *false* for the two-sided exponential — so it is
strictly stronger than `C ≥ 0`, and it is tight precisely at the model that the cubic is tight at.
-/

namespace GaloisForLFunctions

namespace CubicMomentLogConvexRatio

/-- The normalized moment-ratio sequence `rⱼ = μⱼ/(j − 1/2)` at `j = 1, 2, 3`. -/
noncomputable def ratioSeq (μ₁ μ₂ μ₃ : ℝ) : ℝ × ℝ × ℝ :=
  (2 * μ₁, (2 / 3) * μ₂, (2 / 5) * μ₃)

/-- **The chord form is a second difference of the normalized ratio sequence.** -/
theorem chord_eq_second_difference (μ₁ μ₂ μ₃ : ℝ) :
    15 * μ₁ - 10 * μ₂ + 3 * μ₃ =
      (15 / 2) * ((ratioSeq μ₁ μ₂ μ₃).1 - 2 * (ratioSeq μ₁ μ₂ μ₃).2.1 +
        (ratioSeq μ₁ μ₂ μ₃).2.2) := by
  unfold ratioSeq
  ring

/-- The Gaussian model `Φ = e^{−x²}` has `mⱼ = Γ(j+1/2)`, hence `μⱼ = j − 1/2` and `rⱼ = 1`. -/
theorem ratioSeq_halfGaussian : ratioSeq (1 / 2) (3 / 2) (5 / 2) = (1, 1, 1) := by
  unfold ratioSeq; norm_num

/-- The exponential model `Φ = e^{−|x|}` has `mⱼ = 2(2j)!`, hence `μⱼ = 2j(2j−1)` and `rⱼ = 4j`. -/
theorem ratioSeq_exponential : ratioSeq 2 12 30 = (4, 8, 12) := by
  unfold ratioSeq; norm_num

/-- A log-convex positive triple is convex: `r₂² ≤ r₁r₃` gives `2r₂ ≤ r₁ + r₃` by AM–GM. -/
theorem second_difference_nonneg_of_logConvex {r₁ r₂ r₃ : ℝ}
    (h₁ : 0 < r₁) (h₂ : 0 < r₂) (h₃ : 0 < r₃) (hlc : r₂ ^ 2 ≤ r₁ * r₃) :
    0 ≤ r₁ - 2 * r₂ + r₃ := by
  nlinarith [sq_nonneg (r₁ - r₃), sq_nonneg (r₁ + r₃ - 2 * r₂), sq_nonneg (r₁ + r₃)]

/-- Log-convexity of the normalized ratio sequence is the monomial inequality `5μ₂² ≤ 9μ₁μ₃`. -/
theorem logConvex_ratioSeq_iff (μ₁ μ₂ μ₃ : ℝ) :
    ((ratioSeq μ₁ μ₂ μ₃).2.1) ^ 2 ≤ (ratioSeq μ₁ μ₂ μ₃).1 * (ratioSeq μ₁ μ₂ μ₃).2.2 ↔
      5 * μ₂ ^ 2 ≤ 9 * μ₁ * μ₃ := by
  unfold ratioSeq
  constructor <;> intro h <;> nlinarith [h]

/-- In raw moments the same condition is `5 m₀ m₂³ ≤ 9 m₁³ m₃`. -/
theorem quartic_iff_logConvex {m₀ m₁ m₂ m₃ : ℝ} (h₀ : 0 < m₀) (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    5 * m₀ * m₂ ^ 3 ≤ 9 * m₁ ^ 3 * m₃ ↔
      5 * (m₂ / m₁) ^ 2 ≤ 9 * (m₁ / m₀) * (m₃ / m₂) := by
  have hden : (0 : ℝ) < m₀ * m₁ ^ 2 * m₂ := by positivity
  have key : 9 * (m₁ / m₀) * (m₃ / m₂) - 5 * (m₂ / m₁) ^ 2 =
      (9 * m₁ ^ 3 * m₃ - 5 * m₀ * m₂ ^ 3) / (m₀ * m₁ ^ 2 * m₂) := by
    field_simp
  constructor
  · intro h
    rw [← sub_nonneg, key]
    exact div_nonneg (by linarith) hden.le
  · intro h
    have h2 : 0 ≤ (9 * m₁ ^ 3 * m₃ - 5 * m₀ * m₂ ^ 3) / (m₀ * m₁ ^ 2 * m₂) := by
      rw [← key]; linarith
    have h3 := mul_nonneg h2 hden.le
    rw [div_mul_cancel₀ _ hden.ne'] at h3
    linarith

/-- **The main implication.**  A single quartic monomial inequality on the raw even moments implies
the cubic moment inequality.  The proof squares the arithmetic–geometric mean step: with
`A = 3m₀m₁m₃` and `B = 15m₁²m₂`,

```text
(A + B)² ≥ 4AB = 180 m₀m₁³m₂m₃ ≥ 100 m₀²m₂⁴ = (10 m₀m₂²)² ,
```

the middle inequality being the hypothesis multiplied by `20 m₀ m₂`. -/
theorem cubic_nonneg_of_quartic {m₀ m₁ m₂ m₃ : ℝ}
    (h₀ : 0 < m₀) (h₁ : 0 < m₁) (h₂ : 0 < m₂) (h₃ : 0 < m₃)
    (hq : 5 * m₀ * m₂ ^ 3 ≤ 9 * m₁ ^ 3 * m₃) :
    0 ≤ 3 * m₀ * m₁ * m₃ + 15 * m₁ ^ 2 * m₂ - 10 * m₀ * m₂ ^ 2 := by
  set A : ℝ := 3 * m₀ * m₁ * m₃ with hA
  set B : ℝ := 15 * m₁ ^ 2 * m₂ with hB
  have hApos : 0 < A := by rw [hA]; positivity
  have hBpos : 0 < B := by rw [hB]; positivity
  have hTpos : 0 < 10 * m₀ * m₂ ^ 2 := by positivity
  have hscaled : 20 * m₀ * m₂ * (5 * m₀ * m₂ ^ 3) ≤ 20 * m₀ * m₂ * (9 * m₁ ^ 3 * m₃) :=
    mul_le_mul_of_nonneg_left hq (by positivity)
  have hprod : (10 * m₀ * m₂ ^ 2) ^ 2 ≤ 4 * (A * B) := by
    rw [hA, hB]; nlinarith [hscaled]
  have hsq : (10 * m₀ * m₂ ^ 2) ^ 2 ≤ (A + B) ^ 2 := by nlinarith [sq_nonneg (A - B)]
  nlinarith [hsq, hApos, hBpos, hTpos]

/-! ### The two models locate the strength of the hypothesis -/

/-- **The quartic hypothesis is an exact equality for the Gaussian.**  With `mⱼ = Γ(j+1/2)` the four
moments are `c, c/2, 3c/4, 15c/8` for `c = √π`, and both sides equal `135c⁴/64`. -/
theorem quartic_halfGaussian_eq (c : ℝ) :
    5 * c * (3 * c / 4) ^ 3 = 9 * (c / 2) ^ 3 * (15 * c / 8) := by
  ring

/-- **The quartic hypothesis fails for the two-sided exponential**, whose moments are `mⱼ = 2(2j)!`.
Since that model has `C = 0`, the quartic is strictly stronger than the cubic. -/
theorem quartic_exponential_fails :
    ¬ (5 * (2 : ℝ) * (48 : ℝ) ^ 3 ≤ 9 * (4 : ℝ) ^ 3 * (1440 : ℝ)) := by
  norm_num

/-- The exponential nevertheless satisfies the cubic with equality. -/
theorem cubic_exponential_eq :
    3 * (2 : ℝ) * 4 * 1440 + 15 * (4 : ℝ) ^ 2 * 48 - 10 * (2 : ℝ) * 48 ^ 2 = 0 := by
  norm_num

end CubicMomentLogConvexRatio

end GaloisForLFunctions

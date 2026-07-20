import Mathlib

/-!
# The fourth reflection jet

The local order-three obstruction of an even reflected product is controlled by one scalar
combination of the first four jets of its positive factor.  This file isolates that combination,
proves its exact Hankel identity, and records its multiplication law.

The multiplication law is the fourth-order analogue of additivity of logarithmic curvature:
the fourth reflection curvature of a product is the sum of the two factor curvatures plus the
bilinear interaction of their logarithmic second jets.
-/

namespace HilbertMetric

noncomputable section

/-- The second logarithmic jet written without taking a logarithm. -/
def logarithmicSecondJet (f₀ f₁ f₂ : ℝ) : ℝ :=
  f₂ / f₀ - (f₁ / f₀) ^ 2

/-- The fourth logarithmic jet written without taking a logarithm. -/
def logarithmicFourthJet (f₀ f₁ f₂ f₃ f₄ : ℝ) : ℝ :=
  f₄ / f₀ - 4 * f₃ * f₁ / f₀ ^ 2 - 3 * (f₂ / f₀) ^ 2 +
    12 * f₂ * f₁ ^ 2 / f₀ ^ 3 - 6 * f₁ ^ 4 / f₀ ^ 4

/-- The fourth reflection curvature `L⁽⁴⁾ + 4(L'')²`, expressed in raw jets. -/
def reflectionFourthCurvatureJet (f₀ f₁ f₂ f₃ f₄ : ℝ) : ℝ :=
  logarithmicFourthJet f₀ f₁ f₂ f₃ f₄ +
    4 * logarithmicSecondJet f₀ f₁ f₂ ^ 2

/-- The second center jet of `t ↦ f(u+t)f(u-t)`. -/
def reflectedProductSecondJet (f₀ f₁ f₂ : ℝ) : ℝ :=
  2 * (f₀ * f₂ - f₁ ^ 2)

/-- The fourth center jet of `t ↦ f(u+t)f(u-t)`. -/
def reflectedProductFourthJet (f₀ f₁ f₂ f₃ f₄ : ℝ) : ℝ :=
  2 * f₀ * f₄ - 8 * f₁ * f₃ + 6 * f₂ ^ 2

/-- Exact conversion from logarithmic fourth reflection curvature to the fourth Hankel
determinant of the reflected product. -/
theorem reflectedProduct_fourthHankel_eq
    {f₀ f₁ f₂ f₃ f₄ : ℝ} (hf₀ : f₀ ≠ 0) :
    f₀ ^ 2 * reflectedProductFourthJet f₀ f₁ f₂ f₃ f₄ -
        reflectedProductSecondJet f₀ f₁ f₂ ^ 2 =
      2 * f₀ ^ 4 * reflectionFourthCurvatureJet f₀ f₁ f₂ f₃ f₄ := by
  unfold reflectedProductFourthJet reflectedProductSecondJet
    reflectionFourthCurvatureJet logarithmicFourthJet logarithmicSecondJet
  field_simp [hf₀]
  ring

/-- Exact second logarithmic jet of a product from the jets of its factors. -/
theorem logarithmicSecondJet_mul
    {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ} (ha₀ : a₀ ≠ 0) (hb₀ : b₀ ≠ 0) :
    logarithmicSecondJet
        (a₀ * b₀)
        (a₁ * b₀ + a₀ * b₁)
        (a₂ * b₀ + 2 * a₁ * b₁ + a₀ * b₂) =
      logarithmicSecondJet a₀ a₁ a₂ + logarithmicSecondJet b₀ b₁ b₂ := by
  unfold logarithmicSecondJet
  field_simp [ha₀, hb₀]
  ring

/-- **Fourth reflection-curvature product law.**  Multiplication creates exactly one interaction
term, eight times the product of the two logarithmic second jets. -/
theorem reflectionFourthCurvatureJet_mul
    {a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ b₃ b₄ : ℝ}
    (ha₀ : a₀ ≠ 0) (hb₀ : b₀ ≠ 0) :
    reflectionFourthCurvatureJet
        (a₀ * b₀)
        (a₁ * b₀ + a₀ * b₁)
        (a₂ * b₀ + 2 * a₁ * b₁ + a₀ * b₂)
        (a₃ * b₀ + 3 * a₂ * b₁ + 3 * a₁ * b₂ + a₀ * b₃)
        (a₄ * b₀ + 4 * a₃ * b₁ + 6 * a₂ * b₂ + 4 * a₁ * b₃ + a₀ * b₄) =
      reflectionFourthCurvatureJet a₀ a₁ a₂ a₃ a₄ +
        reflectionFourthCurvatureJet b₀ b₁ b₂ b₃ b₄ +
          8 * logarithmicSecondJet a₀ a₁ a₂ *
            logarithmicSecondJet b₀ b₁ b₂ := by
  unfold reflectionFourthCurvatureJet logarithmicFourthJet logarithmicSecondJet
  field_simp [ha₀, hb₀]
  ring

/-- The fourth reflection curvature of a jet with zeroth value one. -/
theorem reflectionFourthCurvatureJet_one
    (r₁ r₂ r₃ r₄ : ℝ) :
    reflectionFourthCurvatureJet 1 r₁ r₂ r₃ r₄ =
      r₄ - 4 * r₁ * r₃ - 3 * r₂ ^ 2 +
        12 * r₁ ^ 2 * r₂ - 6 * r₁ ^ 4 +
          4 * (r₂ - r₁ ^ 2) ^ 2 := by
  simp [reflectionFourthCurvatureJet, logarithmicFourthJet,
    logarithmicSecondJet]
  ring

/-- Adding a nonnegative zeroth-order tail cannot make its logarithmic second jet exceed the
unnormalized positive second tail jet. -/
theorem logarithmicSecondJet_one_add_le
    {r₀ r₁ r₂ : ℝ} (hr₀ : 0 ≤ r₀) (hr₂ : 0 ≤ r₂) :
    logarithmicSecondJet (1 + r₀) r₁ r₂ ≤ r₂ := by
  have hg : 0 < 1 + r₀ := by linarith
  have hdiv : r₂ / (1 + r₀) ≤ r₂ := by
    rw [div_le_iff₀ hg]
    nlinarith [mul_nonneg hr₂ hr₀]
  unfold logarithmicSecondJet
  nlinarith [sq_nonneg (r₁ / (1 + r₀))]

/-- Quantitative fourth-curvature stability under an alternating tail.  The fourth tail jet and
the positive Bell-polynomial terms are discarded, so the estimate depends only on the first
three absolute jet bounds. -/
theorem reflectionFourthCurvatureJet_one_add_lower
    {r₀ r₁ r₂ r₃ r₄ R₁ R₂ R₃ : ℝ}
    (hr₀ : 0 ≤ r₀) (hr₂ : 0 ≤ r₂) (hr₄ : 0 ≤ r₄)
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) (hR₃ : 0 ≤ R₃)
    (hr₁ : |r₁| ≤ R₁) (hr₂R : r₂ ≤ R₂) (hr₃ : |r₃| ≤ R₃) :
    -(4 * R₁ * R₃ + 3 * R₂ ^ 2 + 6 * R₁ ^ 4) ≤
      reflectionFourthCurvatureJet (1 + r₀) r₁ r₂ r₃ r₄ := by
  let g := 1 + r₀
  let q := g⁻¹
  have hg : 0 < g := by dsimp [g]; linarith
  have hq0 : 0 ≤ q := (inv_pos.mpr hg).le
  have hq1 : q ≤ 1 := by
    dsimp [q]
    exact (inv_le_one₀ hg).2 (by dsimp [g]; linarith)
  have hq2 : q ^ 2 ≤ 1 := by nlinarith [sq_nonneg q, sq_nonneg (q - 1)]
  have hq3 : 0 ≤ q ^ 3 := pow_nonneg hq0 3
  have hq4 : q ^ 4 ≤ 1 := by
    have := pow_le_pow_left₀ hq0 hq1 4
    simpa using this
  have h13abs : |r₁ * r₃| ≤ R₁ * R₃ := by
    rw [abs_mul]
    exact mul_le_mul hr₁ hr₃ (abs_nonneg _) hR₁
  have h13 : r₁ * r₃ * q ^ 2 ≤ R₁ * R₃ := by
    calc
      r₁ * r₃ * q ^ 2 ≤ |r₁ * r₃| * q ^ 2 := by
        gcongr
        exact le_abs_self _
      _ ≤ (R₁ * R₃) * 1 := by
        exact mul_le_mul h13abs hq2 (sq_nonneg q) (mul_nonneg hR₁ hR₃)
      _ = R₁ * R₃ := by ring
  have hr₂q : 0 ≤ r₂ * q := mul_nonneg hr₂ hq0
  have hr₂qR : r₂ * q ≤ R₂ := by
    calc
      r₂ * q ≤ r₂ * 1 := mul_le_mul_of_nonneg_left hq1 hr₂
      _ = r₂ := by ring
      _ ≤ R₂ := hr₂R
  have h2sq : (r₂ * q) ^ 2 ≤ R₂ ^ 2 := by
    exact pow_le_pow_left₀ hr₂q hr₂qR 2
  have hr₁pow : r₁ ^ 4 ≤ R₁ ^ 4 := by
    have habs0 : 0 ≤ |r₁| := abs_nonneg _
    have hp := pow_le_pow_left₀ habs0 hr₁ 4
    calc
      r₁ ^ 4 = |r₁| ^ 4 := by
        have hpow : 0 ≤ r₁ ^ 4 := by nlinarith [sq_nonneg (r₁ ^ 2)]
        rw [← abs_pow, abs_of_nonneg hpow]
      _ ≤ R₁ ^ 4 := hp
  have h1four : r₁ ^ 4 * q ^ 4 ≤ R₁ ^ 4 := by
    calc
      r₁ ^ 4 * q ^ 4 ≤ R₁ ^ 4 * 1 := by
        exact mul_le_mul hr₁pow hq4 (pow_nonneg hq0 4) (pow_nonneg hR₁ 4)
      _ = R₁ ^ 4 := by ring
  have hfour0 : 0 ≤ r₄ * q := mul_nonneg hr₄ hq0
  have hcubic0 : 0 ≤ 12 * r₂ * r₁ ^ 2 * q ^ 3 := by positivity
  have hsquare0 : 0 ≤ 4 * (r₂ * q - (r₁ * q) ^ 2) ^ 2 := by positivity
  have hmain : -(4 * R₁ * R₃ + 3 * R₂ ^ 2 + 6 * R₁ ^ 4) ≤
      r₄ * q - 4 * r₃ * r₁ * q ^ 2 - 3 * (r₂ * q) ^ 2 +
      12 * r₂ * r₁ ^ 2 * q ^ 3 - 6 * r₁ ^ 4 * q ^ 4 +
        4 * (r₂ * q - (r₁ * q) ^ 2) ^ 2 := by
    nlinarith [h13, h2sq, h1four]
  simpa only [reflectionFourthCurvatureJet, logarithmicFourthJet,
    logarithmicSecondJet, div_eq_mul_inv, g, q, ← inv_pow] using hmain

end

end HilbertMetric

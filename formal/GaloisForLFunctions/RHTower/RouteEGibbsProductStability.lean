import GaloisForLFunctions.RHTower.RouteETwoSidedColumnLoadGradient

/-!
# Route E product-preserving Gibbs stability

Product-preserving recombination does not preserve the one-body Gibbs sum pointwise.  This file
proves the exact second-order defect.  The proof retains the sign of the exponential Taylor
remainder: convexity makes every remainder nonnegative, so the difference of two two-term
remainder sums costs two, rather than four, absolute remainders.
-/

namespace RHTower

noncomputable section

/-- First-order remainder of the real exponential at zero. -/
def routeEExpLinearRemainder (u : ℝ) : ℝ := Real.exp u - 1 - u

theorem routeEExpLinearRemainder_nonneg (u : ℝ) :
    0 ≤ routeEExpLinearRemainder u := by
  unfold routeEExpLinearRemainder
  linarith [Real.add_one_le_exp u]

theorem routeEExpLinearRemainder_le_sq (u : ℝ) (hu : |u| ≤ 1) :
    routeEExpLinearRemainder u ≤ u ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le hu
  change |routeEExpLinearRemainder u| ≤ u ^ 2 at h
  rw [abs_of_nonneg (routeEExpLinearRemainder_nonneg u)] at h
  exact h

private theorem routeENormalizedExpRemainder_le
    (X H A : ℝ) (hX : 0 < X) (hH : 0 ≤ H) (hHX : H < X) (hA : |A| ≤ H) :
    routeEExpLinearRemainder (-A / X) ≤ H ^ 2 / X ^ 2 := by
  have huH : |-A / X| ≤ H / X := by
    rw [abs_div, abs_neg, abs_of_pos hX]
    exact div_le_div_of_nonneg_right hA hX.le
  have hu : |-A / X| ≤ 1 :=
    huH.trans (le_of_lt ((div_lt_one hX).2 hHX))
  have hsquare := routeEExpLinearRemainder_le_sq (-A / X) hu
  have hHXnonneg : 0 ≤ H / X := div_nonneg hH hX.le
  have hsquareBound : (-A / X) ^ 2 ≤ (H / X) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hHXnonneg).2 huH
  calc
    routeEExpLinearRemainder (-A / X) ≤ (-A / X) ^ 2 := hsquare
    _ ≤ (H / X) ^ 2 := hsquareBound
    _ = H ^ 2 / X ^ 2 := by field_simp [ne_of_gt hX]

private theorem routeEProductOffset_linear_defect
    (X H A B C D : ℝ) (hX : 0 < X) (hH : 0 ≤ H)
    (hA : |A| ≤ H) (hB : |B| ≤ H) (hC : |C| ≤ H) (hD : |D| ≤ H)
    (hprod : (X + A) * (X + B) = (X + C) * (X + D)) :
    |A + B - C - D| ≤ 2 * H ^ 2 / X := by
  have hAB : |A * B| ≤ H ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hA hB (abs_nonneg B) hH
  have hCD : |C * D| ≤ H ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hC hD (abs_nonneg D) hH
  have hprodDefect : |C * D - A * B| ≤ 2 * H ^ 2 := by
    calc
      |C * D - A * B| ≤ |C * D| + |A * B| := abs_sub _ _
      _ ≤ H ^ 2 + H ^ 2 := add_le_add hCD hAB
      _ = 2 * H ^ 2 := by ring
  have hlinear : X * (A + B - C - D) = C * D - A * B := by
    nlinarith [hprod]
  apply (le_div_iff₀ hX).2
  calc
    |A + B - C - D| * X = |X * (A + B - C - D)| := by
      rw [abs_mul, abs_of_pos hX]
      ring
    _ = |C * D - A * B| := by rw [hlinear]
    _ ≤ 2 * H ^ 2 := hprodDefect

/-- Offset form of pair-product Gibbs curvature. -/
theorem routeEPairProductGibbsCurvature_offset
    (X H A B C D : ℝ) (hX : 0 < X) (hH : 0 ≤ H) (hHX : H < X)
    (hA : |A| ≤ H) (hB : |B| ≤ H) (hC : |C| ≤ H) (hD : |D| ≤ H)
    (hprod : (X + A) * (X + B) = (X + C) * (X + D)) :
    |Real.exp (-(X + A) / X) + Real.exp (-(X + B) / X) -
        Real.exp (-(X + C) / X) - Real.exp (-(X + D) / X)| ≤
      2 * (Real.exp (-1) + Real.exp (-1 + H / X)) * H ^ 2 / X ^ 2 := by
  let r : ℝ → ℝ := fun T => routeEExpLinearRemainder (-T / X)
  have hr_nonneg : ∀ T, 0 ≤ r T := fun T => routeEExpLinearRemainder_nonneg (-T / X)
  have hrA : r A ≤ H ^ 2 / X ^ 2 :=
    routeENormalizedExpRemainder_le X H A hX hH hHX hA
  have hrB : r B ≤ H ^ 2 / X ^ 2 :=
    routeENormalizedExpRemainder_le X H B hX hH hHX hB
  have hrC : r C ≤ H ^ 2 / X ^ 2 :=
    routeENormalizedExpRemainder_le X H C hX hH hHX hC
  have hrD : r D ≤ H ^ 2 / X ^ 2 :=
    routeENormalizedExpRemainder_le X H D hX hH hHX hD
  have hq : 0 ≤ H ^ 2 / X ^ 2 := div_nonneg (sq_nonneg H) (sq_nonneg X)
  have hrDiff : |(r A + r B) - (r C + r D)| ≤ 2 * (H ^ 2 / X ^ 2) := by
    rw [abs_le]
    constructor <;> nlinarith [hr_nonneg A, hr_nonneg B, hr_nonneg C, hr_nonneg D]
  have hlinear := routeEProductOffset_linear_defect X H A B C D hX hH hA hB hC hD hprod
  have hlinearDiv : |-(A + B - C - D) / X| ≤ 2 * (H ^ 2 / X ^ 2) := by
    rw [abs_div, abs_neg, abs_of_pos hX]
    calc
      |A + B - C - D| / X ≤ (2 * H ^ 2 / X) / X :=
        div_le_div_of_nonneg_right hlinear hX.le
      _ = 2 * (H ^ 2 / X ^ 2) := by field_simp [ne_of_gt hX]
  have hexpansion (T : ℝ) :
      Real.exp (-(X + T) / X) =
        Real.exp (-1) * (1 - T / X + r T) := by
    have harg : -(X + T) / X = -1 + (-T / X) := by
      field_simp [ne_of_gt hX]
      ring
    rw [harg, Real.exp_add]
    unfold r routeEExpLinearRemainder
    ring
  rw [hexpansion A, hexpansion B, hexpansion C, hexpansion D]
  have hrewrite :
      Real.exp (-1) * (1 - A / X + r A) +
          Real.exp (-1) * (1 - B / X + r B) -
          Real.exp (-1) * (1 - C / X + r C) -
          Real.exp (-1) * (1 - D / X + r D) =
        Real.exp (-1) *
          (-(A + B - C - D) / X + ((r A + r B) - (r C + r D))) := by ring
  rw [hrewrite, abs_mul, abs_of_pos (Real.exp_pos (-1))]
  have hinside :
      |-(A + B - C - D) / X + ((r A + r B) - (r C + r D))| ≤
        4 * (H ^ 2 / X ^ 2) := by
    calc
      |-(A + B - C - D) / X + ((r A + r B) - (r C + r D))| ≤
          |-(A + B - C - D) / X| + |(r A + r B) - (r C + r D)| :=
        abs_add_le _ _
      _ ≤ 2 * (H ^ 2 / X ^ 2) + 2 * (H ^ 2 / X ^ 2) :=
        add_le_add hlinearDiv hrDiff
      _ = 4 * (H ^ 2 / X ^ 2) := by ring
  have hexpMono : Real.exp (-1) ≤ Real.exp (-1 + H / X) := by
    apply Real.exp_le_exp.mpr
    exact le_add_of_nonneg_right (div_nonneg hH hX.le)
  calc
    Real.exp (-1) *
        |-(A + B - C - D) / X + ((r A + r B) - (r C + r D))| ≤
      Real.exp (-1) * (4 * (H ^ 2 / X ^ 2)) :=
        mul_le_mul_of_nonneg_left hinside (Real.exp_pos _).le
    _ ≤ 2 * (Real.exp (-1) + Real.exp (-1 + H / X)) *
        (H ^ 2 / X ^ 2) := by
      have hcoeff : 4 * Real.exp (-1) ≤
          2 * (Real.exp (-1) + Real.exp (-1 + H / X)) := by linarith
      nlinarith [mul_nonneg hq (sub_nonneg.mpr hcoeff)]
    _ = 2 * (Real.exp (-1) + Real.exp (-1 + H / X)) * H ^ 2 / X ^ 2 := by
      field_simp [ne_of_gt hX]

/-- **Pair-product Gibbs curvature.**  Exact paper statement for four physical points in the
common aperture `[X-H,X+H]`. -/
theorem routeEPairProductGibbsCurvature
    (X H a b c d : ℝ) (hX : 0 < X) (hH : 0 ≤ H) (hHX : H < X)
    (ha : a ∈ Set.Icc (X - H) (X + H))
    (hb : b ∈ Set.Icc (X - H) (X + H))
    (hc : c ∈ Set.Icc (X - H) (X + H))
    (hd : d ∈ Set.Icc (X - H) (X + H))
    (hprod : a * b = c * d) :
    |Real.exp (-a / X) + Real.exp (-b / X) -
        Real.exp (-c / X) - Real.exp (-d / X)| ≤
      2 * (Real.exp (-1) + Real.exp (-1 + H / X)) * H ^ 2 / X ^ 2 := by
  let A := a - X
  let B := b - X
  let C := c - X
  let D := d - X
  have hA : |A| ≤ H := abs_le.mpr ⟨by dsimp [A]; linarith [ha.1], by dsimp [A]; linarith [ha.2]⟩
  have hB : |B| ≤ H := abs_le.mpr ⟨by dsimp [B]; linarith [hb.1], by dsimp [B]; linarith [hb.2]⟩
  have hC : |C| ≤ H := abs_le.mpr ⟨by dsimp [C]; linarith [hc.1], by dsimp [C]; linarith [hc.2]⟩
  have hD : |D| ≤ H := abs_le.mpr ⟨by dsimp [D]; linarith [hd.1], by dsimp [D]; linarith [hd.2]⟩
  have hprodOffset : (X + A) * (X + B) = (X + C) * (X + D) := by
    calc
      (X + A) * (X + B) = a * b := by dsimp [A, B]; ring
      _ = c * d := hprod
      _ = (X + C) * (X + D) := by dsimp [C, D]; ring
  have h := routeEPairProductGibbsCurvature_offset
    X H A B C D hX hH hHX hA hB hC hD hprodOffset
  convert h using 1 <;> dsimp [A, B, C, D] <;> ring

end

end RHTower

import GaloisForLFunctions.HTGeometry.EllipticGammaZeroNomeDegeneration

/-!
# The parity-correct zero-nome boundary

The multiple elliptic Gamma product is the forward product times the backward one for an odd number
of nomes, and their quotient for an even number.  With the forward product near `1` and the backward
product near `1 - x`, the whole object is near `1 - x` in the odd case and near `(1 - x)⁻¹` in the
even case.

The two elementary estimates are stated separately for products and quotients; the quotient one
needs the backward product bounded away from zero, which the same bound supplies.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A product of a factor near one with a factor near `w` is near `w`. -/
theorem norm_mul_sub_le_of_near {F B w : ℂ} {a b : ℝ} (hF : ‖F - 1‖ ≤ a) (hB : ‖B - w‖ ≤ b)
    (ha : 0 ≤ a) (_hb : 0 ≤ b) : ‖F * B - w‖ ≤ (1 + a) * b + ‖w‖ * a := by
  have hFnorm : ‖F‖ ≤ 1 + a := by
    have := norm_sub_norm_le F 1
    rw [norm_one] at this
    linarith [le_trans this hF]
  have hsplit : F * B - w = F * (B - w) + (F - 1) * w := by ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, norm_mul]
  have h1 : ‖F‖ * ‖B - w‖ ≤ (1 + a) * b :=
    mul_le_mul hFnorm hB (norm_nonneg _) (by linarith)
  have h2 : ‖F - 1‖ * ‖w‖ ≤ a * ‖w‖ := mul_le_mul_of_nonneg_right hF (norm_nonneg _)
  nlinarith [norm_nonneg w]

/-- A quotient of a factor near one by a factor near `w` is near `w⁻¹`. -/
theorem norm_div_sub_inv_le_of_near {F B w : ℂ} (hw : w ≠ 0) {a b : ℝ} (hF : ‖F - 1‖ ≤ a)
    (hB : ‖B - w‖ ≤ b) (ha : 0 ≤ a) (hb : 0 ≤ b) (hbw : b ≤ ‖w‖ / 2) :
    ‖F / B - w⁻¹‖ ≤ (‖w‖ * a + b) * (2 / ‖w‖ ^ (2 : ℕ)) := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hBlow : ‖w‖ / 2 ≤ ‖B‖ := by
    have hrev : ‖w‖ - ‖B‖ ≤ ‖w - B‖ := norm_sub_norm_le w B
    have hBw : ‖w - B‖ = ‖B - w‖ := norm_sub_rev _ _
    rw [hBw] at hrev
    linarith
  have hBne : B ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hBlow
    linarith
  have hsplit : F / B - w⁻¹ = (F * w - B) / (B * w) := by
    field_simp
  rw [hsplit, norm_div, norm_mul]
  have hnum : ‖F * w - B‖ ≤ ‖w‖ * a + b := by
    have hrw : F * w - B = (F - 1) * w + (w - B) := by ring
    rw [hrw]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_sub_rev w B]
    have h1 : ‖F - 1‖ * ‖w‖ ≤ ‖w‖ * a := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hF (norm_nonneg _)
    linarith
  have hden : ‖w‖ ^ (2 : ℕ) / 2 ≤ ‖B‖ * ‖w‖ := by
    have := mul_le_mul_of_nonneg_right hBlow (le_of_lt hwpos)
    nlinarith
  have hdenpos : (0 : ℝ) < ‖B‖ * ‖w‖ := by
    have hBpos : 0 < ‖B‖ := norm_pos_iff.mpr hBne
    positivity
  rw [div_le_iff₀ hdenpos]
  have hnn : (0 : ℝ) ≤ ‖w‖ * a + b := by positivity
  calc ‖F * w - B‖ ≤ ‖w‖ * a + b := hnum
    _ = (‖w‖ * a + b) * (2 / ‖w‖ ^ (2 : ℕ)) * (‖w‖ ^ (2 : ℕ) / 2) := by
        field_simp
    _ ≤ (‖w‖ * a + b) * (2 / ‖w‖ ^ (2 : ℕ)) * (‖B‖ * ‖w‖) := by
        have hfac : (0 : ℝ) ≤ (‖w‖ * a + b) * (2 / ‖w‖ ^ (2 : ℕ)) := by positivity
        exact mul_le_mul_of_nonneg_left hden hfac

/-- The parity-correct zero-nome boundary. -/
def zeroNomeBoundary (ι : Type) [Fintype ι] (z : ℂ) : ℂ :=
  if Even (Fintype.card ι) then (1 - multipleEllipticGammaCoordinate z)⁻¹
  else 1 - multipleEllipticGammaCoordinate z

omit [DecidableEq ι] in
/-- **The multiple elliptic Gamma product degenerates to its parity-correct boundary.** -/
theorem norm_product_sub_zeroNomeBoundary_le {τ : ι → ℂ} {z : ℂ} {a b : ℝ}
    (hx : (1 : ℂ) - multipleEllipticGammaCoordinate z ≠ 0)
    (hF : ‖multipleEllipticGammaForwardProduct τ z - 1‖ ≤ a)
    (hB : ‖multipleEllipticGammaBackwardProduct τ z
      - (1 - multipleEllipticGammaCoordinate z)‖ ≤ b)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbw : b ≤ ‖1 - multipleEllipticGammaCoordinate z‖ / 2) :
    ‖multipleEllipticGammaProduct τ z - zeroNomeBoundary ι z‖
      ≤ max ((1 + a) * b + ‖1 - multipleEllipticGammaCoordinate z‖ * a)
        ((‖1 - multipleEllipticGammaCoordinate z‖ * a + b)
          * (2 / ‖1 - multipleEllipticGammaCoordinate z‖ ^ (2 : ℕ))) := by
  rw [multipleEllipticGammaProduct, zeroNomeBoundary]
  by_cases hpar : Even (Fintype.card ι)
  · rw [if_pos hpar, if_pos hpar]
    exact le_trans (norm_div_sub_inv_le_of_near hx hF hB ha hb hbw) (le_max_right _ _)
  · rw [if_neg hpar, if_neg hpar]
    exact le_trans (norm_mul_sub_le_of_near hF hB ha hb) (le_max_left _ _)

end

end GaloisForLFunctions.HTGeometry

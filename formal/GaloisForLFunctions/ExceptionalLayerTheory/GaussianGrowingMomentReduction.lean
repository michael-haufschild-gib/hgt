import GaloisForLFunctions.ExceptionalLayerTheory.GaussianHigherMomentConstants
import GaloisForLFunctions.ExceptionalLayerTheory.GaussianHigherCentredVaughan

/-!
# Vaughan reduction with a growing Gaussian moment order

Explicit order bounds replace fixed-order constants. At the critical
abscissa, polynomial height costs can then be traded for an exponentially
small error at exponential observation scales.
-/

open Complex Finset Filter Topology RHTower ArithmeticFunction
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The actual higher-moment error after both signed Vaughan pole corrections. -/
def gaussianHigherCentredVaughanError (r : ℕ) (σ t : ℝ) (U V : ℕ) (ε : ℂ) : ℂ :=
  ((∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) * gaussianHigherPrimeMomentWeight r σ t ε n) -
    gaussianHigherMomentPole r ((σ : ℂ) + t * I) ε t) -
    gaussianHigherCentredVaughanCurrent r σ t ε U V

/-- A fixed constant paying both critical-abscissa arithmetic errors. -/
def gaussianGrowingMomentConstant : ℝ :=
  1 + Real.Gamma (1 / 4) + 58 * gaussianQuarterGammaConstant

theorem gaussianGrowingMomentConstant_pos : 0 < gaussianGrowingMomentConstant := by
  have hG := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 4)
  have hQ := gaussianQuarterGammaConstant_pos
  unfold gaussianGrowingMomentConstant
  positivity

/-- The complete error has explicit height costs uniform over all orders `r≤t`. -/
theorem norm_gaussianHigherCentredVaughanError_le_height (r : ℕ) (hr : r ≠ 0)
    {t X : ℝ} {ε : ℂ} (ht : 8192 ≤ t) (hrt : (r : ℝ) ≤ t)
    (hε : 0 < ε.re) (hsector : ‖ε‖ ≤ 4 * ε.re * t)
    (hX : 0 < X) (hscale : ε.re * X ^ 2 = 2) {U V : ℕ}
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hUVX : ((U * V : ℕ) : ℝ) ≤ X) :
    ‖gaussianHigherCentredVaughanError r (1 / 2) t U V ε‖ ≤
      gaussianGrowingMomentConstant *
        (t ^ (7 * r) * ((U * V : ℕ) : ℝ) ^ (2 * r) * X ^ ((1 / 2 : ℝ) - (2 * r : ℕ)) +
          (V : ℝ) * t ^ (4 * r + 1) * X ^ (-(1 / 2 : ℝ))) * (1 + Real.log X) := by
  have ht1 : 1 ≤ t := by linarith only [ht]
  have ht0 : 0 ≤ t := by linarith only [ht]
  have hG := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 4)
  have hQ := gaussianQuarterGammaConstant_pos
  have hC := gaussianGrowingMomentConstant_pos
  have hX1 : 1 ≤ X :=
    (by exact_mod_cast Nat.mul_pos hU hV : (1 : ℝ) ≤ ((U * V : ℕ) : ℝ)).trans hUVX
  have hlog := Real.log_nonneg hX1
  have hK := gaussianHigherMomentLatticeConstant_half_le_height r hr ht hrt
  have hL := gaussianHigherLogMomentConstant_half_le_height r hr (by linarith only [ht]) hrt
  have h8 : (8 : ℝ) ^ r ≤ t ^ (5 * r) := by
    exact (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8)
      (by linarith only [ht] : 8 ≤ t) r).trans (pow_le_pow_right₀ ht1 (by omega))
  have hA : 8 ^ r + gaussianHigherMomentLatticeConstant r (1 / 2) *
      (2 : ℝ) ^ (((2 * r : ℕ) + (1 / 2 : ℝ) - 1) / 2) ≤
      gaussianGrowingMomentConstant * t ^ (5 * r) := by
    apply (_root_.add_le_add h8 hK).trans
    unfold gaussianGrowingMomentConstant
    nlinarith only [mul_nonneg (show 0 ≤ 58 * gaussianQuarterGammaConstant by positivity)
      (pow_nonneg ht0 (5 * r))]
  have hB : gaussianHigherLogMomentConstant r (1 / 2) ≤
      gaussianGrowingMomentConstant * t ^ (4 * r) := by
    apply hL.trans
    unfold gaussianGrowingMomentConstant
    nlinarith only [mul_nonneg (show 0 ≤ 1 + Real.Gamma (1 / 4) by positivity)
      (pow_nonneg ht0 (4 * r))]
  have hh := norm_gaussianHigherMoment_sub_centredVaughan_product_le r hr
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    ht1 hε hsector hX hscale hU hV hUVX
  change ‖gaussianHigherCentredVaughanError r (1 / 2) t U V ε‖ ≤ _ at hh
  apply hh.trans
  calc
    _ ≤ ((gaussianGrowingMomentConstant * t ^ (5 * r)) *
        t ^ (2 * r) * ((U * V : ℕ) : ℝ) ^ (2 * r) * X ^ (1 - 1 / 2 - (2 * r : ℕ)) +
        (gaussianGrowingMomentConstant * t ^ (4 * r)) * V * t * X ^ (-(1 / 2 : ℝ))) *
          (1 + Real.log X) := by gcongr
    _ = _ := by
      have hpow : t ^ (5 * r) * t ^ (2 * r) = t ^ (7 * r) := by
        rw [← pow_add]
        congr 1
        omega
      have he : (1 : ℝ) - 1 / 2 - (2 * r : ℕ) = 1 / 2 - (2 * r : ℕ) := by ring
      rw [he, pow_succ]
      calc
        _ = gaussianGrowingMomentConstant *
            ((t ^ (5 * r) * t ^ (2 * r)) * ((U * V : ℕ) : ℝ) ^ (2 * r) *
              X ^ ((1 / 2 : ℝ) - (2 * r : ℕ)) +
              (V : ℝ) * (t ^ (4 * r) * t) * X ^ (-(1 / 2 : ℝ))) * (1 + Real.log X) := by ring
        _ = _ := by rw [hpow]

/-- Product cutoffs below the Gaussian scale by `t^J` leave only
a rapidly decreasing order power and a logarithmic type-I error. -/
theorem norm_gaussianHigherCentredVaughanError_le_order_budget (r J : ℕ) (hr : r ≠ 0)
    (hJ : 4 ≤ J)
    {t X : ℝ} {ε : ℂ} (ht : 8192 ≤ t) (hrt : (r : ℝ) ≤ t)
    (hε : 0 < ε.re) (hsector : ‖ε‖ ≤ 4 * ε.re * t)
    (hX : 0 < X) (hscale : ε.re * X ^ 2 = 2) {U V : ℕ}
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hVt : (V : ℝ) ≤ t)
    (hK : ((U * V : ℕ) : ℝ) * t ^ J ≤ X) :
    ‖gaussianHigherCentredVaughanError r (1 / 2) t U V ε‖ ≤
      gaussianGrowingMomentConstant *
        (X ^ (1 / 2 : ℝ) / t ^ ((2 * J - 7) * r) + t ^ (4 * r + 2) * X ^ (-(1 / 2 : ℝ))) *
        (1 + Real.log X) := by
  have ht1 : 1 ≤ t := by linarith only [ht]
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hK0 : (0 : ℝ) ≤ ((U * V : ℕ) : ℝ) := Nat.cast_nonneg _
  have hUVX : ((U * V : ℕ) : ℝ) ≤ X :=
    (by nlinarith only [mul_le_mul_of_nonneg_left (one_le_pow₀ ht1 : 1 ≤ t ^ J) hK0] :
      ((U * V : ℕ) : ℝ) ≤ ((U * V : ℕ) : ℝ) * t ^ J).trans hK
  have hX1 : 1 ≤ X :=
    (by exact_mod_cast Nat.mul_pos hU hV : (1 : ℝ) ≤ ((U * V : ℕ) : ℝ)).trans hUVX
  have hA : t ^ (7 * r) * ((U * V : ℕ) : ℝ) ^ (2 * r) *
      X ^ ((1 / 2 : ℝ) - (2 * r : ℕ)) ≤ X ^ (1 / 2 : ℝ) / t ^ ((2 * J - 7) * r) := by
    apply (le_div_iff₀ (pow_pos ht0 ((2 * J - 7) * r))).mpr
    calc
      _ = (((U * V : ℕ) : ℝ) * t ^ J) ^ (2 * r) *
          X ^ ((1 / 2 : ℝ) - (2 * r : ℕ)) := by
        rw [mul_pow, ← pow_mul]
        have hp : t ^ (7 * r) * t ^ ((2 * J - 7) * r) = t ^ (J * (2 * r)) := by
          rw [← pow_add]
          congr 1
          rw [← add_mul, show 7 + (2 * J - 7) = 2 * J by omega]
          ring
        calc
          _ = ((U * V : ℕ) : ℝ) ^ (2 * r) *
              (t ^ (7 * r) * t ^ ((2 * J - 7) * r)) * X ^ ((1 / 2 : ℝ) - (2 * r : ℕ)) := by ring
          _ = _ := by rw [hp]
      _ ≤ X ^ (2 * r) * X ^ ((1 / 2 : ℝ) - (2 * r : ℕ)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hK (2 * r))
          (Real.rpow_nonneg hX.le _)
      _ = _ := by rw [← Real.rpow_natCast X (2 * r), ← Real.rpow_add hX]; congr 1; ring
  have hB : (V : ℝ) * t ^ (4 * r + 1) * X ^ (-(1 / 2 : ℝ)) ≤
      t ^ (4 * r + 2) * X ^ (-(1 / 2 : ℝ)) := by
    calc
      _ ≤ t * t ^ (4 * r + 1) * X ^ (-(1 / 2 : ℝ)) := by gcongr
      _ = _ := by rw [show 4 * r + 2 = (4 * r + 1) + 1 by omega, pow_succ]; ring
  have hC := gaussianGrowingMomentConstant_pos
  have hlog := Real.log_nonneg hX1
  apply (norm_gaussianHigherCentredVaughanError_le_height
    r hr ht hrt hε hsector hX hscale hU hV hUVX).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (_root_.add_le_add hA hB) hC.le) (by linarith only [hlog])

/-- Small order speed and a sufficiently long first cutoff make the complete
centred reduction exponentially accurate at an exponential Gaussian scale. -/
theorem norm_gaussianHigherCentredVaughanError_le_exponential
    (r J : ℕ) (hr : r ≠ 0) (hJ : 4 ≤ J) {a κ t : ℝ}
    (ha : 0 < a) (hκ : 0 < κ) (hκa : κ ≤ a / 32)
    (hJκ : 2 * a ≤ ((2 * J - 7 : ℕ) : ℝ) * κ)
    (ht : 8192 ≤ t) (hrt : (r : ℝ) ≤ t)
    (hrlo : κ * t ≤ 2 * r * Real.log t)
    (hrhi : (r : ℝ) * Real.log t ≤ κ * t)
    {ε : ℂ} (hε : 0 < ε.re) (hsector : ‖ε‖ ≤ 4 * ε.re * t)
    (hscale : ε.re * (Real.exp (a * t)) ^ 2 = 2) {U V : ℕ}
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hVt : (V : ℝ) ≤ t)
    (hK : ((U * V : ℕ) : ℝ) * t ^ J ≤ Real.exp (a * t)) :
    ‖gaussianHigherCentredVaughanError r (1 / 2) t U V ε‖ ≤
      gaussianGrowingMomentConstant * (1 + t ^ 2) * (1 + a * t) *
        Real.exp (-(3 * a / 8) * t) := by
  have ht0 : 0 < t := by linarith only [ht]
  have hp (n : ℕ) : t ^ n = Real.exp ((n : ℝ) * Real.log t) := by
    rw [Real.exp_nat_mul, Real.exp_log ht0]
  have hD : 0 ≤ ((2 * J - 7 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlow : a * t ≤ ((2 * J - 7 : ℕ) : ℝ) * r * Real.log t := by
    have hh := mul_le_mul_of_nonneg_left hrlo hD
    have hj := mul_le_mul_of_nonneg_right hJκ ht0.le
    nlinarith only [hh, hj]
  have hA : Real.exp (a * t) ^ (1 / 2 : ℝ) / t ^ ((2 * J - 7) * r) ≤
      Real.exp (-(3 * a / 8) * t) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, hp, ← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith only [hlow, mul_pos ha ht0]
  have hB : t ^ (4 * r + 2) * Real.exp (a * t) ^ (-(1 / 2 : ℝ)) ≤
      t ^ 2 * Real.exp (-(3 * a / 8) * t) := by
    rw [pow_add, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, hp (4 * r)]
    calc
      _ = t ^ 2 * Real.exp (((4 * r : ℕ) : ℝ) * Real.log t + a * t * (-(1 / 2))) := by
        rw [Real.exp_add]
        ring
      _ ≤ _ := by
        gcongr
        push_cast
        nlinarith only [hrhi, mul_le_mul_of_nonneg_right hκa ht0.le]
  have hC := gaussianGrowingMomentConstant_pos
  have hfac : 0 ≤ 1 + a * t := by positivity
  have hh := norm_gaussianHigherCentredVaughanError_le_order_budget r J hr hJ ht hrt
    hε hsector (Real.exp_pos _) hscale hU hV hVt hK
  rw [Real.log_exp] at hh
  apply hh.trans
  calc
    _ ≤ gaussianGrowingMomentConstant *
        (Real.exp (-(3 * a / 8) * t) + t ^ 2 * Real.exp (-(3 * a / 8) * t)) *
          (1 + a * t) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (_root_.add_le_add hA hB) hC.le) hfac
    _ = _ := by ring

#print axioms norm_gaussianHigherCentredVaughanError_le_exponential
#print axioms norm_gaussianHigherCentredVaughanError_le_height
#print axioms norm_gaussianHigherCentredVaughanError_le_order_budget

end GaloisForLFunctions.ExceptionalLayerTheory

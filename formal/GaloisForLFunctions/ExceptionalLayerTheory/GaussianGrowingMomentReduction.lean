import GaloisForLFunctions.ExceptionalLayerTheory.GaussianHigherMomentConstants
import GaloisForLFunctions.ExceptionalLayerTheory.GaussianHigherCentredVaughan
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

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
        t ^ (2 * r) * ((U * V : ℕ) : ℝ) ^ (2 * r) * X ^ ((1 : ℝ) - 1 / 2 - (2 * r : ℕ)) +
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
    (ha : 0 < a) (hκa : κ ≤ a / 32)
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

/-- Moment order tending to infinity below every fixed multiple of height. -/
def gaussianGrowingMomentOrder (κ t : ℝ) : ℕ := ⌊κ * t / Real.log t⌋₊

/-- The long arithmetic cutoff, within a polynomial factor of the Gaussian scale. -/
def gaussianGrowingLongCutoff (a : ℝ) (J : ℕ) (t : ℝ) : ℕ :=
  ⌊Real.exp (a * t) / t ^ (J + 1)⌋₊

/-- The concrete floor order satisfies both logarithmic budgets eventually. -/
theorem eventually_gaussianGrowingMomentOrder_bounds {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ t : ℝ in atTop,
      gaussianGrowingMomentOrder κ t ≠ 0 ∧
      (gaussianGrowingMomentOrder κ t : ℝ) ≤ t ∧
      κ * t ≤ 2 * gaussianGrowingMomentOrder κ t * Real.log t ∧
      (gaussianGrowingMomentOrder κ t : ℝ) * Real.log t ≤ κ * t := by
  have hlog : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hsmall := hlog.eventually_lt_const (by positivity : (0 : ℝ) < κ / 2)
  have hlarge := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 κ))
  filter_upwards [hsmall, hlarge, eventually_ge_atTop (1 : ℝ)] with t hs hl ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hl1 : 1 ≤ Real.log t := (le_max_left _ _).trans hl
  have hl0 : 0 < Real.log t := zero_lt_one.trans_le hl1
  have hκl : κ ≤ Real.log t := (le_max_right _ _).trans hl
  have hx : 0 ≤ κ * t / Real.log t := by positivity
  have hx2 : 2 ≤ κ * t / Real.log t := by
    apply (le_div_iff₀ hl0).mpr
    have hh := (div_lt_iff₀ ht0).mp hs
    linarith only [hh]
  have hfloor := Nat.floor_le hx
  have hnear := Nat.lt_floor_add_one (κ * t / Real.log t)
  have hr1 : 1 ≤ gaussianGrowingMomentOrder κ t :=
    (Nat.one_le_floor_iff _).mpr (by linarith only [hx2])
  have hr1R : (1 : ℝ) ≤ gaussianGrowingMomentOrder κ t := by exact_mod_cast hr1
  have hrle : (gaussianGrowingMomentOrder κ t : ℝ) ≤ t := by
    apply hfloor.trans
    apply (div_le_iff₀ hl0).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hκl ht0.le]
  have hrlo : κ * t ≤ 2 * gaussianGrowingMomentOrder κ t * Real.log t := by
    apply (div_le_iff₀ hl0).mp
    change κ * t / Real.log t ≤ 2 * (⌊κ * t / Real.log t⌋₊ : ℝ)
    change (1 : ℝ) ≤ (⌊κ * t / Real.log t⌋₊ : ℝ) at hr1R
    linarith only [hnear, hr1R]
  exact ⟨by omega, hrle, hrlo, (le_div_iff₀ hl0).mp hfloor⟩

/-- The concrete long and short cutoffs satisfy the product budget and retain
at least half the unrounded long cutoff eventually. -/
theorem eventually_gaussianGrowingLongCutoff_bounds {a : ℝ} (ha : 0 < a) (J : ℕ) :
    ∀ᶠ t : ℝ in atTop,
      1 ≤ gaussianGrowingLongCutoff a J t ∧
      1 ≤ ⌊t⌋₊ ∧ (⌊t⌋₊ : ℝ) ≤ t ∧
      ((gaussianGrowingLongCutoff a J t * ⌊t⌋₊ : ℕ) : ℝ) * t ^ J ≤ Real.exp (a * t) ∧
      Real.exp (a * t) / (2 * t ^ (J + 1)) ≤ gaussianGrowingLongCutoff a J t := by
  have hh : Tendsto (fun t : ℝ => t ^ (J + 1) * Real.exp (-a * t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((J + 1 : ℕ) : ℝ) a ha
  filter_upwards [hh.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop (1 : ℝ)] with t hsmall ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hp := pow_pos ht0 (J + 1)
  have hx : 0 ≤ Real.exp (a * t) / t ^ (J + 1) := by positivity
  have hpow : 2 * t ^ (J + 1) ≤ Real.exp (a * t) := by
    have hmul := mul_le_mul_of_nonneg_right hsmall.le (Real.exp_pos (a * t)).le
    have he : Real.exp (-a * t) * Real.exp (a * t) = 1 := by
      rw [← Real.exp_add, show -a * t + a * t = 0 by ring, Real.exp_zero]
    rw [mul_assoc, he, mul_one] at hmul
    linarith only [hmul]
  have hx2 : 2 ≤ Real.exp (a * t) / t ^ (J + 1) := (le_div_iff₀ hp).mpr hpow
  have hU1 : 1 ≤ gaussianGrowingLongCutoff a J t :=
    (Nat.one_le_floor_iff _).mpr (by linarith only [hx2])
  have hV1 : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).mpr ht
  have hVt := Nat.floor_le ht0.le
  have hUt := Nat.floor_le hx
  have hprod : ((gaussianGrowingLongCutoff a J t * ⌊t⌋₊ : ℕ) : ℝ) * t ^ J ≤
      Real.exp (a * t) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ (Real.exp (a * t) / t ^ (J + 1)) * t * t ^ J := by gcongr
      _ = _ := by rw [pow_succ]; field_simp
  have hnear := Nat.lt_floor_add_one (Real.exp (a * t) / t ^ (J + 1))
  have hU1R : (1 : ℝ) ≤ gaussianGrowingLongCutoff a J t := by exact_mod_cast hU1
  have hhalf : Real.exp (a * t) / (2 * t ^ (J + 1)) ≤ gaussianGrowingLongCutoff a J t := by
    have hxhalf : Real.exp (a * t) / t ^ (J + 1) / 2 ≤
        gaussianGrowingLongCutoff a J t := by
      change _ ≤ (⌊Real.exp (a * t) / t ^ (J + 1)⌋₊ : ℝ)
      change (1 : ℝ) ≤ (⌊Real.exp (a * t) / t ^ (J + 1)⌋₊ : ℝ) at hU1R
      linarith only [hnear, hU1R]
    convert hxhalf using 1 <;> ring
  exact ⟨hU1, hV1, hVt, hprod, hhalf⟩

private theorem eventually_growing_polynomial_absorbed {a : ℝ} (ha : 0 < a) :
    ∀ᶠ t : ℝ in atTop, (1 + t ^ 2) * (1 + a * t) * Real.exp (-(a / 8) * t) ≤ 1 := by
  have hp (n : ℕ) : Tendsto (fun t : ℝ => t ^ n * Real.exp (-(a / 8) * t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) (a / 8) (by positivity)
  have hlim : Tendsto (fun t : ℝ => (1 + t ^ 2) * (1 + a * t) *
      Real.exp (-(a / 8) * t)) atTop (𝓝 0) := by
    convert (((hp 0).add ((hp 1).const_mul a)).add (hp 2)).add ((hp 3).const_mul a) using 1
    · ext t
      simp only [pow_zero, pow_one]
      ring
    · ring
  exact (hlim.eventually_lt_const zero_lt_one).mono fun _ ht => ht.le

/-- Concrete growing order and integer cutoffs give an exponentially small
complete arithmetic reduction error, uniformly over the damping sector. -/
theorem eventually_gaussianGrowingMomentReduction {a κ : ℝ} (ha : 0 < a)
    (hκ : 0 < κ) (hκa : κ ≤ a / 32) (J : ℕ) (hJ : 4 ≤ J)
    (hJκ : 2 * a ≤ ((2 * J - 7 : ℕ) : ℝ) * κ) :
    ∀ᶠ t : ℝ in atTop, ∀ ε : ℂ, 0 < ε.re → ‖ε‖ ≤ 4 * ε.re * t →
      ε.re * (Real.exp (a * t)) ^ 2 = 2 →
      ‖gaussianHigherCentredVaughanError (gaussianGrowingMomentOrder κ t) (1 / 2) t
        (gaussianGrowingLongCutoff a J t) ⌊t⌋₊ ε‖ ≤
          gaussianGrowingMomentConstant * Real.exp (-(a / 4) * t) := by
  filter_upwards [eventually_gaussianGrowingMomentOrder_bounds hκ, eventually_gaussianGrowingLongCutoff_bounds ha J,
    eventually_growing_polynomial_absorbed ha, eventually_ge_atTop (8192 : ℝ)]
      with t hr hcut hpoly ht
  intro ε hε hsector hscale
  have hh := norm_gaussianHigherCentredVaughanError_le_exponential
    (gaussianGrowingMomentOrder κ t) J hr.1 hJ ha hκa hJκ ht hr.2.1
    hr.2.2.1 hr.2.2.2 hε hsector hscale hcut.1 hcut.2.1 hcut.2.2.1 hcut.2.2.2.1
  have hC := gaussianGrowingMomentConstant_pos
  apply hh.trans
  have he : Real.exp (-(3 * a / 8) * t) =
      Real.exp (-(a / 8) * t) * Real.exp (-(a / 4) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  calc
    _ = (gaussianGrowingMomentConstant *
        ((1 + t ^ 2) * (1 + a * t) * Real.exp (-(a / 8) * t))) *
          Real.exp (-(a / 4) * t) := by ring
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpoly hC.le) (Real.exp_pos (-(a / 4) * t)).le]

#print axioms eventually_gaussianGrowingMomentReduction
#print axioms norm_gaussianHigherCentredVaughanError_le_exponential
#print axioms norm_gaussianHigherCentredVaughanError_le_height
#print axioms norm_gaussianHigherCentredVaughanError_le_order_budget

end GaloisForLFunctions.ExceptionalLayerTheory

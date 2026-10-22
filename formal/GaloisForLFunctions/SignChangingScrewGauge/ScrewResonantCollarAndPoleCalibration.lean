import GaloisForLFunctions.SignChangingScrewGauge.NetPrimeAutocorrelationAndEdgeTentResolution

/-!
# Screw-Resonant Zero-Form Ledger, Plastic Crossover, and Collar Moment Calibration

This module establishes the third leg of Mechanism 3 of Project Argon
(`docs/reports/review-2110/argon.md`, §1.4):

1. **Exact Unification of `screwRegularKernel` and `archLevyDensity`**
   (`screwRegularKernel_eq_two_mul_cosh_sub_archLevyDensity`,
   `archLevyDensity_sub_two_mul_cosh_eq_neg_screwRegularKernel`,
   `archJump_sub_two_cosh_jump_eq_screwResonantJumpEnergy`):
   For every `t > 0`, Suzuki's regular screw kernel satisfies
   `screwRegularKernel t = 2 * Real.cosh (t / 2) - archLevyDensity t`.
   Consequently, subtracting the `2 cosh(t/2)` pole-kernel jump integral from the archimedean
   Lévy jump integral yields `screwResonantJumpEnergy P F = ∫_{t > 0} (−screwRegularKernel t) * gaugeJumpProfile P F t`.

2. **Sub-Plastic vs. Super-Plastic Screw-Kernel Dichotomy**
   (`screwRegularKernel_crossover_dichotomy`,
   `screwResonantJumpEnergy_nonneg_of_two_mul_le_screwSignThreshold`,
   `screwRegularKernel_mul_neg_autoCorr_pos_of_gt_threshold`):
   - The plastic threshold `screwSignThreshold = Real.log plasticRoot` satisfies
     `1 / 10 < screwSignThreshold < Real.log 2` and `screwRegularKernel screwSignThreshold = 0`.
   - Below the plastic threshold (`0 < t ≤ screwSignThreshold`), `-screwRegularKernel t ≥ 0`, so
     `0 ≤ screwResonantJumpEnergy P F` whenever `P ≥ 0` and `2 * R ≤ screwSignThreshold`.
   - Above the plastic threshold (`screwSignThreshold < t`), `screwRegularKernel t > 0`, so any
     opposite-sign two-bump lag with `autoCorr F t < 0` produces strictly positive screw-resonant
     cross-energy `0 < screwRegularKernel t * (-autoCorr F t)`.

3. **Odd-Sector Even-Pole Vanishing & Sign-Changing Collar Cosh-Moment Calibration**
   (`evenPoleMoment_eq_zero_of_odd`, `evenPoleMoment_add`,
   `evenPoleMoment_collar_cancellation`):
   Every odd profile `F` has `evenPoleMoment F = 0`, and decomposing a gauge `P = P₀ + P_col`
   into an inner plateau `P₀` and an outer sign-changing collar `P_col` with
   `evenPoleMoment P_col = -evenPoleMoment P₀` neutralizes `evenPoleMoment (P₀ + P_col) = 0`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.SignChangingScrewGauge

/-! ### Exact unification of `screwRegularKernel` and `archLevyDensity` -/

/-- On `(0, ∞)`, Suzuki's regular screw kernel `screwRegularKernel t` equals
`2 * Real.cosh (t / 2) - archLevyDensity t`. -/
theorem screwRegularKernel_eq_two_mul_cosh_sub_archLevyDensity {t : ℝ} (ht : 0 < t) :
    screwRegularKernel t = 2 * Real.cosh (t / 2) - archLevyDensity t := by
  rw [screwRegularKernel_eq_tailForm ht, Real.cosh_eq]
  unfold archLevyDensity
  rw [show -t / 2 = -(t / 2) by ring, show -2 * t = -(2 * t) by ring]
  ring

/-- Dual form: `archLevyDensity t - 2 * Real.cosh (t / 2) = -screwRegularKernel t` for `t > 0`. -/
theorem archLevyDensity_sub_two_mul_cosh_eq_neg_screwRegularKernel {t : ℝ} (ht : 0 < t) :
    archLevyDensity t - 2 * Real.cosh (t / 2) = -screwRegularKernel t := by
  rw [screwRegularKernel_eq_two_mul_cosh_sub_archLevyDensity ht]
  ring

/-- `Real.exp screwSignThreshold = plasticRoot`. -/
theorem exp_screwSignThreshold : Real.exp screwSignThreshold = plasticRoot :=
  Real.exp_log plasticRoot_pos

/-- At the plastic threshold `screwSignThreshold = Real.log plasticRoot`,
`screwRegularKernel screwSignThreshold = 0`. -/
theorem screwRegularKernel_screwSignThreshold : screwRegularKernel screwSignThreshold = 0 := by
  have ht := screwSignThreshold_pos
  have hfac := screwKernelSignFactor_pos ht
  have hmul := screwRegularKernel_mul_eq_cubic ht
  rw [exp_screwSignThreshold, plasticRoot_cubic] at hmul
  exact (mul_eq_zero.mp hmul).resolve_right hfac.ne'

/-- On `(0, screwSignThreshold]`, `screwRegularKernel t ≤ 0`. -/
theorem screwRegularKernel_nonpos_of_le {t : ℝ} (ht : 0 < t) (hle : t ≤ screwSignThreshold) :
    screwRegularKernel t ≤ 0 := by
  rcases eq_or_lt_of_le hle with rfl | hlt
  · exact screwRegularKernel_screwSignThreshold.le
  · exact (screwRegularKernel_neg_of_lt_threshold ht hlt).le

/-- On `(screwSignThreshold, ∞)`, `0 < screwRegularKernel t`. -/
theorem screwRegularKernel_pos_of_gt {t : ℝ} (hgt : screwSignThreshold < t) :
    0 < screwRegularKernel t :=
  (screwRegularKernel_pos_iff (screwSignThreshold_pos.trans hgt)).mpr hgt

/-- Rational lower bound `331 / 250 < plasticRoot`. -/
theorem plasticRoot_gt : (331 : ℝ) / 250 < plasticRoot := by
  by_contra hle
  rw [not_lt] at hle
  have hpos : 0 < ((331 : ℝ) / 250) ^ 3 - (331 / 250) - 1 ↔ plasticRoot < 331 / 250 :=
    cubic_pos_iff_plasticRoot_lt (by norm_num)
  rcases eq_or_lt_of_le hle with hEq | hlt
  · have hc := plasticRoot_cubic
    rw [hEq] at hc
    norm_num at hc
  · have hc := hpos.mpr hlt
    norm_num at hc

/-- Explicit lower bound `1 / 10 < screwSignThreshold`. -/
theorem one_tenth_lt_screwSignThreshold : (1 : ℝ) / 10 < screwSignThreshold := by
  rw [screwSignThreshold, Real.lt_log_iff_exp_lt plasticRoot_pos]
  have h1 : (9 : ℝ) / 10 ≤ Real.exp (-(1 / 10 : ℝ)) := by
    linarith [Real.add_one_le_exp (-(1 / 10 : ℝ))]
  have h2 : Real.exp (1 / 10 : ℝ) * Real.exp (-(1 / 10 : ℝ)) = 1 := by
    rw [← Real.exp_add]; simp
  have hexp : Real.exp (1 / 10 : ℝ) ≤ 10 / 9 := by
    nlinarith [Real.exp_pos (1 / 10 : ℝ)]
  linarith [plasticRoot_gt]

/-- Explicit upper bound `screwSignThreshold < Real.log 2`. -/
theorem screwSignThreshold_lt_log_two : screwSignThreshold < Real.log 2 :=
  Real.log_lt_log plasticRoot_pos plasticRoot_mem_Ioo.2

/-- **Plastic Crossover Dichotomy of the Screw Kernel.**
The regular screw kernel `screwRegularKernel t = 2 cosh(t/2) − archLevyDensity t` crosses zero
at the plastic threshold `screwSignThreshold = Real.log plasticRoot`:
1. `1 / 10 < screwSignThreshold` and `screwSignThreshold < Real.log 2`,
2. `screwRegularKernel screwSignThreshold = 0`,
3. `-screwRegularKernel t ≥ 0` on the sub-plastic core `0 < t ≤ screwSignThreshold`,
4. `-screwRegularKernel t < 0` on the super-plastic tail `screwSignThreshold < t`. -/
theorem screwRegularKernel_crossover_dichotomy :
    (1 / 10 < screwSignThreshold ∧ screwSignThreshold < Real.log 2) ∧
      screwRegularKernel screwSignThreshold = 0 ∧
      (∀ t, 0 < t → t ≤ screwSignThreshold → 0 ≤ -screwRegularKernel t) ∧
      (∀ t, screwSignThreshold < t → -screwRegularKernel t < 0) := by
  refine ⟨⟨one_tenth_lt_screwSignThreshold, screwSignThreshold_lt_log_two⟩,
    screwRegularKernel_screwSignThreshold, fun t ht hle => ?_, fun t hgt => ?_⟩
  · linarith [screwRegularKernel_nonpos_of_le ht hle]
  · linarith [screwRegularKernel_pos_of_gt hgt]

/-! ### Support and sign properties of `gaugeJumpProfile` and `screwResonantJumpEnergy` -/

/-- When `0 ≤ P` everywhere, `0 ≤ gaugeJumpProfile P F t` at every shift `t`. -/
theorem gaugeJumpProfile_nonneg {P : ℝ → ℝ} (hP0 : ∀ y, 0 ≤ P y) (F : ℝ → ℝ) (t : ℝ) :
    0 ≤ gaugeJumpProfile P F t := by
  unfold gaugeJumpProfile signedShiftJump
  exact integral_nonneg fun x => mul_nonneg (mul_nonneg (hP0 x) (hP0 (x + t))) (sq_nonneg _)

/-- When `P` vanishes for `R ≤ |y|`, `gaugeJumpProfile P F t = 0` for every shift `2 * R ≤ t`. -/
theorem gaugeJumpProfile_eq_zero_of_ge {P F : ℝ → ℝ} {R t : ℝ}
    (hPR : ∀ y, R ≤ |y| → P y = 0) (ht : 2 * R ≤ t) :
    gaugeJumpProfile P F t = 0 := by
  unfold gaugeJumpProfile signedShiftJump
  have hzero : ∀ x, P x * P (x + t) * (F x - F (x + t)) ^ 2 = 0 := fun x => by
    by_cases hx : R ≤ |x|
    · rw [hPR x hx, zero_mul, zero_mul]
    · have hx' : |x| < R := not_le.mp hx
      have hxt : R ≤ |x + t| := by
        have h1 := (abs_lt.mp hx').1
        linarith [le_abs_self (x + t)]
      rw [hPR (x + t) hxt, mul_zero, zero_mul]
  simp [hzero]

/-- The screw-resonant archimedean jump energy:
`∫_{t > 0} (−screwRegularKernel t) * gaugeJumpProfile P F t dt`, where
`screwRegularKernel t = 2 cosh(t/2) − archLevyDensity t`. -/
def screwResonantJumpEnergy (P F : ℝ → ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), -screwRegularKernel t * gaugeJumpProfile P F t

/-- The cosh collar potential energy:
`2 ∫_ℝ F(x)² P(x) (∫_ℝ P(y) cosh((x − y)/2) dy) dx`. -/
def coshCollarPotential (P F : ℝ → ℝ) : ℝ :=
  2 * ∫ x, F x ^ 2 * P x * ∫ y, P y * Real.cosh ((x - y) / 2)

/-- **Exact Screw-Resonant Decomposition of the Archimedean-Minus-Cosh Jump Integral.**
For any gauge `P` and profile `F` such that `archLevyDensity · * gaugeJumpProfile P F ·` and
`2 * cosh(·/2) * gaugeJumpProfile P F ·` are integrable on `(0, ∞)`, their difference equals
`screwResonantJumpEnergy P F`. -/
theorem archJump_sub_two_cosh_jump_eq_screwResonantJumpEnergy {P F : ℝ → ℝ}
    (hω : IntegrableOn (fun t => archLevyDensity t * gaugeJumpProfile P F t) (Ioi 0))
    (hc : IntegrableOn (fun t => 2 * Real.cosh (t / 2) * gaugeJumpProfile P F t) (Ioi 0)) :
    (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P F t) -
        (∫ t in Ioi (0 : ℝ), 2 * Real.cosh (t / 2) * gaugeJumpProfile P F t) =
      screwResonantJumpEnergy P F := by
  unfold screwResonantJumpEnergy
  rw [← integral_sub hω hc]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have h := archLevyDensity_sub_two_mul_cosh_eq_neg_screwRegularKernel ht
  calc archLevyDensity t * gaugeJumpProfile P F t -
        2 * Real.cosh (t / 2) * gaugeJumpProfile P F t
      = (archLevyDensity t - 2 * Real.cosh (t / 2)) * gaugeJumpProfile P F t := by ring
    _ = -screwRegularKernel t * gaugeJumpProfile P F t := by rw [h]

/-- **Sub-Plastic Positivity of the Screw-Resonant Jump Energy.**
When `0 ≤ P` and the collar radius satisfies `2 * R ≤ screwSignThreshold`, every jump profile
`gaugeJumpProfile P F t` is supported in `(0, 2R] ⊆ (0, screwSignThreshold]` where
`-screwRegularKernel t ≥ 0`, so `0 ≤ screwResonantJumpEnergy P F`. -/
theorem screwResonantJumpEnergy_nonneg_of_two_mul_le_screwSignThreshold {P F : ℝ → ℝ} {R : ℝ}
    (hP0 : ∀ y, 0 ≤ P y) (hPR : ∀ y, R ≤ |y| → P y = 0)
    (hR : 2 * R ≤ screwSignThreshold) :
    0 ≤ screwResonantJumpEnergy P F := by
  unfold screwResonantJumpEnergy
  refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  by_cases hts : t ≤ screwSignThreshold
  · exact mul_nonneg (by linarith [screwRegularKernel_nonpos_of_le ht0 hts])
      (gaugeJumpProfile_nonneg hP0 F t)
  · have hts' : screwSignThreshold < t := not_le.mp hts
    rw [gaugeJumpProfile_eq_zero_of_ge hPR (by linarith), mul_zero]

/-- **Super-Plastic Two-Bump Cross-Correlation Positivity.**
At any shift `t > screwSignThreshold` where an odd profile `F` has negative autocorrelation
`autoCorr F t < 0` (such as an odd two-bump profile separated across the plastic threshold),
the screw-resonant cross-term `screwRegularKernel t * (-autoCorr F t)` is strictly positive. -/
theorem screwRegularKernel_mul_neg_autoCorr_pos_of_gt_threshold {F : ℝ → ℝ} {t : ℝ}
    (ht : screwSignThreshold < t) (hA : autoCorr F t < 0) :
    0 < screwRegularKernel t * (-autoCorr F t) :=
  mul_pos (screwRegularKernel_pos_of_gt ht) (neg_pos.mpr hA)

/-! ### Odd-sector even-pole vanishing and sign-changing collar cosh-moment calibration -/

/-- For any odd function `F`, `evenPoleMoment F = ∫ x, F x * cosh(x / 2) = 0`. -/
theorem evenPoleMoment_eq_zero_of_odd {F : ℝ → ℝ} (hodd : ∀ x, F (-x) = -F x) :
    evenPoleMoment F = 0 := by
  unfold evenPoleMoment
  have hneg : (∫ x, F (-x) * Real.cosh (-x / 2)) = ∫ x, F x * Real.cosh (x / 2) :=
    integral_neg_eq_self (fun x => F x * Real.cosh (x / 2)) volume
  have hpt : (∫ x, F (-x) * Real.cosh (-x / 2)) = -∫ x, F x * Real.cosh (x / 2) := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [hodd x, neg_div, Real.cosh_neg]
    ring
  linarith

/-- Linearity of `evenPoleMoment` for continuous compactly supported functions. -/
theorem evenPoleMoment_add {P₀ P_col : ℝ → ℝ}
    (hP₀ : Continuous P₀) (hP₀c : HasCompactSupport P₀)
    (hPcol : Continuous P_col) (hPcolc : HasCompactSupport P_col) :
    evenPoleMoment (fun y => P₀ y + P_col y) =
      evenPoleMoment P₀ + evenPoleMoment P_col := by
  unfold evenPoleMoment
  have hI₀ : Integrable fun y => P₀ y * Real.cosh (y / 2) :=
    (hP₀.mul (by fun_prop)).integrable_of_hasCompactSupport hP₀c.mul_right
  have hIcol : Integrable fun y => P_col y * Real.cosh (y / 2) :=
    (hPcol.mul (by fun_prop)).integrable_of_hasCompactSupport hPcolc.mul_right
  rw [← integral_add hI₀ hIcol]
  exact integral_congr_ae (Eventually.of_forall fun y => by dsimp only; ring)

/-- **Sign-Changing Collar Cosh-Moment Neutralization.**
For any compactly supported continuous plateau `P₀` and sign-changing collar `P_col` such that
`evenPoleMoment P_col = -evenPoleMoment P₀`, the combined gauge `P = P₀ + P_col` has vanishing
even pole moment `evenPoleMoment (fun y => P₀ y + P_col y) = 0`. -/
theorem evenPoleMoment_collar_cancellation {P₀ P_col : ℝ → ℝ}
    (hP₀ : Continuous P₀) (hP₀c : HasCompactSupport P₀)
    (hPcol : Continuous P_col) (hPcolc : HasCompactSupport P_col)
    (hcancel : evenPoleMoment P_col = -evenPoleMoment P₀) :
    evenPoleMoment (fun y => P₀ y + P_col y) = 0 := by
  rw [evenPoleMoment_add hP₀ hP₀c hPcol hPcolc, hcancel]
  ring

end GaloisForLFunctions.SignChangingScrewGauge

end

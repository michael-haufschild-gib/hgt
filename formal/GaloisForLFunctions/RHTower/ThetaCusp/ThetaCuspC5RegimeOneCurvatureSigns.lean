import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodScaleLocalTailCooling
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodSixthFockSector
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodHighSourceJets
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionSixthLogJets
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomFourthMomentFloor
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCompletedCurvatureProjectiveFarTail
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFixedActionC5JacobianGermClosure
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspExactCompletedC5SeamFarTail

/-!
# Regime-I sign facts for the theta-cusp log-curvature jets

Let `c = thetaCuspLogCurvature` (`c = -ℓ''` for the theta-cusp log source `ℓ`) with jets
`c' = thetaCuspLogCurvatureJet`, `c'' = thetaCuspLogCurvatureJetTwo`,
`c''' = thetaCuspLogCurvatureJetThree`.  The corpus writes every jet as a first-atom
(Born–Witten) rational function of `q = A - 3/2` (`A = π e^{2x}`) minus a likelihood jet
`J_k`, a polynomial in the cumulants of the tilted higher-atom spectral measure.

**Regime I** is `A ≥ 6`.  This module proves there

* `(R2)` `c' > 0`, `(R3)` `c'' > 0`, `(R4)` `c · c''' ≤ c' · c''`,

which are the pointwise inputs of the completed C5 compensation gate
(`ThetaCuspC5CompletedGateSigns`).  The engine is a sharp support comparison: the tilted
measure lives on `t ≥ 3`, so for a tilt gap `δ ≥ m/3` the `m`-th moment obeys
`M_m(B) ≤ 3^m e^{-3δ} M_0(B - δ)`; calibrated at `x = 0` (`399 · M_0 < 1`) this gives
`NM_m ≤ 3^m ε(x)` with `ε(x) = e^{-3(A - π)}/399`.  The likelihood jets are then
`O(A^k ε)`, while the Born–Witten difference has the exact closed form
`BW₂ BW₅ - BW₃ BW₄ = -(2q+3)² (1296 q⁴ + 4536 q³ + 4536 q² + 2916 q + 2916) / q⁷`.
-/

open MeasureTheory Set

namespace RHTower

/-- For `t ≥ a > 0` and `δ ≥ m / a`, the function `t ↦ t^m e^{-δ t}` is maximal at `t = a`. -/
theorem pow_mul_exp_neg_le_of_le {m : ℕ} {δ a t : ℝ} (ha : 0 < a)
    (hδ : (m : ℝ) / a ≤ δ) (ht : a ≤ t) :
    t ^ m * Real.exp (-(δ * t)) ≤ a ^ m * Real.exp (-(δ * a)) := by
  have hq : t / a ≤ Real.exp (t / a - 1) := by
    have := Real.add_one_le_exp (t / a - 1)
    linarith
  have hqm : (t / a) ^ m ≤ Real.exp ((m : ℝ) * (t / a - 1)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (div_nonneg (by linarith) ha.le) hq m
  have hexp : Real.exp ((m : ℝ) * (t / a - 1)) ≤ Real.exp (δ * (t - a)) := by
    apply Real.exp_le_exp.mpr
    have h1 : (m : ℝ) * (t / a - 1) = (m / a) * (t - a) := by
      field_simp
    rw [h1]
    exact mul_le_mul_of_nonneg_right hδ (by linarith)
  have hsplit : t ^ m = a ^ m * (t / a) ^ m := by
    rw [← mul_pow, mul_div_cancel₀ _ ha.ne']
  calc t ^ m * Real.exp (-(δ * t))
      = a ^ m * ((t / a) ^ m * Real.exp (-(δ * t))) := by rw [hsplit]; ring
    _ ≤ a ^ m * (Real.exp (δ * (t - a)) * Real.exp (-(δ * t))) := by
        gcongr
        exact hqm.trans hexp
    _ = a ^ m * Real.exp (-(δ * a)) := by
        rw [← Real.exp_add]
        ring_nf

/-- **Sharp support comparison for all tilted moments.**  A tilt gap `δ = B - B₀ ≥ m/3`
transports the `m`-th moment with the factor `3^m e^{-3δ}`. -/
theorem thetaCuspHigherLikelihoodSpectralMoment_le_three_pow_mul_exp_support_comparison
    (m : ℕ) {B₀ B : ℝ} (hB₀ : 0 < B₀) (hδ : (m : ℝ) / 3 ≤ B - B₀) :
    thetaCuspHigherLikelihoodSpectralMoment B m ≤
      3 ^ m * Real.exp (-(3 * (B - B₀))) * thetaCuspHigherLikelihoodSpectralMoment B₀ 0 := by
  have hm3 : (0 : ℝ) ≤ (m : ℝ) / 3 := by positivity
  have hB : 0 < B := by linarith
  rw [thetaCuspHigherLikelihoodSpectralMoment_eq_integral,
    thetaCuspHigherLikelihoodSpectralMoment_eq_integral]
  have hleft := integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure m hB
  have hright :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 0 hB₀).const_mul
      (3 ^ m * Real.exp (-(3 * (B - B₀))))
  rw [← integral_const_mul]
  apply integral_mono_ae hleft hright
  filter_upwards [ae_three_le_thetaCuspHigherLikelihoodSpectralMeasure] with t ht
  simp only [pow_zero, one_mul]
  have key := pow_mul_exp_neg_le_of_le (m := m) (δ := B - B₀) (a := 3) (t := t)
    (by norm_num) hδ ht
  have hsplit : Real.exp (-B * t) = Real.exp (-((B - B₀) * t)) * Real.exp (-B₀ * t) := by
    rw [← Real.exp_add]
    ring_nf
  have hsplit' : Real.exp (-(3 * (B - B₀))) = Real.exp (-((B - B₀) * 3)) := by ring_nf
  rw [hsplit, hsplit', ← mul_assoc]
  exact mul_le_mul_of_nonneg_right key (Real.exp_pos _).le

/-- The regime-I likelihood scale `ε(x) = e^{-3(A(x) - π)} / 399`. -/
noncomputable def regimeOneLikelihoodScale (x : ℝ) : ℝ :=
  Real.exp (-(3 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) / 399

theorem regimeOneLikelihoodScale_pos (x : ℝ) : 0 < regimeOneLikelihoodScale x := by
  unfold regimeOneLikelihoodScale
  positivity

theorem thetaCuspLikelihoodCoordinate_zero_eq :
    thetaCuspLikelihoodCoordinate 0 = Real.pi - 3 / 2 := by
  simp [thetaCuspLikelihoodCoordinate]

theorem thetaCuspLikelihoodCoordinate_sub_zero (x : ℝ) :
    thetaCuspLikelihoodCoordinate x - thetaCuspLikelihoodCoordinate 0 =
      thetaCuspSingleAtomReflectionScale 1 x - Real.pi := by
  rw [thetaCuspSingleAtomScale_likelihoodCoordinate, thetaCuspLikelihoodCoordinate_zero_eq]
  ring

/-- Calibration at the modular point: `M₀(B₀) < 1/399`. -/
theorem thetaCuspHigherLikelihoodSpectralMoment_zero_coordinate_zero_lt :
    thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate 0) 0 < 1 / 399 := by
  have hB₀ : 0 < thetaCuspLikelihoodCoordinate 0 := thetaCuspLikelihoodCoordinate_pos le_rfl
  rw [thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB₀]
  have h := three_hundred_ninety_nine_mul_thetaCuspHigherLikelihoodSpectralResponse_lt_one
    (x := 0) le_rfl
  rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 399)]
  linarith

/-- The partition function is at least one. -/
theorem one_le_thetaCuspLikelihoodPartition {B : ℝ} (hB : 0 < B) :
    1 ≤ thetaCuspLikelihoodPartition B := by
  unfold thetaCuspLikelihoodPartition
  have h0 := thetaCuspHigherLikelihoodSpectralMoment_nonneg (B := B) 0
  rw [thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB] at h0
  linarith

/-- **Regime-I moment majorant.**  For `A(x) - π ≥ m/3` the normalized `m`-th moment is at
most `3^m ε(x)`. -/
theorem thetaCuspLikelihoodNormalizedMoment_le_regimeOneScale (m : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (hm : (m : ℝ) / 3 ≤ thetaCuspSingleAtomReflectionScale 1 x - Real.pi) :
    thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) m ≤
      3 ^ m * regimeOneLikelihoodScale x := by
  have hB := thetaCuspLikelihoodCoordinate_pos hx
  have hB₀ : 0 < thetaCuspLikelihoodCoordinate 0 := thetaCuspLikelihoodCoordinate_pos le_rfl
  have hδ : (m : ℝ) / 3 ≤ thetaCuspLikelihoodCoordinate x - thetaCuspLikelihoodCoordinate 0 := by
    rwa [thetaCuspLikelihoodCoordinate_sub_zero]
  have hcmp :=
    thetaCuspHigherLikelihoodSpectralMoment_le_three_pow_mul_exp_support_comparison m hB₀ hδ
  rw [thetaCuspLikelihoodCoordinate_sub_zero] at hcmp
  have hcal := thetaCuspHigherLikelihoodSpectralMoment_zero_coordinate_zero_lt
  have hZ := one_le_thetaCuspLikelihoodPartition hB
  have hMnn := thetaCuspHigherLikelihoodSpectralMoment_nonneg (B := thetaCuspLikelihoodCoordinate x) m
  unfold thetaCuspLikelihoodNormalizedMoment regimeOneLikelihoodScale
  have h3 : (0 : ℝ) ≤ 3 ^ m * Real.exp (-(3 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) := by
    positivity
  calc thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) m /
        thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x)
      ≤ thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) m :=
        div_le_self hMnn hZ
    _ ≤ 3 ^ m * Real.exp (-(3 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) *
        thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate 0) 0 := hcmp
    _ ≤ 3 ^ m * Real.exp (-(3 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) * (1 / 399) :=
        mul_le_mul_of_nonneg_left hcal.le h3
    _ = 3 ^ m * (Real.exp (-(3 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) / 399) := by
        ring

/-! ## Elementary exponential numerics -/

theorem exp_three_pi_lt_12704 : Real.exp (3 * Real.pi) < 12704 := by
  have h := three_div_seventy_lt_exp_neg_pi
  have hprod : Real.exp (-Real.pi) * Real.exp Real.pi = 1 := by
    rw [← Real.exp_add]
    simp
  have hpi : Real.exp Real.pi < 70 / 3 := by
    nlinarith [Real.exp_pos (-Real.pi), Real.exp_pos Real.pi]
  have h3 : Real.exp (3 * Real.pi) = Real.exp Real.pi ^ (3 : ℕ) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h3]
  calc Real.exp Real.pi ^ (3 : ℕ) < (70 / 3) ^ (3 : ℕ) :=
        pow_lt_pow_left₀ hpi (Real.exp_pos _).le (by norm_num)
    _ < 12704 := by norm_num

theorem exp_eighteen_gt : (65000000 : ℝ) < Real.exp 18 := by
  have h := Real.exp_one_gt_d9
  have h18 : Real.exp 18 = Real.exp 1 ^ (18 : ℕ) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h18]
  calc (65000000 : ℝ) < 2.7182818283 ^ (18 : ℕ) := by norm_num
    _ < Real.exp 1 ^ (18 : ℕ) := pow_lt_pow_left₀ h (by norm_num) (by norm_num)

theorem exp_twentyOne_gt : (1300000000 : ℝ) < Real.exp 21 := by
  have h := Real.exp_one_gt_d9
  have h21 : Real.exp 21 = Real.exp 1 ^ (21 : ℕ) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h21]
  calc (1300000000 : ℝ) < 2.7182818283 ^ (21 : ℕ) := by norm_num
    _ < Real.exp 1 ^ (21 : ℕ) := pow_lt_pow_left₀ h (by norm_num) (by norm_num)

theorem exp_thirty_gt : (10680000000000 : ℝ) < Real.exp 30 := by
  have h := Real.exp_one_gt_d9
  have h30 : Real.exp 30 = Real.exp 1 ^ (30 : ℕ) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h30]
  calc (10680000000000 : ℝ) < 2.7182818283 ^ (30 : ℕ) := by norm_num
    _ < Real.exp 1 ^ (30 : ℕ) := pow_lt_pow_left₀ h (by norm_num) (by norm_num)

/-- `ε` as a function of the scale: `ε = e^{3π} e^{-3A} / 399`. -/
theorem regimeOneLikelihoodScale_eq (x : ℝ) :
    regimeOneLikelihoodScale x =
      Real.exp (3 * Real.pi) / 399 *
        Real.exp (-(3 * thetaCuspSingleAtomReflectionScale 1 x)) := by
  unfold regimeOneLikelihoodScale
  rw [show -(3 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi)) =
      3 * Real.pi + -(3 * thetaCuspSingleAtomReflectionScale 1 x) by ring, Real.exp_add]
  ring

/-- Monotone decay of `A^k ε(A)` beyond `A₁ ≥ k/3`. -/
theorem pow_mul_regimeOneLikelihoodScale_le {k : ℕ} {A₁ : ℝ} {x : ℝ}
    (hA₁ : 0 < A₁) (hk : (k : ℝ) / A₁ ≤ 3)
    (hA : A₁ ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspSingleAtomReflectionScale 1 x ^ k * regimeOneLikelihoodScale x ≤
      A₁ ^ k * (Real.exp (3 * Real.pi) / 399 * Real.exp (-(3 * A₁))) := by
  rw [regimeOneLikelihoodScale_eq]
  have key := pow_mul_exp_neg_le_of_le (m := k) (δ := 3) (a := A₁)
    (t := thetaCuspSingleAtomReflectionScale 1 x) hA₁ hk hA
  have hc : 0 ≤ Real.exp (3 * Real.pi) / 399 := by positivity
  calc thetaCuspSingleAtomReflectionScale 1 x ^ k *
        (Real.exp (3 * Real.pi) / 399 * Real.exp (-(3 * thetaCuspSingleAtomReflectionScale 1 x)))
      = Real.exp (3 * Real.pi) / 399 *
          (thetaCuspSingleAtomReflectionScale 1 x ^ k *
            Real.exp (-(3 * thetaCuspSingleAtomReflectionScale 1 x))) := by ring
    _ ≤ Real.exp (3 * Real.pi) / 399 * (A₁ ^ k * Real.exp (-(3 * A₁))) :=
        mul_le_mul_of_nonneg_left key hc
    _ = A₁ ^ k * (Real.exp (3 * Real.pi) / 399 * Real.exp (-(3 * A₁))) := by ring

/-- Numerical value of the base scale at `A = 6`. -/
theorem base_scale_six_lt :
    Real.exp (3 * Real.pi) / 399 * Real.exp (-(3 * (6 : ℝ))) < 49 / 100000000 := by
  have h1 := exp_three_pi_lt_12704
  have h2 := exp_eighteen_gt
  have hinv : Real.exp (-(3 * (6 : ℝ))) = 1 / Real.exp 18 := by
    rw [show -(3 * (6 : ℝ)) = -18 by norm_num, Real.exp_neg]
    ring
  rw [hinv]
  have hE : 0 < Real.exp 18 := Real.exp_pos _
  rw [show Real.exp (3 * Real.pi) / 399 * (1 / Real.exp 18) =
      Real.exp (3 * Real.pi) / (399 * Real.exp 18) by field_simp]
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

theorem base_scale_seven_lt :
    Real.exp (3 * Real.pi) / 399 * Real.exp (-(3 * (7 : ℝ))) < 245 / 10000000000 := by
  have h1 := exp_three_pi_lt_12704
  have h2 := exp_twentyOne_gt
  have hinv : Real.exp (-(3 * (7 : ℝ))) = 1 / Real.exp 21 := by
    rw [show -(3 * (7 : ℝ)) = -21 by norm_num, Real.exp_neg]
    ring
  rw [hinv]
  have hE : 0 < Real.exp 21 := Real.exp_pos _
  rw [show Real.exp (3 * Real.pi) / 399 * (1 / Real.exp 21) =
      Real.exp (3 * Real.pi) / (399 * Real.exp 21) by field_simp]
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

theorem base_scale_ten_lt :
    Real.exp (3 * Real.pi) / 399 * Real.exp (-(3 * (10 : ℝ))) < 31 / 10000000000000 := by
  have h1 := exp_three_pi_lt_12704
  have h2 := exp_thirty_gt
  have hinv : Real.exp (-(3 * (10 : ℝ))) = 1 / Real.exp 30 := by
    rw [show -(3 * (10 : ℝ)) = -30 by norm_num, Real.exp_neg]
    ring
  rw [hinv]
  have hE : 0 < Real.exp 30 := Real.exp_pos _
  rw [show Real.exp (3 * Real.pi) / 399 * (1 / Real.exp 30) =
      Real.exp (3 * Real.pi) / (399 * Real.exp 30) by field_simp]
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

/-- In regime I the scale itself is below `5·10⁻⁷`. -/
theorem regimeOneLikelihoodScale_le_of_six_le {x : ℝ}
    (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    regimeOneLikelihoodScale x ≤ 5 / 10000000 := by
  have h := pow_mul_regimeOneLikelihoodScale_le (k := 0) (A₁ := 6) (by norm_num) (by norm_num) hA
  simp only [pow_zero, one_mul] at h
  have := base_scale_six_lt
  linarith

/-! ## Cumulant majorants (pure real arithmetic) -/

theorem abs_variance_form_le {m2 μ ε : ℝ} (hε : ε ≤ 1 / 1000000) (hε0 : 0 ≤ ε)
    (hμ0 : 0 ≤ μ) (hμ : μ ≤ 3 * ε) (h20 : 0 ≤ m2) (h2 : m2 ≤ 9 * ε) :
    |m2 - μ ^ (2 : ℕ)| ≤ 9 * ε := by
  have hμ2 : μ ^ (2 : ℕ) ≤ 9 * ε * ε := by nlinarith
  rw [abs_le]
  constructor <;> nlinarith

theorem abs_third_cumulant_form_le {m2 m3 μ ε : ℝ} (hε : ε ≤ 1 / 1000000) (hε0 : 0 ≤ ε)
    (hμ0 : 0 ≤ μ) (hμ : μ ≤ 3 * ε) (h20 : 0 ≤ m2) (h2 : m2 ≤ 9 * ε)
    (h30 : 0 ≤ m3) (h3 : m3 ≤ 27 * ε) :
    |m3 - 3 * μ * m2 + 2 * μ ^ (3 : ℕ)| ≤ 28 * ε := by
  have hμm2 : μ * m2 ≤ 27 * (ε * ε) := by nlinarith
  have hμm2' : 0 ≤ μ * m2 := mul_nonneg hμ0 h20
  have hμ3 : μ ^ (3 : ℕ) ≤ 27 * (ε * ε * ε) := by
    have := pow_le_pow_left₀ hμ0 hμ 3
    nlinarith
  have hμ3' : 0 ≤ μ ^ (3 : ℕ) := by positivity
  have hεε : ε * ε ≤ ε / 1000000 := by nlinarith
  have hεεε : ε * ε * ε ≤ ε / 1000000 := by nlinarith
  rw [abs_le]
  constructor <;> nlinarith

theorem abs_fourth_cumulant_form_le {m2 m3 m4 μ ε : ℝ} (hε : ε ≤ 1 / 1000000) (hε0 : 0 ≤ ε)
    (hμ0 : 0 ≤ μ) (hμ : μ ≤ 3 * ε) (h20 : 0 ≤ m2) (h2 : m2 ≤ 9 * ε)
    (h30 : 0 ≤ m3) (h3 : m3 ≤ 27 * ε) (h40 : 0 ≤ m4) (h4 : m4 ≤ 81 * ε) :
    |m4 - 4 * μ * m3 - 3 * m2 ^ (2 : ℕ) + 12 * μ ^ (2 : ℕ) * m2 - 6 * μ ^ (4 : ℕ)| ≤ 82 * ε := by
  have hεε : ε * ε ≤ ε / 1000000 := by nlinarith
  have hμm3 : μ * m3 ≤ 81 * (ε * ε) := by nlinarith
  have hμm3' : 0 ≤ μ * m3 := mul_nonneg hμ0 h30
  have hm22 : m2 ^ (2 : ℕ) ≤ 81 * (ε * ε) := by nlinarith
  have hm22' : 0 ≤ m2 ^ (2 : ℕ) := by positivity
  have hμ2 : μ ^ (2 : ℕ) ≤ 9 * (ε * ε) := by nlinarith
  have hμ2m2 : μ ^ (2 : ℕ) * m2 ≤ 81 * (ε * ε) * ε := by
    have := mul_le_mul hμ2 h2 h20 (by positivity)
    nlinarith
  have hμ2m2' : 0 ≤ μ ^ (2 : ℕ) * m2 := by positivity
  have hμ4 : μ ^ (4 : ℕ) ≤ 81 * (ε * ε) * (ε * ε) := by
    have := pow_le_pow_left₀ hμ0 hμ 4
    nlinarith
  have hμ4' : 0 ≤ μ ^ (4 : ℕ) := by positivity
  have hεεε : ε * ε * ε ≤ ε / 1000000 := by nlinarith
  have hε4 : ε * ε * (ε * ε) ≤ ε / 1000000 := by nlinarith
  rw [abs_le]
  constructor <;> nlinarith

theorem abs_fifth_cumulant_form_le {m2 m3 m4 m5 μ ε : ℝ} (hε : ε ≤ 1 / 1000000) (hε0 : 0 ≤ ε)
    (hμ0 : 0 ≤ μ) (hμ : μ ≤ 3 * ε) (h20 : 0 ≤ m2) (h2 : m2 ≤ 9 * ε)
    (h30 : 0 ≤ m3) (h3 : m3 ≤ 27 * ε) (h40 : 0 ≤ m4) (h4 : m4 ≤ 81 * ε)
    (h50 : 0 ≤ m5) (h5 : m5 ≤ 243 * ε) :
    |m5 - 5 * μ * m4 - 10 * m2 * m3 + 20 * μ ^ (2 : ℕ) * m3 + 30 * μ * m2 ^ (2 : ℕ) -
      60 * μ ^ (3 : ℕ) * m2 + 24 * μ ^ (5 : ℕ)| ≤ 244 * ε := by
  have hεε : ε * ε ≤ ε / 1000000 := by nlinarith
  have hεεε : ε * ε * ε ≤ ε / 1000000 := by nlinarith
  have hε4 : ε * ε * (ε * ε) ≤ ε / 1000000 := by nlinarith
  have hε5 : ε * ε * (ε * ε) * ε ≤ ε / 1000000 := by nlinarith
  have hμm4 : μ * m4 ≤ 243 * (ε * ε) := by nlinarith
  have hμm4' : 0 ≤ μ * m4 := mul_nonneg hμ0 h40
  have hm2m3 : m2 * m3 ≤ 243 * (ε * ε) := by nlinarith
  have hm2m3' : 0 ≤ m2 * m3 := mul_nonneg h20 h30
  have hμ2 : μ ^ (2 : ℕ) ≤ 9 * (ε * ε) := by nlinarith
  have hμ2m3 : μ ^ (2 : ℕ) * m3 ≤ 243 * (ε * ε * ε) := by
    have := mul_le_mul hμ2 h3 h30 (by positivity)
    nlinarith
  have hμ2m3' : 0 ≤ μ ^ (2 : ℕ) * m3 := by positivity
  have hm22 : m2 ^ (2 : ℕ) ≤ 81 * (ε * ε) := by nlinarith
  have hμm22 : μ * m2 ^ (2 : ℕ) ≤ 243 * (ε * ε * ε) := by
    have := mul_le_mul hμ hm22 (by positivity) (by positivity)
    nlinarith
  have hμm22' : 0 ≤ μ * m2 ^ (2 : ℕ) := by positivity
  have hμ3 : μ ^ (3 : ℕ) ≤ 27 * (ε * ε * ε) := by
    have := pow_le_pow_left₀ hμ0 hμ 3
    nlinarith
  have hμ3m2 : μ ^ (3 : ℕ) * m2 ≤ 243 * (ε * ε * (ε * ε)) := by
    have := mul_le_mul hμ3 h2 h20 (by positivity)
    nlinarith
  have hμ3m2' : 0 ≤ μ ^ (3 : ℕ) * m2 := by positivity
  have hμ5 : μ ^ (5 : ℕ) ≤ 243 * (ε * ε * (ε * ε) * ε) := by
    have := pow_le_pow_left₀ hμ0 hμ 5
    nlinarith
  have hμ5' : 0 ≤ μ ^ (5 : ℕ) := by positivity
  rw [abs_le]
  constructor <;> nlinarith

/-! ## Likelihood jets in regime I -/

/-- `A ≥ 6` forces `x > 0`. -/
theorem regimeOne_pos_of_six_le {x : ℝ} (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 < x := by
  by_contra hneg
  have hneg' : x ≤ 0 := not_lt.mp hneg
  have h1 : Real.exp (2 * x) ≤ 1 := by
    have := Real.exp_le_exp.mpr (show 2 * x ≤ 0 by linarith)
    simpa using this
  have hpi := Real.pi_lt_four
  unfold thetaCuspSingleAtomReflectionScale at hA
  simp only [Nat.cast_one, one_pow, mul_one] at hA
  have hprod : 0 ≤ Real.pi * (1 - Real.exp (2 * x)) :=
    mul_nonneg Real.pi_pos.le (by linarith)
  nlinarith

/-- Regime-I moment majorants: `NM_m ≤ 3^m ε` for `m ≤ 5`. -/
theorem regimeOne_moment_bound {x : ℝ} (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (m : ℕ) (hm : m ≤ 5) :
    thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) m ≤
      3 ^ m * regimeOneLikelihoodScale x := by
  have hx : 0 ≤ x := (regimeOne_pos_of_six_le hA).le
  apply thetaCuspLikelihoodNormalizedMoment_le_regimeOneScale m hx
  have hm' : (m : ℝ) ≤ 5 := by exact_mod_cast hm
  have := Real.pi_lt_four
  linarith

/-- The mean, variance and cumulants of the corpus in regime I. -/
theorem regimeOne_cumulant_bounds {x : ℝ} (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 ≤ thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x) ∧
    thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x) ≤ 3 * regimeOneLikelihoodScale x ∧
    |thetaCuspLikelihoodVariance (thetaCuspLikelihoodCoordinate x)| ≤
      9 * regimeOneLikelihoodScale x ∧
    |thetaCuspLikelihoodThirdCumulant (thetaCuspLikelihoodCoordinate x)| ≤
      28 * regimeOneLikelihoodScale x ∧
    |thetaCuspLikelihoodFourthCumulant (thetaCuspLikelihoodCoordinate x)| ≤
      82 * regimeOneLikelihoodScale x ∧
    |thetaCuspLikelihoodFifthCumulant (thetaCuspLikelihoodCoordinate x)| ≤
      244 * regimeOneLikelihoodScale x := by
  have hx : 0 ≤ x := (regimeOne_pos_of_six_le hA).le
  have hB : 0 < thetaCuspLikelihoodCoordinate x := thetaCuspLikelihoodCoordinate_pos hx
  have hε0 : 0 ≤ regimeOneLikelihoodScale x := (regimeOneLikelihoodScale_pos x).le
  have hε : regimeOneLikelihoodScale x ≤ 1 / 1000000 := by
    have := regimeOneLikelihoodScale_le_of_six_le hA
    linarith
  have hZ := thetaCuspLikelihoodPartition_pos hB
  have hnn : ∀ m : ℕ, 0 ≤ thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) m :=
    fun m => div_nonneg (thetaCuspHigherLikelihoodSpectralMoment_nonneg m) hZ.le
  have h1 := regimeOne_moment_bound hA 1 (by norm_num)
  have h2 := regimeOne_moment_bound hA 2 (by norm_num)
  have h3 := regimeOne_moment_bound hA 3 (by norm_num)
  have h4 := regimeOne_moment_bound hA 4 (by norm_num)
  have h5 := regimeOne_moment_bound hA 5 (by norm_num)
  norm_num at h1 h2 h3 h4 h5
  set B := thetaCuspLikelihoodCoordinate x with hBdef
  set ε := regimeOneLikelihoodScale x with hεdef
  have hmean : thetaCuspLikelihoodMean B = thetaCuspLikelihoodNormalizedMoment B 1 := rfl
  have hvar : thetaCuspLikelihoodVariance B =
      thetaCuspLikelihoodNormalizedMoment B 2 - thetaCuspLikelihoodMean B ^ (2 : ℕ) := rfl
  have hk3 : thetaCuspLikelihoodThirdCumulant B =
      thetaCuspLikelihoodNormalizedMoment B 3 -
        3 * thetaCuspLikelihoodMean B * thetaCuspLikelihoodNormalizedMoment B 2 +
        2 * thetaCuspLikelihoodMean B ^ (3 : ℕ) := rfl
  have hk4 : thetaCuspLikelihoodFourthCumulant B =
      thetaCuspLikelihoodNormalizedMoment B 4 -
        4 * thetaCuspLikelihoodMean B * thetaCuspLikelihoodNormalizedMoment B 3 -
        3 * thetaCuspLikelihoodNormalizedMoment B 2 ^ (2 : ℕ) +
        12 * thetaCuspLikelihoodMean B ^ (2 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 2 -
        6 * thetaCuspLikelihoodMean B ^ (4 : ℕ) := rfl
  have hk5 : thetaCuspLikelihoodFifthCumulant B =
      thetaCuspLikelihoodNormalizedMoment B 5 -
        5 * thetaCuspLikelihoodMean B * thetaCuspLikelihoodNormalizedMoment B 4 -
        10 * thetaCuspLikelihoodNormalizedMoment B 2 * thetaCuspLikelihoodNormalizedMoment B 3 +
        20 * thetaCuspLikelihoodMean B ^ (2 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 3 +
        30 * thetaCuspLikelihoodMean B * thetaCuspLikelihoodNormalizedMoment B 2 ^ (2 : ℕ) -
        60 * thetaCuspLikelihoodMean B ^ (3 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 2 +
        24 * thetaCuspLikelihoodMean B ^ (5 : ℕ) := rfl
  have hμ0 : 0 ≤ thetaCuspLikelihoodMean B := by rw [hmean]; exact hnn 1
  have hμ : thetaCuspLikelihoodMean B ≤ 3 * ε := by rw [hmean]; exact h1
  refine ⟨hμ0, hμ, ?_, ?_, ?_, ?_⟩
  · rw [hvar]
    exact abs_variance_form_le hε hε0 hμ0 hμ (hnn 2) h2
  · rw [hk3]
    exact abs_third_cumulant_form_le hε hε0 hμ0 hμ (hnn 2) h2 (hnn 3) h3
  · rw [hk4]
    exact abs_fourth_cumulant_form_le hε hε0 hμ0 hμ (hnn 2) h2 (hnn 3) h3 (hnn 4) h4
  · rw [hk5]
    exact abs_fifth_cumulant_form_le hε hε0 hμ0 hμ (hnn 2) h2 (hnn 3) h3 (hnn 4) h4 (hnn 5) h5

/-- Two-sided bound from an absolute-value bound, scaled by a nonnegative factor. -/
theorem scaled_bounds_of_abs_le {k b c : ℝ} (h : |k| ≤ b) (hc : 0 ≤ c) :
    -(c * b) ≤ c * k ∧ c * k ≤ c * b := by
  have h' := abs_le.mp h
  constructor
  · have := mul_le_mul_of_nonneg_left h'.1 hc
    linarith
  · exact mul_le_mul_of_nonneg_left h'.2 hc

/-- Regime-I majorant of `J₂`. -/
theorem regimeOne_jetTwo_bound {x : ℝ} (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspLikelihoodSourceLogPartitionJetTwo x| ≤
      38 * thetaCuspSingleAtomReflectionScale 1 x ^ (2 : ℕ) * regimeOneLikelihoodScale x := by
  obtain ⟨hμ0, hμ, hv, -, -, -⟩ := regimeOne_cumulant_bounds hA
  have hε0 : 0 ≤ regimeOneLikelihoodScale x := (regimeOneLikelihoodScale_pos x).le
  unfold thetaCuspLikelihoodSourceLogPartitionJetTwo
  set A := thetaCuspSingleAtomReflectionScale 1 x with hAdef
  set ε := regimeOneLikelihoodScale x with hεdef
  set μ := thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x)
  set v := thetaCuspLikelihoodVariance (thetaCuspLikelihoodCoordinate x)
  have hA0 : 0 ≤ A := by linarith
  have e1 := scaled_bounds_of_abs_le hv (show 0 ≤ 4 * A ^ (2 : ℕ) by positivity)
  have e2 := mul_le_mul_of_nonneg_left hμ (show 0 ≤ 4 * A by positivity)
  have e2' := mul_le_mul_of_nonneg_left hμ0 (show 0 ≤ 4 * A by positivity)
  have p12 : 6 * A ≤ A ^ (2 : ℕ) := by nlinarith
  have hAε := mul_le_mul_of_nonneg_right p12 hε0
  rw [abs_le]
  constructor <;> nlinarith [e1.1, e1.2, e2, e2', hAε]

/-- Regime-I majorant of `J₃`. -/
theorem regimeOne_jetThree_bound {x : ℝ} (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspLikelihoodSourceLogPartitionJetThree x| ≤
      261 * thetaCuspSingleAtomReflectionScale 1 x ^ (3 : ℕ) * regimeOneLikelihoodScale x := by
  obtain ⟨hμ0, hμ, hv, hk3, -, -⟩ := regimeOne_cumulant_bounds hA
  have hε0 : 0 ≤ regimeOneLikelihoodScale x := (regimeOneLikelihoodScale_pos x).le
  unfold thetaCuspLikelihoodSourceLogPartitionJetThree
  set A := thetaCuspSingleAtomReflectionScale 1 x with hAdef
  set ε := regimeOneLikelihoodScale x with hεdef
  set μ := thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x)
  set v := thetaCuspLikelihoodVariance (thetaCuspLikelihoodCoordinate x)
  set k3 := thetaCuspLikelihoodThirdCumulant (thetaCuspLikelihoodCoordinate x)
  have hA0 : 0 ≤ A := by linarith
  have e1 := scaled_bounds_of_abs_le hk3 (show 0 ≤ 8 * A ^ (3 : ℕ) by positivity)
  have e2 := scaled_bounds_of_abs_le hv (show 0 ≤ 24 * A ^ (2 : ℕ) by positivity)
  have e3 := mul_le_mul_of_nonneg_left hμ (show 0 ≤ 8 * A by positivity)
  have e3' := mul_le_mul_of_nonneg_left hμ0 (show 0 ≤ 8 * A by positivity)
  have p12 : 6 * A ≤ A ^ (2 : ℕ) := by nlinarith
  have p23 : 6 * A ^ (2 : ℕ) ≤ A ^ (3 : ℕ) := by nlinarith
  have hAε := mul_le_mul_of_nonneg_right p12 hε0
  have hA2ε := mul_le_mul_of_nonneg_right p23 hε0
  rw [abs_le]
  constructor <;> nlinarith [e1.1, e1.2, e2.1, e2.2, e3, e3', hAε, hA2ε]

/-- Regime-I majorant of `J₄`. -/
theorem regimeOne_jetFour_bound {x : ℝ} (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspLikelihoodSourceLogPartitionJetFour x| ≤
      1800 * thetaCuspSingleAtomReflectionScale 1 x ^ (4 : ℕ) * regimeOneLikelihoodScale x := by
  obtain ⟨hμ0, hμ, hv, hk3, hk4, -⟩ := regimeOne_cumulant_bounds hA
  have hε0 : 0 ≤ regimeOneLikelihoodScale x := (regimeOneLikelihoodScale_pos x).le
  unfold thetaCuspLikelihoodSourceLogPartitionJetFour
  set A := thetaCuspSingleAtomReflectionScale 1 x with hAdef
  set ε := regimeOneLikelihoodScale x with hεdef
  set μ := thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x)
  set v := thetaCuspLikelihoodVariance (thetaCuspLikelihoodCoordinate x)
  set k3 := thetaCuspLikelihoodThirdCumulant (thetaCuspLikelihoodCoordinate x)
  set k4 := thetaCuspLikelihoodFourthCumulant (thetaCuspLikelihoodCoordinate x)
  have hA0 : 0 ≤ A := by linarith
  have e1 := scaled_bounds_of_abs_le hk4 (show 0 ≤ 16 * A ^ (4 : ℕ) by positivity)
  have e2 := scaled_bounds_of_abs_le hk3 (show 0 ≤ 96 * A ^ (3 : ℕ) by positivity)
  have e3 := scaled_bounds_of_abs_le hv (show 0 ≤ 112 * A ^ (2 : ℕ) by positivity)
  have e4 := mul_le_mul_of_nonneg_left hμ (show 0 ≤ 16 * A by positivity)
  have e4' := mul_le_mul_of_nonneg_left hμ0 (show 0 ≤ 16 * A by positivity)
  have p12 : 6 * A ≤ A ^ (2 : ℕ) := by nlinarith
  have p23 : 6 * A ^ (2 : ℕ) ≤ A ^ (3 : ℕ) := by nlinarith
  have p34 : 6 * A ^ (3 : ℕ) ≤ A ^ (4 : ℕ) := by nlinarith
  have hAε := mul_le_mul_of_nonneg_right p12 hε0
  have hA2ε := mul_le_mul_of_nonneg_right p23 hε0
  have hA3ε := mul_le_mul_of_nonneg_right p34 hε0
  rw [abs_le]
  constructor <;> nlinarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4, e4', hAε, hA2ε, hA3ε]

/-- Regime-I majorant of `J₅`. -/
theorem regimeOne_jetFive_bound {x : ℝ} (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspLikelihoodSourceLogPartitionJetFive x| ≤
      12900 * thetaCuspSingleAtomReflectionScale 1 x ^ (5 : ℕ) * regimeOneLikelihoodScale x := by
  obtain ⟨hμ0, hμ, hv, hk3, hk4, hk5⟩ := regimeOne_cumulant_bounds hA
  have hε0 : 0 ≤ regimeOneLikelihoodScale x := (regimeOneLikelihoodScale_pos x).le
  unfold thetaCuspLikelihoodSourceLogPartitionJetFive
  set A := thetaCuspSingleAtomReflectionScale 1 x with hAdef
  set ε := regimeOneLikelihoodScale x with hεdef
  set μ := thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x)
  set v := thetaCuspLikelihoodVariance (thetaCuspLikelihoodCoordinate x)
  set k3 := thetaCuspLikelihoodThirdCumulant (thetaCuspLikelihoodCoordinate x)
  set k4 := thetaCuspLikelihoodFourthCumulant (thetaCuspLikelihoodCoordinate x)
  set k5 := thetaCuspLikelihoodFifthCumulant (thetaCuspLikelihoodCoordinate x)
  have hA0 : 0 ≤ A := by linarith
  have e1 := scaled_bounds_of_abs_le hk5 (show 0 ≤ 32 * A ^ (5 : ℕ) by positivity)
  have e2 := scaled_bounds_of_abs_le hk4 (show 0 ≤ 320 * A ^ (4 : ℕ) by positivity)
  have e3 := scaled_bounds_of_abs_le hk3 (show 0 ≤ 800 * A ^ (3 : ℕ) by positivity)
  have e4 := scaled_bounds_of_abs_le hv (show 0 ≤ 480 * A ^ (2 : ℕ) by positivity)
  have e5 := mul_le_mul_of_nonneg_left hμ (show 0 ≤ 32 * A by positivity)
  have e5' := mul_le_mul_of_nonneg_left hμ0 (show 0 ≤ 32 * A by positivity)
  have p12 : 6 * A ≤ A ^ (2 : ℕ) := by nlinarith
  have p23 : 6 * A ^ (2 : ℕ) ≤ A ^ (3 : ℕ) := by nlinarith
  have p34 : 6 * A ^ (3 : ℕ) ≤ A ^ (4 : ℕ) := by nlinarith
  have p45 : 6 * A ^ (4 : ℕ) ≤ A ^ (5 : ℕ) := by nlinarith
  have hAε := mul_le_mul_of_nonneg_right p12 hε0
  have hA2ε := mul_le_mul_of_nonneg_right p23 hε0
  have hA3ε := mul_le_mul_of_nonneg_right p34 hε0
  have hA4ε := mul_le_mul_of_nonneg_right p45 hε0
  rw [abs_le]
  constructor <;>
    nlinarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5, e5', hAε, hA2ε, hA3ε, hA4ε]

/-! ## Jet decompositions: curvature jets = Born–Witten part − likelihood jet -/

theorem thetaCuspLogCurvature_eq_bornWitten_sub_jet {x : ℝ} (hx : 0 < x) :
    thetaCuspLogCurvature x =
      thetaCuspBornWittenLogCurvature 1 x - thetaCuspLikelihoodSourceLogPartitionJetTwo x := by
  unfold thetaCuspLogCurvature
  rw [iteratedDeriv_two_thetaCuspLogSource_eq_factor hx,
    thetaCuspLikelihoodSourceLogPartitionJetTwo_eq_higherLikelihoodLogJetTwo hx]
  ring

theorem thetaCuspLogCurvatureJet_eq_bornWitten_sub_jet {x : ℝ} (hx : 0 < x) :
    thetaCuspLogCurvatureJet x =
      thetaCuspBornWittenLogThirdDerivative 1 x - thetaCuspLikelihoodSourceLogPartitionJetThree x := by
  unfold thetaCuspLogCurvatureJet
  rw [iteratedDeriv_three_thetaCuspLogSource_eq_full_jets hx,
    thetaCuspLikelihoodSourceLogPartitionJetThree_eq_higherLikelihoodLogJetThree hx]
  unfold thetaCuspFirstAtomLogJetThree
  ring

theorem thetaCuspLogCurvatureJetTwo_eq_bornWitten_sub_jet {x : ℝ} (hx : 0 < x) :
    thetaCuspLogCurvatureJetTwo x =
      thetaCuspBornWittenLogFourthDerivative 1 x - thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  unfold thetaCuspLogCurvatureJetTwo
  rw [iteratedDeriv_four_thetaCuspLogSource_eq_factor hx,
    thetaCuspLikelihoodSourceLogPartitionJetFour_eq_higherLikelihoodLogJetFour hx]
  ring

theorem thetaCuspLogCurvatureJetThree_eq_bornWitten_sub_jet {x : ℝ} (hx : 0 < x) :
    thetaCuspLogCurvatureJetThree x =
      thetaCuspBornWittenLogFifthDerivative 1 x - thetaCuspLikelihoodSourceLogPartitionJetFive x := by
  unfold thetaCuspLogCurvatureJetThree
  rw [iteratedDeriv_five_thetaCuspLogSource_eq_full_jets hx]
  unfold thetaCuspFullLogJetFive
  ring

/-! ## The Born–Witten jets as functions of `q = A − 3/2` -/

theorem thetaCuspBornWittenWeight_one_eq_scale_sub (x : ℝ) :
    thetaCuspBornWittenWeight 1 x = thetaCuspSingleAtomReflectionScale 1 x - 3 / 2 := by
  rw [thetaCuspC5FarTail_bornWittenWeight_one_eq_coordinate,
    thetaCuspSingleAtomScale_likelihoodCoordinate]

theorem thetaCuspMorseScale_one_eq_weight_add (x : ℝ) :
    thetaCuspMorseScale 1 x = thetaCuspBornWittenWeight 1 x + 3 / 2 := by
  rw [thetaCuspBornWittenWeight_eq]
  ring

/-- Closed forms of `BW₂ … BW₅` in `q` (with `2q + 3 = 2A`). -/
theorem bornWitten_jets_eq (x : ℝ) :
    let q := thetaCuspBornWittenWeight 1 x
    thetaCuspBornWittenLogCurvature 1 x = (2 * q + 3) * (2 + 3 / q ^ (2 : ℕ)) ∧
    thetaCuspBornWittenLogThirdDerivative 1 x = (2 * q + 3) * (4 - 6 / q ^ (2 : ℕ) - 18 / q ^ (3 : ℕ)) ∧
    thetaCuspBornWittenLogFourthDerivative 1 x =
      (2 * q + 3) * (8 + 12 / q ^ (2 : ℕ) + 108 / q ^ (3 : ℕ) + 162 / q ^ (4 : ℕ)) ∧
    thetaCuspBornWittenLogFifthDerivative 1 x =
      (2 * q + 3) * (16 - 24 / q ^ (2 : ℕ) - 504 / q ^ (3 : ℕ) - 1944 / q ^ (4 : ℕ) - 1944 / q ^ (5 : ℕ)) := by
  intro q
  refine ⟨?_, rfl, rfl, rfl⟩
  unfold thetaCuspBornWittenLogCurvature thetaCuspBornWittenCurvature
  rw [thetaCuspMorseScale_one_eq_weight_add]
  ring

/-- The exact Born–Witten difference `BW₂ BW₅ − BW₃ BW₄`. -/
theorem bornWitten_difference_eq {q : ℝ} (hq : q ≠ 0) :
    (2 * q + 3) * (2 + 3 / q ^ (2 : ℕ)) *
        ((2 * q + 3) * (16 - 24 / q ^ (2 : ℕ) - 504 / q ^ (3 : ℕ) - 1944 / q ^ (4 : ℕ) - 1944 / q ^ (5 : ℕ))) -
      (2 * q + 3) * (4 - 6 / q ^ (2 : ℕ) - 18 / q ^ (3 : ℕ)) *
        ((2 * q + 3) * (8 + 12 / q ^ (2 : ℕ) + 108 / q ^ (3 : ℕ) + 162 / q ^ (4 : ℕ))) =
      -((2 * q + 3) ^ (2 : ℕ) * (1296 * q ^ (4 : ℕ) + 4536 * q ^ (3 : ℕ) + 4536 * q ^ (2 : ℕ) + 2916 * q + 2916) / q ^ (7 : ℕ)) := by
  field_simp
  ring

/-- Bracket bounds for `q ≥ 9/2`. -/
theorem bornWitten_bracket_bounds {q : ℝ} (hq : 9 / 2 ≤ q) :
    2 ≤ 2 + 3 / q ^ (2 : ℕ) ∧ 2 + 3 / q ^ (2 : ℕ) ≤ 43 / 20 ∧
    7 / 2 ≤ 4 - 6 / q ^ (2 : ℕ) - 18 / q ^ (3 : ℕ) ∧ 4 - 6 / q ^ (2 : ℕ) - 18 / q ^ (3 : ℕ) ≤ 4 ∧
    8 ≤ 8 + 12 / q ^ (2 : ℕ) + 108 / q ^ (3 : ℕ) + 162 / q ^ (4 : ℕ) ∧
      8 + 12 / q ^ (2 : ℕ) + 108 / q ^ (3 : ℕ) + 162 / q ^ (4 : ℕ) ≤ 51 / 5 ∧
    17 / 5 ≤ 16 - 24 / q ^ (2 : ℕ) - 504 / q ^ (3 : ℕ) - 1944 / q ^ (4 : ℕ) - 1944 / q ^ (5 : ℕ) ∧
      16 - 24 / q ^ (2 : ℕ) - 504 / q ^ (3 : ℕ) - 1944 / q ^ (4 : ℕ) - 1944 / q ^ (5 : ℕ) ≤ 16 := by
  have hq0 : 0 < q := by linarith
  have h2 : 3 / q ^ (2 : ℕ) ≤ 3 / (9 / 2) ^ (2 : ℕ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hq 2)
  have h2' : 6 / q ^ (2 : ℕ) ≤ 6 / (9 / 2) ^ (2 : ℕ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hq 2)
  have h3 : 18 / q ^ (3 : ℕ) ≤ 18 / (9 / 2) ^ (3 : ℕ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hq 3)
  have h12 : 12 / q ^ (2 : ℕ) ≤ 12 / (9 / 2) ^ (2 : ℕ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hq 2)
  have h108 : 108 / q ^ (3 : ℕ) ≤ 108 / (9 / 2) ^ (3 : ℕ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hq 3)
  have h162 : 162 / q ^ (4 : ℕ) ≤ 162 / (9 / 2) ^ (4 : ℕ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hq 4)
  have h24 : 24 / q ^ (2 : ℕ) ≤ 24 / (9 / 2) ^ (2 : ℕ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hq 2)
  have h504 : 504 / q ^ (3 : ℕ) ≤ 504 / (9 / 2) ^ (3 : ℕ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hq 3)
  have h1944 : 1944 / q ^ (4 : ℕ) ≤ 1944 / (9 / 2) ^ (4 : ℕ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hq 4)
  have h1944' : 1944 / q ^ (5 : ℕ) ≤ 1944 / (9 / 2) ^ (5 : ℕ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hq 5)
  have p2 : 0 ≤ 3 / q ^ (2 : ℕ) := by positivity
  have p2' : 0 ≤ 6 / q ^ (2 : ℕ) := by positivity
  have p3 : 0 ≤ 18 / q ^ (3 : ℕ) := by positivity
  have p12 : 0 ≤ 12 / q ^ (2 : ℕ) := by positivity
  have p108 : 0 ≤ 108 / q ^ (3 : ℕ) := by positivity
  have p162 : 0 ≤ 162 / q ^ (4 : ℕ) := by positivity
  have p24 : 0 ≤ 24 / q ^ (2 : ℕ) := by positivity
  have p504 : 0 ≤ 504 / q ^ (3 : ℕ) := by positivity
  have p1944 : 0 ≤ 1944 / q ^ (4 : ℕ) := by positivity
  have p1944' : 0 ≤ 1944 / q ^ (5 : ℕ) := by positivity
  norm_num at h2 h2' h3 h12 h108 h162 h24 h504 h1944 h1944'
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

/-! ## The three sign facts in regime I -/

/-- Package of the regime-I quantities and bounds used by the sign facts. -/
theorem regimeOne_data {x : ℝ} (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspBornWittenWeight 1 x = thetaCuspSingleAtomReflectionScale 1 x - 3 / 2 ∧
    9 / 2 ≤ thetaCuspBornWittenWeight 1 x ∧ 0 < x ∧ 0 ≤ regimeOneLikelihoodScale x ∧
    thetaCuspSingleAtomReflectionScale 1 x ^ (2 : ℕ) * regimeOneLikelihoodScale x ≤
      36 * (49 / 100000000) ∧
    thetaCuspSingleAtomReflectionScale 1 x ^ (3 : ℕ) * regimeOneLikelihoodScale x ≤
      216 * (49 / 100000000) ∧
    thetaCuspSingleAtomReflectionScale 1 x ^ (6 : ℕ) * regimeOneLikelihoodScale x ≤
      46656 * (49 / 100000000) ∧
    thetaCuspSingleAtomReflectionScale 1 x * regimeOneLikelihoodScale x ≤ 6 * (49 / 100000000) := by
  have hq : thetaCuspBornWittenWeight 1 x = thetaCuspSingleAtomReflectionScale 1 x - 3 / 2 :=
    thetaCuspBornWittenWeight_one_eq_scale_sub x
  have hx := regimeOne_pos_of_six_le hA
  have hε0 : 0 ≤ regimeOneLikelihoodScale x := (regimeOneLikelihoodScale_pos x).le
  have hb := base_scale_six_lt
  have h2 := pow_mul_regimeOneLikelihoodScale_le (k := 2) (A₁ := 6) (by norm_num) (by norm_num) hA
  have h3 := pow_mul_regimeOneLikelihoodScale_le (k := 3) (A₁ := 6) (by norm_num) (by norm_num) hA
  have h6 := pow_mul_regimeOneLikelihoodScale_le (k := 6) (A₁ := 6) (by norm_num) (by norm_num) hA
  have h1 := pow_mul_regimeOneLikelihoodScale_le (k := 1) (A₁ := 6) (by norm_num) (by norm_num) hA
  refine ⟨hq, by rw [hq]; linarith, hx, hε0, ?_, ?_, ?_, ?_⟩
  · exact h2.trans (by nlinarith)
  · exact h3.trans (by nlinarith)
  · exact h6.trans (by nlinarith)
  · simp only [pow_one] at h1
    exact h1.trans (by nlinarith)

/-- `(R2)` in regime I: the curvature jet is positive. -/
theorem thetaCuspLogCurvatureJet_pos_of_six_le {x : ℝ}
    (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 < thetaCuspLogCurvatureJet x := by
  obtain ⟨hq, hq9, hx, hε0, hA2ε, -, -, -⟩ := regimeOne_data hA
  have hJ := regimeOne_jetThree_bound hA
  obtain ⟨-, hBW3, -, -⟩ := bornWitten_jets_eq x
  obtain ⟨-, -, hb3, -, -, -, -, -⟩ := bornWitten_bracket_bounds hq9
  rw [thetaCuspLogCurvatureJet_eq_bornWitten_sub_jet hx, hBW3]
  set A := thetaCuspSingleAtomReflectionScale 1 x with hAdef
  set q := thetaCuspBornWittenWeight 1 x with hqdef
  set ε := regimeOneLikelihoodScale x with hεdef
  have hA6 : 6 ≤ A := hA
  have hJ' := (abs_le.mp hJ).2
  have hlow : 7 * A ≤ (2 * q + 3) * (4 - 6 / q ^ (2 : ℕ) - 18 / q ^ (3 : ℕ)) := by
    have : 2 * q + 3 = 2 * A := by rw [hq]; ring
    rw [this]
    nlinarith
  have hA3ε : 261 * A ^ (3 : ℕ) * ε ≤ 261 * A * (36 * (49 / 100000000)) := by
    have : A ^ (3 : ℕ) * ε = A * (A ^ (2 : ℕ) * ε) := by ring
    rw [mul_assoc, this]
    have := mul_le_mul_of_nonneg_left hA2ε (show 0 ≤ A by linarith)
    nlinarith
  nlinarith

/-- `(R3)` in regime I: the second curvature jet is positive. -/
theorem thetaCuspLogCurvatureJetTwo_pos_of_six_le {x : ℝ}
    (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 < thetaCuspLogCurvatureJetTwo x := by
  obtain ⟨hq, hq9, hx, hε0, -, hA3ε, -, -⟩ := regimeOne_data hA
  have hJ := regimeOne_jetFour_bound hA
  obtain ⟨-, -, hBW4, -⟩ := bornWitten_jets_eq x
  obtain ⟨-, -, -, -, hb4, -, -, -⟩ := bornWitten_bracket_bounds hq9
  rw [thetaCuspLogCurvatureJetTwo_eq_bornWitten_sub_jet hx, hBW4]
  set A := thetaCuspSingleAtomReflectionScale 1 x with hAdef
  set q := thetaCuspBornWittenWeight 1 x with hqdef
  set ε := regimeOneLikelihoodScale x with hεdef
  have hA6 : 6 ≤ A := hA
  have hJ' := (abs_le.mp hJ).2
  have hlow : 16 * A ≤ (2 * q + 3) * (8 + 12 / q ^ (2 : ℕ) + 108 / q ^ (3 : ℕ) + 162 / q ^ (4 : ℕ)) := by
    have : 2 * q + 3 = 2 * A := by rw [hq]; ring
    rw [this]
    nlinarith
  have hA4ε : 1800 * A ^ (4 : ℕ) * ε ≤ 1800 * A * (216 * (49 / 100000000)) := by
    have : A ^ (4 : ℕ) * ε = A * (A ^ (3 : ℕ) * ε) := by ring
    rw [mul_assoc, this]
    have := mul_le_mul_of_nonneg_left hA3ε (show 0 ≤ A by linarith)
    nlinarith
  nlinarith

/-- Lower bound on the difference through its two leading terms. -/
theorem bornWitten_difference_le {q : ℝ} (hq : 0 < q) :
    -((2 * q + 3) ^ (2 : ℕ) * (1296 * q ^ (4 : ℕ) + 4536 * q ^ (3 : ℕ) + 4536 * q ^ (2 : ℕ) + 2916 * q + 2916) / q ^ (7 : ℕ)) ≤
      -((2 * q + 3) ^ (2 : ℕ) * (1296 / q ^ (3 : ℕ) + 4536 / q ^ (4 : ℕ))) := by
  rw [neg_le_neg_iff]
  have hrew : 1296 / q ^ (3 : ℕ) + 4536 / q ^ (4 : ℕ) = (1296 * q ^ (4 : ℕ) + 4536 * q ^ (3 : ℕ)) / q ^ (7 : ℕ) := by
    field_simp
    try ring
  rw [hrew, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  nlinarith [sq_nonneg q]

/-- `(R4)` in regime I: the curvature times its third jet is at most the product of the first
two jets. -/
theorem thetaCuspLogCurvature_mul_jetThree_le_of_six_le {x : ℝ}
    (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspLogCurvature x * thetaCuspLogCurvatureJetThree x ≤
      thetaCuspLogCurvatureJet x * thetaCuspLogCurvatureJetTwo x := by
  obtain ⟨hq, hq9, hx, hε0, -, -, hA6ε, hAε⟩ := regimeOne_data hA
  have hJ2 := regimeOne_jetTwo_bound hA
  have hJ3 := regimeOne_jetThree_bound hA
  have hJ4 := regimeOne_jetFour_bound hA
  have hJ5 := regimeOne_jetFive_bound hA
  obtain ⟨hBW2, hBW3, hBW4, hBW5⟩ := bornWitten_jets_eq x
  obtain ⟨hb2l, hb2u, hb3l, hb3u, hb4l, hb4u, hb5l, hb5u⟩ := bornWitten_bracket_bounds hq9
  have h6 := pow_mul_regimeOneLikelihoodScale_le (k := 6) (A₁ := 7) (x := x) (by norm_num) (by norm_num)
  have h7 := pow_mul_regimeOneLikelihoodScale_le (k := 7) (A₁ := 10) (x := x) (by norm_num) (by norm_num)
  have hb7 := base_scale_seven_lt
  have hb10 := base_scale_ten_lt
  rw [thetaCuspLogCurvature_eq_bornWitten_sub_jet hx, thetaCuspLogCurvatureJet_eq_bornWitten_sub_jet hx,
    thetaCuspLogCurvatureJetTwo_eq_bornWitten_sub_jet hx,
    thetaCuspLogCurvatureJetThree_eq_bornWitten_sub_jet hx, hBW2, hBW3, hBW4, hBW5]
  clear hBW2 hBW3 hBW4 hBW5
  generalize hj2 : thetaCuspLikelihoodSourceLogPartitionJetTwo x = j2 at hJ2 ⊢
  generalize hj3 : thetaCuspLikelihoodSourceLogPartitionJetThree x = j3 at hJ3 ⊢
  generalize hj4 : thetaCuspLikelihoodSourceLogPartitionJetFour x = j4 at hJ4 ⊢
  generalize hj5 : thetaCuspLikelihoodSourceLogPartitionJetFive x = j5 at hJ5 ⊢
  generalize hεdef : regimeOneLikelihoodScale x = ε at *
  generalize hqdef : thetaCuspBornWittenWeight 1 x = q at *
  generalize hAdef : thetaCuspSingleAtomReflectionScale 1 x = A at *
  have hA6 : 6 ≤ A := hA
  have hA0 : 0 < A := by linarith only [hA6]
  have hq0 : 0 < q := by linarith only [hq9]
  have h2A : 2 * q + 3 = 2 * A := by rw [hq]; ring
  have h2A0 : 0 ≤ 2 * A := by positivity
  -- Born–Witten bounds in `A`
  have hc0b : 4 * A ≤ (2 * q + 3) * (2 + 3 / q ^ (2 : ℕ)) ∧
      (2 * q + 3) * (2 + 3 / q ^ (2 : ℕ)) ≤ 43 / 10 * A := by
    rw [h2A]
    have u1 := mul_le_mul_of_nonneg_left hb2l h2A0
    have u2 := mul_le_mul_of_nonneg_left hb2u h2A0
    constructor <;> linarith only [u1, u2]
  have hc1b : 7 * A ≤ (2 * q + 3) * (4 - 6 / q ^ (2 : ℕ) - 18 / q ^ (3 : ℕ)) ∧
      (2 * q + 3) * (4 - 6 / q ^ (2 : ℕ) - 18 / q ^ (3 : ℕ)) ≤ 8 * A := by
    rw [h2A]
    have u1 := mul_le_mul_of_nonneg_left hb3l h2A0
    have u2 := mul_le_mul_of_nonneg_left hb3u h2A0
    constructor <;> linarith only [u1, u2]
  have hc2b : 16 * A ≤ (2 * q + 3) * (8 + 12 / q ^ (2 : ℕ) + 108 / q ^ (3 : ℕ) + 162 / q ^ (4 : ℕ)) ∧
      (2 * q + 3) * (8 + 12 / q ^ (2 : ℕ) + 108 / q ^ (3 : ℕ) + 162 / q ^ (4 : ℕ)) ≤ 102 / 5 * A := by
    rw [h2A]
    have u1 := mul_le_mul_of_nonneg_left hb4l h2A0
    have u2 := mul_le_mul_of_nonneg_left hb4u h2A0
    constructor <;> linarith only [u1, u2]
  have hc3b : 34 / 5 * A ≤ (2 * q + 3) * (16 - 24 / q ^ (2 : ℕ) - 504 / q ^ (3 : ℕ) - 1944 / q ^ (4 : ℕ) - 1944 / q ^ (5 : ℕ)) ∧
      (2 * q + 3) * (16 - 24 / q ^ (2 : ℕ) - 504 / q ^ (3 : ℕ) - 1944 / q ^ (4 : ℕ) - 1944 / q ^ (5 : ℕ)) ≤ 32 * A := by
    rw [h2A]
    have u1 := mul_le_mul_of_nonneg_left hb5l h2A0
    have u2 := mul_le_mul_of_nonneg_left hb5u h2A0
    constructor <;> linarith only [u1, u2]
  -- the exact difference and its lower bound
  have hDle : (2 * q + 3) * (2 + 3 / q ^ (2 : ℕ)) *
      ((2 * q + 3) * (16 - 24 / q ^ (2 : ℕ) - 504 / q ^ (3 : ℕ) - 1944 / q ^ (4 : ℕ) - 1944 / q ^ (5 : ℕ))) -
      (2 * q + 3) * (4 - 6 / q ^ (2 : ℕ) - 18 / q ^ (3 : ℕ)) *
      ((2 * q + 3) * (8 + 12 / q ^ (2 : ℕ) + 108 / q ^ (3 : ℕ) + 162 / q ^ (4 : ℕ))) ≤
      -(4 * A ^ (2 : ℕ) * (1296 / q ^ (3 : ℕ) + 4536 / q ^ (4 : ℕ))) := by
    rw [bornWitten_difference_eq hq0.ne', h2A]
    have := bornWitten_difference_le hq0
    rw [h2A] at this
    have e : ((2 : ℝ) * A) ^ (2 : ℕ) = 4 * A ^ (2 : ℕ) := by ring
    rw [e] at this ⊢
    exact this
  generalize hc0 : (2 * q + 3) * (2 + 3 / q ^ (2 : ℕ)) = c0 at hc0b hDle ⊢
  generalize hc1 : (2 * q + 3) * (4 - 6 / q ^ (2 : ℕ) - 18 / q ^ (3 : ℕ)) = c1 at hc1b hDle ⊢
  generalize hc2 : (2 * q + 3) * (8 + 12 / q ^ (2 : ℕ) + 108 / q ^ (3 : ℕ) + 162 / q ^ (4 : ℕ)) = c2 at hc2b hDle ⊢
  generalize hc3 : (2 * q + 3) * (16 - 24 / q ^ (2 : ℕ) - 504 / q ^ (3 : ℕ) - 1944 / q ^ (4 : ℕ) - 1944 / q ^ (5 : ℕ)) = c3
    at hc3b hDle ⊢
  have hc0p : 0 ≤ c0 := by linarith only [hc0b.1, hA0]
  have hc1p : 0 ≤ c1 := by linarith only [hc1b.1, hA0]
  have hc2p : 0 ≤ c2 := by linarith only [hc2b.1, hA0]
  have hc3p : 0 ≤ c3 := by linarith only [hc3b.1, hA0]
  -- absolute bounds of the jets
  generalize hb2 : 38 * A ^ (2 : ℕ) * ε = b2 at hJ2
  generalize hb3 : 261 * A ^ (3 : ℕ) * ε = b3 at hJ3
  generalize hb4 : 1800 * A ^ (4 : ℕ) * ε = b4 at hJ4
  generalize hb5 : 12900 * A ^ (5 : ℕ) * ε = b5 at hJ5
  have hb2p : 0 ≤ b2 := by rw [← hb2]; positivity
  have hb3p : 0 ≤ b3 := by rw [← hb3]; positivity
  have hb4p : 0 ≤ b4 := by rw [← hb4]; positivity
  have hb5p : 0 ≤ b5 := by rw [← hb5]; positivity
  have hj2j5 : j2 * j5 ≤ b2 * b5 := by
    calc j2 * j5 ≤ |j2 * j5| := le_abs_self _
      _ = |j2| * |j5| := abs_mul _ _
      _ ≤ b2 * b5 := mul_le_mul hJ2 hJ5 (abs_nonneg _) hb2p
  have hj3j4 : -(b3 * b4) ≤ j3 * j4 := by
    have : |j3 * j4| ≤ b3 * b4 := by
      rw [abs_mul]; exact mul_le_mul hJ3 hJ4 (abs_nonneg _) hb3p
    linarith only [(abs_le.mp this).1]
  have hc0j5 := scaled_bounds_of_abs_le hJ5 hc0p
  have hc3j2 := scaled_bounds_of_abs_le hJ2 hc3p
  have hc1j4 := scaled_bounds_of_abs_le hJ4 hc1p
  have hc2j3 := scaled_bounds_of_abs_le hJ3 hc2p
  -- the error budget
  have herr : c0 * b5 + c3 * b2 + b2 * b5 + c1 * b4 + c2 * b3 + b3 * b4 ≤
      58100 * (A ^ (6 : ℕ) * ε) := by
    have h216 : (216 : ℝ) ≤ A ^ (3 : ℕ) := by
      have := pow_le_pow_left₀ (by norm_num) hA6 3
      norm_num at this
      exact this
    have h36 : (36 : ℝ) ≤ A ^ (2 : ℕ) := by
      have := pow_le_pow_left₀ (by norm_num) hA6 2
      norm_num at this
      exact this
    have hA3ε : 216 * (A ^ (3 : ℕ) * ε) ≤ A ^ (6 : ℕ) * ε := by
      have u := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h216 (pow_nonneg hA0.le 3)) hε0
      have e : A ^ (3 : ℕ) * A ^ (3 : ℕ) * ε = A ^ (6 : ℕ) * ε := by ring
      have e' : A ^ (3 : ℕ) * 216 * ε = 216 * (A ^ (3 : ℕ) * ε) := by ring
      linarith only [u, e, e']
    have hA4ε : 36 * (A ^ (4 : ℕ) * ε) ≤ A ^ (6 : ℕ) * ε := by
      have u := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h36 (pow_nonneg hA0.le 4)) hε0
      have e : A ^ (4 : ℕ) * A ^ (2 : ℕ) * ε = A ^ (6 : ℕ) * ε := by ring
      have e' : A ^ (4 : ℕ) * 36 * ε = 36 * (A ^ (4 : ℕ) * ε) := by ring
      linarith only [u, e, e']
    have hA5ε : 6 * (A ^ (5 : ℕ) * ε) ≤ A ^ (6 : ℕ) * ε := by
      have u := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA6 (pow_nonneg hA0.le 5)) hε0
      have e : A ^ (5 : ℕ) * A * ε = A ^ (6 : ℕ) * ε := by ring
      have e' : A ^ (5 : ℕ) * 6 * ε = 6 * (A ^ (5 : ℕ) * ε) := by ring
      linarith only [u, e, e']
    have t1 : c0 * b5 ≤ 55470 * (A ^ (6 : ℕ) * ε) := by
      calc c0 * b5 ≤ 43 / 10 * A * b5 := mul_le_mul_of_nonneg_right hc0b.2 hb5p
        _ = 55470 * (A ^ (6 : ℕ) * ε) := by rw [← hb5]; ring
    have t2 : c3 * b2 ≤ 1216 * (A ^ (3 : ℕ) * ε) := by
      calc c3 * b2 ≤ 32 * A * b2 := mul_le_mul_of_nonneg_right hc3b.2 hb2p
        _ = 1216 * (A ^ (3 : ℕ) * ε) := by rw [← hb2]; ring
    have t3 : c1 * b4 ≤ 14400 * (A ^ (5 : ℕ) * ε) := by
      calc c1 * b4 ≤ 8 * A * b4 := mul_le_mul_of_nonneg_right hc1b.2 hb4p
        _ = 14400 * (A ^ (5 : ℕ) * ε) := by rw [← hb4]; ring
    have t4 : c2 * b3 ≤ 26622 / 5 * (A ^ (4 : ℕ) * ε) := by
      calc c2 * b3 ≤ 102 / 5 * A * b3 := mul_le_mul_of_nonneg_right hc2b.2 hb3p
        _ = 26622 / 5 * (A ^ (4 : ℕ) * ε) := by rw [← hb3]; ring
    have t5 : b2 * b5 + b3 * b4 = 960000 * (A ^ (6 : ℕ) * ε) * (A * ε) := by
      rw [← hb2, ← hb3, ← hb4, ← hb5]; ring
    have t6 : 960000 * (A ^ (6 : ℕ) * ε) * (A * ε) ≤ 960000 * (A ^ (6 : ℕ) * ε) * (6 * (49 / 100000000)) :=
      mul_le_mul_of_nonneg_left hAε (by positivity)
    have hM : 0 ≤ A ^ (6 : ℕ) * ε := mul_nonneg (pow_nonneg hA0.le 6) hε0
    linarith only [t1, t2, t3, t4, t5, t6, hA3ε, hA4ε, hA5ε, hM]
  -- reduce to `D + err ≤ 0`
  suffices hkey : c0 * c3 - c1 * c2 +
      (c0 * b5 + c3 * b2 + b2 * b5 + c1 * b4 + c2 * b3 + b3 * b4) ≤ 0 by
    linarith only [hc0j5.1, hc3j2.1, hc1j4.2, hc2j3.2, hj2j5, hj3j4, hkey]
  -- chambers in `A`
  rcases le_or_gt A 7 with hA7 | hA7
  · -- `6 ≤ A ≤ 7`: `q ≤ 11/2`
    have hq11 : q ≤ 11 / 2 := by rw [hq]; linarith only [hA7]
    have d3 : 1296 / (11 / 2 : ℝ) ^ (3 : ℕ) ≤ 1296 / q ^ (3 : ℕ) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hq0.le hq11 3)
    have d4 : 4536 / (11 / 2 : ℝ) ^ (4 : ℕ) ≤ 4536 / q ^ (4 : ℕ) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hq0.le hq11 4)
    have hA2 : (36 : ℝ) ≤ A ^ (2 : ℕ) := by
      have := pow_le_pow_left₀ (by norm_num) hA6 2
      norm_num at this
      exact this
    have hDnum : 4 * 36 * (1296 / (11 / 2 : ℝ) ^ (3 : ℕ) + 4536 / (11 / 2 : ℝ) ^ (4 : ℕ)) ≤
        4 * A ^ (2 : ℕ) * (1296 / q ^ (3 : ℕ) + 4536 / q ^ (4 : ℕ)) := by
      have hs : 0 ≤ 1296 / (11 / 2 : ℝ) ^ (3 : ℕ) + 4536 / (11 / 2 : ℝ) ^ (4 : ℕ) := by positivity
      have u := mul_le_mul hA2 (add_le_add d3 d4) hs (by positivity)
      linarith only [u]
    have hnum : (1835 : ℝ) ≤ 4 * 36 * (1296 / (11 / 2 : ℝ) ^ (3 : ℕ) + 4536 / (11 / 2 : ℝ) ^ (4 : ℕ)) := by
      norm_num
    linarith only [hDle, herr, hA6ε, hDnum, hnum]
  · rcases le_or_gt A 10 with hA10 | hA10
    · -- `7 ≤ A ≤ 10`: `q ≤ 17/2`
      have hq17 : q ≤ 17 / 2 := by rw [hq]; linarith only [hA10]
      have d3 : 1296 / (17 / 2 : ℝ) ^ (3 : ℕ) ≤ 1296 / q ^ (3 : ℕ) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hq0.le hq17 3)
      have d4 : 4536 / (17 / 2 : ℝ) ^ (4 : ℕ) ≤ 4536 / q ^ (4 : ℕ) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hq0.le hq17 4)
      have hA2 : (49 : ℝ) ≤ A ^ (2 : ℕ) := by
        have := pow_le_pow_left₀ (by norm_num) hA7.le 2
        norm_num at this
        exact this
      have hDnum : 4 * 49 * (1296 / (17 / 2 : ℝ) ^ (3 : ℕ) + 4536 / (17 / 2 : ℝ) ^ (4 : ℕ)) ≤
          4 * A ^ (2 : ℕ) * (1296 / q ^ (3 : ℕ) + 4536 / q ^ (4 : ℕ)) := by
        have hs : 0 ≤ 1296 / (17 / 2 : ℝ) ^ (3 : ℕ) + 4536 / (17 / 2 : ℝ) ^ (4 : ℕ) := by positivity
        have u := mul_le_mul hA2 (add_le_add d3 d4) hs (by positivity)
        linarith only [u]
      have hnum : (583 : ℝ) ≤ 4 * 49 * (1296 / (17 / 2 : ℝ) ^ (3 : ℕ) + 4536 / (17 / 2 : ℝ) ^ (4 : ℕ)) := by
        norm_num
      have hA6ε' : A ^ (6 : ℕ) * ε ≤ 117649 * (245 / 10000000000) := by
        refine (h6 hA7.le).trans ?_
        have u := mul_le_mul_of_nonneg_left hb7.le (show (0 : ℝ) ≤ 7 ^ (6 : ℕ) by norm_num)
        norm_num at u ⊢
        linarith only [u]
      linarith only [hDle, herr, hA6ε', hDnum, hnum]
    · -- `A ≥ 10`: `|D| ≥ 5184 / A`
      have hqA : q ≤ A := by rw [hq]; linarith only []
      have d3 : 1296 / A ^ (3 : ℕ) ≤ 1296 / q ^ (3 : ℕ) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hq0.le hqA 3)
      have hd4 : 0 ≤ 4 * A ^ (2 : ℕ) * (4536 / q ^ (4 : ℕ)) * A := by positivity
      have hA0' : A ≠ 0 := hA0.ne'
      have hid : 4 * A ^ (2 : ℕ) * (1296 / A ^ (3 : ℕ)) * A = 5184 := by
        field_simp
        ring
      have hDA : 5184 ≤ 4 * A ^ (2 : ℕ) * (1296 / q ^ (3 : ℕ) + 4536 / q ^ (4 : ℕ)) * A := by
        have hm := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left d3 (show 0 ≤ 4 * A ^ (2 : ℕ) by positivity)) hA0.le
        have hsplit : 4 * A ^ (2 : ℕ) * (1296 / q ^ (3 : ℕ) + 4536 / q ^ (4 : ℕ)) * A =
            4 * A ^ (2 : ℕ) * (1296 / q ^ (3 : ℕ)) * A + 4 * A ^ (2 : ℕ) * (4536 / q ^ (4 : ℕ)) * A := by ring
        rw [hsplit]
        linarith only [hm, hd4, hid]
      have hA7ε : A ^ (7 : ℕ) * ε ≤ 10000000 * (31 / 10000000000000) := by
        refine (h7 hA10.le).trans ?_
        have u := mul_le_mul_of_nonneg_left hb10.le (show (0 : ℝ) ≤ 10 ^ (7 : ℕ) by norm_num)
        norm_num at u ⊢
        linarith only [u]
      have hmul : (c0 * c3 - c1 * c2 +
          (c0 * b5 + c3 * b2 + b2 * b5 + c1 * b4 + c2 * b3 + b3 * b4)) * A ≤ 0 := by
        have e1 : (c0 * c3 - c1 * c2) * A ≤ -(4 * A ^ (2 : ℕ) * (1296 / q ^ (3 : ℕ) + 4536 / q ^ (4 : ℕ))) * A :=
          mul_le_mul_of_nonneg_right hDle hA0.le
        have e2 : (c0 * b5 + c3 * b2 + b2 * b5 + c1 * b4 + c2 * b3 + b3 * b4) * A ≤
            58100 * (A ^ (6 : ℕ) * ε) * A := mul_le_mul_of_nonneg_right herr hA0.le
        have hsum : (c0 * c3 - c1 * c2 +
            (c0 * b5 + c3 * b2 + b2 * b5 + c1 * b4 + c2 * b3 + b3 * b4)) * A =
            (c0 * c3 - c1 * c2) * A +
              (c0 * b5 + c3 * b2 + b2 * b5 + c1 * b4 + c2 * b3 + b3 * b4) * A := by ring
        have e3 : 58100 * (A ^ (6 : ℕ) * ε) * A = 58100 * (A ^ (7 : ℕ) * ε) := by ring
        rw [hsum]
        linarith only [e1, e2, hDA, hA7ε, e3]
      exact nonpos_of_mul_nonpos_left hmul hA0

/-- **Regime-I sign package.** -/
theorem regimeOne_curvature_signs {x : ℝ} (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 < thetaCuspLogCurvatureJet x ∧ 0 < thetaCuspLogCurvatureJetTwo x ∧
    thetaCuspLogCurvature x * thetaCuspLogCurvatureJetThree x ≤
      thetaCuspLogCurvatureJet x * thetaCuspLogCurvatureJetTwo x :=
  ⟨thetaCuspLogCurvatureJet_pos_of_six_le hA, thetaCuspLogCurvatureJetTwo_pos_of_six_le hA,
    thetaCuspLogCurvature_mul_jetThree_le_of_six_le hA⟩

end RHTower

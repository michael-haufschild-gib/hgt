import GaloisForLFunctions.WindowTowerOfSpecZ.TheOddCubicGaugeRetainsAVariance
import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.OddPrimeFreeGammaJumpCount
import GaloisForLFunctions.WindowTowerOfSpecZ.TheTransferAcrossAStage
import GaloisForLFunctions.RHTower.RiemannSiegelThresholdLaw

/-!
# The frozen odd form away from its cubic moment

On the unit support window, every odd C² test satisfies
`Q₁(F) + 20 M(F)² ≥ ‖F‖²/125`, with one explicit cubic moment `M`.
The ground-state variance pays both the Gamma and pole costs. The sharper
bound has moment coefficient `115/6` and mass coefficient
`5849/3360 − γ − log π − 3/320`.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly
open _root_.RHTower.WeilMarkovPole _root_.RHTower.WeilLevyPoleGauss
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open LatticeSectionTheory ArithmeticIncidencePositivity ArithmeticCriticalityTheory
open BiScaleUncertainty SpacingScaleHarmonicAnalysis

/-- The cubic moment selecting the potentially negative frozen odd direction. -/
def cubicOddMoment (F : ℝ → ℝ) : ℝ :=
  ∫ x, F x * (x * (1 - 16 * x ^ 2 / 5))

private theorem integral_even_unit {f : ℝ → ℝ}
    (hs : ∀ x, 1 ≤ |x| → f x = 0) (heven : ∀ x, f (-x) = f x) :
    (∫ x, f x) = 2 * ∫ x in Ioo (0 : ℝ) 1, f x := by
  have habs : ∀ x, f |x| = f x := by
    intro x
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, heven]
  rw [← integral_congr_ae (Eventually.of_forall habs), integral_comp_abs (f := f)]
  have he : ∀ x ∈ Ioi (0 : ℝ), f x = (Iic (1 : ℝ)).indicator f x := by
    intro x hx
    by_cases h : x ≤ 1
    · exact (Set.indicator_of_mem (Set.mem_Iic.mpr h) f).symm
    · rw [Set.indicator_of_notMem (show x ∉ Iic (1 : ℝ) from fun h' => h h'),
        hs x (by rw [abs_of_pos hx]; exact (lt_of_not_ge h).le)]
  rw [setIntegral_congr_fun measurableSet_Ioi he, setIntegral_indicator measurableSet_Iic,
    Ioi_inter_Iic, integral_Ioc_eq_integral_Ioo]

private theorem odd_logarithmic_cubic_unit {F : ℝ → ℝ} (hFc : Continuous F) {K : ℝ}
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|)
    (hFs : ∀ x, 1 ≤ |x| → F x = 0) (hFo : ∀ x, F (-x) = -F x) :
    (Real.log 2 + 7 / 5 + 11 / 28) * (∫ x, F x ^ 2) ≤
      (∫ t in Ioc (0 : ℝ) 2, (autocorr F 0 - autocorr F t) / t) +
      (15 / 2 : ℝ) * (∫ x in Ioo (0 : ℝ) 1, F x * oddCubicGauge x) ^ 2 := by
  have hF0 : F 0 = 0 := by have h := hFo 0; simp only [neg_zero] at h; linarith only [h]
  have hF1 : F 1 = 0 := hFs 1 (by norm_num)
  have hgap := folded_logarithmic_jump_cubic_gap hFc hF0 hF1 (fun x _ y _ => hFL x y)
  have hlag := logarithmic_pair_eq_lag hFc hFL hFs
  have hpair := logarithmic_pair_eq_folded_count hFc hFL hFs hFo
  have hm : (∫ x, F x ^ 2) = 2 * ∫ x in Ioo (0 : ℝ) 1, F x ^ 2 :=
    integral_even_unit (fun x hx => by rw [hFs x hx]; norm_num)
      (fun x => by rw [hFo, neg_sq])
  rw [hm]
  linarith only [hgap, hlag, hpair]

private theorem autocorr_half (F : ℝ → ℝ) (t : ℝ) :
    autocorr (fun x => F ((1 / 2) * x)) t = 2 * autocorr F ((1 / 2) * t) := by
  unfold autocorr
  have h := Measure.integral_comp_mul_left (fun x => F x * F (x + (1 / 2) * t)) (1 / 2 : ℝ)
  norm_num [smul_eq_mul] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards with x
  rw [mul_add]

/-- Scaling the cubic variance to a unit support window gives the moment debit `15M²`. -/
theorem odd_logarithmic_jump_cubic_half {F : ℝ → ℝ} (hFc : Continuous F) {K : ℝ}
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|)
    (hFs : ∀ x, (1 / 2 : ℝ) ≤ |x| → F x = 0) (hFo : ∀ x, F (-x) = -F x) :
    (Real.log 2 + 7 / 5 + 11 / 28) * (∫ x, F x ^ 2) ≤
      (∫ t in Ioc (0 : ℝ) 1, (autocorr F 0 - autocorr F t) / t) +
      15 * cubicOddMoment F ^ 2 := by
  let U : ℝ → ℝ := fun x => F ((1 / 2) * x)
  have hUc : Continuous U := hFc.comp (continuous_const.mul continuous_id)
  have hUL : ∀ x y, |U x - U y| ≤ (K / 2) * |x - y| := by
    intro x y
    have h := hFL ((1 / 2) * x) ((1 / 2) * y)
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
    dsimp [U]
    linarith only [h]
  have hUs : ∀ x, 1 ≤ |x| → U x = 0 := by
    intro x hx
    apply hFs
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith only [hx]
  have hUo : ∀ x, U (-x) = -U x := by intro x; dsimp [U]; rw [mul_neg, hFo]
  have hgap := odd_logarithmic_cubic_unit hUc hUL hUs hUo
  have hmass : (∫ x, U x ^ 2) = 2 * ∫ x, F x ^ 2 := by
    have h := Measure.integral_comp_mul_left (fun x => F x ^ 2) (1 / 2 : ℝ)
    norm_num [smul_eq_mul] at h
    exact h
  have hmoment : (∫ x in Ioo (0 : ℝ) 1, U x * oddCubicGauge x) = 2 * cubicOddMoment F := by
    have hfull : (∫ x, U x * oddCubicGauge x) =
        2 * ∫ x in Ioo (0 : ℝ) 1, U x * oddCubicGauge x := by
      apply integral_even_unit
      · intro x hx
        rw [hUs x hx, zero_mul]
      · intro x
        rw [hUo]
        unfold oddCubicGauge
        ring
    have h := Measure.integral_comp_mul_left
      (fun x => F x * (x * (1 - 16 * x ^ 2 / 5))) (1 / 2 : ℝ)
    norm_num [smul_eq_mul] at h
    change (∫ x, F ((1 / 2) * x) *
      (((1 / 2) * x) * (1 - 16 * ((1 / 2) * x) ^ 2 / 5))) = 2 * cubicOddMoment F at h
    have he : (fun x => F ((1 / 2) * x) *
        (((1 / 2) * x) * (1 - 16 * ((1 / 2) * x) ^ 2 / 5))) =
        (fun x => (1 / 2 : ℝ) * (U x * oddCubicGauge x)) := by
      funext x
      dsimp [U, oddCubicGauge]
      ring
    rw [he, integral_const_mul, hfull] at h
    linarith only [h]
  have hlag : (∫ t in Ioc (0 : ℝ) 2, (autocorr U 0 - autocorr U t) / t) =
      2 * ∫ t in Ioc (0 : ℝ) 1, (autocorr F 0 - autocorr F t) / t := by
    have he : ∀ t, (autocorr U 0 - autocorr U t) / t =
        (autocorr F 0 - autocorr F ((1 / 2) * t)) / ((1 / 2) * t) := by
      intro t
      dsimp [U]
      rw [autocorr_half F 0, autocorr_half F t, mul_zero]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc (fun t _ => he t),
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    have h := intervalIntegral.integral_comp_mul_left
      (fun t => (autocorr F 0 - autocorr F t) / t) (a := 0) (b := 2)
      (by norm_num : (1 / 2 : ℝ) ≠ 0)
    norm_num [smul_eq_mul] at h
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
    exact h
  rw [hmass, hmoment, hlag] at hgap
  nlinarith only [hgap]


private def cubicPoleResidual (x : ℝ) : ℝ :=
  2 * Real.sinh (x / 2) - (5 / 3 : ℝ) * (x * (1 - 16 * x ^ 2 / 5))

private theorem cosh_quarter_square_bound : Real.cosh (1 / 4 : ℝ) ^ 2 ≤ 16 / 15 := by
  have hc := pow_le_pow_left₀ (Real.cosh_pos (1 / 4 : ℝ)).le
    (Real.cosh_le_exp_half_sq (1 / 4 : ℝ)) 2
  rw [← Real.exp_nat_mul] at hc
  norm_num at hc
  have he : Real.exp (1 / 16 : ℝ) * Real.exp (-(1 / 16 : ℝ)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hl : (15 / 16 : ℝ) ≤ Real.exp (-(1 / 16 : ℝ)) := by
    linarith only [Real.add_one_le_exp (-(1 / 16 : ℝ))]
  have hm := mul_le_mul_of_nonneg_left hl (Real.exp_pos (1 / 16 : ℝ)).le
  linarith only [hc, he, hm]

private theorem half_sinh_residual_bound {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |2 * Real.sinh (x / 2) - x| ≤ |x| ^ 3 * Real.cosh (1 / 4 : ℝ) / 24 := by
  have hab (a : ℝ) : |Real.sinh a - a| = Real.sinh |a| - |a| := by
    by_cases ha : 0 ≤ a
    · rw [abs_of_nonneg ha, abs_of_nonneg (sub_nonneg.mpr (Real.self_le_sinh_iff.mpr ha))]
    · have hn : 0 ≤ -a := by linarith only [ha]
      rw [abs_of_neg (lt_of_not_ge ha),
        show Real.sinh a - a = -(Real.sinh (-a) - (-a)) by rw [Real.sinh_neg]; ring,
        abs_neg, abs_of_nonneg (sub_nonneg.mpr (Real.self_le_sinh_iff.mpr hn))]
  have hcosh : Real.cosh (|x| / 2) ≤ Real.cosh (1 / 4 : ℝ) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (by positivity : 0 ≤ |x| / 2),
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    linarith only [hx]
  have ht := _root_.RHTower.sinh_sub_self_le (show 0 ≤ |x| / 2 by positivity)
  have hm := mul_le_mul_of_nonneg_left hcosh (show 0 ≤ (|x| / 2) ^ 3 / 6 by positivity)
  rw [show 2 * Real.sinh (x / 2) - x = 2 * (Real.sinh (x / 2) - x / 2) by ring,
    abs_mul, abs_two, hab, abs_div, abs_two]
  nlinarith only [ht, hm]

/-- The squared sinh remainder is at most `x⁶/540` on the unit support window. -/
theorem unit_sinh_linear_residual_square_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    (2 * Real.sinh (x / 2) - x) ^ 2 ≤ x ^ 6 / 540 := by
  have hr := half_sinh_residual_bound hx
  rw [← abs_pow] at hr
  have hs := pow_le_pow_left₀ (abs_nonneg _) hr 2
  rw [sq_abs, div_pow, mul_pow, sq_abs] at hs
  have hc := mul_le_mul_of_nonneg_left cosh_quarter_square_bound
    (show 0 ≤ x ^ 6 by positivity)
  nlinarith only [hs, hc]

private theorem cubicPoleResidual_square_le {x : ℝ}
    (hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    cubicPoleResidual x ^ 2 ≤
      (21 / 20 : ℝ) * (x - (5 / 3 : ℝ) * (x * (1 - 16 * x ^ 2 / 5))) ^ 2 +
      (7 / 180 : ℝ) * x ^ 6 := by
  have hr2 := unit_sinh_linear_residual_square_le (abs_le.mpr hx)
  have hy := sq_nonneg ((x - (5 / 3 : ℝ) * (x * (1 - 16 * x ^ 2 / 5))) -
    20 * (2 * Real.sinh (x / 2) - x))
  unfold cubicPoleResidual
  nlinarith only [hy, hr2]

private theorem cubic_linear_residual_integral :
    (∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2),
      (x - (5 / 3 : ℝ) * (x * (1 - 16 * x ^ 2 / 5))) ^ 2) = 11 / 945 := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)]
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ =>
      4 * x ^ 3 / 27 - 64 * x ^ 5 / 45 + 256 * x ^ 7 / 63)
      ((x - (5 / 3 : ℝ) * (x * (1 - 16 * x ^ 2 / 5))) ^ 2) x := by
    have h := ((((hasDerivAt_pow 3 x).const_mul 4).div_const 27).sub
      (((hasDerivAt_pow 5 x).const_mul 64).div_const 45)).add
      (((hasDerivAt_pow 7 x).const_mul 256).div_const 63)
    exact h.congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((by fun_prop : Continuous (fun x : ℝ =>
      (x - (5 / 3 : ℝ) * (x * (1 - 16 * x ^ 2 / 5))) ^ 2)).intervalIntegrable _ _)]
  norm_num

/-- The sinh vector lies within squared distance `1/80` of the cubic moment vector. -/
private theorem cubicPoleResidual_integral_le :
    (∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), cubicPoleResidual x ^ 2) ≤ 1 / 80 := by
  have hd : Continuous (fun x : ℝ =>
      (x - (5 / 3 : ℝ) * (x * (1 - 16 * x ^ 2 / 5))) ^ 2) := by fun_prop
  have hr : Continuous (fun x => cubicPoleResidual x ^ 2) := by unfold cubicPoleResidual; fun_prop
  have hiD : IntegrableOn (fun x : ℝ =>
      (x - (5 / 3 : ℝ) * (x * (1 - 16 * x ^ 2 / 5))) ^ 2)
      (Icc (-(1 / 2 : ℝ)) (1 / 2)) := hd.integrableOn_Icc
  have hi6 : IntegrableOn (fun x : ℝ => x ^ 6)
      (Icc (-(1 / 2 : ℝ)) (1 / 2)) := (continuous_pow 6).integrableOn_Icc
  have hiSum : IntegrableOn (fun x : ℝ => (21 / 20 : ℝ) *
      (x - (5 / 3 : ℝ) * (x * (1 - 16 * x ^ 2 / 5))) ^ 2 + (7 / 180 : ℝ) * x ^ 6)
      (Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
    (hiD.const_mul (21 / 20)).add (hi6.const_mul (7 / 180))
  have h6 : (∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), x ^ 6) = (1 / 448 : ℝ) := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2), integral_pow]
    norm_num
  have h := setIntegral_mono_on (μ := volume) (s := Icc (-(1 / 2 : ℝ)) (1 / 2))
    (f := fun x => cubicPoleResidual x ^ 2)
    (g := fun x => (21 / 20 : ℝ) *
      (x - (5 / 3 : ℝ) * (x * (1 - 16 * x ^ 2 / 5))) ^ 2 + (7 / 180 : ℝ) * x ^ 6)
    hr.integrableOn_Icc hiSum
    measurableSet_Icc (fun x hx => cubicPoleResidual_square_le hx)
  rw [integral_add (f := fun x => (21 / 20 : ℝ) *
      (x - (5 / 3 : ℝ) * (x * (1 - 16 * x ^ 2 / 5))) ^ 2)
      (g := fun x => (7 / 180 : ℝ) * x ^ 6)
      (hiD.const_mul (21 / 20)) (hi6.const_mul (7 / 180)),
    integral_const_mul, integral_const_mul, cubic_linear_residual_integral, h6] at h
  norm_num at h
  linarith only [h]

private theorem cubic_pole_cost_le {F : ℝ → ℝ} (hFc : Continuous F)
    (hcs : HasCompactSupport F) (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    sinhPairing F ^ 2 / 2 ≤ (25 / 6 : ℝ) * cubicOddMoment F ^ 2 +
      (3 / 320 : ℝ) * (∫ x, F x ^ 2) := by
  let R : ℝ → ℝ := (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator cubicPoleResidual
  have hRc : Continuous cubicPoleResidual := by unfold cubicPoleResidual; fun_prop
  have hRmeas : AEStronglyMeasurable R := hRc.aestronglyMeasurable.indicator measurableSet_Icc
  have hRsq : (fun x => R x ^ 2) =
      (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun x => cubicPoleResidual x ^ 2) := by
    funext x
    by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) <;>
      simp only [R, Set.indicator_apply, hx, if_true, if_false, zero_pow two_ne_zero]
  have hRint : Integrable (fun x => R x ^ 2) := by
    rw [hRsq]
    exact (integrable_indicator_iff measurableSet_Icc).mpr (hRc.pow 2).integrableOn_Icc
  have hFint : Integrable (fun x => F x ^ 2) := (hFc.pow 2).integrable_of_hasCompactSupport
    (_root_.RHTower.CHMDPolar.hasCompactSupport_sq hcs)
  have hCS := GaloisForLFunctions.HTGeometry.sq_integral_mul_le
    hFc.aestronglyMeasurable hRmeas hFint hRint
  have hRbound : (∫ x, R x ^ 2) ≤ 1 / 80 := by
    rw [hRsq, integral_indicator measurableSet_Icc]
    exact cubicPoleResidual_integral_le
  have hE : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hres : (∫ x, F x * R x) ^ 2 ≤ (∫ x, F x ^ 2) / 80 := by
    have hm := mul_le_mul_of_nonneg_left hRbound hE
    nlinarith only [hCS, hm]
  have hsplit : sinhPairing F = (5 / 3 : ℝ) * cubicOddMoment F + ∫ x, F x * R x := by
    have hpoint : (fun x => F x * R x) = (fun x => F x * cubicPoleResidual x) := by
      funext x
      by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)
      · simp only [R, Set.indicator_of_mem hx]
      · have hz : F x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
        rw [hz, zero_mul, zero_mul]
    rw [hpoint]
    have hI1 : Integrable (fun x => F x * (2 * Real.sinh (x / 2))) :=
      (hFc.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right
    have hI2 : Integrable (fun x => F x * (x * (1 - 16 * x ^ 2 / 5))) :=
      (hFc.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right
    have he : (fun x => F x * cubicPoleResidual x) =
        (fun x => F x * (2 * Real.sinh (x / 2)) -
          (5 / 3 : ℝ) * (F x * (x * (1 - 16 * x ^ 2 / 5)))) := by
      funext x
      unfold cubicPoleResidual
      ring
    rw [he, integral_sub hI1 (hI2.const_mul _), integral_const_mul]
    unfold sinhPairing cubicOddMoment
    ring
  have hy := sq_nonneg (2 * ((5 / 3 : ℝ) * cubicOddMoment F) - (∫ x, F x * R x))
  rw [hsplit]
  nlinarith only [hy, hres]

private theorem odd_logarithmic_jump_cubic_smooth {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    (Real.log 2 + 7 / 5 + 11 / 28) * (∫ x, F x ^ 2) ≤
      (∫ t in Ioc (0 : ℝ) 1, (autocorr F 0 - autocorr F t) / t) +
      15 * cubicOddMoment F ^ 2 := by
  obtain ⟨K, hK⟩ := _root_.RHTower.CHMDDoobGraph.compact_source_lipschitz hF hcs
  have hFL : ∀ x y, |F x - F y| ≤ (K : ℝ) * |x - y| := by
    intro x y
    simpa only [Real.dist_eq] using hK.dist_le_mul x y
  have hz : Ioi (1 / 2 : ℝ) ⊆ {x | F x = 0} := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport fun h => not_le_of_gt hx (hs h).2
  have hzr : ∀ x, (1 / 2 : ℝ) ≤ x → F x = 0 := by
    have h := closure_minimal hz (isClosed_eq hF.continuous continuous_const)
    rw [closure_Ioi] at h
    exact fun x hx => h hx
  have hsupport : ∀ x, (1 / 2 : ℝ) ≤ |x| → F x = 0 := by
    intro x hx
    rcases le_total 0 x with hx0 | hx0
    · exact hzr x (by rwa [abs_of_nonneg hx0] at hx)
    · have hneg := hzr (-x) (by rwa [abs_of_nonpos hx0] at hx)
      rw [ho] at hneg
      exact neg_eq_zero.mp hneg
  exact odd_logarithmic_jump_cubic_half hF.continuous hFL hsupport ho

private theorem unit_gamma_weight_lower {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    1 / t + 1 / 2 - t / 24 - t ^ 2 / 16 ≤ archLevySinhWeight t := by
  refine le_of_mul_le_mul_left (a := t) ?_ ht
  have h := mul_archLevyDensity_ge_sharp ht ht1
  rw [archLevySinhWeight, exp_half_div_sinh_eq ht]
  have he : t * (1 / t + 1 / 2 - t / 24 - t ^ 2 / 16) =
      2 * (1 / 2 + t / 4 - t ^ 2 / 48 - t ^ 3 / 32) := by
    field_simp [ht.ne']
    ring
  rw [he]
  linarith only [h]

private theorem unit_gamma_tail_lower :
    Real.log 2 + Real.pi / 4 - 1 / 4 + 1 / 96 ≤ archLevyAntideriv 1 := by
  have hlog : Real.log (1 / 4 : ℝ) = -2 * Real.log 2 := by
    rw [show (1 / 4 : ℝ) = (2 ^ (2 : ℕ))⁻¹ by norm_num, Real.log_inv, Real.log_pow]
    norm_num
  have h := archLevyAntideriv_ge_second (y := 1) (by norm_num) (by norm_num)
  rw [hlog] at h
  norm_num at h
  linarith only [h]

/-- On the unit odd window, the Gamma form loses only an explicit constant from logarithmic jumps. -/
theorem unit_odd_gamma_jump_lower {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    (∫ t in Ioc (0 : ℝ) 1, (autocorr F 0 - autocorr F t) / t) -
      (Real.eulerMascheroniConstant + Real.log Real.pi + Real.log 2 + 5 / 96) *
        (∫ x, F x ^ 2) ≤ EF.gammaBracket 0 * (∫ x, F x ^ 2) + biScaleLevyEnergy F := by
  set M := autocorr F 0
  set D := fun t => M - autocorr F t
  set W := fun t => D t * archLevySinhWeight t
  have hc : Continuous (autocorr F) :=
    _root_.RHTower.ArchimedeanExactForm.continuous_autocorr hF hcs
  have hdc : Continuous D := continuous_const.sub hc
  have hd : ∀ t, 0 ≤ D t := fun t => sub_nonneg.mpr
    ((le_abs_self _).trans (abs_autocorr_le_zero hcs hF.continuous t))
  have hi : IntegrableOn W (Ioi (0 : ℝ)) := integrableOn_biScaleLevyIntegrand hF hcs
  have hsub : Ioc (0 : ℝ) 1 ⊆ Ioi 0 := fun _ ht => ht.1
  have hsubtail : Ioi (1 : ℝ) ⊆ Ioi 0 := fun t ht =>
    show (0 : ℝ) < t from lt_trans zero_lt_one ht
  have hilog : IntegrableOn (fun t => D t / t) (Ioc (0 : ℝ) 1) := by
    apply (hi.mono_set hsub).mono'
      ((hdc.measurable.div measurable_id).aestronglyMeasurable.restrict)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    change ‖D t / t‖ ≤ W t
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hd t) ht.1.le)]
    have hw := unit_gamma_weight_lower ht.1 ht.2
    have ht2 : t ^ 2 ≤ 1 := by nlinarith only [ht.1, ht.2]
    have hwinv : 1 / t ≤ archLevySinhWeight t := by linarith only [hw, ht.2, ht2]
    simpa only [W, div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hwinv (hd t)
  have hiD : IntegrableOn D (Ioc (0 : ℝ) 1) :=
    hdc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hitD : IntegrableOn (fun t => t * D t) (Ioc (0 : ℝ) 1) :=
    (continuous_id.mul hdc).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hit2D : IntegrableOn (fun t => t ^ 2 * D t) (Ioc (0 : ℝ) 1) :=
    ((continuous_pow 2).mul hdc).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hiSum : IntegrableOn (fun t => D t / t + D t / 2) (Ioc (0 : ℝ) 1) :=
    hilog.add (hiD.div_const 2)
  have hiSub : IntegrableOn (fun t => D t / t + D t / 2 - t * D t / 24)
      (Ioc (0 : ℝ) 1) := hiSum.sub (hitD.div_const 24)
  have hcomp : (∫ t in Ioc (0 : ℝ) 1,
      D t / t + D t / 2 - t * D t / 24 - t ^ 2 * D t / 16) ≤
      ∫ t in Ioc (0 : ℝ) 1, W t := by
    apply setIntegral_mono_on (hiSub.sub (hit2D.div_const 16))
      (hi.mono_set hsub) measurableSet_Ioc
    intro t ht
    have h := mul_le_mul_of_nonneg_left (unit_gamma_weight_lower ht.1 ht.2) (hd t)
    change D t / t + D t / 2 - t * D t / 24 - t ^ 2 * D t / 16 ≤ W t
    calc _ = D t * (1 / t + 1 / 2 - t / 24 - t ^ 2 / 16) := by ring
      _ ≤ W t := h
  have hzero := odd_autocorr_integral_zero ⟨hF, hcs⟩ hs ho
  norm_num at hzero
  have hD : (∫ t in Ioc (0 : ℝ) 1, D t) = M := by
    change (∫ t in Ioc (0 : ℝ) 1, M - autocorr F t) = M
    rw [integral_sub (f := fun _ : ℝ => M) (g := autocorr F)
      (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self), hzero, sub_zero, setIntegral_const]
    norm_num
  have hmom := odd_jump_first_moment_le ⟨hF, hcs⟩ (by norm_num : (0 : ℝ) < 1 / 2) hs ho
  norm_num at hmom
  have hmom2 : (∫ t in Ioc (0 : ℝ) 1, t ^ 2 * D t) ≤ (2 / 3 : ℝ) * M := by
    have hbound : ∀ t, t ^ 2 * D t ≤ (2 * M) * t ^ 2 := by
      intro t
      have hC := abs_autocorr_le_zero hcs hF.continuous t
      have hD2 : D t ≤ 2 * M := by
        have hn := neg_abs_le (autocorr F t)
        dsimp [D, M]
        linarith only [hC, hn]
      nlinarith only [mul_le_mul_of_nonneg_left hD2 (sq_nonneg t)]
    have h := setIntegral_mono_on (f := fun t => t ^ 2 * D t)
      (g := fun t => (2 * M) * t ^ 2) hit2D
      ((continuous_const.mul (continuous_pow 2)).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      measurableSet_Ioc (fun t _ => hbound t)
    have hpow : (∫ t in Ioc (0 : ℝ) 1, t ^ 2) = (1 / 3 : ℝ) := by
      rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_pow]
      norm_num
    rw [integral_const_mul, hpow] at h
    norm_num at h
    nlinarith only [h]
  rw [integral_sub hiSub (hit2D.div_const 16), integral_sub hiSum (hitD.div_const 24),
    integral_add hilog (hiD.div_const 2), integral_div, integral_div, integral_div, hD] at hcomp
  have htail : (∫ t in Ioi (1 : ℝ), W t) = 2 * archLevyAntideriv 1 * M := by
    have he : ∀ t ∈ Ioi (1 : ℝ), W t = 2 * archLevyDensity t * M := by
      intro t ht
      dsimp [W, D, M]
      rw [autocorr_eq_zero_of_support (x := t) hs (by norm_num; exact ht), sub_zero,
        archLevySinhWeight, exp_half_div_sinh_eq (lt_trans zero_lt_one ht)]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi he, integral_mul_const, integral_const_mul,
      WeilLevyCoshCrossover.integral_archLevyDensity_Ioi (by norm_num : (0 : ℝ) < 1)]
  have hsplit : (∫ t in Ioc (0 : ℝ) 1, W t) +
      (∫ t in Ioi (1 : ℝ), W t) = biScaleLevyEnergy F := by
    rw [← setIntegral_union (s := Ioc (0 : ℝ) 1) (t := Ioi (1 : ℝ))
      (Set.disjoint_left.mpr (fun t ht ht' => not_lt_of_ge ht.2 ht'))
      measurableSet_Ioi (hi.mono_set hsub) (hi.mono_set hsubtail),
      Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
    rfl
  rw [htail] at hsplit
  have hE : 0 ≤ M := by
    change 0 ≤ autocorr F 0
    rw [autocorr_zero_eq]
    exact integral_nonneg fun x => sq_nonneg _
  have htailM := mul_le_mul_of_nonneg_right unit_gamma_tail_lower hE
  have hGamma := congrArg (fun z : ℝ => z * M) neg_gammaBracket_zero_eq
  rw [← autocorr_zero_eq]
  change (∫ t in Ioc (0 : ℝ) 1, D t / t) -
    (Real.eulerMascheroniConstant + Real.log Real.pi + Real.log 2 + 5 / 96) * M ≤ _
  change (∫ t in Ioc (0 : ℝ) 1, t * D t) ≤ (3 / 4 : ℝ) * M at hmom
  nlinarith only [hcomp, hmom, hmom2, hsplit, htailM, hGamma]

/-- The retained cubic variance pays the frozen Gamma cost on the unit odd window. -/
private theorem cubic_frozen_arch_lower {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    (5849 / 3360 - Real.eulerMascheroniConstant - Real.log Real.pi) * (∫ x, F x ^ 2) ≤
      EF.gammaBracket 0 * (∫ x, F x ^ 2) + biScaleLevyEnergy F + 15 * cubicOddMoment F ^ 2 := by
  have hgamma := unit_odd_gamma_jump_lower hF hcs hs ho
  have hlog := odd_logarithmic_jump_cubic_smooth hF hcs hs ho
  nlinarith only [hgamma, hlog]

/-- The Markov jump count and the autocorrelation Lévy energy agree for compact C² tests. -/
theorem levyJump_eq_biScale {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F) :
    levyJump F = biScaleLevyEnergy F := by
  have he : ∀ t ∈ Ioi (0 : ℝ),
      archLevyDensity t * (∫ x, (F x - F (x + t)) ^ 2) =
        (autocorr F 0 - autocorr F t) * archLevySinhWeight t := by
    intro t ht
    rw [integral_sub_shift_sq hcs hF.continuous t, archLevySinhWeight,
      exp_half_div_sinh_eq ht]
    ring
  have hi : IntegrableOn (fun t => archLevyDensity t * (∫ x, (F x - F (x + t)) ^ 2))
      (Ioi (0 : ℝ)) := by
    apply (integrableOn_biScaleLevyIntegrand hF hcs).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (he t ht).symm
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t => archLevyDensity t * (∫ x, (F x - F (x + t)) ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (archLevyDensity_pos ht).le (integral_nonneg fun x => sq_nonneg _)
  unfold levyJump biScaleLevyEnergy
  rw [← integral_eq_lintegral_of_nonneg_ae hn hi.aestronglyMeasurable]
  exact setIntegral_congr_fun measurableSet_Ioi he

private theorem frozen_cubic_margin :
    (1 / 125 : ℝ) ≤ 5849 / 3360 - Real.eulerMascheroniConstant - Real.log Real.pi - 3 / 320 := by
  have hu : Real.log Real.pi ≤ Real.log 3 + Real.pi / 3 - 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < Real.pi / 3 by positivity)
    rw [Real.log_div Real.pi_ne_zero (by norm_num)] at h
    linarith only [h]
  have hg := _root_.RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  linarith only [hu, hg, Real.log_three_lt_d9, Real.pi_lt_d4]

/-- The exact cubic-moment bound after paying the Gamma and hyperbolic pole terms. -/
theorem stageForm_one_cubicMoment_lower {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2))
    (ho : ∀ x, F (-x) = -F x) :
    (5849 / 3360 - Real.eulerMascheroniConstant - Real.log Real.pi - 3 / 320) *
      (∫ x, F x ^ 2) ≤ stageForm 1 F + (115 / 6 : ℝ) * cubicOddMoment F ^ 2 := by
  have hcs : HasCompactSupport F := HasCompactSupport.intro isCompact_Icc
    (fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)))
  have harch := cubic_frozen_arch_lower hF hcs hs ho
  have hpole := cubic_pole_cost_le hF.continuous hcs hs
  have hJ := levyJump_eq_biScale hF hcs
  have hstage : EF.gammaBracket 0 * (∫ x, F x ^ 2) + biScaleLevyEnergy F -
      sinhPairing F ^ 2 / 2 ≤ stageForm 1 F := by
    norm_num [stageForm, markovForm, creationPotential, primeJump]
    rw [hJ]
    nlinarith only [sq_nonneg (coshPairing F)]
  nlinarith only [harch, hpole, hstage]

/-- One cubic moment pays every negative frozen odd direction on the unit support window. -/
theorem stageForm_one_add_cubicMoment_ge {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2))
    (ho : ∀ x, F (-x) = -F x) :
    (1 / 125 : ℝ) * (∫ x, F x ^ 2) ≤ stageForm 1 F + 20 * cubicOddMoment F ^ 2 := by
  have h := stageForm_one_cubicMoment_lower hF hs ho
  have hE : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hm := mul_le_mul_of_nonneg_right frozen_cubic_margin hE
  nlinarith only [h, hm, sq_nonneg (cubicOddMoment F)]

/-- The frozen odd form is coercive on the kernel of its explicit cubic moment. -/
theorem stageForm_one_coercive_of_cubicMoment_zero {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2))
    (ho : ∀ x, F (-x) = -F x) (hm : cubicOddMoment F = 0) :
    (1 / 125 : ℝ) * (∫ x, F x ^ 2) ≤ stageForm 1 F := by
  simpa only [hm, zero_pow two_ne_zero, mul_zero, add_zero] using
    stageForm_one_add_cubicMoment_ge hF hs ho

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.stageForm_one_add_cubicMoment_ge
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.stageForm_one_cubicMoment_lower
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.stageForm_one_coercive_of_cubicMoment_zero
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.unit_odd_gamma_jump_lower

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.unit_sinh_linear_residual_square_le

import GaloisForLFunctions.RHTower.PMAnalyticPowerModel

/-!
# Exact optimal variance of the PM analytic power model

Finite integrals include the zero interval `(0,1]`. Their literal mean uniquely
minimizes every scalar-centered square error. The first and second moments give
closed variance formulas on either side of the exponent `1/2`, including the
logarithmic formula at equality. These statements concern the comparison model,
not the actual arithmetic Chebyshev profile.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

theorem integral_pmPowerProfile_comp (σ R : ℝ) (hR : 1 ≤ R)
    (g : ℝ → ℝ) (hg : g 0 = 0) :
    (∫ x in Ioo (0 : ℝ) R, g (pmPowerProfile σ x)) =
      ∫ x in (1 : ℝ)..R, g (1 + x ^ (σ - 1)) := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← Ioc_union_Ioc_eq_Ioc zero_le_one hR, union_comm]
  rw [integral_union_eq_left_of_forall measurableSet_Ioc
    (fun x (hx : x ∈ Ioc (0 : ℝ) 1) => by
      simpa [pmPowerProfile, pmPowerModel, hx.2] using hg)]
  rw [intervalIntegral.integral_of_le hR]
  exact setIntegral_congr_fun measurableSet_Ioc (fun x hx => by rw [pmPowerProfile_eq hx.1])

theorem integrableOn_pmPowerProfile_pow {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (n : ℕ) (R : ℝ) : IntegrableOn (fun x => pmPowerProfile σ x ^ n) (Ioo 0 R) := by
  refine Measure.integrableOn_of_bounded (M := (2 : ℝ) ^ n) measure_Ioo_lt_top.ne
    ((measurable_pmPowerProfile hσ0).pow_const n).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (pmPowerProfile_bounds hσ1 x).1 n)]
    exact pow_le_pow_left₀ (pmPowerProfile_bounds hσ1 x).1 (pmPowerProfile_bounds hσ1 x).2 n

theorem integral_pmPowerProfile {σ R : ℝ} (hσ : 0 < σ) (hR : 1 ≤ R) :
    (∫ x in Ioo (0 : ℝ) R, pmPowerProfile σ x) =
      R - 1 + (R ^ σ - 1) / σ := by
  rw [integral_pmPowerProfile_comp σ R hR (fun y => y) rfl]
  rw [intervalIntegral.integral_add intervalIntegrable_const
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < σ - 1)),
    intervalIntegral.integral_const, smul_eq_mul, mul_one,
    integral_rpow (Or.inl (by linarith : -1 < σ - 1))]
  simp only [sub_add_cancel, Real.one_rpow]

theorem integral_pmPowerProfile_sq_split {σ R : ℝ} (hσ : 0 < σ) (hR : 1 ≤ R) :
    (∫ x in Ioo (0 : ℝ) R, pmPowerProfile σ x ^ 2) =
      R - 1 + 2 * (R ^ σ - 1) / σ + ∫ x in (1 : ℝ)..R, x ^ (2 * σ - 2) := by
  have hz : (0 : ℝ) ∉ uIcc 1 R := by simp [uIcc_of_le hR]
  have hp : IntervalIntegrable (fun x : ℝ => x ^ (σ - 1)) volume 1 R :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr hz)
  have hq : IntervalIntegrable (fun x : ℝ => x ^ (2 * σ - 2)) volume 1 R :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr hz)
  have ha : IntervalIntegrable (fun x : ℝ => 1 + 2 * x ^ (σ - 1)) volume 1 R :=
    intervalIntegrable_const.add (hp.const_mul 2)
  rw [integral_pmPowerProfile_comp σ R hR (fun y => y ^ 2) (by norm_num)]
  calc
    _ = ∫ x in (1 : ℝ)..R, (1 + 2 * x ^ (σ - 1)) + x ^ (2 * σ - 2) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx0 : 0 ≤ x := le_trans zero_le_one ((uIcc_of_le hR ▸ hx).1)
      have he : x ^ (2 * σ - 2) = (x ^ (σ - 1)) ^ 2 := by
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hx0]
        congr 1
        ring
      dsimp only
      rw [he]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add ha hq,
        intervalIntegral.integral_add intervalIntegrable_const (hp.const_mul 2),
        intervalIntegral.integral_const, smul_eq_mul, mul_one,
        intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by linarith : -1 < σ - 1))]
      simp only [sub_add_cancel, Real.one_rpow]
      ring

theorem integral_pmPowerProfile_sq {σ R : ℝ} (hσ : 0 < σ)
    (hhalf : 2 * σ - 1 ≠ 0) (hR : 1 ≤ R) :
    (∫ x in Ioo (0 : ℝ) R, pmPowerProfile σ x ^ 2) =
      R - 1 + 2 * (R ^ σ - 1) / σ + (R ^ (2 * σ - 1) - 1) / (2 * σ - 1) := by
  rw [integral_pmPowerProfile_sq_split hσ hR,
    integral_rpow (Or.inr ⟨by intro h; apply hhalf; linarith,
      by simp [uIcc_of_le hR]⟩)]
  rw [show 2 * σ - 2 + 1 = 2 * σ - 1 by ring, Real.one_rpow]

theorem integral_pmPowerProfile_sq_half {R : ℝ} (hR : 1 ≤ R) :
    (∫ x in Ioo (0 : ℝ) R, pmPowerProfile (1 / 2) x ^ 2) =
      R - 1 + 4 * (R ^ (1 / 2 : ℝ) - 1) + Real.log R := by
  rw [integral_pmPowerProfile_sq_split (by norm_num : (0 : ℝ) < 1 / 2) hR]
  norm_num only [show 2 * (1 / 2 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]
  rw [integral_inv_of_pos zero_lt_one (lt_of_lt_of_le zero_lt_one hR), div_one]
  ring

/-- Mean of the literal comparison profile on the full interval, including its zero head. -/
def pmPowerMean (σ R : ℝ) : ℝ := (∫ x in Ioo (0 : ℝ) R, pmPowerProfile σ x) / R

/-- Intrinsic variance of the literal comparison profile. -/
def pmPowerVariance (σ R : ℝ) : ℝ :=
  ∫ x in Ioo (0 : ℝ) R, (pmPowerMean σ R - pmPowerProfile σ x) ^ 2

theorem pmPowerVariance_nonneg (σ R : ℝ) : 0 ≤ pmPowerVariance σ R :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem integral_sq_sub_pmPowerProfile {σ R : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hR : 0 ≤ R) (B : ℝ) :
    (∫ x in Ioo (0 : ℝ) R, (B - pmPowerProfile σ x) ^ 2) =
      R * B ^ 2 - 2 * B * (∫ x in Ioo (0 : ℝ) R, pmPowerProfile σ x) +
        ∫ x in Ioo (0 : ℝ) R, pmPowerProfile σ x ^ 2 := by
  have hf : IntegrableOn (pmPowerProfile σ) (Ioo 0 R) := by
    simpa using integrableOn_pmPowerProfile_pow hσ0 hσ1 1 R
  have hq := integrableOn_pmPowerProfile_pow hσ0 hσ1 2 R
  have hc : IntegrableOn (fun _ : ℝ => B ^ 2) (Ioo 0 R) :=
    integrableOn_const measure_Ioo_lt_top.ne
  have hs : IntegrableOn (fun x => B ^ 2 - 2 * B * pmPowerProfile σ x) (Ioo 0 R) :=
    hc.sub (hf.const_mul (2 * B))
  calc
    _ = ∫ x in Ioo (0 : ℝ) R, (B ^ 2 - 2 * B * pmPowerProfile σ x) +
        pmPowerProfile σ x ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x _
      ring
    _ = _ := by
      rw [integral_add hs hq, integral_sub hc (hf.const_mul _), integral_const_mul,
        setIntegral_const, Real.volume_real_Ioo_of_le hR, sub_zero, smul_eq_mul]

theorem pmPowerVariance_moments {σ R : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hR : 0 < R) :
    pmPowerVariance σ R = (∫ x in Ioo (0 : ℝ) R, pmPowerProfile σ x ^ 2) -
      (∫ x in Ioo (0 : ℝ) R, pmPowerProfile σ x) ^ 2 / R := by
  rw [pmPowerVariance, integral_sq_sub_pmPowerProfile hσ0 hσ1 hR.le, pmPowerMean]
  field_simp
  ring

theorem pmPowerVariance_decomposition {σ R : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hR : 0 < R) (B : ℝ) :
    (∫ x in Ioo (0 : ℝ) R, (B - pmPowerProfile σ x) ^ 2) =
      R * (B - pmPowerMean σ R) ^ 2 + pmPowerVariance σ R := by
  rw [integral_sq_sub_pmPowerProfile hσ0 hσ1 hR.le,
    pmPowerVariance_moments hσ0 hσ1 hR, pmPowerMean]
  field_simp
  ring

theorem pmPowerVariance_minimizes {σ R : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hR : 0 < R) (B : ℝ) :
    pmPowerVariance σ R ≤ ∫ x in Ioo (0 : ℝ) R, (B - pmPowerProfile σ x) ^ 2 := by
  rw [pmPowerVariance_decomposition hσ0 hσ1 hR]
  exact le_add_of_nonneg_left (mul_nonneg hR.le (sq_nonneg _))

theorem pmPowerVariance_unique_minimizer {σ R : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hR : 0 < R) (B : ℝ) :
    (∫ x in Ioo (0 : ℝ) R, (B - pmPowerProfile σ x) ^ 2) = pmPowerVariance σ R ↔
      B = pmPowerMean σ R := by
  rw [pmPowerVariance_decomposition hσ0 hσ1 hR]
  constructor
  · intro h
    have hs : (B - pmPowerMean σ R) ^ 2 = 0 := by nlinarith [sq_nonneg (B - pmPowerMean σ R)]
    nlinarith [sq_nonneg (B - pmPowerMean σ R)]
  · intro h
    simp [h]

theorem pmPowerVariance_formula {σ R : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hhalf : 2 * σ - 1 ≠ 0) (hR : 1 ≤ R) :
    pmPowerVariance σ R =
      (1 - σ) ^ 2 / (σ ^ 2 * (2 * σ - 1)) * R ^ (2 * σ - 1) +
        1 - 1 / (2 * σ - 1) + 2 * (1 / σ) * (1 + 1 / σ) * R ^ (σ - 1) -
          (1 + 1 / σ) ^ 2 / R := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  rw [pmPowerVariance_moments hσ0.le hσ1 hRp,
    integral_pmPowerProfile hσ0 hR, integral_pmPowerProfile_sq hσ0 hhalf hR]
  have hp : R ^ (2 * σ) = (R ^ σ) ^ 2 := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hRp.le]
    congr 1
    ring
  rw [Real.rpow_sub_one hRp.ne' (2 * σ), Real.rpow_sub_one hRp.ne' σ, hp]
  field_simp
  ring

theorem pmPowerVariance_half_formula {R : ℝ} (hR : 1 ≤ R) :
    pmPowerVariance (1 / 2) R = Real.log R - 3 + 12 * R ^ (-1 / 2 : ℝ) - 9 / R := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  rw [pmPowerVariance_moments (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hRp,
    integral_pmPowerProfile (by norm_num : (0 : ℝ) < 1 / 2) hR,
    integral_pmPowerProfile_sq_half hR]
  have hs : (R ^ (1 / 2 : ℝ)) ^ 2 = R := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hRp.le]
    norm_num
  have hn : R ^ (-1 / 2 : ℝ) = R ^ (1 / 2 : ℝ) / R := by
    convert Real.rpow_sub_one hRp.ne' (1 / 2 : ℝ) using 1
    norm_num
  rw [hn]
  field_simp
  nlinarith [hs]

end RHTower

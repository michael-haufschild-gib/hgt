import GaloisForLFunctions.RHTower.XiWardCubicFourShiftGammaCancellation

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- Elementary lower kernel retained by the four-shift Gamma-cancelled feature. -/
def fourShiftGammaLowerKernel (r a : ℝ) : ℝ :=
  Real.exp (-4 * a * r) * (1 - Real.exp (-2 * a * r)) ^ 3

/-- The Gamma-cancelled feature dominates a positive cubic finite-difference kernel. -/
theorem fourShiftGammaLowerKernel_le
    {r a : ℝ} (hr : 0 ≤ r) (ha0 : 0 < a) (ha : a ≤ 1 / 2) :
    fourShiftGammaLowerKernel r a ≤
      fourShiftGammaCancelledEnergyFeature r a := by
  rw [fourShiftGammaCancelledEnergyFeature_eq_factor,
    fourShiftGammaLowerKernel]
  let x := Real.exp (-2 * a * r)
  let q := Real.exp (-2 * r)
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hx1 : x ≤ 1 := by
    rw [show x = Real.exp (-2 * a * r) by rfl, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hq1 : q ≤ 1 := by
    rw [show q = Real.exp (-2 * r) by rfl, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hqx : q * x ≤ x := by
    nlinarith
  have hqxx : q ≤ x ^ 2 := by
    rw [show q = Real.exp (-2 * r) by rfl,
      show x ^ 2 = Real.exp (-4 * a * r) by
        rw [show x = Real.exp (-2 * a * r) by rfl, pow_two, ← Real.exp_add]
        congr 1
        ring]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hleft : 1 - x ≤ 1 - q * x := by linarith
  have hright : x * (1 - x) ≤ x - q := by nlinarith
  have hbase : 0 ≤ x * (1 - x) := mul_nonneg hx0 (sub_nonneg.mpr hx1)
  have hmiddle : 0 ≤ 1 - q * x := sub_nonneg.mpr (hqx.trans hx1)
  have hx2 : Real.exp (-4 * a * r) = x ^ 2 := by
    rw [show x = Real.exp (-2 * a * r) by rfl, pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hx2]
  change x ^ 2 * (1 - x) ^ 3 ≤ x * (1 - x) * (1 - q * x) * (x - q)
  calc
    x ^ 2 * (1 - x) ^ 3 =
        x * (1 - x) * (1 - x) * (x * (1 - x)) := by ring
    _ ≤ x * (1 - x) * (1 - q * x) * (x * (1 - x)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hleft hbase) hbase
    _ ≤ x * (1 - x) * (1 - q * x) * (x - q) := by
      exact mul_le_mul_of_nonneg_left hright (mul_nonneg hbase hmiddle)

/-- In the zeta strip, the four-shift feature is nonnegative and exponentially bounded. -/
theorem fourShiftGammaCancelledEnergyFeature_nonneg_le_exp
    {r a : ℝ} (hr : 0 ≤ r) (ha0 : 0 < a) (ha : a ≤ 1 / 2) :
    0 ≤ fourShiftGammaCancelledEnergyFeature r a ∧
      fourShiftGammaCancelledEnergyFeature r a ≤ Real.exp (-2 * a * r) := by
  rw [fourShiftGammaCancelledEnergyFeature_eq_factor]
  have hx0 : 0 ≤ Real.exp (-2 * a * r) := (Real.exp_pos _).le
  have hq0 : 0 ≤ Real.exp (-2 * r) := (Real.exp_pos _).le
  have hx1 : Real.exp (-2 * a * r) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hq1 : Real.exp (-2 * r) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hqx : Real.exp (-2 * r) ≤ Real.exp (-2 * a * r) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hqxx : Real.exp (-2 * r) * Real.exp (-2 * a * r) ≤ 1 := by
    calc
      Real.exp (-2 * r) * Real.exp (-2 * a * r) ≤
          1 * Real.exp (-2 * a * r) :=
        mul_le_mul_of_nonneg_right hq1 hx0
      _ ≤ 1 := by simpa using hx1
  have hfac2 : 1 - Real.exp (-2 * r) * Real.exp (-2 * a * r) ≤ 1 := by
    nlinarith [mul_nonneg hq0 hx0]
  have hfac1 : 1 - Real.exp (-2 * a * r) ≤ 1 := by linarith
  have hfac3 : Real.exp (-2 * a * r) - Real.exp (-2 * r) ≤ 1 := by
    linarith
  constructor
  · positivity
  · calc
      Real.exp (-2 * a * r) * (1 - Real.exp (-2 * a * r)) *
            (1 - Real.exp (-2 * r) * Real.exp (-2 * a * r)) *
              (Real.exp (-2 * a * r) - Real.exp (-2 * r)) ≤
          Real.exp (-2 * a * r) * 1 * 1 * 1 := by
        gcongr
      _ = Real.exp (-2 * a * r) := by ring

private theorem integral_fourShift_cubic_exp {rate : ℝ} (hrate : 0 < rate) :
    (∫ t : ℝ in Ioi 0, t ^ 2 * Real.exp (-(rate * t))) =
      2 / rate ^ 3 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (3 : ℝ)) (r := rate) (by norm_num) hrate
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two] at h
  have hgamma : Real.Gamma 3 = 2 := by
    rw [show (3 : ℝ) = (2 : ℕ) + 1 by norm_num,
      Real.Gamma_nat_eq_factorial]
    norm_num
  rw [hgamma] at h
  norm_num at h ⊢
  rw [h]
  field_simp [hrate.ne']

private theorem integrableOn_fourShift_cubic_exp {rate : ℝ} (hrate : 0 < rate) :
    IntegrableOn (fun t : ℝ => t ^ 2 * Real.exp (-(rate * t))) (Ioi 0) := by
  have hvalue := integral_fourShift_cubic_exp hrate
  have hne : (∫ t : ℝ in Ioi 0,
      t ^ 2 * Real.exp (-(rate * t))) ≠ 0 := by
    rw [hvalue]
    positivity
  exact Integrable.of_integral_ne_zero hne

private theorem fourShiftGammaLowerKernel_sq_expand (a r : ℝ) :
    r ^ 2 * fourShiftGammaLowerKernel r a ^ 2 =
      r ^ 2 * Real.exp (-((8 * a) * r)) -
      6 * (r ^ 2 * Real.exp (-((10 * a) * r))) +
      15 * (r ^ 2 * Real.exp (-((12 * a) * r))) -
      20 * (r ^ 2 * Real.exp (-((14 * a) * r))) +
      15 * (r ^ 2 * Real.exp (-((16 * a) * r))) -
      6 * (r ^ 2 * Real.exp (-((18 * a) * r))) +
      r ^ 2 * Real.exp (-((20 * a) * r)) := by
  unfold fourShiftGammaLowerKernel
  have hpow (n : ℕ) :
      Real.exp (-((8 + 2 * n) * a * r)) =
        Real.exp (-(8 * a * r)) * Real.exp (-(2 * a * r)) ^ n := by
    rw [← Real.exp_nat_mul]
    rw [← Real.exp_add]
    congr 1
    ring
  have hbase : Real.exp (-4 * a * r) ^ 2 = Real.exp (-(8 * a * r)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, hbase]
  rw [show Real.exp (-((8 * a) * r)) =
      Real.exp (-(8 * a * r)) by congr 1]
  rw [show Real.exp (-((10 * a) * r)) =
      Real.exp (-(8 * a * r)) * Real.exp (-(2 * a * r)) ^ 1 by
        convert hpow 1 using 1
        norm_num]
  rw [show Real.exp (-((12 * a) * r)) =
      Real.exp (-(8 * a * r)) * Real.exp (-(2 * a * r)) ^ 2 by
        convert hpow 2 using 1
        norm_num]
  rw [show Real.exp (-((14 * a) * r)) =
      Real.exp (-(8 * a * r)) * Real.exp (-(2 * a * r)) ^ 3 by
        convert hpow 3 using 1
        norm_num]
  rw [show Real.exp (-((16 * a) * r)) =
      Real.exp (-(8 * a * r)) * Real.exp (-(2 * a * r)) ^ 4 by
        convert hpow 4 using 1
        norm_num]
  rw [show Real.exp (-((18 * a) * r)) =
      Real.exp (-(8 * a * r)) * Real.exp (-(2 * a * r)) ^ 5 by
        convert hpow 5 using 1
        norm_num]
  rw [show Real.exp (-((20 * a) * r)) =
      Real.exp (-(8 * a * r)) * Real.exp (-(2 * a * r)) ^ 6 by
        convert hpow 6 using 1
        norm_num]
  ring

/-- Exact cubic self-energy of the elementary lower kernel. -/
theorem integral_fourShiftGammaLowerKernel_sq
    {a : ℝ} (ha : 0 < a) :
    (∫ r : ℝ in Ioi 0, r ^ 2 * fourShiftGammaLowerKernel r a ^ 2) =
      4410583 / (21337344000 * a ^ 3) := by
  let f8 : ℝ → ℝ := fun r => r ^ 2 * Real.exp (-((8 * a) * r))
  let f10 : ℝ → ℝ := fun r => -6 * (r ^ 2 * Real.exp (-((10 * a) * r)))
  let f12 : ℝ → ℝ := fun r => 15 * (r ^ 2 * Real.exp (-((12 * a) * r)))
  let f14 : ℝ → ℝ := fun r => -20 * (r ^ 2 * Real.exp (-((14 * a) * r)))
  let f16 : ℝ → ℝ := fun r => 15 * (r ^ 2 * Real.exp (-((16 * a) * r)))
  let f18 : ℝ → ℝ := fun r => -6 * (r ^ 2 * Real.exp (-((18 * a) * r)))
  let f20 : ℝ → ℝ := fun r => r ^ 2 * Real.exp (-((20 * a) * r))
  have h8r : 0 < 8 * a := mul_pos (by norm_num) ha
  have h10r : 0 < 10 * a := mul_pos (by norm_num) ha
  have h12r : 0 < 12 * a := mul_pos (by norm_num) ha
  have h14r : 0 < 14 * a := mul_pos (by norm_num) ha
  have h16r : 0 < 16 * a := mul_pos (by norm_num) ha
  have h18r : 0 < 18 * a := mul_pos (by norm_num) ha
  have h20r : 0 < 20 * a := mul_pos (by norm_num) ha
  have h8 : IntegrableOn f8 (Ioi 0) := integrableOn_fourShift_cubic_exp h8r
  have h10 : IntegrableOn f10 (Ioi 0) :=
    (integrableOn_fourShift_cubic_exp h10r).const_mul (-6)
  have h12 : IntegrableOn f12 (Ioi 0) :=
    (integrableOn_fourShift_cubic_exp h12r).const_mul 15
  have h14 : IntegrableOn f14 (Ioi 0) :=
    (integrableOn_fourShift_cubic_exp h14r).const_mul (-20)
  have h16 : IntegrableOn f16 (Ioi 0) :=
    (integrableOn_fourShift_cubic_exp h16r).const_mul 15
  have h18 : IntegrableOn f18 (Ioi 0) :=
    (integrableOn_fourShift_cubic_exp h18r).const_mul (-6)
  have h20 : IntegrableOn f20 (Ioi 0) := integrableOn_fourShift_cubic_exp h20r
  have hpoint :
      (fun r : ℝ => r ^ 2 * fourShiftGammaLowerKernel r a ^ 2) =
        ((((((f8 + f10) + f12) + f14) + f16) + f18) + f20) := by
    funext r
    rw [fourShiftGammaLowerKernel_sq_expand]
    change _ = f8 r + f10 r + f12 r + f14 r + f16 r + f18 r + f20 r
    ring
  rw [hpoint]
  change (∫ r : ℝ in Ioi 0,
    ((((((f8 + f10) + f12) + f14) + f16) + f18) + f20) r) = _
  simp only [Pi.add_apply]
  have hsum20 := integral_add
    (((((h8.add h10).add h12).add h14).add h16).add h18) h20
  have hsum18 := integral_add
    ((((h8.add h10).add h12).add h14).add h16) h18
  have hsum16 := integral_add (((h8.add h10).add h12).add h14) h16
  have hsum14 := integral_add ((h8.add h10).add h12) h14
  have hsum12 := integral_add (h8.add h10) h12
  have hsum10 := integral_add h8 h10
  simp only [Pi.add_apply] at hsum20 hsum18 hsum16 hsum14 hsum12 hsum10
  rw [hsum20, hsum18, hsum16, hsum14, hsum12, hsum10]
  change
    (∫ r : ℝ in Ioi 0, r ^ 2 * Real.exp (-((8 * a) * r))) +
      (∫ r : ℝ in Ioi 0, -6 * (r ^ 2 * Real.exp (-((10 * a) * r)))) +
      (∫ r : ℝ in Ioi 0, 15 * (r ^ 2 * Real.exp (-((12 * a) * r)))) +
      (∫ r : ℝ in Ioi 0, -20 * (r ^ 2 * Real.exp (-((14 * a) * r)))) +
      (∫ r : ℝ in Ioi 0, 15 * (r ^ 2 * Real.exp (-((16 * a) * r)))) +
      (∫ r : ℝ in Ioi 0, -6 * (r ^ 2 * Real.exp (-((18 * a) * r)))) +
      (∫ r : ℝ in Ioi 0, r ^ 2 * Real.exp (-((20 * a) * r))) = _
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul]
  rw [integral_fourShift_cubic_exp h8r,
    integral_fourShift_cubic_exp h10r,
    integral_fourShift_cubic_exp h12r,
    integral_fourShift_cubic_exp h14r,
    integral_fourShift_cubic_exp h16r,
    integral_fourShift_cubic_exp h18r,
    integral_fourShift_cubic_exp h20r]
  field_simp [ha.ne']
  ring

private theorem integrableOn_fourShiftGammaLowerKernel_sq
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun r : ℝ => r ^ 2 * fourShiftGammaLowerKernel r a ^ 2)
      (Ioi 0) := by
  have hvalue := integral_fourShiftGammaLowerKernel_sq ha
  have hne : (∫ r : ℝ in Ioi 0,
      r ^ 2 * fourShiftGammaLowerKernel r a ^ 2) ≠ 0 := by
    rw [hvalue]
    positivity
  exact Integrable.of_integral_ne_zero hne

private theorem integrableOn_fourShiftGammaCancelledSelfEnergy
    {a : ℝ} (ha : 0 < a) (hhalf : a ≤ 1 / 2) :
    IntegrableOn (fun r : ℝ =>
      r ^ 2 * fourShiftGammaCancelledEnergyFeature r a ^ 2) (Ioi 0) := by
  have hrate : 0 < 4 * a := mul_pos (by norm_num) ha
  have hmajor := integrableOn_fourShift_cubic_exp hrate
  apply hmajor.mono'
  · apply Continuous.aestronglyMeasurable
    unfold fourShiftGammaCancelledEnergyFeature
      fourShiftGammaCancelledPolynomial
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hb := fourShiftGammaCancelledEnergyFeature_nonneg_le_exp hr.le ha hhalf
    have hsq : fourShiftGammaCancelledEnergyFeature r a ^ 2 ≤
        Real.exp (-2 * a * r) ^ 2 := by nlinarith
    have hexp : Real.exp (-2 * a * r) ^ 2 =
        Real.exp (-((4 * a) * r)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [hexp] at hsq
    have hnon : 0 ≤ r ^ 2 * fourShiftGammaCancelledEnergyFeature r a ^ 2 := by
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnon]
    exact mul_le_mul_of_nonneg_left hsq (sq_nonneg r)

/-- Exact scale-sensitive divisor self-charge retained after cancelling both Gamma tails. -/
theorem fourShiftGammaCancelledSelfEnergy_ge_exact
    {a : ℝ} (ha : 0 < a) (hhalf : a ≤ 1 / 2) :
    4410583 / (21337344000 * a ^ 3) ≤
      fourShiftGammaCancelledSelfEnergy a := by
  have hlower := integrableOn_fourShiftGammaLowerKernel_sq ha
  have hcurrent := integrableOn_fourShiftGammaCancelledSelfEnergy ha hhalf
  rw [fourShiftGammaCancelledSelfEnergy,
    ← integral_fourShiftGammaLowerKernel_sq ha]
  apply MeasureTheory.integral_mono_ae hlower hcurrent
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hl := fourShiftGammaLowerKernel_le hr.le ha hhalf
  have hkernel0 : 0 ≤ fourShiftGammaLowerKernel r a := by
    unfold fourShiftGammaLowerKernel
    have hx1 : Real.exp (-2 * a * r) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have har : 0 ≤ a * r := mul_nonneg ha.le hr.le
      nlinarith
    exact mul_nonneg (Real.exp_pos _).le (pow_nonneg (sub_nonneg.mpr hx1) _)
  have hfeature0 :=
    (fourShiftGammaCancelledEnergyFeature_nonneg_le_exp hr.le ha hhalf).1
  have hsq : fourShiftGammaLowerKernel r a ^ 2 ≤
      fourShiftGammaCancelledEnergyFeature r a ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_left hsq (sq_nonneg r)

/-- Uniform positive self-charge for every off-line displacement in the zeta strip. -/
theorem fourShiftGammaCancelledSelfEnergy_ge
    {a : ℝ} (ha : 0 < a) (hhalf : a ≤ 1 / 2) :
    4410583 / 2667168000 ≤ fourShiftGammaCancelledSelfEnergy a := by
  apply le_trans ?_ (fourShiftGammaCancelledSelfEnergy_ge_exact ha hhalf)
  have hfactor :
      0 ≤ (1 / 2 - a) * ((1 / 2 : ℝ) ^ 2 + (1 / 2 : ℝ) * a + a ^ 2) := by
    apply mul_nonneg (sub_nonneg.mpr hhalf)
    nlinarith [sq_nonneg a]
  have hcube : a ^ 3 ≤ (1 / 2 : ℝ) ^ 3 := by
    nlinarith
  have hden : 0 < 21337344000 * a ^ 3 := by positivity
  apply (div_le_div_iff_of_pos_left (by norm_num) (by norm_num) hden).2
  norm_num at hcube ⊢
  nlinarith

end

end RHTower

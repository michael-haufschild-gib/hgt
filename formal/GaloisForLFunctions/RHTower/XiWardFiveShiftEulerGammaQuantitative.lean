import GaloisForLFunctions.RHTower.XiWardFiveShiftEulerGammaPrimeGap

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

def fiveShiftEulerGammaLowerKernel (r a : ℝ) : ℝ :=
  (1 / 5) * Real.exp (-8 * a * r) *
    (1 - Real.exp (-2 * a * r)) ^ 4

theorem fiveShiftEulerGammaLowerKernel_le
    {r a : ℝ} (hr : 0 ≤ r) (ha0 : 0 < a) (ha : a ≤ 1 / 2) :
    fiveShiftEulerGammaLowerKernel r a ≤ fiveShiftEulerGammaFeature r a := by
  rw [fiveShiftEulerGammaFeature, fiveShiftEulerGammaPolynomial,
    fiveShiftEulerGammaLowerKernel]
  let y := Real.exp (-(2 / 5 : ℝ) * a * r)
  let x := Real.exp (-2 * a * r)
  let t := Real.exp (-(6 / 5 : ℝ) * r)
  let q := Real.exp (-2 * r)
  let u := Real.exp (-(21 / 10 : ℝ) * r)
  have hy0 : 0 ≤ y := (Real.exp_pos _).le
  have hy1 : y ≤ 1 := by
    rw [show y = Real.exp (-(2 / 5 : ℝ) * a * r) by rfl, ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have har : 0 ≤ a * r := mul_nonneg ha0.le hr
    nlinarith
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x ≤ 1 := by
    rw [show x = Real.exp (-2 * a * r) by rfl, ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have har : 0 ≤ a * r := mul_nonneg ha0.le hr
    nlinarith
  have hxy : x = y ^ 5 := by
    rw [show x = Real.exp (-2 * a * r) by rfl,
      show y = Real.exp (-(2 / 5 : ℝ) * a * r) by rfl,
      ← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hty : t ≤ y ^ 6 := by
    rw [show t = Real.exp (-(6 / 5 : ℝ) * r) by rfl,
      show y = Real.exp (-(2 / 5 : ℝ) * a * r) by rfl,
      ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have har : a * r ≤ (1 / 2) * r := mul_le_mul_of_nonneg_right ha hr
    nlinarith
  have hqx2 : q ≤ x ^ 2 := by
    rw [show q = Real.exp (-2 * r) by rfl,
      show x = Real.exp (-2 * a * r) by rfl, pow_two, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have har : a * r ≤ (1 / 2) * r := mul_le_mul_of_nonneg_right ha hr
    nlinarith
  have hux2 : u ≤ x ^ 2 := by
    rw [show u = Real.exp (-(21 / 10 : ℝ) * r) by rfl,
      show x = Real.exp (-2 * a * r) by rfl, pow_two, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have har : a * r ≤ (1 / 2) * r := mul_le_mul_of_nonneg_right ha hr
    nlinarith
  have hgeom : (1 / 5 : ℝ) * (1 - x) ≤ 1 - y := by
    rw [hxy]
    have hsum : y ^ 4 + y ^ 3 + y ^ 2 + y + 1 ≤ 5 := by
      have hy2 : y ^ 2 ≤ 1 := pow_le_one₀ hy0 hy1
      have hy3 : y ^ 3 ≤ 1 := pow_le_one₀ hy0 hy1
      have hy4 : y ^ 4 ≤ 1 := pow_le_one₀ hy0 hy1
      linarith
    have hfactor : 1 - y ^ 5 = (1 - y) *
        (y ^ 4 + y ^ 3 + y ^ 2 + y + 1) := by ring
    rw [hfactor]
    have hnon : 0 ≤ 1 - y := sub_nonneg.mpr hy1
    nlinarith [mul_le_mul_of_nonneg_left hsum hnon]
  have hxt : x * (1 - y) ≤ x - t := by
    rw [hxy]
    nlinarith
  have hxq : x * (1 - x) ≤ x - q := by nlinarith
  have hxu : x * (1 - x) ≤ x - u := by nlinarith
  have hxpow : Real.exp (-8 * a * r) = x ^ 4 := by
    rw [show x = Real.exp (-2 * a * r) by rfl, ← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [hxpow]
  have hbase : 0 ≤ x * (1 - x) := mul_nonneg hx0 (sub_nonneg.mpr hx1)
  have hybase : 0 ≤ x * (1 - y) := mul_nonneg hx0 (sub_nonneg.mpr hy1)
  have hxt0 : 0 ≤ x - t := hybase.trans hxt
  have hxq0 : 0 ≤ x - q := hbase.trans hxq
  have hxu0 : 0 ≤ x - u := hbase.trans hxu
  have hgeomx : (1 / 5) * x * (1 - x) ≤ x * (1 - y) := by
    calc
      (1 / 5) * x * (1 - x) = x * ((1 / 5) * (1 - x)) := by ring
      _ ≤ x * (1 - y) := mul_le_mul_of_nonneg_left hgeom hx0
  calc
    (1 / 5) * x ^ 4 * (1 - x) ^ 4 =
        x * (1 - x) * ((1 / 5) * x * (1 - x)) *
          (x * (1 - x)) * (x * (1 - x)) := by ring
    _ ≤ x * (1 - x) * (x * (1 - y)) *
          (x * (1 - x)) * (x * (1 - x)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hgeomx hbase) hbase) hbase
    _ ≤ x * (1 - x) * (x - t) * (x - q) * (x - u) := by
      calc
        x * (1 - x) * (x * (1 - y)) * (x * (1 - x)) * (x * (1 - x)) =
            (x * (1 - x)) * (x * (1 - y)) *
              (x * (1 - x)) * (x * (1 - x)) := by ring
        _ ≤ (x * (1 - x)) * (x - t) * (x - q) * (x - u) := by
          exact mul_le_mul
            (mul_le_mul
              (mul_le_mul_of_nonneg_left hxt hbase)
              hxq hbase (mul_nonneg hbase hxt0))
            hxu hbase (mul_nonneg (mul_nonneg hbase hxt0) hxq0)

private theorem integral_fiveShift_cubic_exp {rate : ℝ} (hrate : 0 < rate) :
    (∫ t : ℝ in Ioi 0, t ^ 2 * Real.exp (-(rate * t))) = 2 / rate ^ 3 := by
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

private theorem integrableOn_fiveShift_cubic_exp {rate : ℝ} (hrate : 0 < rate) :
    IntegrableOn (fun t : ℝ => t ^ 2 * Real.exp (-(rate * t))) (Ioi 0) := by
  have hvalue := integral_fiveShift_cubic_exp hrate
  have hne : (∫ t : ℝ in Ioi 0,
      t ^ 2 * Real.exp (-(rate * t))) ≠ 0 := by
    rw [hvalue]
    positivity
  exact Integrable.of_integral_ne_zero hne

private theorem fiveShiftEulerGammaLowerKernel_expand (a r : ℝ) :
    r ^ 2 * fiveShiftEulerGammaLowerKernel r a =
      (1 / 5) * (r ^ 2 * Real.exp (-((8 * a) * r))) -
      (4 / 5) * (r ^ 2 * Real.exp (-((10 * a) * r))) +
      (6 / 5) * (r ^ 2 * Real.exp (-((12 * a) * r))) -
      (4 / 5) * (r ^ 2 * Real.exp (-((14 * a) * r))) +
      (1 / 5) * (r ^ 2 * Real.exp (-((16 * a) * r))) := by
  unfold fiveShiftEulerGammaLowerKernel
  have hpow (n : ℕ) :
      Real.exp (-((8 + 2 * n) * a * r)) =
        Real.exp (-(8 * a * r)) * Real.exp (-(2 * a * r)) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [show Real.exp (-((8 * a) * r)) = Real.exp (-(8 * a * r)) by congr 1]
  rw [show Real.exp (-((10 * a) * r)) =
      Real.exp (-(8 * a * r)) * Real.exp (-(2 * a * r)) by
        convert hpow 1 using 1
        · norm_num
        · simp]
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
  ring

theorem integral_fiveShiftEulerGammaLowerKernel
    {a : ℝ} (ha : 0 < a) :
    (∫ r : ℝ in Ioi 0, r ^ 2 * fiveShiftEulerGammaLowerKernel r a) =
      334699 / (3951360000 * a ^ 3) := by
  let f8 : ℝ → ℝ := fun r => (1 / 5) * (r ^ 2 * Real.exp (-((8 * a) * r)))
  let f10 : ℝ → ℝ := fun r => -(4 / 5) * (r ^ 2 * Real.exp (-((10 * a) * r)))
  let f12 : ℝ → ℝ := fun r => (6 / 5) * (r ^ 2 * Real.exp (-((12 * a) * r)))
  let f14 : ℝ → ℝ := fun r => -(4 / 5) * (r ^ 2 * Real.exp (-((14 * a) * r)))
  let f16 : ℝ → ℝ := fun r => (1 / 5) * (r ^ 2 * Real.exp (-((16 * a) * r)))
  have h8r : 0 < 8 * a := mul_pos (by norm_num) ha
  have h10r : 0 < 10 * a := mul_pos (by norm_num) ha
  have h12r : 0 < 12 * a := mul_pos (by norm_num) ha
  have h14r : 0 < 14 * a := mul_pos (by norm_num) ha
  have h16r : 0 < 16 * a := mul_pos (by norm_num) ha
  have h8 : IntegrableOn f8 (Ioi 0) :=
    (integrableOn_fiveShift_cubic_exp h8r).const_mul (1 / 5)
  have h10 : IntegrableOn f10 (Ioi 0) :=
    (integrableOn_fiveShift_cubic_exp h10r).const_mul (-(4 / 5))
  have h12 : IntegrableOn f12 (Ioi 0) :=
    (integrableOn_fiveShift_cubic_exp h12r).const_mul (6 / 5)
  have h14 : IntegrableOn f14 (Ioi 0) :=
    (integrableOn_fiveShift_cubic_exp h14r).const_mul (-(4 / 5))
  have h16 : IntegrableOn f16 (Ioi 0) :=
    (integrableOn_fiveShift_cubic_exp h16r).const_mul (1 / 5)
  have hpoint : (fun r : ℝ => r ^ 2 * fiveShiftEulerGammaLowerKernel r a) =
      ((((f8 + f10) + f12) + f14) + f16) := by
    funext r
    rw [fiveShiftEulerGammaLowerKernel_expand]
    change _ = f8 r + f10 r + f12 r + f14 r + f16 r
    ring
  rw [hpoint]
  change (∫ r : ℝ in Ioi 0, ((((f8 + f10) + f12) + f14) + f16) r) = _
  simp only [Pi.add_apply]
  have hsum16 := integral_add (((h8.add h10).add h12).add h14) h16
  have hsum14 := integral_add ((h8.add h10).add h12) h14
  have hsum12 := integral_add (h8.add h10) h12
  have hsum10 := integral_add h8 h10
  simp only [Pi.add_apply] at hsum16 hsum14 hsum12 hsum10
  rw [hsum16, hsum14, hsum12, hsum10]
  change
    (∫ r : ℝ in Ioi 0, (1 / 5) * (r ^ 2 * Real.exp (-((8 * a) * r)))) +
      (∫ r : ℝ in Ioi 0, -(4 / 5) * (r ^ 2 * Real.exp (-((10 * a) * r)))) +
      (∫ r : ℝ in Ioi 0, (6 / 5) * (r ^ 2 * Real.exp (-((12 * a) * r)))) +
      (∫ r : ℝ in Ioi 0, -(4 / 5) * (r ^ 2 * Real.exp (-((14 * a) * r)))) +
      (∫ r : ℝ in Ioi 0, (1 / 5) * (r ^ 2 * Real.exp (-((16 * a) * r)))) = _
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul]
  rw [integral_fiveShift_cubic_exp h8r,
    integral_fiveShift_cubic_exp h10r,
    integral_fiveShift_cubic_exp h12r,
    integral_fiveShift_cubic_exp h14r,
    integral_fiveShift_cubic_exp h16r]
  field_simp [ha.ne']
  ring

theorem fiveShiftEulerGammaFeature_nonneg_le_exp
    {r a : ℝ} (hr : 0 ≤ r) (ha0 : 0 < a) (ha : a ≤ 1 / 2) :
    0 ≤ fiveShiftEulerGammaFeature r a ∧
      fiveShiftEulerGammaFeature r a ≤ Real.exp (-2 * a * r) := by
  rw [fiveShiftEulerGammaFeature, fiveShiftEulerGammaPolynomial]
  let x := Real.exp (-2 * a * r)
  let t := Real.exp (-(6 / 5 : ℝ) * r)
  let q := Real.exp (-2 * r)
  let u := Real.exp (-(21 / 10 : ℝ) * r)
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x ≤ 1 := by
    rw [show x = Real.exp (-2 * a * r) by rfl, ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have har : 0 ≤ a * r := mul_nonneg ha0.le hr
    nlinarith
  have htx : t ≤ x := by
    rw [show t = Real.exp (-(6 / 5 : ℝ) * r) by rfl,
      show x = Real.exp (-2 * a * r) by rfl]
    apply Real.exp_le_exp.mpr
    have har := mul_le_mul_of_nonneg_right ha hr
    nlinarith
  have hqx : q ≤ x := by
    rw [show q = Real.exp (-2 * r) by rfl,
      show x = Real.exp (-2 * a * r) by rfl]
    apply Real.exp_le_exp.mpr
    have har := mul_le_mul_of_nonneg_right ha hr
    nlinarith
  have hux : u ≤ x := by
    rw [show u = Real.exp (-(21 / 10 : ℝ) * r) by rfl,
      show x = Real.exp (-2 * a * r) by rfl]
    apply Real.exp_le_exp.mpr
    have har := mul_le_mul_of_nonneg_right ha hr
    nlinarith
  have ht0 : 0 ≤ t := (Real.exp_pos _).le
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hu0 : 0 ≤ u := (Real.exp_pos _).le
  have hf0 : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hft0 : 0 ≤ x - t := sub_nonneg.mpr htx
  have hfq0 : 0 ≤ x - q := sub_nonneg.mpr hqx
  have hfu0 : 0 ≤ x - u := sub_nonneg.mpr hux
  have hf1 : 1 - x ≤ 1 := by linarith
  have hft1 : x - t ≤ 1 := by linarith
  have hfq1 : x - q ≤ 1 := by linarith
  have hfu1 : x - u ≤ 1 := by linarith
  constructor
  · positivity
  · calc
      x * (1 - x) * (x - t) * (x - q) * (x - u) ≤
          x * 1 * 1 * 1 * 1 := by
        gcongr
      _ = x := by ring

def fiveShiftEulerGammaCubicMoment (a : ℝ) : ℝ :=
  ∫ r : ℝ in Ioi 0, r ^ 2 * fiveShiftEulerGammaFeature r a

private theorem integrableOn_fiveShiftEulerGammaLowerKernel
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun r : ℝ => r ^ 2 * fiveShiftEulerGammaLowerKernel r a)
      (Ioi 0) := by
  have hvalue := integral_fiveShiftEulerGammaLowerKernel ha
  have hne : (∫ r : ℝ in Ioi 0,
      r ^ 2 * fiveShiftEulerGammaLowerKernel r a) ≠ 0 := by
    rw [hvalue]
    positivity
  exact Integrable.of_integral_ne_zero hne

private theorem integrableOn_fiveShiftEulerGammaCubicMoment
    {a : ℝ} (ha : 0 < a) (hhalf : a ≤ 1 / 2) :
    IntegrableOn (fun r : ℝ => r ^ 2 * fiveShiftEulerGammaFeature r a)
      (Ioi 0) := by
  have hrate : 0 < 2 * a := mul_pos (by norm_num) ha
  have hmajor := integrableOn_fiveShift_cubic_exp hrate
  apply hmajor.mono'
  · apply Continuous.aestronglyMeasurable
    unfold fiveShiftEulerGammaFeature fiveShiftEulerGammaPolynomial
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hb := fiveShiftEulerGammaFeature_nonneg_le_exp hr.le ha hhalf
    have hnon : 0 ≤ r ^ 2 * fiveShiftEulerGammaFeature r a :=
      mul_nonneg (sq_nonneg r) hb.1
    rw [Real.norm_eq_abs, abs_of_nonneg hnon]
    have hexp : Real.exp (-2 * a * r) = Real.exp (-((2 * a) * r)) := by
      congr 1
      ring
    rw [hexp] at hb
    exact mul_le_mul_of_nonneg_left hb.2 (sq_nonneg r)

theorem fiveShiftEulerGammaCubicMoment_ge_exact
    {a : ℝ} (ha : 0 < a) (hhalf : a ≤ 1 / 2) :
    334699 / (3951360000 * a ^ 3) ≤
      fiveShiftEulerGammaCubicMoment a := by
  have hlower := integrableOn_fiveShiftEulerGammaLowerKernel ha
  have hcurrent := integrableOn_fiveShiftEulerGammaCubicMoment ha hhalf
  rw [fiveShiftEulerGammaCubicMoment,
    ← integral_fiveShiftEulerGammaLowerKernel ha]
  apply MeasureTheory.integral_mono_ae hlower hcurrent
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact mul_le_mul_of_nonneg_left
    (fiveShiftEulerGammaLowerKernel_le hr.le ha hhalf) (sq_nonneg r)

theorem fiveShiftEulerGammaCubicMoment_ge
    {a : ℝ} (ha : 0 < a) (hhalf : a ≤ 1 / 2) :
    334699 / 493920000 ≤ fiveShiftEulerGammaCubicMoment a := by
  apply le_trans ?_ (fiveShiftEulerGammaCubicMoment_ge_exact ha hhalf)
  have hfactor :
      0 ≤ (1 / 2 - a) * ((1 / 2 : ℝ) ^ 2 + (1 / 2 : ℝ) * a + a ^ 2) := by
    apply mul_nonneg (sub_nonneg.mpr hhalf)
    nlinarith [sq_nonneg a]
  have hcube : a ^ 3 ≤ (1 / 2 : ℝ) ^ 3 := by
    nlinarith
  have hden : 0 < 3951360000 * a ^ 3 := by positivity
  apply (div_le_div_iff_of_pos_left (by norm_num) (by norm_num) hden).2
  norm_num at hcube ⊢
  nlinarith

/-- Multiplicity-exact finite zero-side charge of the five-shift cubic moment. -/
def finiteFiveShiftEulerGammaCubicCharge {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (m : ι → ℕ) : ℝ :=
  ∑ i ∈ s, (m i : ℝ) * fiveShiftEulerGammaCubicMoment (a i)

/-- Every strict-right multiplicity copy in the zeta strip receives a fixed rational quantum. -/
theorem finiteFiveShiftEulerGammaCubicCharge_ge {ι : Type*}
    (s : Finset ι) {a : ι → ℝ} (m : ι → ℕ)
    (ha0 : ∀ i ∈ s, 0 < a i) (ha : ∀ i ∈ s, a i ≤ 1 / 2) :
    (334699 / 493920000) * ∑ i ∈ s, (m i : ℝ) ≤
      finiteFiveShiftEulerGammaCubicCharge s a m := by
  rw [finiteFiveShiftEulerGammaCubicCharge, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    (334699 / 493920000) * (m i : ℝ) =
        (m i : ℝ) * (334699 / 493920000) := by ring
    _ ≤ (m i : ℝ) * fiveShiftEulerGammaCubicMoment (a i) :=
      mul_le_mul_of_nonneg_left
        (fiveShiftEulerGammaCubicMoment_ge (ha0 i hi) (ha i hi))
        (Nat.cast_nonneg _)

/-- Exact `75%` receiver for any arithmetic upper bound on the five-shift charge. -/
theorem three_quarters_line_of_fiveShiftEulerGammaCubicCharge
    {N N0 R E : ℝ} (hsplit : N = N0 + 2 * R)
    (hcharge : (334699 / 493920000) * R ≤ E)
    (hbudget : (493920000 / 334699) * E ≤ N / 8) :
    3 * N / 4 ≤ N0 := by
  nlinarith

end

end RHTower

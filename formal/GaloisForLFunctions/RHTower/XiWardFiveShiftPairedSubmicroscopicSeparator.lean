import GaloisForLFunctions.RHTower.XiWardFiveShiftEulerGammaQuantitative

/-!
# Functional-equation-paired submicroscopic separator

Symmetrizing the five-shift prime-gap feature across `a ↦ -a` removes one-sided
right-divisor selection.  The symmetric pair vanishes at the critical diagonal.  Away from it,
the forced singular normalization `a⁻²` cancels quadratic coalescence and leaves a uniform
source-scale-one charge of at least `1/81`, for every `0 < a ≤ 1/2`.

This is a multiplicity-exact zero-side receiver.  It does not assert the remaining explicit-formula
landing or its arithmetic upper budget.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

def fiveShiftEulerGammaPairedFeature (r a : ℝ) : ℝ :=
  -(fiveShiftEulerGammaFeature r a + fiveShiftEulerGammaFeature r (-a))

def fiveShiftEulerGammaPairedRenormalizedFeature (r a : ℝ) : ℝ :=
  a⁻¹ ^ (2 : ℕ) * fiveShiftEulerGammaPairedFeature r a

theorem fiveShiftEulerGammaPairedRenormalizedFeature_zero (r : ℝ) :
    fiveShiftEulerGammaPairedRenormalizedFeature r 0 = 0 := by
  simp [fiveShiftEulerGammaPairedRenormalizedFeature,
    fiveShiftEulerGammaPairedFeature, fiveShiftEulerGammaFeature_zero]

theorem fiveShiftEulerGammaPolynomial_reciprocal
    {q t u x : ℝ} (hx : x ≠ 0) :
    fiveShiftEulerGammaPolynomial q t u x⁻¹ =
      -(1 - x) * (1 - t * x) * (1 - q * x) * (1 - u * x) / x ^ (5 : ℕ) := by
  rw [fiveShiftEulerGammaPolynomial]
  field_simp [hx]
  ring

theorem fiveShiftEulerGammaPolynomial_neg_pair_lower
    {q t u x : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1)
    (ht0 : 0 ≤ t) (hq0 : 0 ≤ q) (hu0 : 0 ≤ u)
    (htx : t < x) (hqx : q < x) (hux : u < x) :
    (1 - x) ^ (2 : ℕ) * (x - q) * (x - u) ≤
      -(fiveShiftEulerGammaPolynomial q t u x +
        fiveShiftEulerGammaPolynomial q t u x⁻¹) := by
  let B := (x - t) * (x - q) * (x - u)
  let C := (1 - t * x) * (1 - q * x) * (1 - u * x)
  have hx0' : 0 ≤ x := hx0.le
  have hxm : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have ht1 : t ≤ 1 := htx.le.trans hx1
  have hq1 : q ≤ 1 := hqx.le.trans hx1
  have hu1 : u ≤ 1 := hux.le.trans hx1
  have htx0 : 0 ≤ x - t := sub_nonneg.mpr htx.le
  have hqx0 : 0 ≤ x - q := sub_nonneg.mpr hqx.le
  have hux0 : 0 ≤ x - u := sub_nonneg.mpr hux.le
  have htx1 : 0 ≤ 1 - t * x := by
    have hmul : t * x ≤ 1 * 1 := mul_le_mul ht1 hx1 hx0' zero_le_one
    nlinarith
  have hqx1 : 0 ≤ 1 - q * x := by
    have hmul : q * x ≤ 1 * 1 := mul_le_mul hq1 hx1 hx0' zero_le_one
    nlinarith
  have hux1 : 0 ≤ 1 - u * x := by
    have hmul : u * x ≤ 1 * 1 := mul_le_mul hu1 hx1 hx0' zero_le_one
    nlinarith
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hxpow0 : 0 < x ^ (5 : ℕ) := pow_pos hx0 _
  have hxpow1 : x ^ (5 : ℕ) ≤ 1 := pow_le_one₀ hx0' hx1
  have hCdiv : C ≤ C / x ^ (5 : ℕ) := by
    rw [le_div_iff₀ hxpow0]
    nlinarith [mul_le_mul_of_nonneg_left hxpow1 hC0]
  have hxB : x * B ≤ B := by
    nlinarith [mul_le_mul_of_nonneg_right hx1 hB0]
  have hqcomp : x - q ≤ 1 - q * x := by
    have hnon : 0 ≤ (1 + q) * (1 - x) :=
      mul_nonneg (by positivity) hxm
    nlinarith
  have hucomp : x - u ≤ 1 - u * x := by
    have hnon : 0 ≤ (1 + u) * (1 - x) :=
      mul_nonneg (by positivity) hxm
    nlinarith
  have hCmid : (1 - t * x) * (x - q) * (x - u) ≤ C := by
    dsimp [C]
    gcongr
  have hmid_sub :
      (1 + t) * (1 - x) * (x - q) * (x - u) ≤ C - B := by
    have heq :
        (1 - t * x) * (x - q) * (x - u) - B =
          (1 + t) * (1 - x) * (x - q) * (x - u) := by
      dsimp [B]
      ring
    linarith
  have hbase :
      (1 - x) * (x - q) * (x - u) ≤ C - B := by
    calc
      (1 - x) * (x - q) * (x - u) ≤
          (1 + t) * (1 - x) * (x - q) * (x - u) := by
        gcongr
        nlinarith [mul_nonneg ht0 hxm]
      _ ≤ C - B := hmid_sub
  have hbracket :
      (1 - x) * (x - q) * (x - u) ≤ C / x ^ (5 : ℕ) - x * B := by
    nlinarith
  rw [fiveShiftEulerGammaPolynomial_reciprocal hx0.ne']
  rw [fiveShiftEulerGammaPolynomial]
  have hpair :
      -(x * (1 - x) * (x - t) * (x - q) * (x - u) +
          (-(1 - x) * (1 - t * x) * (1 - q * x) * (1 - u * x) /
            x ^ (5 : ℕ))) =
        (1 - x) * (C / x ^ (5 : ℕ) - x * B) := by
    dsimp [B, C]
    ring
  rw [hpair]
  calc
    (1 - x) ^ (2 : ℕ) * (x - q) * (x - u) =
        (1 - x) * ((1 - x) * (x - q) * (x - u)) := by ring
    _ ≤ (1 - x) * (C / x ^ (5 : ℕ) - x * B) :=
      mul_le_mul_of_nonneg_left hbracket hxm

theorem fiveShiftEulerGammaPairedFeature_lower
    {r a : ℝ} (hr : 0 < r) (ha0 : 0 < a) (ha : a ≤ 1 / 2) :
    (1 - Real.exp (-2 * a * r)) ^ (2 : ℕ) *
        (Real.exp (-2 * a * r) - Real.exp (-2 * r)) *
        (Real.exp (-2 * a * r) - Real.exp (-(21 / 10 : ℝ) * r)) ≤
      fiveShiftEulerGammaPairedFeature r a := by
  have hx0 : 0 < Real.exp (-2 * a * r) := Real.exp_pos _
  have hx1 : Real.exp (-2 * a * r) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_pos ha0 hr]
  have ht0 : 0 ≤ Real.exp (-(6 / 5 : ℝ) * r) := (Real.exp_pos _).le
  have hq0 : 0 ≤ Real.exp (-2 * r) := (Real.exp_pos _).le
  have hu0 : 0 ≤ Real.exp (-(21 / 10 : ℝ) * r) := (Real.exp_pos _).le
  have htx : Real.exp (-(6 / 5 : ℝ) * r) < Real.exp (-2 * a * r) := by
    apply Real.exp_lt_exp.mpr
    have har := mul_le_mul_of_nonneg_right ha hr.le
    nlinarith
  have hqx : Real.exp (-2 * r) < Real.exp (-2 * a * r) := by
    apply Real.exp_lt_exp.mpr
    have har := mul_le_mul_of_nonneg_right ha hr.le
    nlinarith
  have hux : Real.exp (-(21 / 10 : ℝ) * r) < Real.exp (-2 * a * r) := by
    apply Real.exp_lt_exp.mpr
    have har := mul_le_mul_of_nonneg_right ha hr.le
    nlinarith
  have hbase := fiveShiftEulerGammaPolynomial_neg_pair_lower
    hx0 hx1 ht0 hq0 hu0 htx hqx hux
  rw [fiveShiftEulerGammaPairedFeature, fiveShiftEulerGammaFeature,
    fiveShiftEulerGammaFeature]
  have hinv : Real.exp (-2 * -a * r) = (Real.exp (-2 * a * r))⁻¹ := by
    rw [show -2 * -a * r = -(-2 * a * r) by ring, Real.exp_neg]
  rw [hinv]
  exact hbase

theorem mul_exp_neg_le_one_sub_exp_neg (y : ℝ) :
    y * Real.exp (-y) ≤ 1 - Real.exp (-y) := by
  have h := Real.add_one_le_exp y
  have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos (-y)).le
  rw [← Real.exp_add] at hmul
  have hzero : y + -y = 0 := by ring
  rw [hzero, Real.exp_zero] at hmul
  nlinarith

theorem fiveShiftEulerGammaPairedRenormalizedFeature_lower
    {r a : ℝ} (hr : 0 < r) (ha0 : 0 < a) (ha : a ≤ 1 / 2) :
    4 * r ^ (2 : ℕ) * Real.exp (-4 * r) * (1 - Real.exp (-r)) ^ (2 : ℕ) ≤
      fiveShiftEulerGammaPairedRenormalizedFeature r a := by
  let x := Real.exp (-2 * a * r)
  let e := Real.exp (-r)
  let q := Real.exp (-2 * r)
  let u := Real.exp (-(21 / 10 : ℝ) * r)
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x ≤ 1 := by
    dsimp [x]
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_pos ha0 hr]
  have he0 : 0 < e := Real.exp_pos _
  have he1 : e < 1 := by
    dsimp [e]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hqgap : x * (1 - e) ≤ x - q := by
    have hqe : q ≤ x * e := by
      dsimp [q, x, e]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have har := mul_le_mul_of_nonneg_right ha hr.le
      nlinarith
    nlinarith
  have hugap : x * (1 - e) ≤ x - u := by
    have hue : u ≤ x * e := by
      dsimp [u, x, e]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have har := mul_le_mul_of_nonneg_right ha hr.le
      nlinarith
    nlinarith
  have hpair := fiveShiftEulerGammaPairedFeature_lower hr ha0 ha
  change (1 - x) ^ (2 : ℕ) * (x - q) * (x - u) ≤
    fiveShiftEulerGammaPairedFeature r a at hpair
  have hgap0 : 0 ≤ x * (1 - e) :=
    mul_nonneg hx0.le (sub_nonneg.mpr he1.le)
  have hqgap0 : 0 ≤ x - q := hgap0.trans hqgap
  have hugap0 : 0 ≤ x - u := hgap0.trans hugap
  have hpair' :
      (1 - x) ^ (2 : ℕ) * (x * (1 - e)) * (x * (1 - e)) ≤
        fiveShiftEulerGammaPairedFeature r a := by
    apply le_trans ?_ hpair
    gcongr
  have hexplower := mul_exp_neg_le_one_sub_exp_neg (2 * a * r)
  have hxeq : Real.exp (-(2 * a * r)) = x := by
    dsimp [x]
    congr 1
    ring
  rw [hxeq] at hexplower
  have hlin : 2 * a * r * x ≤ 1 - x := by
    convert hexplower using 1
  have hlin0 : 0 ≤ 2 * a * r * x := by positivity
  have hsq : (2 * a * r * x) ^ (2 : ℕ) ≤ (1 - x) ^ (2 : ℕ) :=
    (sq_le_sq₀ hlin0 (sub_nonneg.mpr hx1)).2 hlin
  have hraw :
      4 * a ^ (2 : ℕ) * r ^ (2 : ℕ) * Real.exp (-8 * a * r) * (1 - e) ^ (2 : ℕ) ≤
        fiveShiftEulerGammaPairedFeature r a := by
    apply le_trans ?_ hpair'
    have hxpow : x ^ (4 : ℕ) = Real.exp (-8 * a * r) := by
      dsimp [x]
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
      ring
    rw [← hxpow]
    nlinarith [mul_le_mul_of_nonneg_right hsq
      (mul_nonneg (sq_nonneg x) (sq_nonneg (1 - e)))]
  have hnorm :
      4 * r ^ (2 : ℕ) * Real.exp (-8 * a * r) * (1 - e) ^ (2 : ℕ) ≤
        fiveShiftEulerGammaPairedRenormalizedFeature r a := by
    rw [fiveShiftEulerGammaPairedRenormalizedFeature]
    calc
      4 * r ^ (2 : ℕ) * Real.exp (-8 * a * r) * (1 - e) ^ (2 : ℕ) =
          a⁻¹ ^ (2 : ℕ) *
            (4 * a ^ (2 : ℕ) * r ^ (2 : ℕ) * Real.exp (-8 * a * r) * (1 - e) ^ (2 : ℕ)) := by
              field_simp [ha0.ne']
      _ ≤ a⁻¹ ^ (2 : ℕ) * fiveShiftEulerGammaPairedFeature r a :=
        mul_le_mul_of_nonneg_left hraw (sq_nonneg _)
  have hexp : Real.exp (-4 * r) ≤ Real.exp (-8 * a * r) := by
    apply Real.exp_le_exp.mpr
    have har := mul_le_mul_of_nonneg_right ha hr.le
    nlinarith
  calc
    4 * r ^ (2 : ℕ) * Real.exp (-4 * r) * (1 - Real.exp (-r)) ^ (2 : ℕ) ≤
        4 * r ^ (2 : ℕ) * Real.exp (-8 * a * r) * (1 - e) ^ (2 : ℕ) := by
      dsimp [e]
      gcongr
    _ ≤ fiveShiftEulerGammaPairedRenormalizedFeature r a := hnorm

theorem fiveShiftEulerGammaPairedRenormalizedFeature_one_ge
    {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2) :
    1 / 81 ≤ fiveShiftEulerGammaPairedRenormalizedFeature 1 a := by
  have hbase := fiveShiftEulerGammaPairedRenormalizedFeature_lower
    (r := 1) (by norm_num) ha0 ha
  norm_num only [one_pow, mul_one] at hbase
  have hexp4 : Real.exp 4 < 81 := by
    have hpow : Real.exp 4 = Real.exp 1 ^ (4 : ℕ) := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    rw [hpow, show (81 : ℝ) = 3 ^ (4 : ℕ) by norm_num]
    gcongr
    exact Real.exp_one_lt_three
  have hexpneg4 : (1 / 81 : ℝ) < Real.exp (-4) := by
    rw [Real.exp_neg]
    simpa [one_div] using
      (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 81) (Real.exp_pos 4)).2 hexp4
  have hexpneg1 : Real.exp (-1) < (1 / 2 : ℝ) := by
    rw [Real.exp_neg]
    simpa [one_div] using
      (inv_lt_inv₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2)).2
        Real.exp_one_gt_two
  have hgap : (1 / 2 : ℝ) < 1 - Real.exp (-1) := by linarith
  have hgapsq : (1 / 4 : ℝ) ≤ (1 - Real.exp (-1)) ^ (2 : ℕ) := by nlinarith
  calc
    (1 / 81 : ℝ) = 4 * (1 / 81 : ℝ) * (1 / 4 : ℝ) := by norm_num
    _ ≤ 4 * Real.exp (-4) * (1 - Real.exp (-1)) ^ (2 : ℕ) := by gcongr
    _ ≤ fiveShiftEulerGammaPairedRenormalizedFeature 1 a := by
      simpa using hbase

/-- Finite multiplicity-exact functional-equation-paired charge at source scale one. -/
def finiteFiveShiftEulerGammaPairedCharge {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (m : ι → ℕ) : ℝ :=
  ∑ i ∈ s, (m i : ℝ) *
    fiveShiftEulerGammaPairedRenormalizedFeature 1 (a i)

theorem finiteFiveShiftEulerGammaPairedCharge_ge {ι : Type*}
    (s : Finset ι) {a : ι → ℝ} (m : ι → ℕ)
    (ha0 : ∀ i ∈ s, 0 < a i) (ha : ∀ i ∈ s, a i ≤ 1 / 2) :
    (1 / 81) * ∑ i ∈ s, (m i : ℝ) ≤
      finiteFiveShiftEulerGammaPairedCharge s a m := by
  rw [finiteFiveShiftEulerGammaPairedCharge, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    (1 / 81) * (m i : ℝ) = (m i : ℝ) * (1 / 81) := by ring
    _ ≤ (m i : ℝ) *
        fiveShiftEulerGammaPairedRenormalizedFeature 1 (a i) :=
      mul_le_mul_of_nonneg_left
        (fiveShiftEulerGammaPairedRenormalizedFeature_one_ge
          (ha0 i hi) (ha i hi)) (Nat.cast_nonneg _)

theorem three_quarters_line_of_fiveShiftEulerGammaPairedCharge
    {N N0 R E : ℝ} (hsplit : N = N0 + 2 * R)
    (hcharge : (1 / 81) * R ≤ E)
    (hbudget : 81 * E ≤ N / 8) :
    3 * N / 4 ≤ N0 := by
  nlinarith

end

end RHTower

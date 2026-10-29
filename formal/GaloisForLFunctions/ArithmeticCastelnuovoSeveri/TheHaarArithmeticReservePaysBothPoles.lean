import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHaarPrimeDefectHasAUniformMassFloor
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.EveryHaarCellHasPositiveWeilEnergy

/-!
# Both original Haar poles are paid by the arithmetic reserve

Centering a weight at the shared boundary of a balanced pair retains its
exact first distance moment. The resulting half-exponential estimates are
summable in Haar mass. Their full signed pole product is smaller than the
uniform divisor-square reserve, including every low arithmetic index.
-/

noncomputable section
open MeasureTheory Set Finset
open RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry

private theorem rawCell_distance_integrals {n : ℕ} (hn : 1 ≤ n) :
    (∫ x, rawCell n x * (Real.log ((n + 1 : ℕ) : ℝ) - x)) = logCellWidth n ^ 2 / 2 ∧
    (∫ x, rawCell n x * (x - Real.log (n : ℝ))) = logCellWidth n ^ 2 / 2 := by
  have hlo : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) (by push_cast; linarith)
  have hind (f : ℝ → ℝ) : (fun x => rawCell n x * f x) =
      (Ico (Real.log (n : ℝ)) (Real.log ((n + 1 : ℕ) : ℝ))).indicator f := by
    funext x
    unfold rawCell
    simp only [indicator_apply]
    split_ifs <;> simp only [one_mul, zero_mul]
  constructor
  · rw [hind, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hlo,
      intervalIntegral.integral_sub (f := fun _ : ℝ => Real.log ((n + 1 : ℕ) : ℝ))
        (g := fun x : ℝ => x) (continuous_const.intervalIntegrable _ _)
        (continuous_id.intervalIntegrable _ _), intervalIntegral.integral_const, integral_id]
    simp only [smul_eq_mul, logCellWidth, Nat.cast_add, Nat.cast_one]
    ring
  · rw [hind, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hlo,
      intervalIntegral.integral_sub (f := fun x : ℝ => x)
        (g := fun _ : ℝ => Real.log (n : ℝ)) (continuous_id.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const, integral_id]
    simp only [smul_eq_mul, logCellWidth, Nat.cast_add, Nat.cast_one]
    ring

/-- The exact first absolute moment about the shared boundary retains half the pair width. -/
theorem integral_haarProfile_distance {a : ℕ} (ha : 1 ≤ a) :
    (∫ x, |haarProfile a x * (x - Real.log ((2 * a + 1 : ℕ) : ℝ))|) =
      haarMass a * logCellWidth a / 2 := by
  have hn := haarCoeff_nonneg ha
  have he (x : ℝ) : |haarProfile a x * (x - Real.log ((2 * a + 1 : ℕ) : ℝ))| =
      haarLeftCoeff a * (rawCell (2 * a) x * (Real.log ((2 * a + 1 : ℕ) : ℝ) - x)) +
      haarRightCoeff a * (rawCell (2 * a + 1) x * (x - Real.log ((2 * a + 1 : ℕ) : ℝ))) := by
    unfold haarProfile rawCell
    simp only [indicator_apply]
    split_ifs with hl hr hr
    · exact False.elim ((not_lt_of_ge hr.1) hl.2)
    · simp only [mul_one, mul_zero, sub_zero, zero_mul, add_zero, abs_mul,
        abs_of_nonneg hn.1, abs_of_nonpos (sub_nonpos.mpr hl.2.le)]
      ring
    · simp only [mul_one, mul_zero, zero_sub, zero_mul, zero_add, abs_mul,
        abs_neg, abs_of_nonneg hn.2, abs_of_nonneg (sub_nonneg.mpr hr.1), one_mul]
    · simp only [mul_zero, sub_zero, zero_mul, abs_zero, add_zero]
  have hl : Integrable (fun x => rawCell (2 * a) x *
      (Real.log ((2 * a + 1 : ℕ) : ℝ) - x)) :=
    integrable_compact_bv_mul (rawCell_bv _) (rawCell_compact _) (by fun_prop)
  have hr : Integrable (fun x => rawCell (2 * a + 1) x *
      (x - Real.log ((2 * a + 1 : ℕ) : ℝ))) :=
    integrable_compact_bv_mul (rawCell_bv _) (rawCell_compact _) (by fun_prop)
  simp_rw [he]
  rw [integral_add (hl.const_mul _) (hr.const_mul _), integral_const_mul,
    integral_const_mul,
    (rawCell_distance_integrals (show 1 ≤ 2 * a by omega)).1,
    (rawCell_distance_integrals (show 1 ≤ 2 * a + 1 by omega)).2,
    ← logCellWidth_pair_sum ha]
  have hlm := (haarCoeff_mass a).1
  have hrm := (haarCoeff_mass a).2
  nlinarith only [congrArg (fun t => t * logCellWidth (2 * a)) hlm,
    congrArg (fun t => t * logCellWidth (2 * a + 1)) hrm]

/-- Centering at the seam turns a Lipschitz estimate into an exact distance-moment bound. -/
theorem abs_haarProfile_moment_le_slope {a : ℕ} (ha : 1 ≤ a) {w : ℝ → ℝ}
    (hw : Continuous w) (L : ℝ)
    (hb : ∀ x ∈ Ico (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ)),
      |w x - w (Real.log ((2 * a + 1 : ℕ) : ℝ))| ≤
        L * |x - Real.log ((2 * a + 1 : ℕ) : ℝ)|) :
    |∫ x, haarProfile a x * w x| ≤ L * (haarMass a * logCellWidth a / 2) := by
  let c := Real.log ((2 * a + 1 : ℕ) : ℝ)
  have hi := integrable_compact_bv_mul (haarProfile_bv a) (haarProfile_compact a) hw
  have hq := (integrable_haarProfile a).mul_const (w c)
  have he : (∫ x, haarProfile a x * w x) = ∫ x, haarProfile a x * (w x - w c) := by
    simp_rw [mul_sub]
    rw [integral_sub hi hq, integral_mul_const, integral_haarProfile ha, zero_mul, sub_zero]
  have hd : Integrable (fun x => haarProfile a x * (w x - w c)) :=
    integrable_compact_bv_mul (haarProfile_bv a) (haarProfile_compact a) (hw.sub continuous_const)
  have hx : Integrable (fun x => haarProfile a x * (x - c)) :=
    integrable_compact_bv_mul (haarProfile_bv a) (haarProfile_compact a) (by fun_prop)
  have hb' (x : ℝ) : |haarProfile a x * (w x - w c)| ≤ L * |haarProfile a x * (x - c)| := by
    by_cases hmem : x ∈ Ico (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))
    · rw [abs_mul, abs_mul]
      simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left (hb x hmem) (abs_nonneg (haarProfile a x))
    · rw [haarProfile_zero_outside_pair ha hmem, zero_mul, zero_mul, abs_zero, mul_zero]
  calc
    _ = |∫ x, haarProfile a x * (w x - w c)| := congrArg abs he
    _ ≤ ∫ x, |haarProfile a x * (w x - w c)| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => haarProfile a x * (w x - w c))
    _ ≤ ∫ x, L * |haarProfile a x * (x - c)| := integral_mono hd.abs (hx.abs.const_mul L) hb'
    _ = _ := by rw [integral_const_mul, integral_haarProfile_distance ha]

private theorem exp_sub_le_slope (u v : ℝ) :
    Real.exp v - Real.exp u ≤ Real.exp v * (v - u) := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (u - v)) (Real.exp_pos v).le
  rw [← Real.exp_add] at h
  have he : v + (u - v) = u := by ring
  rw [he] at h
  linarith only [h]

private theorem abs_exp_sub_le_slope {u v R : ℝ} (hu : u ≤ R) (hv : v ≤ R) :
    |Real.exp u - Real.exp v| ≤ Real.exp R * |u - v| := by
  rcases le_total u v with huv | hvu
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr huv)), neg_sub,
      abs_of_nonpos (sub_nonpos.mpr huv), neg_sub]
    exact (exp_sub_le_slope u v).trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr hv) (sub_nonneg.mpr huv))
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hvu)),
      abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact (exp_sub_le_slope v u).trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr hu) (sub_nonneg.mpr hvu))

private def expandingMomentBudget (a : ℕ) : ℝ :=
  haarMass a * logCellWidth a ^ 2 * ((2 * a + 2 : ℕ) : ℝ) / 16

private def contractingMomentBudget (a : ℕ) : ℝ :=
  haarMass a * logCellWidth a ^ 2 / (16 * ((2 * a : ℕ) : ℝ))

private theorem expanding_moment_sq {a : ℕ} (ha : 1 ≤ a) :
    (∫ x, haarProfile a x * Real.exp (x / 2)) ^ 2 ≤ haarMass a * expandingMomentBudget a := by
  have hN : (0 : ℝ) < ((2 * a + 2 : ℕ) : ℝ) := by positivity
  have hc : Real.log ((2 * a + 1 : ℕ) : ℝ) ≤ Real.log ((2 * a + 2 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show 2 * a + 1 ≤ 2 * a + 2 by omega))
  have hexp : Real.exp (Real.log ((2 * a + 2 : ℕ) : ℝ) / 2) =
      Real.sqrt ((2 * a + 2 : ℕ) : ℝ) := by rw [Real.exp_half, Real.exp_log hN]
  have hb := abs_haarProfile_moment_le_slope ha (show Continuous (fun x : ℝ => Real.exp (x / 2)) by fun_prop)
    (Real.sqrt ((2 * a + 2 : ℕ) : ℝ) / 2) (by
      intro x hx
      have h := abs_exp_sub_le_slope (u := x / 2)
        (v := Real.log ((2 * a + 1 : ℕ) : ℝ) / 2)
        (R := Real.log ((2 * a + 2 : ℕ) : ℝ) / 2)
        (by linarith only [hx.2]) (by linarith only [hc])
      rw [show x / 2 - Real.log ((2 * a + 1 : ℕ) : ℝ) / 2 =
          (x - Real.log ((2 * a + 1 : ℕ) : ℝ)) / 2 by ring,
        abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), hexp] at h
      convert h using 1
      ring)
  have hs := sq_le_sq' (abs_le.mp hb).1 (abs_le.mp hb).2
  calc
    _ ≤ (Real.sqrt ((2 * a + 2 : ℕ) : ℝ) / 2 * (haarMass a * logCellWidth a / 2)) ^ 2 := hs
    _ = _ := by
      rw [mul_pow, div_pow, Real.sq_sqrt hN.le]
      unfold expandingMomentBudget
      ring

private theorem contracting_moment_sq {a : ℕ} (ha : 1 ≤ a) :
    (∫ x, haarProfile a x * Real.exp (-x / 2)) ^ 2 ≤ haarMass a * contractingMomentBudget a := by
  have hN : (0 : ℝ) < ((2 * a : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 * a by omega)
  have hc : Real.log ((2 * a : ℕ) : ℝ) ≤ Real.log ((2 * a + 1 : ℕ) : ℝ) :=
    Real.log_le_log hN (by exact_mod_cast (show 2 * a ≤ 2 * a + 1 by omega))
  have hexp : Real.exp (-Real.log ((2 * a : ℕ) : ℝ) / 2) =
      (Real.sqrt ((2 * a : ℕ) : ℝ))⁻¹ := by
    rw [neg_div, Real.exp_neg, Real.exp_half, Real.exp_log hN]
  have hb := abs_haarProfile_moment_le_slope ha (show Continuous (fun x : ℝ => Real.exp (-x / 2)) by fun_prop)
    (1 / (2 * Real.sqrt ((2 * a : ℕ) : ℝ))) (by
      intro x hx
      have h := abs_exp_sub_le_slope (u := -x / 2)
        (v := -Real.log ((2 * a + 1 : ℕ) : ℝ) / 2)
        (R := -Real.log ((2 * a : ℕ) : ℝ) / 2)
        (by linarith only [hx.1]) (by linarith only [hc])
      rw [show -x / 2 - -Real.log ((2 * a + 1 : ℕ) : ℝ) / 2 =
          -(x - Real.log ((2 * a + 1 : ℕ) : ℝ)) / 2 by ring,
        abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        hexp] at h
      convert h using 1
      ring)
  have hs := sq_le_sq' (abs_le.mp hb).1 (abs_le.mp hb).2
  calc
    _ ≤ (1 / (2 * Real.sqrt ((2 * a : ℕ) : ℝ)) * (haarMass a * logCellWidth a / 2)) ^ 2 := hs
    _ = _ := by
      rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hN.le]
      unfold contractingMomentBudget
      ring

private theorem haarMass_le_quarter_inverse {a : ℕ} (ha : 1 ≤ a) :
    haarMass a ≤ 1 / (4 * (a : ℝ)) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have h := (four_haarMass_le_width ha).trans (logCellWidth_le_inv ha)
  rw [le_div_iff₀ ha0] at h
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (a : ℝ))]
  nlinarith only [h]

private theorem first_moment_budgets :
    expandingMomentBudget 1 ≤ 343 / 16000 ∧ contractingMomentBudget 1 ≤ 343 / 128000 := by
  have hw : logCellWidth 1 ≤ 7 / 10 := by
    norm_num only [logCellWidth, Nat.cast_one, Real.log_one, sub_zero]
    linarith only [Real.log_two_lt_d9]
  have hw0 := (logCellWidth_pos (show 1 ≤ 1 by omega)).le
  have hM := four_haarMass_le_width (show 1 ≤ 1 by omega)
  have hM7 : haarMass 1 ≤ 7 / 40 := by linarith only [hM, hw]
  have hw2 : logCellWidth 1 ^ 2 ≤ 49 / 100 := by nlinarith only [hw0, hw]
  have hprod := mul_le_mul hM7 hw2 (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 7 / 40)
  constructor
  · dsimp only [expandingMomentBudget]
    norm_num only [Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat]
    nlinarith only [hprod]
  · dsimp only [contractingMomentBudget]
    norm_num only [Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat]
    nlinarith only [hprod]

private theorem moment_budgets_tail {a : ℕ} (ha : 2 ≤ a) :
    expandingMomentBudget a ≤ 3 / (64 * (a : ℝ) ^ 2) ∧
      contractingMomentBudget a ≤ 1 / (512 * (a : ℝ) ^ 2) := by
  have ha1 : 1 ≤ a := by omega
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hw0 := (logCellWidth_pos ha1).le
  have hw := logCellWidth_le_inv ha1
  have hM := haarMass_le_quarter_inverse ha1
  have hw2 : logCellWidth a ^ 2 ≤ (1 / (a : ℝ)) ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self hw0 hw
  have hprod : haarMass a * logCellWidth a ^ 2 ≤ 1 / (4 * (a : ℝ) ^ 3) := by
    have h := mul_le_mul hM hw2 (sq_nonneg _) (by positivity : 0 ≤ 1 / (4 * (a : ℝ)))
    calc
      _ ≤ (1 / (4 * (a : ℝ))) * (1 / (a : ℝ)) ^ 2 := h
      _ = _ := by field_simp [ha0.ne']
  constructor
  · unfold expandingMomentBudget
    have h := mul_le_mul_of_nonneg_right hprod
      (div_nonneg (Nat.cast_nonneg (2 * a + 2)) (by norm_num : (0 : ℝ) ≤ 16))
    calc
      _ ≤ (1 / (4 * (a : ℝ) ^ 3)) * (((2 * a + 2 : ℕ) : ℝ) / 16) := by
        simpa only [mul_div_assoc] using h
      _ ≤ 3 / (64 * (a : ℝ) ^ 2) := by
        have he : (1 / (4 * (a : ℝ) ^ 3)) * (((2 * a + 2 : ℕ) : ℝ) / 16) =
            ((a : ℝ) + 1) / (32 * (a : ℝ) ^ 3) := by push_cast; ring
        rw [he]
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith only [mul_nonneg (sq_nonneg (a : ℝ)) (sub_nonneg.mpr haR)]
  · unfold contractingMomentBudget
    have h := div_le_div_of_nonneg_right hprod
      (show 0 ≤ 16 * ((2 * a : ℕ) : ℝ) by positivity)
    calc
      _ ≤ (1 / (4 * (a : ℝ) ^ 3)) / (16 * ((2 * a : ℕ) : ℝ)) := h
      _ ≤ 1 / (512 * (a : ℝ) ^ 2) := by
        have he : (1 / (4 * (a : ℝ) ^ 3)) / (16 * ((2 * a : ℕ) : ℝ)) =
            1 / (128 * (a : ℝ) ^ 4) := by push_cast; ring
        rw [he]
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        have hsq : 4 ≤ (a : ℝ) ^ 2 := by nlinarith only [haR]
        nlinarith only [mul_nonneg (sq_nonneg (a : ℝ)) (sub_nonneg.mpr hsq)]

private theorem moment_budgets_pronic {a : ℕ} (ha : 1 ≤ a) :
    expandingMomentBudget a ≤ (1 / 12 : ℝ) / ((a : ℝ) * ((a : ℝ) + 1)) ∧
    contractingMomentBudget a ≤ (1 / 144 : ℝ) / ((a : ℝ) * ((a : ℝ) + 1)) := by
  by_cases ha1 : a = 1
  · subst a
    norm_num only [Nat.cast_one]
    constructor <;> linarith only [first_moment_budgets.1, first_moment_budgets.2]
  have ha2 : 2 ≤ a := by omega
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha2
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have ht := moment_budgets_tail ha2
  constructor
  · refine ht.1.trans ?_
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [mul_nonneg ha0.le (sub_nonneg.mpr haR)]
  · refine ht.2.trans ?_
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [mul_nonneg ha0.le (sub_nonneg.mpr haR)]

private theorem pronic_mass_sum_le_one (X : ℕ) :
    (∑ a ∈ Finset.Icc 1 X, 1 / ((a : ℝ) * ((a : ℝ) + 1))) ≤ 1 := by
  by_cases hX : X = 0
  · subst X
    simp
  have hX1 : 1 ≤ X := by omega
  calc
    _ = ∑ a ∈ Finset.Icc 1 X, (-(1 / ((a + 1 : ℕ) : ℝ)) - -(1 / (a : ℝ))) := by
      apply sum_congr rfl
      intro a ha
      have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by have := (Finset.mem_Icc.mp ha).1; omega)
      push_cast
      field_simp [ha0.ne']
      ring
    _ = -(1 / ((X + 1 : ℕ) : ℝ)) - -(1 / ((1 : ℕ) : ℝ)) :=
      Finset.sum_Icc_sub hX1 (fun a : ℕ => -(1 / (a : ℝ)))
    _ ≤ 1 := by
      have hn : (0 : ℝ) ≤ 1 / ((X + 1 : ℕ) : ℝ) := by positivity
      norm_num only [Nat.cast_one, div_one, sub_neg_eq_add]
      linarith only [hn]

private theorem section_moment_sq_le_pronic (d : ℕ → ℝ) (X : ℕ) {w : ℝ → ℝ}
    (hw : Continuous w) {K : ℝ} (hK : 0 ≤ K)
    (hp : ∀ a, 1 ≤ a → (∫ x, haarProfile a x * w x) ^ 2 ≤
      haarMass a * (K / ((a : ℝ) * ((a : ℝ) + 1)))) :
    (∫ x, haarSectionProfile d X x * w x) ^ 2 ≤
      K * ∑ a ∈ Finset.Icc 1 X, haarMass a * d a ^ 2 := by
  let P : ℕ → ℝ := fun a => ∫ x, haarProfile a x * w x
  have hi (a : ℕ) : Integrable (fun x => haarProfile a x * w x) :=
    integrable_compact_bv_mul (haarProfile_bv a) (haarProfile_compact a) hw
  have he : (∫ x, haarSectionProfile d X x * w x) = ∑ a ∈ Finset.Icc 1 X, d a * P a := by
    unfold haarSectionProfile
    simp_rw [sum_mul, mul_assoc]
    rw [integral_finsetSum _ fun a _ => (hi a).const_mul (d a)]
    simp only [integral_const_mul, P]
  rw [he]
  have hprod (a : ℕ) (ha : a ∈ Finset.Icc 1 X) :
      (Real.sqrt (haarMass a) * d a) * (P a / Real.sqrt (haarMass a)) = d a * P a := by
    have hs := (Real.sqrt_pos.mpr (haarMass_pos (Finset.mem_Icc.mp ha).1)).ne'
    field_simp [hs]
  have hsq (a : ℕ) (ha : a ∈ Finset.Icc 1 X) :
      (Real.sqrt (haarMass a) * d a) ^ 2 = haarMass a * d a ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (haarMass_pos (Finset.mem_Icc.mp ha).1).le]
  have hnorm (a : ℕ) (ha : a ∈ Finset.Icc 1 X) :
      (P a / Real.sqrt (haarMass a)) ^ 2 ≤ K / ((a : ℝ) * ((a : ℝ) + 1)) := by
    have hM := haarMass_pos (Finset.mem_Icc.mp ha).1
    rw [div_pow, Real.sq_sqrt hM.le, div_le_iff₀ hM]
    simpa only [P, mul_comm] using hp a (Finset.mem_Icc.mp ha).1
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 X)
    (fun a => Real.sqrt (haarMass a) * d a) (fun a => P a / Real.sqrt (haarMass a))
  rw [sum_congr rfl hprod, sum_congr rfl hsq] at hcs
  have hb : (∑ a ∈ Finset.Icc 1 X, (P a / Real.sqrt (haarMass a)) ^ 2) ≤ K := by
    calc
      _ ≤ ∑ a ∈ Finset.Icc 1 X, K / ((a : ℝ) * ((a : ℝ) + 1)) := sum_le_sum hnorm
      _ = K * ∑ a ∈ Finset.Icc 1 X, 1 / ((a : ℝ) * ((a : ℝ) + 1)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro a _
        ring
      _ ≤ K := by simpa only [mul_one] using mul_le_mul_of_nonneg_left (pronic_mass_sum_le_one X) hK
  have hm : 0 ≤ ∑ a ∈ Finset.Icc 1 X, haarMass a * d a ^ 2 :=
    sum_nonneg fun a ha => mul_nonneg (haarMass_pos (Finset.mem_Icc.mp ha).1).le (sq_nonneg _)
  exact hcs.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb hm)

/-- All signed expanding pole moments share a fixed fraction of exact Haar mass. -/
theorem haarSectionProfile_exp_pos_sq_le_twelfth (d : ℕ → ℝ) (X : ℕ) :
    (∫ x, haarSectionProfile d X x * Real.exp (x / 2)) ^ 2 ≤
      (1 / 12 : ℝ) * ∑ a ∈ Finset.Icc 1 X, haarMass a * d a ^ 2 :=
  section_moment_sq_le_pronic d X (by fun_prop) (by norm_num) fun _ ha =>
    (expanding_moment_sq ha).trans
      (mul_le_mul_of_nonneg_left (moment_budgets_pronic ha).1 (haarMass_pos ha).le)

/-- The contracting moment has a separate summable bound on the same signed section. -/
theorem haarSectionProfile_exp_neg_sq_le_oneHundredFortyFourth (d : ℕ → ℝ) (X : ℕ) :
    (∫ x, haarSectionProfile d X x * Real.exp (-x / 2)) ^ 2 ≤
      (1 / 144 : ℝ) * ∑ a ∈ Finset.Icc 1 X, haarMass a * d a ^ 2 :=
  section_moment_sq_le_pronic d X (by fun_prop) (by norm_num) fun _ ha =>
    (contracting_moment_sq ha).trans
      (mul_le_mul_of_nonneg_left (moment_budgets_pronic ha).2 (haarMass_pos ha).le)

/-- The two distance-moment bounds pay the original signed pole product jointly. -/
theorem haarSectionProfile_pole_ge_distance_budget (d : ℕ → ℝ) (X : ℕ) :
    -(7 / 144 : ℝ) * (∑ a ∈ Finset.Icc 1 X, haarMass a * d a ^ 2) ≤
      2 * coshHalfMoment (haarSectionProfile d X) ^ 2 -
        2 * sinhHalfMoment (haarSectionProfile d X) ^ 2 := by
  have hp : Integrable (fun x => Real.exp (x / 2) * haarSectionProfile d X x) := by
    simpa only [mul_comm] using integrable_compact_bv_mul (haarSectionProfile_bv d X)
      (haarSectionProfile_compact d X) (show Continuous (fun x : ℝ => Real.exp (x / 2)) by fun_prop)
  have hm : Integrable (fun x => Real.exp (-(x / 2)) * haarSectionProfile d X x) := by
    simpa only [mul_comm] using integrable_compact_bv_mul (haarSectionProfile_bv d X)
      (haarSectionProfile_compact d X) (show Continuous (fun x : ℝ => Real.exp (-(x / 2))) by fun_prop)
  have hps : (∫ x, Real.exp (x / 2) * haarSectionProfile d X x) ^ 2 ≤
      (1 / 12 : ℝ) * ∑ a ∈ Finset.Icc 1 X, haarMass a * d a ^ 2 := by
    simpa only [mul_comm] using haarSectionProfile_exp_pos_sq_le_twelfth d X
  have hms : (∫ x, Real.exp (-(x / 2)) * haarSectionProfile d X x) ^ 2 ≤
      (1 / 144 : ℝ) * ∑ a ∈ Finset.Icc 1 X, haarMass a * d a ^ 2 := by
    simpa only [neg_div, mul_comm] using haarSectionProfile_exp_neg_sq_le_oneHundredFortyFourth d X
  rw [(halfMoments_eq_exp hp hm).1, (halfMoments_eq_exp hp hm).2]
  nlinarith only [hps, hms,
    sq_nonneg ((∫ x, Real.exp (x / 2) * haarSectionProfile d X x) / 2 +
      2 * ∫ x, Real.exp (-(x / 2)) * haarSectionProfile d X x)]

private theorem defect_ge_eighteenth_mass (d : ℕ → ℝ) (X : ℕ) :
    (1 / 18 : ℝ) * (∑ a ∈ Finset.Icc 1 X, haarMass a * d a ^ 2) ≤
      haarPrimeLogDefect d X := by
  have hmass : 0 ≤ ∑ a ∈ Finset.Icc 1 X, haarMass a * d a ^ 2 :=
    sum_nonneg fun a ha => mul_nonneg (haarMass_pos (Finset.mem_Icc.mp ha).1).le (sq_nonneg _)
  have hlog : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hfloor := haarPrimeLogDefect_ge_mass d X
  nlinarith only [hfloor, mul_nonneg hmass (sub_nonneg.mpr hlog)]

/-- Both original poles leave a positive share of the entire arithmetic square form. -/
theorem haarPrimeLogDefect_add_pole_ge_eighth_defect (d : ℕ → ℝ) (X : ℕ) :
    (1 / 8 : ℝ) * haarPrimeLogDefect d X ≤
      haarPrimeLogDefect d X + 2 * coshHalfMoment (haarSectionProfile d X) ^ 2 -
        2 * sinhHalfMoment (haarSectionProfile d X) ^ 2 := by
  linarith only [defect_ge_eighteenth_mass d X, haarSectionProfile_pole_ge_distance_budget d X]

/-- Both original pole moments fit inside the divisor-square reserve, at every index. -/
theorem haarPrimeLogDefect_add_pole_ge_mass (d : ℕ → ℝ) (X : ℕ) :
    (1 / 144 : ℝ) * (∑ a ∈ Finset.Icc 1 X, haarMass a * d a ^ 2) ≤
      haarPrimeLogDefect d X + 2 * coshHalfMoment (haarSectionProfile d X) ^ 2 -
        2 * sinhHalfMoment (haarSectionProfile d X) ^ 2 := by
  linarith only [defect_ge_eighteenth_mass d X, haarPrimeLogDefect_add_pole_ge_eighth_defect d X]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells

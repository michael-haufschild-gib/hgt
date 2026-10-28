import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellProfiles

/-!
# Pole moments of balanced complete-cell profiles

Zero mean removes the constant part of each exponential weight. The residual
oscillation across a pair is at most the reciprocal square root of its lower
arithmetic endpoint, making the pole moments summable in the exact source mass.
-/

noncomputable section
open MeasureTheory Set
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry

private theorem abs_haarProfile {a : ℕ} (ha : 1 ≤ a) (x : ℝ) :
    |haarProfile a x| = haarLeftCoeff a * rawCell (2 * a) x +
      haarRightCoeff a * rawCell (2 * a + 1) x := by
  have hn := haarCoeff_nonneg ha
  unfold haarProfile rawCell
  simp only [indicator_apply]
  split_ifs with hl hr hr
  · exact False.elim ((not_lt_of_ge hr.1) hl.2)
  · simpa only [mul_one, mul_zero, sub_zero, add_zero] using abs_of_nonneg hn.1
  · simpa only [mul_one, mul_zero, zero_sub, zero_add, abs_neg] using abs_of_nonneg hn.2
  · simp only [mul_zero, sub_zero, abs_zero, add_zero]

/-- The L¹ mass of a balanced profile is twice its square mass. -/
theorem integral_abs_haarProfile {a : ℕ} (ha : 1 ≤ a) :
    ∫ x, |haarProfile a x| = 2 * haarMass a := by
  simp_rw [abs_haarProfile ha]
  rw [integral_add ((integrable_rawCell _).const_mul _) ((integrable_rawCell _).const_mul _),
    integral_const_mul, integral_const_mul,
    integral_rawCell (show 1 ≤ 2 * a by omega), integral_rawCell (show 1 ≤ 2 * a + 1 by omega),
    (haarCoeff_mass a).1, (haarCoeff_mass a).2, two_mul]

/-- Mean cancellation turns a weight oscillation into an exact-mass moment bound. -/
theorem abs_haarProfile_moment_le {a : ℕ} (ha : 1 ≤ a) {w : ℝ → ℝ}
    (hw : Continuous w) (q d : ℝ)
    (hb : ∀ x ∈ Ico (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ)),
      |w x - q| ≤ d) :
    |∫ x, haarProfile a x * w x| ≤ 2 * haarMass a * d := by
  have hi := integrable_compact_bv_mul (haarProfile_bv a) (haarProfile_compact a) hw
  have hq := (integrable_haarProfile a).mul_const q
  have he : (∫ x, haarProfile a x * w x) = ∫ x, haarProfile a x * (w x - q) := by
    simp_rw [mul_sub]
    rw [integral_sub hi hq, integral_mul_const, integral_haarProfile ha, zero_mul, sub_zero]
  have hd : Integrable (fun x => haarProfile a x * (w x - q)) :=
    integrable_compact_bv_mul (haarProfile_bv a) (haarProfile_compact a) (hw.sub continuous_const)
  have hb' (x : ℝ) : |haarProfile a x * (w x - q)| ≤ |haarProfile a x| * d := by
    by_cases hx : x ∈ Ico (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hb x hx) (abs_nonneg _)
    · rw [haarProfile_zero_outside_pair ha hx, zero_mul, abs_zero, zero_mul]
  calc
    _ = |∫ x, haarProfile a x * (w x - q)| := congrArg abs he
    _ ≤ ∫ x, |haarProfile a x * (w x - q)| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => haarProfile a x * (w x - q))
    _ ≤ ∫ x, |haarProfile a x| * d :=
      integral_mono hd.abs ((integrable_haarProfile a).abs.mul_const d) hb'
    _ = _ := by rw [integral_mul_const, integral_abs_haarProfile ha]

private theorem sqrt_successor_pair_oscillation {a : ℕ} (ha : 1 ≤ a) :
    Real.sqrt ((2 * a + 2 : ℕ) : ℝ) - Real.sqrt ((2 * a : ℕ) : ℝ) ≤
      1 / Real.sqrt ((2 * a : ℕ) : ℝ) := by
  have hlo : (0 : ℝ) < ((2 * a : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 * a by omega)
  have hx := Real.sqrt_pos.mpr hlo
  have hx2 := Real.sq_sqrt hlo.le
  have hy2 := Real.sq_sqrt (show (0 : ℝ) ≤ ((2 * a + 2 : ℕ) : ℝ) by positivity)
  have he : ((2 * a + 2 : ℕ) : ℝ) = ((2 * a : ℕ) : ℝ) + 2 := by push_cast; ring
  rw [le_div_iff₀ hx]
  nlinarith only [hx2, hy2, he,
    sq_nonneg (Real.sqrt ((2 * a + 2 : ℕ) : ℝ) - Real.sqrt ((2 * a : ℕ) : ℝ))]

private theorem exp_pos_pair_oscillation {a : ℕ} (ha : 1 ≤ a) {x : ℝ}
    (hx : x ∈ Ico (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))) :
    |Real.exp (x / 2) - Real.exp (Real.log ((2 * a : ℕ) : ℝ) / 2)| ≤
      1 / Real.sqrt ((2 * a : ℕ) : ℝ) := by
  have hlo : (0 : ℝ) < ((2 * a : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 * a by omega)
  have hhi : (0 : ℝ) < ((2 * a + 2 : ℕ) : ℝ) := by positivity
  have hleft : Real.exp (Real.log ((2 * a : ℕ) : ℝ) / 2) ≤ Real.exp (x / 2) :=
    Real.exp_le_exp.mpr (by linarith only [hx.1])
  have hright : Real.exp (x / 2) ≤ Real.exp (Real.log ((2 * a + 2 : ℕ) : ℝ) / 2) :=
    Real.exp_le_exp.mpr (by linarith only [hx.2])
  rw [abs_of_nonneg (sub_nonneg.mpr hleft)]
  calc
    _ ≤ Real.exp (Real.log ((2 * a + 2 : ℕ) : ℝ) / 2) -
        Real.exp (Real.log ((2 * a : ℕ) : ℝ) / 2) := sub_le_sub_right hright _
    _ = Real.sqrt ((2 * a + 2 : ℕ) : ℝ) - Real.sqrt ((2 * a : ℕ) : ℝ) := by
      rw [Real.exp_half, Real.exp_log hhi, Real.exp_half, Real.exp_log hlo]
    _ ≤ _ := sqrt_successor_pair_oscillation ha

private theorem inv_sub_inv_le_sub {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    A⁻¹ - B⁻¹ ≤ B - A := by
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hBp : 0 < B := hAp.trans_le hAB
  have hp : 1 ≤ A * B := by
    simpa only [one_mul] using mul_le_mul hA (hA.trans hAB) zero_le_one hAp.le
  have hd : 0 ≤ B - A := sub_nonneg.mpr hAB
  calc
    _ = (B - A) / (A * B) := by field_simp [hAp.ne', hBp.ne']
    _ ≤ B - A := by
      rw [div_le_iff₀ (mul_pos hAp hBp)]
      nlinarith only [mul_le_mul_of_nonneg_left hp hd]

private theorem exp_neg_pair_oscillation {a : ℕ} (ha : 1 ≤ a) {x : ℝ}
    (hx : x ∈ Ico (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))) :
    |Real.exp (-x / 2) - Real.exp (-Real.log ((2 * a : ℕ) : ℝ) / 2)| ≤
      1 / Real.sqrt ((2 * a : ℕ) : ℝ) := by
  have hlo : 0 ≤ Real.log ((2 * a : ℕ) : ℝ) := Real.log_nonneg
    (by exact_mod_cast (show 1 ≤ 2 * a by omega))
  have hA : 1 ≤ Real.exp (Real.log ((2 * a : ℕ) : ℝ) / 2) :=
    Real.one_le_exp_iff.mpr (by linarith only [hlo])
  have hAB : Real.exp (Real.log ((2 * a : ℕ) : ℝ) / 2) ≤ Real.exp (x / 2) :=
    Real.exp_le_exp.mpr (by linarith only [hx.1])
  have hneg : Real.exp (-x / 2) ≤ Real.exp (-Real.log ((2 * a : ℕ) : ℝ) / 2) :=
    Real.exp_le_exp.mpr (by linarith only [hx.1])
  rw [abs_of_nonpos (sub_nonpos.mpr hneg), neg_sub]
  calc
    _ = (Real.exp (Real.log ((2 * a : ℕ) : ℝ) / 2))⁻¹ - (Real.exp (x / 2))⁻¹ := by
      rw [neg_div, Real.exp_neg, neg_div, Real.exp_neg]
    _ ≤ Real.exp (x / 2) - Real.exp (Real.log ((2 * a : ℕ) : ℝ) / 2) :=
      inv_sub_inv_le_sub hA hAB
    _ ≤ _ := by
      simpa only [abs_of_nonneg (sub_nonneg.mpr hAB)] using exp_pos_pair_oscillation ha hx

/-- The expanding pole moment is summably small in the arithmetic index. -/
theorem abs_haarProfile_exp_pos_le {a : ℕ} (ha : 1 ≤ a) :
    |∫ x, haarProfile a x * Real.exp (x / 2)| ≤
      2 * haarMass a / Real.sqrt ((2 * a : ℕ) : ℝ) := by
  simpa only [mul_one_div] using abs_haarProfile_moment_le ha (by fun_prop)
    (Real.exp (Real.log ((2 * a : ℕ) : ℝ) / 2)) (1 / Real.sqrt ((2 * a : ℕ) : ℝ))
    (fun _ hx => exp_pos_pair_oscillation ha hx)

/-- The contracting pole moment obeys the same horizon-independent bound. -/
theorem abs_haarProfile_exp_neg_le {a : ℕ} (ha : 1 ≤ a) :
    |∫ x, haarProfile a x * Real.exp (-x / 2)| ≤
      2 * haarMass a / Real.sqrt ((2 * a : ℕ) : ℝ) := by
  simpa only [mul_one_div] using abs_haarProfile_moment_le ha (by fun_prop)
    (Real.exp (-Real.log ((2 * a : ℕ) : ℝ) / 2)) (1 / Real.sqrt ((2 * a : ℕ) : ℝ))
    (fun _ hx => exp_neg_pair_oscillation ha hx)

private theorem moment_sq_le_pronic {a : ℕ} (ha : 1 ≤ a) {p : ℝ}
    (hp : |p| ≤ 2 * haarMass a / Real.sqrt ((2 * a : ℕ) : ℝ)) :
    p ^ 2 ≤ haarMass a / ((a : ℝ) * ((a : ℝ) + 1)) := by
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha1
  have hM := (haarMass_pos ha).le
  have hsq : p ^ 2 ≤ (2 * haarMass a / Real.sqrt ((2 * a : ℕ) : ℝ)) ^ 2 :=
    sq_le_sq' (abs_le.mp hp).1 (abs_le.mp hp).2
  have hden : (0 : ℝ) < ((2 * a : ℕ) : ℝ) := by positivity
  have he : (2 * haarMass a / Real.sqrt ((2 * a : ℕ) : ℝ)) ^ 2 =
      2 * haarMass a ^ 2 / (a : ℝ) := by
    rw [div_pow, Real.sq_sqrt hden.le]
    push_cast
    field_simp [ha0.ne']
  have hMbound : 2 * haarMass a ≤ 1 / ((a : ℝ) + 1) := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (a : ℝ) + 1)).mp
      (haarMass_bounds ha).2
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (a : ℝ) + 1)]
    nlinarith only [h, mul_nonneg hM (show 0 ≤ 2 * (a : ℝ) - 1 by linarith only [ha1])]
  calc
    p ^ 2 ≤ 2 * haarMass a ^ 2 / (a : ℝ) := he ▸ hsq
    _ = (haarMass a / (a : ℝ)) * (2 * haarMass a) := by ring
    _ ≤ (haarMass a / (a : ℝ)) * (1 / ((a : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hMbound (div_nonneg hM ha0.le)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

private theorem sum_pronic_le_one (X : ℕ) :
    (∑ a ∈ Finset.Icc 1 X, 1 / ((a : ℝ) * ((a : ℝ) + 1))) ≤ 1 := by
  by_cases hX : X = 0
  · subst X
    simp
  have hX1 : 1 ≤ X := Nat.one_le_iff_ne_zero.mpr hX
  calc
    _ = ∑ a ∈ Finset.Icc 1 X, (-(1 / ((a + 1 : ℕ) : ℝ)) - -(1 / (a : ℝ))) := by
      apply Finset.sum_congr rfl
      intro a ha
      have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by have := (Finset.mem_Icc.mp ha).1; omega)
      push_cast
      field_simp [ha0.ne']
      ring
    _ = -(1 / ((X + 1 : ℕ) : ℝ)) - -(1 / ((1 : ℕ) : ℝ)) :=
      Finset.sum_Icc_sub hX1 (fun a : ℕ => -(1 / (a : ℝ)))
    _ ≤ 1 := by
      have hnonneg : (0 : ℝ) ≤ 1 / ((X + 1 : ℕ) : ℝ) := by positivity
      norm_num only [Nat.cast_one, div_one, sub_neg_eq_add]
      linarith only [hnonneg]

private theorem section_moment_sq_le (c : ℕ → ℝ) (X : ℕ) {w : ℝ → ℝ} (hw : Continuous w)
    (hp : ∀ a, 1 ≤ a → (∫ x, haarProfile a x * w x) ^ 2 ≤
      haarMass a / ((a : ℝ) * ((a : ℝ) + 1))) :
    (∫ x, haarSectionProfile c X x * w x) ^ 2 ≤
      ∑ a ∈ Finset.Icc 1 X, haarMass a * c a ^ 2 := by
  let P : ℕ → ℝ := fun a => ∫ x, haarProfile a x * w x
  have hi (a : ℕ) : Integrable (fun x => haarProfile a x * w x) :=
    integrable_compact_bv_mul (haarProfile_bv a) (haarProfile_compact a) hw
  have he : (∫ x, haarSectionProfile c X x * w x) = ∑ a ∈ Finset.Icc 1 X, c a * P a := by
    unfold haarSectionProfile
    simp_rw [Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum _ fun a _ => (hi a).const_mul (c a)]
    simp only [integral_const_mul, P]
  rw [he]
  have hprod (a : ℕ) (ha : a ∈ Finset.Icc 1 X) :
      (Real.sqrt (haarMass a) * c a) * (P a / Real.sqrt (haarMass a)) = c a * P a := by
    have hs := (Real.sqrt_pos.mpr (haarMass_pos (Finset.mem_Icc.mp ha).1)).ne'
    field_simp [hs]
  have hsq (a : ℕ) (ha : a ∈ Finset.Icc 1 X) :
      (Real.sqrt (haarMass a) * c a) ^ 2 = haarMass a * c a ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (haarMass_pos (Finset.mem_Icc.mp ha).1).le]
  have hnorm (a : ℕ) (ha : a ∈ Finset.Icc 1 X) :
      (P a / Real.sqrt (haarMass a)) ^ 2 ≤ 1 / ((a : ℝ) * ((a : ℝ) + 1)) := by
    have hM := haarMass_pos (Finset.mem_Icc.mp ha).1
    rw [div_pow, Real.sq_sqrt hM.le, div_le_iff₀ hM]
    simpa only [P, div_eq_mul_inv, one_mul, mul_comm] using hp a (Finset.mem_Icc.mp ha).1
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 X)
    (fun a => Real.sqrt (haarMass a) * c a) (fun a => P a / Real.sqrt (haarMass a))
  rw [Finset.sum_congr rfl hprod, Finset.sum_congr rfl hsq] at hcs
  have hb : (∑ a ∈ Finset.Icc 1 X, (P a / Real.sqrt (haarMass a)) ^ 2) ≤ 1 :=
    (Finset.sum_le_sum hnorm).trans (sum_pronic_le_one X)
  exact hcs.trans (mul_le_of_le_one_right
    (Finset.sum_nonneg fun a ha => mul_nonneg (haarMass_pos (Finset.mem_Icc.mp ha).1).le
      (sq_nonneg _)) hb)

/-- The expanding pole functional is bounded by the section's exact square mass. -/
theorem haarSectionProfile_exp_pos_sq_le (c : ℕ → ℝ) (X : ℕ) :
    (∫ x, haarSectionProfile c X x * Real.exp (x / 2)) ^ 2 ≤
      ∑ a ∈ Finset.Icc 1 X, haarMass a * c a ^ 2 :=
  section_moment_sq_le c X (by fun_prop) fun _ ha =>
    moment_sq_le_pronic ha (abs_haarProfile_exp_pos_le ha)

/-- The contracting pole functional has the same bound on every finite signed section. -/
theorem haarSectionProfile_exp_neg_sq_le (c : ℕ → ℝ) (X : ℕ) :
    (∫ x, haarSectionProfile c X x * Real.exp (-x / 2)) ^ 2 ≤
      ∑ a ∈ Finset.Icc 1 X, haarMass a * c a ^ 2 :=
  section_moment_sq_le c X (by fun_prop) fun _ ha =>
    moment_sq_le_pronic ha (abs_haarProfile_exp_neg_le ha)

/-- The original adverse pole product costs at most twice the exact section mass. -/
theorem haarSectionProfile_pole_ge (c : ℕ → ℝ) (X : ℕ) :
    -2 * (∑ a ∈ Finset.Icc 1 X, haarMass a * c a ^ 2) ≤
      2 * coshHalfMoment (haarSectionProfile c X) ^ 2 -
        2 * sinhHalfMoment (haarSectionProfile c X) ^ 2 := by
  have hp : Integrable (fun x => Real.exp (x / 2) * haarSectionProfile c X x) := by
    simpa only [mul_comm] using integrable_compact_bv_mul (haarSectionProfile_bv c X)
      (haarSectionProfile_compact c X) (show Continuous (fun x : ℝ => Real.exp (x / 2)) by fun_prop)
  have hm : Integrable (fun x => Real.exp (-(x / 2)) * haarSectionProfile c X x) := by
    simpa only [mul_comm] using integrable_compact_bv_mul (haarSectionProfile_bv c X)
      (haarSectionProfile_compact c X) (show Continuous (fun x : ℝ => Real.exp (-(x / 2))) by fun_prop)
  have hps : (∫ x, Real.exp (x / 2) * haarSectionProfile c X x) ^ 2 ≤
      ∑ a ∈ Finset.Icc 1 X, haarMass a * c a ^ 2 := by
    simpa only [mul_comm] using haarSectionProfile_exp_pos_sq_le c X
  have hms : (∫ x, Real.exp (-(x / 2)) * haarSectionProfile c X x) ^ 2 ≤
      ∑ a ∈ Finset.Icc 1 X, haarMass a * c a ^ 2 := by
    simpa only [neg_div, mul_comm] using haarSectionProfile_exp_neg_sq_le c X
  rw [(halfMoments_eq_exp hp hm).1, (halfMoments_eq_exp hp hm).2]
  nlinarith only [hps, hms,
    sq_nonneg ((∫ x, Real.exp (x / 2) * haarSectionProfile c X x) +
      ∫ x, Real.exp (-(x / 2)) * haarSectionProfile c X x)]

#print axioms integral_abs_haarProfile
#print axioms abs_haarProfile_exp_pos_le
#print axioms abs_haarProfile_exp_neg_le
#print axioms haarSectionProfile_exp_pos_sq_le
#print axioms haarSectionProfile_exp_neg_sq_le
#print axioms haarSectionProfile_pole_ge

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells

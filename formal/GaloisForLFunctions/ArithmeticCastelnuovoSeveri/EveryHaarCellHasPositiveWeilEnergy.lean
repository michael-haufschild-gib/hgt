import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheGammaEnergyOfABalancedPair
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellEffectivity
import GaloisForLFunctions.RHTower.DigammaQuarter

/-!
# Original Weil energy of individual balanced complete cells

Exact interval polarization pays the central archimedean mass at every
arithmetic index. Centering both exponential weights bounds the remaining
pole product in the cell's exact mass. No prime lag couples a cell to itself.
-/

noncomputable section
open MeasureTheory Set
open RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry

private theorem normalized_balancedGamma_lower {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hw1 : u + v ≤ 1) :
    1 - Real.log ((u * v / (u + v)) / 4) + Real.pi / 2 -
        (u + v) ^ 2 / 16 - 5 * (u + v) ^ 3 / 192 ≤
      intervalGammaCost u / u + intervalGammaCost v / v -
        intervalGammaCost (u + v) / (u + v) := by
  have hw : 0 < u + v := add_pos hu hv
  have hl : 1 - Real.log (u / 4) + Real.pi / 2 - u / 4 - u ^ 2 / 24 ≤
      intervalGammaCost u / u := by
    rw [le_div_iff₀ hu, mul_comm]
    exact intervalGammaCost_lower hu (by linarith only [hv, hw1])
  have hr : 1 - Real.log (v / 4) + Real.pi / 2 - v / 4 - v ^ 2 / 24 ≤
      intervalGammaCost v / v := by
    rw [le_div_iff₀ hv, mul_comm]
    exact intervalGammaCost_lower hv (by linarith only [hu, hw1])
  have hc : intervalGammaCost (u + v) / (u + v) ≤
      1 - Real.log ((u + v) / 4) + Real.pi / 2 - (u + v) / 4 +
        (u + v) ^ 2 / 48 + 5 * (u + v) ^ 3 / 192 := by
    rw [div_le_iff₀ hw, mul_comm]
    exact intervalGammaCost_upper hw hw1
  have he : Real.log ((u * v / (u + v)) / 4) =
      Real.log (u / 4) + Real.log (v / 4) - Real.log ((u + v) / 4) := by
    rw [Real.log_div (by positivity : u * v / (u + v) ≠ 0) (by norm_num),
      Real.log_div (by positivity : u * v ≠ 0) hw.ne', Real.log_mul hu.ne' hv.ne',
      Real.log_div hu.ne' (by norm_num), Real.log_div hv.ne' (by norm_num),
      Real.log_div hw.ne' (by norm_num)]
    ring
  rw [he]
  nlinarith only [hl, hr, hc, mul_pos hu hv]

/-- The two half-widths add to the width of the complete pair. -/
theorem logCellWidth_pair_sum {a : ℕ} (ha : 1 ≤ a) :
    logCellWidth (2 * a) + logCellWidth (2 * a + 1) = logCellWidth a := by
  rw [← haarPairWidth ha]
  simp only [logCellWidth, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

private theorem haarWidth_le_log_two {a : ℕ} (ha : 1 ≤ a) :
    logCellWidth a ≤ Real.log 2 := by
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha1
  unfold logCellWidth
  rw [← Real.log_div (by positivity : (a : ℝ) + 1 ≠ 0) ha0.ne']
  apply Real.log_le_log (by positivity)
  rw [div_le_iff₀ ha0]
  linarith only [ha1]

/-- The exact balanced square mass never exceeds one quarter of the pair width. -/
theorem four_haarMass_le_width {a : ℕ} (ha : 1 ≤ a) :
    4 * haarMass a ≤ logCellWidth a := by
  have hu := logCellWidth_pos (show 1 ≤ 2 * a by omega)
  have hv := logCellWidth_pos (show 1 ≤ 2 * a + 1 by omega)
  rw [← logCellWidth_pair_sum ha, haarMass]
  rw [← mul_div_assoc, div_le_iff₀ (add_pos hu hv)]
  nlinarith only [sq_nonneg (logCellWidth (2 * a) - logCellWidth (2 * a + 1))]

/-- Exact balanced energy per unit mass is the sum of both half-cell finite parts minus
the finite part of their union. -/
theorem haarProfile_gamma_div_mass {a : ℕ} (ha : 1 ≤ a) :
    levyEnergy (haarProfile a) / haarMass a =
      intervalGammaCost (logCellWidth (2 * a)) / logCellWidth (2 * a) +
        intervalGammaCost (logCellWidth (2 * a + 1)) / logCellWidth (2 * a + 1) -
        intervalGammaCost (logCellWidth a) / logCellWidth a := by
  have hu := logCellWidth_pos (show 1 ≤ 2 * a by omega)
  have hv := logCellWidth_pos (show 1 ≤ 2 * a + 1 by omega)
  have hw := add_pos hu hv
  rw [haarProfile_levyEnergy_eq ha,
    rawCell_levyEnergy_eq_intervalGammaCost (show 1 ≤ 2 * a by omega),
    rawCell_levyEnergy_eq_intervalGammaCost (show 1 ≤ 2 * a + 1 by omega),
    rawCell_levyEnergy_eq_intervalGammaCost ha, ← logCellWidth_pair_sum ha]
  unfold haarLeftCoeff haarRightCoeff haarMass
  field_simp [hu.ne', hv.ne', hw.ne']

private theorem phase_zero_value :
    2 * gammaHardyPhaseRate 0 =
      -(3 * Real.log 2 + Real.eulerMascheroniConstant + Real.pi / 2) - Real.log Real.pi := by
  have hline : linePt 0 / 2 = (1 / 4 : ℂ) := by unfold linePt; norm_num
  unfold gammaHardyPhaseRate
  rw [hline, GaloisForLFunctions.RHTower.digamma_quarter]
  simp only [Complex.neg_re, Complex.ofReal_re]
  ring

/-- The shared linear width term cancels, leaving a logarithmic mass floor for the actual
archimedean form of every balanced cell. -/
theorem haarProfile_archimedean_finite_part {a : ℕ} (ha : 1 ≤ a) :
    1 - Real.eulerMascheroniConstant - Real.log (2 * Real.pi * haarMass a) -
        logCellWidth a ^ 2 / 16 - 5 * logCellWidth a ^ 3 / 192 ≤
      levyEnergy (haarProfile a) / haarMass a + 2 * gammaHardyPhaseRate 0 := by
  have hw1 : logCellWidth a ≤ 1 :=
    (haarWidth_le_log_two ha).trans (by linarith only [Real.log_two_lt_d9])
  have h := normalized_balancedGamma_lower
    (logCellWidth_pos (show 1 ≤ 2 * a by omega))
    (logCellWidth_pos (show 1 ≤ 2 * a + 1 by omega))
    (by rwa [logCellWidth_pair_sum ha])
  change 1 - Real.log (haarMass a / 4) + Real.pi / 2 -
      (logCellWidth (2 * a) + logCellWidth (2 * a + 1)) ^ 2 / 16 -
      5 * (logCellWidth (2 * a) + logCellWidth (2 * a + 1)) ^ 3 / 192 ≤ _ at h
  rw [logCellWidth_pair_sum ha, ← haarProfile_gamma_div_mass ha] at h
  have hlog : Real.log (2 * Real.pi * haarMass a) =
      Real.log (haarMass a / 4) + 3 * Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by positivity : 2 * Real.pi ≠ 0) (haarMass_pos ha).ne',
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_pos.ne',
      Real.log_div (haarMass_pos ha).ne' (by norm_num),
      show Real.log 4 = 2 * Real.log 2 from by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num]
    ring
  rw [hlog, phase_zero_value]
  linarith only [h]

private theorem haarMass_le_seven_fortieths {a : ℕ} (ha : 1 ≤ a) :
    haarMass a ≤ 7 / 40 := by
  have h := (four_haarMass_le_width ha).trans (haarWidth_le_log_two ha)
  linarith only [h, Real.log_two_lt_d9]

/-- The original Gamma term pays the central archimedean mass on every individual Haar cell. -/
theorem haarProfile_archimedean_ge {a : ℕ} (ha : 1 ≤ a) :
    (1 / 5 : ℝ) * haarMass a ≤
      levyEnergy (haarProfile a) + 2 * gammaHardyPhaseRate 0 * haarMass a := by
  have hM := haarMass_pos ha
  have hMb := haarMass_le_seven_fortieths ha
  have hγ : Real.eulerMascheroniConstant ≤ 3 / 5 := by
    linarith only
      [RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion]
  have hpi : Real.pi ≤ 22 / 7 := by linarith only [Real.pi_lt_d6]
  have hprod := mul_le_mul hpi hMb hM.le (by norm_num : (0 : ℝ) ≤ 22 / 7)
  have hlog : Real.log (2 * Real.pi * haarMass a) ≤ 1 / 10 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 2 * Real.pi * haarMass a by positivity)
    linarith only [hprod, h]
  have hw : 0 ≤ logCellWidth a := (logCellWidth_pos ha).le
  have hw1 : logCellWidth a ≤ 1 :=
    (haarWidth_le_log_two ha).trans (by linarith only [Real.log_two_lt_d9])
  have h2 : logCellWidth a ^ 2 ≤ 1 := pow_le_one₀ hw hw1
  have h3 : logCellWidth a ^ 3 ≤ 1 := pow_le_one₀ hw hw1
  have hbase := haarProfile_archimedean_finite_part ha
  have hfloor : (1 / 5 : ℝ) ≤ levyEnergy (haarProfile a) / haarMass a +
      2 * gammaHardyPhaseRate 0 := by
    linarith only [hbase, hγ, hlog, h2, h3]
  have h := mul_le_mul_of_nonneg_right hfloor hM.le
  simpa only [add_mul, div_mul_cancel₀ _ hM.ne'] using h

private theorem abs_haarProfile_moment_of_range {a : ℕ} (ha : 1 ≤ a)
    {f : ℝ → ℝ} (hf : Continuous f) {l u : ℝ}
    (hb : ∀ x ∈ Ico (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ)),
      l ≤ f x ∧ f x ≤ u) :
    |∫ x, haarProfile a x * f x| ≤ haarMass a * (u - l) := by
  have h := abs_haarProfile_moment_le ha hf ((l + u) / 2) ((u - l) / 2)
    (fun x hx => abs_le.mpr ⟨by linarith only [(hb x hx).1],
      by linarith only [(hb x hx).2]⟩)
  convert h using 1
  ring

private theorem sqrt_pair_oscillation_product {a : ℕ} (ha : 1 ≤ a) :
    (Real.sqrt ((2 * a + 2 : ℕ) : ℝ) - Real.sqrt ((2 * a : ℕ) : ℝ)) *
      ((Real.sqrt ((2 * a : ℕ) : ℝ))⁻¹ - (Real.sqrt ((2 * a + 2 : ℕ) : ℝ))⁻¹) ≤ 1 / 4 := by
  have ha0 : 0 < a := by omega
  have hs : 0 < Real.sqrt ((2 * a : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have ht : 0 < Real.sqrt ((2 * a + 2 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : Real.sqrt ((2 * a : ℕ) : ℝ) ^ 2 = 2 * (a : ℝ) := by
    rw [Real.sq_sqrt (by positivity)]
    push_cast
    rfl
  have ht2 : Real.sqrt ((2 * a + 2 : ℕ) : ℝ) ^ 2 = 2 * (a : ℝ) + 2 := by
    rw [Real.sq_sqrt (by positivity)]
    push_cast
    rfl
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hst : Real.sqrt ((2 * a : ℕ) : ℝ) ≤ Real.sqrt ((2 * a + 2 : ℕ) : ℝ) := by
    nlinarith only [hs, ht, hs2, ht2]
  have hbound : Real.sqrt ((2 * a + 2 : ℕ) : ℝ) ≤
      3 * Real.sqrt ((2 * a : ℕ) : ℝ) / 2 := by
    nlinarith only [hs, ht, hs2, ht2, ha1]
  have hdiff : Real.sqrt ((2 * a + 2 : ℕ) : ℝ) - Real.sqrt ((2 * a : ℕ) : ℝ) ≤
      Real.sqrt ((2 * a : ℕ) : ℝ) / 2 := by linarith only [hbound]
  have hsq := mul_self_le_mul_self (sub_nonneg.mpr hst) hdiff
  have hmul := mul_le_mul_of_nonneg_left hst hs.le
  have he : (Real.sqrt ((2 * a : ℕ) : ℝ))⁻¹ -
      (Real.sqrt ((2 * a + 2 : ℕ) : ℝ))⁻¹ =
      (Real.sqrt ((2 * a + 2 : ℕ) : ℝ) - Real.sqrt ((2 * a : ℕ) : ℝ)) /
        (Real.sqrt ((2 * a : ℕ) : ℝ) * Real.sqrt ((2 * a + 2 : ℕ) : ℝ)) := by
    field_simp [hs.ne', ht.ne']
  rw [he, ← mul_div_assoc, div_le_iff₀ (mul_pos hs ht)]
  nlinarith only [hsq, hmul]

/-- Centering each exponential weight pays the full pole product by a quadratic cell mass. -/
theorem haarProfile_pole_ge_mass_sq {a : ℕ} (ha : 1 ≤ a) :
    -(haarMass a ^ 2 / 2) ≤
      2 * coshHalfMoment (haarProfile a) ^ 2 - 2 * sinhHalfMoment (haarProfile a) ^ 2 := by
  have ha0 : 0 < a := by omega
  have hlo : (0 : ℝ) < ((2 * a : ℕ) : ℝ) := by positivity
  have hhi : (0 : ℝ) < ((2 * a + 2 : ℕ) : ℝ) := by positivity
  have hs := Real.sqrt_pos.mpr hlo
  have ht := Real.sqrt_pos.mpr hhi
  have hrange (x : ℝ)
      (hx : x ∈ Ico (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))) :
      Real.sqrt ((2 * a : ℕ) : ℝ) ≤ Real.exp (x / 2) ∧
        Real.exp (x / 2) ≤ Real.sqrt ((2 * a + 2 : ℕ) : ℝ) := by
    have hl : Real.exp (Real.log ((2 * a : ℕ) : ℝ) / 2) ≤ Real.exp (x / 2) :=
      Real.exp_le_exp.mpr (by linarith only [hx.1])
    have hu : Real.exp (x / 2) ≤ Real.exp (Real.log ((2 * a + 2 : ℕ) : ℝ) / 2) :=
      Real.exp_le_exp.mpr (by linarith only [hx.2])
    have helo : Real.exp (Real.log ((2 * a : ℕ) : ℝ) / 2) = Real.sqrt ((2 * a : ℕ) : ℝ) := by
      rw [Real.exp_half, Real.exp_log hlo]
    have hehi : Real.exp (Real.log ((2 * a + 2 : ℕ) : ℝ) / 2) =
        Real.sqrt ((2 * a + 2 : ℕ) : ℝ) := by
      rw [Real.exp_half, Real.exp_log hhi]
    rw [helo] at hl
    rw [hehi] at hu
    exact ⟨hl, hu⟩
  have hp := abs_haarProfile_moment_of_range ha
    (show Continuous (fun x : ℝ => Real.exp (x / 2)) by fun_prop) hrange
  have hn := abs_haarProfile_moment_of_range ha
    (show Continuous (fun x : ℝ => Real.exp (-x / 2)) by fun_prop)
    (l := (Real.sqrt ((2 * a + 2 : ℕ) : ℝ))⁻¹)
    (u := (Real.sqrt ((2 * a : ℕ) : ℝ))⁻¹) (fun x hx => by
      rw [neg_div, Real.exp_neg]
      exact ⟨inv_anti₀ (Real.exp_pos _) (hrange x hx).2,
        inv_anti₀ hs (hrange x hx).1⟩)
  have hM := (haarMass_pos ha).le
  have hpn := mul_le_mul hp hn (abs_nonneg _) (le_trans (abs_nonneg _) hp)
  have hosc := mul_le_mul_of_nonneg_left (sqrt_pair_oscillation_product ha)
    (sq_nonneg (haarMass a))
  have habs : |(∫ x, haarProfile a x * Real.exp (x / 2)) *
      (∫ x, haarProfile a x * Real.exp (-x / 2))| ≤ haarMass a ^ 2 / 4 := by
    rw [abs_mul]
    nlinarith only [hpn, hosc]
  have hip : Integrable (fun x => Real.exp (x / 2) * haarProfile a x) := by
    simpa only [mul_comm] using integrable_compact_bv_mul (haarProfile_bv a)
      (haarProfile_compact a) (show Continuous (fun x : ℝ => Real.exp (x / 2)) by fun_prop)
  have hin : Integrable (fun x => Real.exp (-(x / 2)) * haarProfile a x) := by
    simpa only [mul_comm] using integrable_compact_bv_mul (haarProfile_bv a)
      (haarProfile_compact a) (show Continuous (fun x : ℝ => Real.exp (-(x / 2))) by fun_prop)
  rw [(halfMoments_eq_exp hip hin).1, (halfMoments_eq_exp hip hin).2]
  have hneg := (abs_le.mp habs).1
  simp only [mul_comm (haarProfile a _), neg_div] at hneg
  nlinarith only [hneg]

/-- The full actual prime series has no diagonal on an individual balanced cell. -/
theorem primeSum_haarProfile_eq_zero {a : ℕ} (ha : 1 ≤ a) :
    primeSum (haarProfile a) = 0 := by
  classical
  let c : ℕ → ℝ := fun b => if b = a then 1 else 0
  have hmem : a ∈ Finset.Icc 1 a := Finset.mem_Icc.mpr ⟨ha, le_rfl⟩
  have he : haarSectionProfile c a = haarProfile a := by
    funext x
    unfold haarSectionProfile
    rw [Finset.sum_eq_single a]
    · simp only [c, if_pos rfl, one_mul]
    · intro b _hb hba
      simp only [c, if_neg hba, zero_mul]
    · intro hn
      exact False.elim (hn hmem)
  rw [← he, ← haarPrimeEnergy_eq_primeSum, haarPrimeEnergy_eq]
  apply Finset.sum_eq_zero
  intro m hm
  have hm2 := (Finset.mem_Icc.mp hm).1
  have hne : (2 * a + 1) * m ≠ 2 * a + 1 := by
    have h := Nat.mul_le_mul_left (2 * a + 1) hm2
    omega
  have hs : (∑ b ∈ Finset.Icc 1 a, ∑ j ∈ Finset.Icc 1 a,
      c b * c j * (if (2 * b + 1) * m = 2 * j + 1 then haarMass j else 0)) = 0 := by
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single a]
      · simp only [c, if_pos rfl, if_neg hne, mul_zero]
      · intro j _hj hja
        simp only [c, if_neg hja, mul_zero, zero_mul]
      · intro hn
        exact False.elim (hn hmem)
    · intro b _hb hba
      simp only [c, if_neg hba, zero_mul, Finset.sum_const_zero]
    · intro hn
      exact False.elim (hn hmem)
  rw [hs, mul_zero]

/-- Every individual complete Haar cell has a positive original Weil mass floor,
including the lowest arithmetic index. -/
theorem haarProfile_roughWeil_ge {a : ℕ} (ha : 1 ≤ a) :
    (1 / 10 : ℝ) * haarMass a ≤ roughWeil (haarProfile a) := by
  have harch := haarProfile_archimedean_ge ha
  have hpole := haarProfile_pole_ge_mass_sq ha
  have hM := (haarMass_pos ha).le
  have hmass := mul_le_mul_of_nonneg_left (haarMass_le_seven_fortieths ha) hM
  unfold roughWeil
  rw [integral_haarProfile_sq ha, primeSum_haarProfile_eq_zero ha]
  nlinarith only [harch, hpole, hmass, hM]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells

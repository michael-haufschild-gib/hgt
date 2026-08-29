import GaloisForLFunctions.RHTower.Sieve.VaughanSecondThirdMixedHybridBlock

/-!
# Explicit power envelopes for the Kubalalika block estimate

The mixed second/third-derivative Vaughan block envelope is bounded by an explicit monomial in
`A`, `B` and `X = T r`.  Every constant is elementary: `(72π)^{-1/6} ≤ 1`, `√(36π) ≥ 10`,
`(1152π)^{1/6} ≤ 4`, `√(288π) ≤ 31`, `√(20π) ≤ 8` and `√4000 ≤ 64`.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

theorem rpow_div_mul_pow {X c : ℝ} (hX : 0 < X) (hc : 0 < c) {A : ℕ} (hA : 1 ≤ A) (e : ℝ) :
    (X / (c * (A : ℝ) ^ 4)) ^ e = X ^ e * c ^ (-e) * (A : ℝ) ^ (-(4 * e)) := by
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hA4 : (0 : ℝ) < (A : ℝ) ^ 4 := by positivity
  have hden : (0 : ℝ) < c * (A : ℝ) ^ 4 := by positivity
  rw [Real.div_rpow hX.le hden.le, Real.mul_rpow hc.le hA4.le]
  have hpow : ((A : ℝ) ^ 4) ^ e = (A : ℝ) ^ (4 * e) := by
    rw [← Real.rpow_natCast (A : ℝ) 4, ← Real.rpow_mul hA0.le]
    norm_num
  rw [hpow, Real.rpow_neg hc.le, Real.rpow_neg hA0.le]
  field_simp

/-- The first mixed coefficient is `≤ 87552 · A^{1/3} X^{1/6}`. -/
theorem sharpThirdDerivativeFibreFirstCoefficient_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A : ℕ} (hA : 1 ≤ A) :
    sharpThirdDerivativeFibreFirstCoefficient T r A
      ≤ 87552 * (A : ℝ) ^ (1 / 3 : ℝ) * (T * r) ^ (1 / 6 : ℝ) := by
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hX : (0 : ℝ) < T * r := by positivity
  have hpi : (0 : ℝ) < 72 * Real.pi := by positivity
  rw [sharpThirdDerivativeFibreFirstCoefficient, rpow_div_mul_pow hX hpi hA]
  have hconst : (72 * Real.pi : ℝ) ^ (-(1 / 6 : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg hpi.le]
    have h1 : (1 : ℝ) ≤ (72 * Real.pi) ^ (1 / 6 : ℝ) :=
      Real.one_le_rpow (by nlinarith [Real.pi_gt_three]) (by norm_num)
    exact inv_le_one_of_one_le₀ h1
  have hApow : (A : ℝ) * (A : ℝ) ^ (-(4 * (1 / 6 : ℝ))) = (A : ℝ) ^ (1 / 3 : ℝ) := by
    have hadd := Real.rpow_add hA0 1 (-(4 * (1 / 6 : ℝ)))
    rw [Real.rpow_one] at hadd
    rw [← hadd]
    norm_num
  have hnn : (0 : ℝ) ≤ 87552 * (A : ℝ) ^ (1 / 3 : ℝ) * (T * r) ^ (1 / 6 : ℝ) := by
    have h1 : (0 : ℝ) ≤ (A : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_nonneg hA0.le _
    have h2 : (0 : ℝ) ≤ (T * r) ^ (1 / 6 : ℝ) := Real.rpow_nonneg hX.le _
    positivity
  have hkey : 16 * 1368 * (4 * (A : ℝ))
      * ((T * r) ^ (1 / 6 : ℝ) * (72 * Real.pi) ^ (-(1 / 6 : ℝ))
        * (A : ℝ) ^ (-(4 * (1 / 6 : ℝ))))
      = (87552 * (A : ℝ) ^ (1 / 3 : ℝ) * (T * r) ^ (1 / 6 : ℝ))
        * (72 * Real.pi) ^ (-(1 / 6 : ℝ)) := by
    rw [← hApow]
    ring
  rw [hkey]
  calc (87552 * (A : ℝ) ^ (1 / 3 : ℝ) * (T * r) ^ (1 / 6 : ℝ))
        * (72 * Real.pi) ^ (-(1 / 6 : ℝ))
      ≤ (87552 * (A : ℝ) ^ (1 / 3 : ℝ) * (T * r) ^ (1 / 6 : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left hconst hnn
    _ = 87552 * (A : ℝ) ^ (1 / 3 : ℝ) * (T * r) ^ (1 / 6 : ℝ) := by ring


/-- The second mixed coefficient is `≤ 218880 · A^{7/6} X^{-1/6}`. -/
theorem sharpThirdDerivativeFibreSecondCoefficient_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A : ℕ} (hA : 1 ≤ A) :
    sharpThirdDerivativeFibreSecondCoefficient T r A
      ≤ 218880 * (A : ℝ) ^ (7 / 6 : ℝ) * (T * r) ^ (-(1 / 6 : ℝ)) := by
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hX : (0 : ℝ) < T * r := by positivity
  have hpi : (0 : ℝ) < 1152 * Real.pi := by positivity
  rw [sharpThirdDerivativeFibreSecondCoefficient, rpow_div_mul_pow hX hpi hA]
  have hconst : (1152 * Real.pi : ℝ) ^ (-(-(1 / 6 : ℝ))) ≤ 5 := by
    rw [neg_neg]
    have h4 : (1152 * Real.pi : ℝ) ≤ 5 ^ (6 : ℕ) := by
      have hp : Real.pi ≤ 4 := Real.pi_le_four
      norm_num
      nlinarith [hp]
    have hmono : (1152 * Real.pi : ℝ) ^ (1 / 6 : ℝ) ≤ ((5 : ℝ) ^ (6 : ℕ)) ^ (1 / 6 : ℝ) :=
      Real.rpow_le_rpow hpi.le h4 (by norm_num)
    have hval : ((5 : ℝ) ^ (6 : ℕ)) ^ (1 / 6 : ℝ) = 5 := by
      rw [← Real.rpow_natCast (5 : ℝ) 6, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 5)]
      norm_num
    linarith [hmono, hval.le, hval.ge]
  have hsqrt : Real.sqrt (4 * (A : ℝ)) = 2 * (A : ℝ) ^ (1 / 2 : ℝ) := by
    rw [show (4 : ℝ) * (A : ℝ) = 2 ^ 2 * (A : ℝ) by norm_num,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2),
      Real.sqrt_eq_rpow]
  have hApow : (A : ℝ) ^ (1 / 2 : ℝ) * (A : ℝ) ^ (-(4 * -(1 / 6 : ℝ))) = (A : ℝ) ^ (7 / 6 : ℝ) := by
    rw [← Real.rpow_add hA0]
    norm_num
  have hnn : (0 : ℝ) ≤ 43776 * (A : ℝ) ^ (7 / 6 : ℝ) * (T * r) ^ (-(1 / 6 : ℝ)) := by
    have h1 : (0 : ℝ) ≤ (A : ℝ) ^ (7 / 6 : ℝ) := Real.rpow_nonneg hA0.le _
    have h2 : (0 : ℝ) ≤ (T * r) ^ (-(1 / 6 : ℝ)) := Real.rpow_nonneg hX.le _
    positivity
  have hkey : 16 * 1368 * (2 * (A : ℝ) ^ (1 / 2 : ℝ))
      * ((T * r) ^ (-(1 / 6 : ℝ)) * (1152 * Real.pi) ^ (-(-(1 / 6 : ℝ)))
        * (A : ℝ) ^ (-(4 * -(1 / 6 : ℝ))))
      = (43776 * (A : ℝ) ^ (7 / 6 : ℝ) * (T * r) ^ (-(1 / 6 : ℝ)))
        * (1152 * Real.pi) ^ (-(-(1 / 6 : ℝ))) := by
    rw [← hApow]
    ring
  rw [hsqrt, hkey]
  calc (43776 * (A : ℝ) ^ (7 / 6 : ℝ) * (T * r) ^ (-(1 / 6 : ℝ)))
        * (1152 * Real.pi) ^ (-(-(1 / 6 : ℝ)))
      ≤ (43776 * (A : ℝ) ^ (7 / 6 : ℝ) * (T * r) ^ (-(1 / 6 : ℝ))) * 5 :=
        mul_le_mul_of_nonneg_left hconst hnn
    _ = 218880 * (A : ℝ) ^ (7 / 6 : ℝ) * (T * r) ^ (-(1 / 6 : ℝ)) := by ring


theorem rpow_div_mul {X c : ℝ} (hX : 0 < X) (hc : 0 < c) {A : ℕ} (hA : 1 ≤ A) (e : ℝ) :
    (X / (c * (A : ℝ))) ^ e = X ^ e * c ^ (-e) * (A : ℝ) ^ (-e) := by
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hden : (0 : ℝ) < c * (A : ℝ) := by positivity
  rw [Real.div_rpow hX.le hden.le, Real.mul_rpow hc.le hA0.le,
    Real.rpow_neg hc.le, Real.rpow_neg hA0.le]
  field_simp

/-- The fibre kernel is `≤ 250 · X^{1/2} A^{-1/2}`. -/
theorem fibreKernel_le_power {T r : ℝ} (hT : 0 < T) (hr : 0 < r) {A : ℕ} (hA : 1 ≤ A) :
    fibreKernel T r A ≤ 250 * (T * r) ^ (1 / 2 : ℝ) * (A : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hX : (0 : ℝ) < T * r := by positivity
  have hpi : (0 : ℝ) < 36 * Real.pi := by positivity
  rw [fibreKernel, Real.sqrt_eq_rpow, rpow_div_mul hX hpi hA]
  have hconst : (36 * Real.pi : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 / 10 := by
    rw [Real.rpow_neg hpi.le]
    have h100 : (100 : ℝ) ≤ 36 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hmono : (100 : ℝ) ^ (1 / 2 : ℝ) ≤ (36 * Real.pi) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) h100 (by norm_num)
    have hval : (100 : ℝ) ^ (1 / 2 : ℝ) = 10 := by
      rw [show (100 : ℝ) = 10 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast (10 : ℝ) 2,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 10)]
      norm_num
    have hge : (10 : ℝ) ≤ (36 * Real.pi) ^ (1 / 2 : ℝ) := by linarith [hmono, hval.le, hval.ge]
    have hpos : (0 : ℝ) < (36 * Real.pi) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hpi _
    rw [inv_le_iff_one_le_mul₀ hpos]
    nlinarith [hge]
  have hnn : (0 : ℝ) ≤ 2500 * ((T * r) ^ (1 / 2 : ℝ) * (A : ℝ) ^ (-(1 / 2 : ℝ))) := by
    have h1 : (0 : ℝ) ≤ (T * r) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hX.le _
    have h2 : (0 : ℝ) ≤ (A : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hA0.le _
    positivity
  calc 2500 * ((T * r) ^ (1 / 2 : ℝ) * (36 * Real.pi) ^ (-(1 / 2 : ℝ))
        * (A : ℝ) ^ (-(1 / 2 : ℝ)))
      = (2500 * ((T * r) ^ (1 / 2 : ℝ) * (A : ℝ) ^ (-(1 / 2 : ℝ))))
        * (36 * Real.pi) ^ (-(1 / 2 : ℝ)) := by ring
    _ ≤ (2500 * ((T * r) ^ (1 / 2 : ℝ) * (A : ℝ) ^ (-(1 / 2 : ℝ)))) * (1 / 10) :=
        mul_le_mul_of_nonneg_left hconst hnn
    _ = 250 * (T * r) ^ (1 / 2 : ℝ) * (A : ℝ) ^ (-(1 / 2 : ℝ)) := by ring


/-- **The mixed main coefficient is `≤ 10^5 · A^{1/3} X^{1/6}`.** -/
theorem secondThirdMixedFibreMainCoefficient_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A : ℕ} (hA : 1 ≤ A) :
    secondThirdMixedFibreMainCoefficient T r A
      ≤ 100000 * (A : ℝ) ^ (1 / 3 : ℝ) * (T * r) ^ (1 / 6 : ℝ) := by
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hX : (0 : ℝ) < T * r := by positivity
  have hXh : (0 : ℝ) < (T * r) ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hX _
  have hAh : (0 : ℝ) < (A : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hA0 _
  have h1 := sharpThirdDerivativeFibreFirstCoefficient_le hT hr hA
  have h2 := sharpThirdDerivativeFibreSecondCoefficient_le hT hr hA
  have hk := fibreKernel_le_power hT hr hA
  have h2nn : 0 ≤ sharpThirdDerivativeFibreSecondCoefficient T r A :=
    sharpThirdDerivativeFibreSecondCoefficient_nonneg hT hr hA
  have hbnn : (0 : ℝ) ≤ 250 * (T * r) ^ (1 / 2 : ℝ) * (A : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have ha : (0 : ℝ) ≤ (T * r) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hX.le _
    have hb : (0 : ℝ) ≤ (A : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hA0.le _
    positivity
  have hprod : fibreKernel T r A * sharpThirdDerivativeFibreSecondCoefficient T r A
      ≤ (250 * (T * r) ^ (1 / 2 : ℝ) * (A : ℝ) ^ (-(1 / 2 : ℝ)))
        * (218880 * (A : ℝ) ^ (7 / 6 : ℝ) * (T * r) ^ (-(1 / 6 : ℝ))) :=
    mul_le_mul hk h2 h2nn hbnn
  have hXid : (T * r) ^ (1 / 2 : ℝ) * (T * r) ^ (-(1 / 6 : ℝ))
      = ((T * r) ^ (1 / 6 : ℝ)) ^ 2 := by
    rw [← Real.rpow_add hX, ← Real.rpow_natCast ((T * r) ^ (1 / 6 : ℝ)) 2,
      ← Real.rpow_mul hX.le]
    norm_num
  have hAid : (A : ℝ) ^ (-(1 / 2 : ℝ)) * (A : ℝ) ^ (7 / 6 : ℝ)
      = ((A : ℝ) ^ (1 / 3 : ℝ)) ^ 2 := by
    rw [← Real.rpow_add hA0, ← Real.rpow_natCast ((A : ℝ) ^ (1 / 3 : ℝ)) 2,
      ← Real.rpow_mul hA0.le]
    norm_num
  have hsq : (250 * (T * r) ^ (1 / 2 : ℝ) * (A : ℝ) ^ (-(1 / 2 : ℝ)))
        * (218880 * (A : ℝ) ^ (7 / 6 : ℝ) * (T * r) ^ (-(1 / 6 : ℝ)))
      = 54720000 * ((T * r) ^ (1 / 6 : ℝ) * (A : ℝ) ^ (1 / 3 : ℝ)) ^ 2 := by
    have hexp : (250 * (T * r) ^ (1 / 2 : ℝ) * (A : ℝ) ^ (-(1 / 2 : ℝ)))
        * (218880 * (A : ℝ) ^ (7 / 6 : ℝ) * (T * r) ^ (-(1 / 6 : ℝ)))
        = 54720000 * (((T * r) ^ (1 / 2 : ℝ) * (T * r) ^ (-(1 / 6 : ℝ)))
          * ((A : ℝ) ^ (-(1 / 2 : ℝ)) * (A : ℝ) ^ (7 / 6 : ℝ))) := by ring
    rw [hexp, hXid, hAid]
    ring
  have hsqrtle : Real.sqrt (fibreKernel T r A * sharpThirdDerivativeFibreSecondCoefficient T r A)
      ≤ 7398 * ((T * r) ^ (1 / 6 : ℝ) * (A : ℝ) ^ (1 / 3 : ℝ)) := by
    refine le_trans (Real.sqrt_le_sqrt hprod) ?_
    rw [hsq]
    have hy : (0 : ℝ) ≤ (T * r) ^ (1 / 6 : ℝ) * (A : ℝ) ^ (1 / 3 : ℝ) := by positivity
    have hid : (54720000 : ℝ) * ((T * r) ^ (1 / 6 : ℝ) * (A : ℝ) ^ (1 / 3 : ℝ)) ^ 2
        ≤ (7398 * ((T * r) ^ (1 / 6 : ℝ) * (A : ℝ) ^ (1 / 3 : ℝ))) ^ 2 := by
      nlinarith only [hy, sq_nonneg ((T * r) ^ (1 / 6 : ℝ) * (A : ℝ) ^ (1 / 3 : ℝ))]
    calc Real.sqrt (54720000 * ((T * r) ^ (1 / 6 : ℝ) * (A : ℝ) ^ (1 / 3 : ℝ)) ^ 2)
        ≤ Real.sqrt ((7398 * ((T * r) ^ (1 / 6 : ℝ) * (A : ℝ) ^ (1 / 3 : ℝ))) ^ 2) :=
          Real.sqrt_le_sqrt hid
      _ = 7398 * ((T * r) ^ (1 / 6 : ℝ) * (A : ℝ) ^ (1 / 3 : ℝ)) :=
          Real.sqrt_sq (by positivity)
  rw [secondThirdMixedFibreMainCoefficient]
  nlinarith only [h1, hsqrtle, hXh, hAh]


/-- The fibre tail is `≤ 748 · B^{3/2} X^{-1/2}`. -/
theorem fibreTail_le_power {T r : ℝ} (hT : 0 < T) (hr : 0 < r) {B : ℕ} (hB : 1 ≤ B) :
    fibreTail T r B ≤ 748 * (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2 : ℝ)) := by
  have hB0 : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hX : (0 : ℝ) < T * r := by positivity
  have hpi : (0 : ℝ) < 288 * Real.pi := by positivity
  have hrew : 36 * Real.pi * (2 * (B : ℝ)) ^ 3 / (T * r)
      = 288 * Real.pi * (B : ℝ) ^ 3 / (T * r) := by ring
  rw [fibreTail, hrew, Real.sqrt_eq_rpow]
  have hsplit : (288 * Real.pi * (B : ℝ) ^ 3 / (T * r)) ^ (1 / 2 : ℝ)
      = (288 * Real.pi) ^ (1 / 2 : ℝ) * (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2 : ℝ)) := by
    have hnum : (0 : ℝ) < 288 * Real.pi * (B : ℝ) ^ 3 := by positivity
    rw [Real.div_rpow hnum.le hX.le, Real.mul_rpow hpi.le (by positivity)]
    have hBpow : ((B : ℝ) ^ 3) ^ (1 / 2 : ℝ) = (B : ℝ) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast (B : ℝ) 3, ← Real.rpow_mul hB0.le]
      norm_num
    rw [hBpow, Real.rpow_neg hX.le]
    field_simp
  rw [hsplit]
  have hconst : (288 * Real.pi : ℝ) ^ (1 / 2 : ℝ) ≤ 34 := by
    have h4 : (288 * Real.pi : ℝ) ≤ 34 ^ (2 : ℕ) := by
      have hp : Real.pi ≤ 4 := Real.pi_le_four
      norm_num
      nlinarith [hp]
    have hmono : (288 * Real.pi : ℝ) ^ (1 / 2 : ℝ) ≤ ((34 : ℝ) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hpi.le h4 (by norm_num)
    have hval : ((34 : ℝ) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = 34 := by
      rw [← Real.rpow_natCast (34 : ℝ) 2, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 34)]
      norm_num
    linarith [hmono, hval.le, hval.ge]
  have hnn : (0 : ℝ) ≤ (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2 : ℝ)) := by
    have h1 : (0 : ℝ) ≤ (B : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hB0.le _
    have h2 : (0 : ℝ) ≤ (T * r) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hX.le _
    positivity
  calc 22 * ((288 * Real.pi) ^ (1 / 2 : ℝ) * (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2 : ℝ)))
      = (22 * ((B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2 : ℝ))))
        * (288 * Real.pi) ^ (1 / 2 : ℝ) := by ring
    _ ≤ (22 * ((B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2 : ℝ)))) * 34 :=
        mul_le_mul_of_nonneg_left hconst (by positivity)
    _ = 748 * (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2 : ℝ)) := by ring


/-- The explicit power form of the hybrid Type-II root envelope. -/
def kubalalikaRootPower (T r : ℝ) (B U V : ℕ) : ℝ :=
  (B : ℝ) * (V : ℝ) ^ (-(1 / 2) : ℝ)
    + 64 * (T * r) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (3 / 4 : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ)
    + 9 * (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ) * Real.sqrt (1 + Real.log B)
    + 2 * (B : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ)

theorem sqrt_sq_div_le {B V : ℕ} (hV : 1 ≤ V) :
    Real.sqrt ((B : ℝ) ^ 2 / V) = (B : ℝ) * (V : ℝ) ^ (-(1 / 2) : ℝ) := by
  have hV0 : (0 : ℝ) < (V : ℝ) := by exact_mod_cast hV
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg _
  rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hB0, Real.sqrt_eq_rpow,
    Real.rpow_neg hV0.le]
  field_simp

theorem sqrt_two_sq_div_le {B U : ℕ} (hU : 1 ≤ U) :
    Real.sqrt (2 * (B : ℝ) ^ 2 / U) ≤ 2 * (B : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ) := by
  have hU0 : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg _
  have hid : (2 : ℝ) * (B : ℝ) ^ 2 / U ≤ (2 * (B : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ)) ^ 2 := by
    have hUp : (U : ℝ) ^ (-(1 / 2) : ℝ) = ((U : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
      rw [Real.rpow_neg hU0.le]
    have hUsq : ((U : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (U : ℝ) := by
      rw [← Real.rpow_natCast ((U : ℝ) ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hU0.le]
      norm_num
    have hUpos : (0 : ℝ) < (U : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hU0 _
    rw [hUp, mul_pow, mul_pow, inv_pow, hUsq, div_le_iff₀ hU0]
    field_simp
    nlinarith only [hB0, hU0, sq_nonneg (B : ℝ)]
  calc Real.sqrt (2 * (B : ℝ) ^ 2 / U)
      ≤ Real.sqrt ((2 * (B : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ)) ^ 2) := Real.sqrt_le_sqrt hid
    _ = 2 * (B : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ) := Real.sqrt_sq (by positivity)


theorem rpow_sq_half {x : ℝ} (hx : 0 < x) (e : ℝ) : (x ^ e) ^ 2 = x ^ (2 * e) := by
  rw [← Real.rpow_natCast (x ^ e) 2, ← Real.rpow_mul hx.le]
  norm_num
  ring_nf

theorem sqrt_vaughan_second_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r) {A B U : ℕ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hU : 1 ≤ U) (hBA : B ≤ 2 * A) :
    Real.sqrt (2000 * Real.sqrt (T * r) * (B : ℝ) ^ 2 * Real.sqrt B / ((A : ℝ) * U))
      ≤ 64 * (T * r) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (3 / 4 : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ) := by
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hB0 : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hU0 : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU
  have hX : (0 : ℝ) < T * r := by positivity
  have hBA' : (B : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast hBA
  have hsqX : Real.sqrt (T * r) = (T * r) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hsqB : Real.sqrt (B : ℝ) = (B : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hBsq : (B : ℝ) ^ 2 * (B : ℝ) ^ (1 / 2 : ℝ) = (B : ℝ) ^ (5 / 2 : ℝ) := by
    rw [← Real.rpow_natCast (B : ℝ) 2, ← Real.rpow_add hB0]
    norm_num
  have hTarget : (64 * (T * r) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (3 / 4 : ℝ)
      * (U : ℝ) ^ (-(1 / 2) : ℝ)) ^ 2
      = 4096 * (T * r) ^ (1 / 2 : ℝ) * (B : ℝ) ^ (3 / 2 : ℝ) * (U : ℝ) ^ (-(1 : ℝ)) := by
    rw [mul_pow, mul_pow, mul_pow, rpow_sq_half hX, rpow_sq_half hB0, rpow_sq_half hU0]
    norm_num
  have hUinv : (U : ℝ) ^ (-(1 : ℝ)) = ((U : ℝ))⁻¹ := by
    rw [Real.rpow_neg hU0.le, Real.rpow_one]
  have hinner : 2000 * (T * r) ^ (1 / 2 : ℝ) * (B : ℝ) ^ 2 * (B : ℝ) ^ (1 / 2 : ℝ)
        / ((A : ℝ) * U)
      ≤ 4096 * (T * r) ^ (1 / 2 : ℝ) * (B : ℝ) ^ (3 / 2 : ℝ) * (U : ℝ) ^ (-(1 : ℝ)) := by
    rw [hUinv]
    have hnum : 2000 * (T * r) ^ (1 / 2 : ℝ) * (B : ℝ) ^ 2 * (B : ℝ) ^ (1 / 2 : ℝ)
        = 2000 * (T * r) ^ (1 / 2 : ℝ) * (B : ℝ) ^ (5 / 2 : ℝ) := by
      rw [mul_assoc (2000 * (T * r) ^ (1 / 2 : ℝ)), hBsq]
    rw [hnum, div_le_iff₀ (by positivity)]
    have hBpow : (B : ℝ) ^ (5 / 2 : ℝ) = (B : ℝ) ^ (3 / 2 : ℝ) * (B : ℝ) := by
      have hadd := Real.rpow_add hB0 (3 / 2 : ℝ) 1
      rw [Real.rpow_one] at hadd
      rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, hadd]
    have hXnn : (0 : ℝ) ≤ (T * r) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hX.le _
    have hBnn : (0 : ℝ) ≤ (B : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hB0.le _
    rw [hBpow]
    have hkey : (B : ℝ) ≤ 2 * (A : ℝ) := hBA'
    have hfac : 4096 * (T * r) ^ (1 / 2 : ℝ) * (B : ℝ) ^ (3 / 2 : ℝ) * (U : ℝ)⁻¹
        * ((A : ℝ) * U) = 4096 * (T * r) ^ (1 / 2 : ℝ) * (B : ℝ) ^ (3 / 2 : ℝ) * (A : ℝ) := by
      field_simp
    rw [hfac]
    have hc : (0 : ℝ) ≤ (T * r) ^ (1 / 2 : ℝ) * (B : ℝ) ^ (3 / 2 : ℝ) := mul_nonneg hXnn hBnn
    have hstep := mul_le_mul_of_nonneg_left hkey hc
    have hPQA : (0 : ℝ) ≤ (T * r) ^ (1 / 2 : ℝ) * (B : ℝ) ^ (3 / 2 : ℝ) * (A : ℝ) :=
      mul_nonneg hc hA0.le
    nlinarith only [hstep, hPQA]
  have hrw : 2000 * Real.sqrt (T * r) * (B : ℝ) ^ 2 * Real.sqrt B / ((A : ℝ) * U)
      = 2000 * (T * r) ^ (1 / 2 : ℝ) * (B : ℝ) ^ 2 * (B : ℝ) ^ (1 / 2 : ℝ) / ((A : ℝ) * U) := by
    rw [hsqX, hsqB]
  rw [hrw]
  calc Real.sqrt (2000 * (T * r) ^ (1 / 2 : ℝ) * (B : ℝ) ^ 2 * (B : ℝ) ^ (1 / 2 : ℝ)
        / ((A : ℝ) * U))
      ≤ Real.sqrt ((64 * (T * r) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (3 / 4 : ℝ)
          * (U : ℝ) ^ (-(1 / 2) : ℝ)) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [hTarget]
        exact hinner
    _ = 64 * (T * r) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (3 / 4 : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ) :=
        Real.sqrt_sq (by positivity)


theorem sqrt_vaughan_third_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r) {B : ℕ} (hB : 1 ≤ B) :
    Real.sqrt (20 * Real.pi * (B : ℝ) ^ 3 / (T * r) * invSum B)
      ≤ 9 * (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ) * Real.sqrt (1 + Real.log B) := by
  have hB0 : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hX : (0 : ℝ) < T * r := by positivity
  have hlog : (0 : ℝ) ≤ Real.log B := Real.log_nonneg hB1
  have hlog1 : (0 : ℝ) ≤ 1 + Real.log B := by linarith
  have hinv := invSum_le_one_add_log hB
  have hinvnn : (0 : ℝ) ≤ invSum B := invSum_nonneg B
  have hBsq : ((B : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = (B : ℝ) ^ 3 := by
    rw [rpow_sq_half hB0, ← Real.rpow_natCast (B : ℝ) 3]
    norm_num
  have hXsq : ((T * r) ^ (-(1 / 2) : ℝ)) ^ 2 = ((T * r))⁻¹ := by
    rw [rpow_sq_half hX, show (2 : ℝ) * (-(1 / 2)) = -1 by norm_num,
      Real.rpow_neg hX.le, Real.rpow_one]
  have hlsq : (Real.sqrt (1 + Real.log B)) ^ 2 = 1 + Real.log B := Real.sq_sqrt hlog1
  have hTarget : (9 * (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ)
      * Real.sqrt (1 + Real.log B)) ^ 2
      = 81 * (B : ℝ) ^ 3 * ((T * r))⁻¹ * (1 + Real.log B) := by
    rw [mul_pow, mul_pow, mul_pow, hBsq, hXsq, hlsq]
    norm_num
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hinner : 20 * Real.pi * (B : ℝ) ^ 3 / (T * r) * invSum B
      ≤ 81 * (B : ℝ) ^ 3 * ((T * r))⁻¹ * (1 + Real.log B) := by
    have hB3 : (0 : ℝ) ≤ (B : ℝ) ^ 3 := by positivity
    have hXi : (0 : ℝ) < ((T * r))⁻¹ := by positivity
    have h1 : 20 * Real.pi * (B : ℝ) ^ 3 / (T * r) * invSum B
        ≤ 80 * (B : ℝ) ^ 3 * ((T * r))⁻¹ * invSum B := by
      rw [div_eq_mul_inv]
      have hfac : (0 : ℝ) ≤ (B : ℝ) ^ 3 * ((T * r))⁻¹ * invSum B := by positivity
      have hprod : (0 : ℝ) ≤ (80 - 20 * Real.pi) * ((B : ℝ) ^ 3 * ((T * r))⁻¹ * invSum B) :=
        mul_nonneg (by linarith) hfac
      nlinarith only [hprod]
    have h2 : 80 * (B : ℝ) ^ 3 * ((T * r))⁻¹ * invSum B
        ≤ 80 * (B : ℝ) ^ 3 * ((T * r))⁻¹ * (1 + Real.log B) := by
      have hc : (0 : ℝ) ≤ 80 * (B : ℝ) ^ 3 * ((T * r))⁻¹ := by positivity
      exact mul_le_mul_of_nonneg_left hinv hc
    have h3 : 80 * (B : ℝ) ^ 3 * ((T * r))⁻¹ * (1 + Real.log B)
        ≤ 81 * (B : ℝ) ^ 3 * ((T * r))⁻¹ * (1 + Real.log B) := by
      have hc : (0 : ℝ) ≤ (B : ℝ) ^ 3 * ((T * r))⁻¹ * (1 + Real.log B) := by positivity
      nlinarith only [hc]
    linarith
  calc Real.sqrt (20 * Real.pi * (B : ℝ) ^ 3 / (T * r) * invSum B)
      ≤ Real.sqrt ((9 * (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ)
          * Real.sqrt (1 + Real.log B)) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [hTarget]
        exact hinner
    _ = 9 * (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ) * Real.sqrt (1 + Real.log B) :=
        Real.sqrt_sq (by positivity)

/-- **The hybrid Type-II root envelope in explicit power form.** -/
theorem typeIIHybridVaughanRootEnvelope_le_power {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B U V : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hU : 1 ≤ U) (hV : 1 ≤ V) (hBA : B ≤ 2 * A) :
    typeIIHybridVaughanRootEnvelope T r A B U V ≤ kubalalikaRootPower T r B U V := by
  rw [typeIIHybridVaughanRootEnvelope, kubalalikaRootPower]
  have h1 := sqrt_sq_div_le (B := B) hV
  have h2 := sqrt_vaughan_second_le hT hr hA hB hU hBA
  have h3 := sqrt_vaughan_third_le hT hr hB
  have h4 := sqrt_two_sq_div_le (B := B) hU
  linarith [h1.le, h1.ge, h2, h3, h4]

end

end RHTower.Sieve

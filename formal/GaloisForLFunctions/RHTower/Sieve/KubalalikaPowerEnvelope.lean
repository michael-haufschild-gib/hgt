import GaloisForLFunctions.RHTower.Sieve.VaughanSecondThirdMixedHybridBlock

/-!
# Explicit power envelopes for the Kubalalika block estimate

The mixed second/third-derivative Vaughan block envelope is bounded by an explicit monomial in
`A`, `B` and `X = T r`.  Every constant is elementary: `(72π)^{-1/6} ≤ 1`, `√(36π) ≥ 10`,
`(1152π)^{1/6} ≤ 4`, `√(288π) ≤ 31`, `√(20π) ≤ 8` and `√4000 ≤ 64`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction RHTower

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


/-! ### The dyadic block count -/

theorem natLogTwo_succ_le_two_mul_one_add_log {N : ℕ} (hN : 1 ≤ N) :
    ((Nat.log 2 N : ℝ) + 1) ≤ 2 * (1 + Real.log N) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpowNat : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hpow : ((2 : ℝ)) ^ (Nat.log 2 N) ≤ (N : ℝ) := by exact_mod_cast hpowNat
  have hlog : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
    have h := Real.log_le_log (by positivity) hpow
    rwa [Real.log_pow] at h
  have h2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hnn : (0 : ℝ) ≤ (Nat.log 2 N : ℝ) := Nat.cast_nonneg _
  have hlogN : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN1
  nlinarith only [hlog, h2, hnn, hlogN]

/-! ### The explicit power envelope of the mixed hybrid Vaughan block -/

/-- The explicit monomial envelope of the mixed second/third-derivative hybrid Vaughan block. -/
def kubalalikaBlockPower (D T r : ℝ) (A B U V : ℕ) : ℝ :=
  D * (1 + Real.log B) ^ 4 *
    ((A : ℝ) ^ (1 / 3 : ℝ) * (T * r) ^ (1 / 6 : ℝ) * Real.sqrt (U * V)
      + (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ)
      + (B : ℝ) * (V : ℝ) ^ (-(1 / 2) : ℝ)
      + (T * r) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (3 / 4 : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ)
      + (B : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ))

/-- The scalar shape of the Type-I total: two aggregates weighted by logarithms. -/
theorem typeI_scalar_bound {s a b p q : ℝ} (hs : 1 ≤ s) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (_hla : 0 ≤ a) (_hlb : 0 ≤ b)
    (hA1 : a ≤ 400000 * p + 748 * q * s) (hA2 : b ≤ 400000 * p + 748 * q * s) :
    s * a + 2 * s * b ≤ 1200000 * s ^ 2 * (p + q) := by
  have hs0 : (0 : ℝ) ≤ s := le_trans zero_le_one hs
  have h1 : s * a ≤ s * (400000 * p + 748 * q * s) := mul_le_mul_of_nonneg_left hA1 hs0
  have h2 : 2 * s * b ≤ 2 * s * (400000 * p + 748 * q * s) :=
    mul_le_mul_of_nonneg_left hA2 (by positivity)
  have hss : s ≤ s ^ 2 := by nlinarith only [hs, hs0]
  have hsp : 1200000 * s * p ≤ 1200000 * s ^ 2 * p := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hss (by norm_num : (0:ℝ) ≤ 1200000)) hp
    linarith
  have hsq : 2244 * q * s ^ 2 ≤ 1200000 * s ^ 2 * q := by
    have hsqn : (0 : ℝ) ≤ s ^ 2 := sq_nonneg s
    nlinarith only [hq, hsqn]
  nlinarith only [h1, h2, hsp, hsq]

/-- **The Type-I total in explicit power form.** -/
theorem secondThirdMixedVaughanTypeIEnvelope_le_power {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B U V : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) (hU : 1 ≤ U) (hV : 1 ≤ V) (hUVB : U * V ≤ B) :
    secondThirdMixedVaughanTypeIEnvelope T r A B U V
      ≤ 1200000 * (1 + Real.log B) ^ 2 *
          ((A : ℝ) ^ (1 / 3 : ℝ) * (T * r) ^ (1 / 6 : ℝ) * Real.sqrt (U * V)
            + (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ)) := by
  have hB : 1 ≤ B := le_trans hA hAB
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hUV1 : 1 ≤ U * V := by simpa using Nat.mul_le_mul hU hV
  have hUV1R : (1 : ℝ) ≤ ((U * V : ℕ) : ℝ) := by exact_mod_cast hUV1
  have hV1R : (1 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV
  have hUVB' : ((U * V : ℕ) : ℝ) ≤ (B : ℝ) := by exact_mod_cast hUVB
  have hVB : V ≤ B := le_trans (by simpa [mul_comm] using Nat.mul_le_mul_left V hU) hUVB
  have hVB' : (V : ℝ) ≤ (B : ℝ) := by exact_mod_cast hVB
  set s : ℝ := 1 + Real.log B with hsdef
  have hlogB : (0 : ℝ) ≤ Real.log B := Real.log_nonneg hB1
  have hs : (1 : ℝ) ≤ s := by rw [hsdef]; linarith
  set P : ℝ := (A : ℝ) ^ (1 / 3 : ℝ) * (T * r) ^ (1 / 6 : ℝ) * Real.sqrt (U * V) with hPdef
  set Q : ℝ := (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ) with hQdef
  have hP0 : (0 : ℝ) ≤ P := by rw [hPdef]; positivity
  have hQ0 : (0 : ℝ) ≤ Q := by rw [hQdef]; positivity
  -- the two logarithmic weights
  have hlogUV : Real.log ((U * V : ℕ) : ℝ) ≤ s := by
    have := Real.log_le_log (by positivity) hUVB'
    rw [hsdef]; linarith
  have hlogUV0 : (0 : ℝ) ≤ Real.log ((U * V : ℕ) : ℝ) := Real.log_nonneg hUV1R
  -- coefficient bounds
  have hC1 : 0 ≤ secondThirdMixedFibreMainCoefficient T r A := by
    rw [secondThirdMixedFibreMainCoefficient]
    exact add_nonneg (sharpThirdDerivativeFibreFirstCoefficient_nonneg hT hr hA)
      (Real.sqrt_nonneg _)
  have hC1le := secondThirdMixedFibreMainCoefficient_le hT hr hA
  have hFt0 : 0 ≤ fibreTail T r B := fibreTail_nonneg T r B
  have hFtle := fibreTail_le_power hT hr hB
  have hFtle' : fibreTail T r B ≤ 748 * Q := by rw [hQdef]; linarith [hFtle]
  -- the two square roots
  have hsqUV : Real.sqrt ((U * V : ℕ) : ℝ) = Real.sqrt ((U : ℝ) * (V : ℝ)) := by
    push_cast; ring_nf
  have hsqV : Real.sqrt (V : ℝ) ≤ Real.sqrt ((U : ℝ) * (V : ℝ)) := by
    refine Real.sqrt_le_sqrt ?_
    have hU1R : (1 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU
    nlinarith only [hU1R, hV1R]
  have hAX : (0 : ℝ) ≤ (A : ℝ) ^ (1 / 3 : ℝ) * (T * r) ^ (1 / 6 : ℝ) := by positivity
  -- the two aggregates
  have hAgg : ∀ K : ℕ, 1 ≤ K → Real.sqrt K ≤ Real.sqrt ((U : ℝ) * (V : ℝ)) →
      ((K : ℝ)) ≤ (B : ℝ) →
      secondThirdMixedAggregateEnvelope T r A B K ≤ 400000 * P + 748 * Q * s := by
    intro K hK hKsq hKB
    have hinv : invSum K ≤ 1 + Real.log K := invSum_le_one_add_log hK
    have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    have hlogK : Real.log K ≤ Real.log B := Real.log_le_log (by positivity) hKB
    have hinvs : invSum K ≤ s := by rw [hsdef]; linarith
    have hinv0 : (0 : ℝ) ≤ invSum K := invSum_nonneg K
    have hstep1 : 4 * secondThirdMixedFibreMainCoefficient T r A * Real.sqrt K
        ≤ 400000 * P := by
      have h1 : 4 * secondThirdMixedFibreMainCoefficient T r A
          ≤ 400000 * ((A : ℝ) ^ (1 / 3 : ℝ) * (T * r) ^ (1 / 6 : ℝ)) := by
        nlinarith only [hC1le]
      have h2 : (0 : ℝ) ≤ 4 * secondThirdMixedFibreMainCoefficient T r A := by linarith
      calc 4 * secondThirdMixedFibreMainCoefficient T r A * Real.sqrt K
          ≤ 400000 * ((A : ℝ) ^ (1 / 3 : ℝ) * (T * r) ^ (1 / 6 : ℝ)) * Real.sqrt K :=
            mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
        _ ≤ 400000 * ((A : ℝ) ^ (1 / 3 : ℝ) * (T * r) ^ (1 / 6 : ℝ))
              * Real.sqrt ((U : ℝ) * (V : ℝ)) :=
            mul_le_mul_of_nonneg_left hKsq (by positivity)
        _ = 400000 * P := by rw [hPdef]; ring
    have hstep2 : fibreTail T r B * invSum K ≤ 748 * Q * s := by
      calc fibreTail T r B * invSum K ≤ (748 * Q) * invSum K :=
            mul_le_mul_of_nonneg_right hFtle' hinv0
        _ ≤ (748 * Q) * s := mul_le_mul_of_nonneg_left hinvs (by positivity)
        _ = 748 * Q * s := by ring
    rw [secondThirdMixedAggregateEnvelope]
    linarith
  have hUVsq : Real.sqrt ((U * V : ℕ) : ℝ) ≤ Real.sqrt ((U : ℝ) * (V : ℝ)) := by
    push_cast
    exact le_rfl
  have hAggUV := hAgg (U * V) hUV1 hUVsq hUVB'
  have hAggV := hAgg V hV hsqV hVB'
  have hnn1 : (0 : ℝ) ≤ secondThirdMixedAggregateEnvelope T r A B (U * V) := by
    rw [secondThirdMixedAggregateEnvelope]
    exact add_nonneg (by positivity) (mul_nonneg hFt0 (invSum_nonneg _))
  have hnn2 : (0 : ℝ) ≤ secondThirdMixedAggregateEnvelope T r A B V := by
    rw [secondThirdMixedAggregateEnvelope]
    exact add_nonneg (by positivity) (mul_nonneg hFt0 (invSum_nonneg _))
  rw [secondThirdMixedVaughanTypeIEnvelope]
  have hbase := typeI_scalar_bound (s := s) hs hP0 hQ0 hnn1 hnn2 hAggUV hAggV
  have hw1 : Real.log ((U * V : ℕ) : ℝ) * secondThirdMixedAggregateEnvelope T r A B (U * V)
      ≤ s * secondThirdMixedAggregateEnvelope T r A B (U * V) :=
    mul_le_mul_of_nonneg_right hlogUV hnn1
  have hw2 : 2 * Real.log B * secondThirdMixedAggregateEnvelope T r A B V
      ≤ 2 * s * secondThirdMixedAggregateEnvelope T r A B V := by
    refine mul_le_mul_of_nonneg_right ?_ hnn2
    rw [hsdef]; linarith
  have hcast : Real.log ((U : ℕ) * (V : ℕ) : ℕ) = Real.log ((U * V : ℕ) : ℝ) := by norm_num
  push_cast at hw1 ⊢
  linarith

theorem sqrt_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
  calc Real.sqrt x ≤ Real.sqrt (x ^ 2) := Real.sqrt_le_sqrt (by nlinarith only [hx, hx0])
    _ = x := Real.sqrt_sq hx0

/-- The root envelope in a single logarithmic power. -/
theorem kubalalikaRootPower_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r) {B U V : ℕ} (hB : 1 ≤ B) :
    kubalalikaRootPower T r B U V
      ≤ 64 * (1 + Real.log B) *
          ((B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ)
            + (B : ℝ) * (V : ℝ) ^ (-(1 / 2) : ℝ)
            + (T * r) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (3 / 4 : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ)
            + (B : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ)) := by
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hlogB : (0 : ℝ) ≤ Real.log B := Real.log_nonneg hB1
  set s : ℝ := 1 + Real.log B with hsdef
  have hs : (1 : ℝ) ≤ s := by rw [hsdef]; linarith
  have hsqrts : Real.sqrt s ≤ s := sqrt_le_self_of_one_le hs
  set P2 : ℝ := (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ) with hP2
  set P3 : ℝ := (B : ℝ) * (V : ℝ) ^ (-(1 / 2) : ℝ) with hP3
  set P4 : ℝ := (T * r) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (3 / 4 : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ) with hP4
  set P5 : ℝ := (B : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ) with hP5
  have h2 : (0 : ℝ) ≤ P2 := by rw [hP2]; positivity
  have h3 : (0 : ℝ) ≤ P3 := by rw [hP3]; positivity
  have h4 : (0 : ℝ) ≤ P4 := by rw [hP4]; positivity
  have h5 : (0 : ℝ) ≤ P5 := by rw [hP5]; positivity
  have hrew : kubalalikaRootPower T r B U V = P3 + 64 * P4 + 9 * P2 * Real.sqrt s + 2 * P5 := by
    rw [kubalalikaRootPower, hP2, hP3, hP4, hP5, hsdef]
    ring
  rw [hrew]
  have hkey : 9 * P2 * Real.sqrt s ≤ 9 * P2 * s :=
    mul_le_mul_of_nonneg_left hsqrts (by positivity)
  nlinarith only [hkey, h2, h3, h4, h5, hs]

/-- **The Type-II total in explicit power form.** -/
theorem typeIIHybridPieceEnvelope_le_power {C T r : ℝ} (hC : 0 < C) (hT : 0 < T) (hr : 0 < r)
    {A B U V : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hU : 1 ≤ U) (hV : 1 ≤ V) (hBA : B ≤ 2 * A) :
    typeIIHybridPieceEnvelope C T r A B B U V
      ≤ 512 * Real.sqrt C * (1 + Real.log B) ^ 4 *
          ((B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ)
            + (B : ℝ) * (V : ℝ) ^ (-(1 / 2) : ℝ)
            + (T * r) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (3 / 4 : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ)
            + (B : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ)) := by
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hlogB : (0 : ℝ) ≤ Real.log B := Real.log_nonneg hB1
  set s : ℝ := 1 + Real.log B with hsdef
  have hs : (1 : ℝ) ≤ s := by rw [hsdef]; linarith
  have hs0 : (0 : ℝ) ≤ s := le_trans zero_le_one hs
  set S : ℝ := (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ)
      + (B : ℝ) * (V : ℝ) ^ (-(1 / 2) : ℝ)
      + (T * r) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (3 / 4 : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ)
      + (B : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ) with hSdef
  have hS0 : (0 : ℝ) ≤ S := by rw [hSdef]; positivity
  -- the dyadic block count
  have h1 : ((Nat.log 2 B : ℝ) + 1) ≤ 2 * s := natLogTwo_succ_le_two_mul_one_add_log hB
  have h10 : (0 : ℝ) ≤ ((Nat.log 2 B : ℝ) + 1) := by positivity
  -- the polylogarithmic factor
  have hCs : (0 : ℝ) ≤ 4 * Real.sqrt C * s ^ 2 := by positivity
  have hsqC : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt hC.le
  have hrad : 8 * C * Real.log B * typeIIPolylogEnvelope B ≤ (4 * Real.sqrt C * s ^ 2) ^ 2 := by
    have hpoly : typeIIPolylogEnvelope B ≤ 2 * s ^ 3 := by
      rw [typeIIPolylogEnvelope, ← hsdef]
      have hs3 : (1 : ℝ) ≤ s ^ 3 := by
        nlinarith only [hs, hs0, mul_nonneg (sub_nonneg.2 hs) (mul_nonneg hs0 hs0)]
      linarith
    have hpoly0 : (0 : ℝ) ≤ typeIIPolylogEnvelope B := typeIIPolylogEnvelope_nonneg B
    have hstep1 : 8 * C * Real.log B ≤ 8 * C * s := by
      have : Real.log B ≤ s := by rw [hsdef]; linarith
      nlinarith only [this, hC]
    have hstep10 : (0 : ℝ) ≤ 8 * C * Real.log B := by positivity
    have hchain : 8 * C * Real.log B * typeIIPolylogEnvelope B ≤ (8 * C * s) * (2 * s ^ 3) := by
      calc 8 * C * Real.log B * typeIIPolylogEnvelope B
          ≤ (8 * C * s) * typeIIPolylogEnvelope B :=
            mul_le_mul_of_nonneg_right hstep1 hpoly0
        _ ≤ (8 * C * s) * (2 * s ^ 3) := mul_le_mul_of_nonneg_left hpoly (by positivity)
    have hval : (4 * Real.sqrt C * s ^ 2) ^ 2 = (8 * C * s) * (2 * s ^ 3) := by
      have : (4 * Real.sqrt C * s ^ 2) ^ 2 = 16 * (Real.sqrt C) ^ 2 * s ^ 4 := by ring
      rw [this, hsqC]; ring
    rw [hval]
    exact hchain
  have h2 : Real.sqrt (8 * C * Real.log B * typeIIPolylogEnvelope B)
      ≤ 4 * Real.sqrt C * s ^ 2 := by
    calc Real.sqrt (8 * C * Real.log B * typeIIPolylogEnvelope B)
        ≤ Real.sqrt ((4 * Real.sqrt C * s ^ 2) ^ 2) := Real.sqrt_le_sqrt hrad
      _ = 4 * Real.sqrt C * s ^ 2 := Real.sqrt_sq hCs
  have h20 : (0 : ℝ) ≤ Real.sqrt (8 * C * Real.log B * typeIIPolylogEnvelope B) :=
    Real.sqrt_nonneg _
  -- the root envelope
  have h3 : typeIIHybridVaughanRootEnvelope T r A B U V ≤ 64 * s * S := by
    refine le_trans (typeIIHybridVaughanRootEnvelope_le_power hT hr hA hB hU hV hBA) ?_
    rw [hSdef, hsdef]
    exact kubalalikaRootPower_le hT hr hB
  have h30 : (0 : ℝ) ≤ typeIIHybridVaughanRootEnvelope T r A B U V :=
    typeIIHybridVaughanRootEnvelope_nonneg T r A B U V
  rw [typeIIHybridPieceEnvelope]
  have hprod : Real.sqrt (8 * C * Real.log B * typeIIPolylogEnvelope B)
      * typeIIHybridVaughanRootEnvelope T r A B U V
      ≤ (4 * Real.sqrt C * s ^ 2) * (64 * s * S) :=
    mul_le_mul h2 h3 h30 hCs
  have hall : ((Nat.log 2 B : ℝ) + 1) *
      (Real.sqrt (8 * C * Real.log B * typeIIPolylogEnvelope B)
        * typeIIHybridVaughanRootEnvelope T r A B U V)
      ≤ (2 * s) * ((4 * Real.sqrt C * s ^ 2) * (64 * s * S)) :=
    mul_le_mul h1 hprod (mul_nonneg h20 h30) (by positivity)
  refine le_trans hall (le_of_eq ?_)
  ring

/-- **The mixed hybrid Vaughan block estimate in explicit monomial form.**

With the dyadic parameter taken equal to the block endpoint, the whole envelope collapses to a
single logarithmic power times the five monomials
`A^{1/3}X^{1/6}√(UV)`, `B^{3/2}X^{-1/2}`, `B V^{-1/2}`, `X^{1/4}B^{3/4}U^{-1/2}` and `B U^{-1/2}`,
where `X = T r`. -/
theorem exists_norm_sum_vonMangoldt_ndPhaseExp_le_kubalalika_power :
    ∃ D : ℝ, 0 < D ∧ ∀ {T r : ℝ} {A B U V : ℕ},
      0 < T → 0 < r → 1 ≤ A → A ≤ B → B ≤ 2 * A → 1 ≤ U → 1 ≤ V → U < A →
      U * V ≤ A → 8 * r ≤ (A : ℝ) →
      T * r * ((U * V : ℕ) : ℝ) ^ 3 ≤ 72 * Real.pi * (A : ℝ) ^ 4 →
      (∀ b ∈ Finset.Icc 1 (U * V),
        fibreKernel T r A ≤
            secondThirdMixedFibreMainCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ)) →
          nearDiagonalLambda T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1) →
      ‖∑ n ∈ Finset.Ico A B, ((vonMangoldt n : ℝ) : ℂ) * ndPhaseExp T r n‖
        ≤ kubalalikaBlockPower D T r A B U V := by
  obtain ⟨C, hC0, hblock⟩ := exists_norm_sum_vonMangoldt_ndPhaseExp_le_secondThird_mixed_hybrid
  refine ⟨1200000 + 512 * Real.sqrt C, by positivity, ?_⟩
  intro T r A B U V hT hr hA hAB hBA hU hV hUA hUVA h8 hcurv hsecond
  have hB : 1 ≤ B := le_trans hA hAB
  have hUVB : U * V ≤ B := le_trans hUVA hAB
  have hVUV : V ≤ U * V := by simpa [mul_comm] using Nat.mul_le_mul_left V hU
  have hVB : V ≤ B := le_trans hVUV hUVB
  have hbound := hblock (L := B) hT hr hA hAB hBA (by omega) hB hU hV hUA hUVA hUVB hVB h8
    hcurv hsecond
  refine le_trans hbound ?_
  have hI := secondThirdMixedVaughanTypeIEnvelope_le_power hT hr hA hAB hU hV hUVB
  have hII := typeIIHybridPieceEnvelope_le_power hC0 hT hr hA hB hU hV hBA
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hlogB : (0 : ℝ) ≤ Real.log B := Real.log_nonneg hB1
  rw [vaughanSecondThirdMixedHybridBlockEnvelope, kubalalikaBlockPower]
  set s : ℝ := 1 + Real.log B with hsdef
  set P1 : ℝ := (A : ℝ) ^ (1 / 3 : ℝ) * (T * r) ^ (1 / 6 : ℝ) * Real.sqrt (U * V) with hP1
  set P2 : ℝ := (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ) with hP2
  set P3 : ℝ := (B : ℝ) * (V : ℝ) ^ (-(1 / 2) : ℝ) with hP3
  set P4 : ℝ := (T * r) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (3 / 4 : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ) with hP4
  set P5 : ℝ := (B : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ) with hP5
  have hs : (1 : ℝ) ≤ s := by rw [hsdef]; linarith
  have hs0 : (0 : ℝ) ≤ s := le_trans zero_le_one hs
  have h1 : (0 : ℝ) ≤ P1 := by rw [hP1]; positivity
  have h2 : (0 : ℝ) ≤ P2 := by rw [hP2]; positivity
  have h3 : (0 : ℝ) ≤ P3 := by rw [hP3]; positivity
  have h4 : (0 : ℝ) ≤ P4 := by rw [hP4]; positivity
  have h5 : (0 : ℝ) ≤ P5 := by rw [hP5]; positivity
  have hs24 : s ^ 2 ≤ s ^ 4 := by
    nlinarith only [hs, hs0, sq_nonneg s, sq_nonneg (s ^ 2 - 1), sq_nonneg (s - 1)]
  have hsum : (0 : ℝ) ≤ P1 + P2 + P3 + P4 + P5 := by linarith
  have hstep1 : 1200000 * s ^ 2 * (P1 + P2)
      ≤ 1200000 * s ^ 4 * (P1 + P2 + P3 + P4 + P5) := by
    have ha : (1200000 : ℝ) * s ^ 2 ≤ 1200000 * s ^ 4 := by linarith
    have hb : P1 + P2 ≤ P1 + P2 + P3 + P4 + P5 := by linarith
    exact mul_le_mul ha hb (by linarith) (by positivity)
  have hstep2 : 512 * Real.sqrt C * s ^ 4 * (P2 + P3 + P4 + P5)
      ≤ 512 * Real.sqrt C * s ^ 4 * (P1 + P2 + P3 + P4 + P5) := by
    refine mul_le_mul_of_nonneg_left (by linarith) ?_
    positivity
  have hsplit : (1200000 + 512 * Real.sqrt C) * s ^ 4 * (P1 + P2 + P3 + P4 + P5)
      = 1200000 * s ^ 4 * (P1 + P2 + P3 + P4 + P5)
        + 512 * Real.sqrt C * s ^ 4 * (P1 + P2 + P3 + P4 + P5) := by ring
  linarith

end

end RHTower.Sieve

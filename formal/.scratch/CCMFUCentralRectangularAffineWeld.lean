import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeRectangularPrimitiveCurrent
import GaloisForLFunctions.RHTower.CCMFirstClockVolterra

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

private theorem centralPolarTriangleIntegral
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ h in (0 : ℝ)..t, (t - h) * (2 * Real.cosh (h / 2))) =
      8 * (Real.cosh (t / 2) - 1) := by
  let P : ℝ → ℝ := fun h =>
    4 * ((t - h) * Real.sinh (h / 2)) + 8 * Real.cosh (h / 2)
  have hP : ∀ h ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt P ((t - h) * (2 * Real.cosh (h / 2))) h := by
    intro h _hh
    have hlin : HasDerivAt (fun x : ℝ => t - x) (-1) h := by
      simpa using (hasDerivAt_id h).const_sub t
    have hsinh : HasDerivAt (fun x : ℝ => Real.sinh (x / 2))
        ((1 / 2 : ℝ) * Real.cosh (h / 2)) h := by
      apply ((Real.hasDerivAt_sinh (h / 2)).comp h
        ((hasDerivAt_id h).div_const 2)).congr_deriv
      ring
    have hcosh : HasDerivAt (fun x : ℝ => Real.cosh (x / 2))
        ((1 / 2 : ℝ) * Real.sinh (h / 2)) h := by
      apply ((Real.hasDerivAt_cosh (h / 2)).comp h
        ((hasDerivAt_id h).div_const 2)).congr_deriv
      ring
    have hraw := ((hlin.mul hsinh).const_mul 4).add (hcosh.const_mul 8)
    exact hraw.congr_deriv (by ring)
  have hInt : IntervalIntegrable
      (fun h : ℝ => (t - h) * (2 * Real.cosh (h / 2))) volume 0 t :=
    (by fun_prop : Continuous (fun h : ℝ =>
      (t - h) * (2 * Real.cosh (h / 2)))) |>.intervalIntegrable 0 t
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hP hInt]
  dsimp only [P]
  norm_num
  ring

private theorem centralPolarTriangleSetIntegral
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ h in Set.Ioc (0 : ℝ) t,
        (((t - h) * (2 * Real.cosh (h / 2)) : ℝ) : ℂ)) =
      ((8 * (Real.cosh (t / 2) - 1) : ℝ) : ℂ) := by
  rw [← intervalIntegral.integral_of_le ht]
  rw [intervalIntegral.integral_ofReal]
  norm_cast
  exact centralPolarTriangleIntegral ht

private theorem centralRectangularPrimePolarSource_eq_stieltjesPairing
    {t : ℝ} (ht : 0 ≤ t) :
    rectangularPrimePolarSourceCoefficient (t / 2) (t / 2) =
      2 * (criticalMellinStieltjesPairing (t / 2)
        (fun h : ℝ => ((t - h : ℝ) : ℂ))).re := by
  have hprime := rectangularPrimeAutocorrelationSum_central_eq_commonTriangle
    (L := t) ht (le_refl t)
  have hprime' :
      rectangularPrimeAutocorrelationSum (t / 2) (t / 2) =
        ∑ k ∈ Finset.Icc 2 ⌊Real.exp t⌋₊,
          criticalMellinAtomWeight k * (t - Real.log k) := by
    rw [hprime]
    apply Finset.sum_congr rfl
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkpos : (0 : ℝ) < k := by
      exact_mod_cast (show 0 < k by omega)
    have hkexp : (k : ℝ) ≤ Real.exp t :=
      (Nat.le_floor_iff (Real.exp_pos t).le).mp (Finset.mem_Icc.mp hk).2
    have hlogt : Real.log k ≤ t := (Real.log_le_iff_le_exp hkpos).mpr hkexp
    rw [max_eq_right (sub_nonneg.mpr hlogt), criticalMellinAtomWeight_eq_div_sqrt]
  have hpolar := centralPolarTriangleSetIntegral ht
  rw [rectangularPrimePolarSourceCoefficient, hprime',
    rectangularEvenPolarFeature_central_sq ht,
    criticalMellinStieltjesPairing]
  have hpolar' :
      (∫ h in Set.Ioc (0 : ℝ) (2 * (t / 2)),
        ((t - h : ℝ) : ℂ) * (2 * Real.cosh (h / 2) : ℂ)) =
        ((8 * (Real.cosh (t / 2) - 1) : ℝ) : ℂ) := by
    rw [show 2 * (t / 2) = t by ring]
    convert hpolar using 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards with h
    push_cast
    ring
  rw [hpolar']
  rw [show 2 * (t / 2) = t by ring]
  have hsum :
      (∑ x ∈ Finset.Icc 2 ⌊Real.exp t⌋₊,
        (criticalMellinAtomWeight x : ℂ) * ((t - Real.log x : ℝ) : ℂ)).re =
      ∑ x ∈ Finset.Icc 2 ⌊Real.exp t⌋₊,
        criticalMellinAtomWeight x * (t - Real.log x) := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Complex.ofReal_mul]
    exact Complex.ofReal_re _
  rw [Complex.sub_re, Complex.ofReal_re, hsum]
  ring

/-- Central two-edge prime--polar source is twice the first primitive of the completed
critical-Mellin error. This identity is valid through every prime-entry kink. -/
theorem centralRectangularPrimePolarSource_eq_completedErrorPrimitive
    {t : ℝ} (ht : 0 ≤ t) :
    rectangularPrimePolarSourceCoefficient (t / 2) (t / 2) =
      2 * ∫ h in (0 : ℝ)..t, criticalMellinCompletedError h := by
  have hibp := criticalMellinStieltjesPairing_integrationByParts
    (a := t / 2) (by positivity : 0 ≤ t / 2)
    (F := fun h : ℝ => ((t - h : ℝ) : ℂ))
    (F' := fun _h : ℝ => (-1 : ℂ))
    (fun x hx => by
      have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
        simpa using (hasDerivAt_id (x : ℂ)).comp_ofReal
      simpa only [Complex.ofReal_sub] using hid.const_sub (t : ℂ))
    (continuous_const.intervalIntegrable 0 t)
    (by norm_num; push_cast; ring)
  rw [show 2 * (t / 2) = t by ring] at hibp
  rw [centralRectangularPrimePolarSource_eq_stieltjesPairing ht, hibp]
  have hreal :
      (∫ h in Set.Ioc (0 : ℝ) t,
        (criticalMellinCompletedError h : ℂ) * (-1 : ℂ)).re =
        -(∫ h in (0 : ℝ)..t, criticalMellinCompletedError h) := by
    rw [show (fun h : ℝ =>
        (criticalMellinCompletedError h : ℂ) * (-1 : ℂ)) =
        fun h : ℝ => ((-criticalMellinCompletedError h : ℝ) : ℂ) by
      funext h
      push_cast
      ring]
    rw [integral_re, ← intervalIntegral.integral_of_le ht]
    simp only [Complex.ofReal_re]
    rw [← MeasureTheory.integral_neg]
  rw [hreal]
  ring

/-- Affine-renormalized central source increment. Its subtracted jet is the literal completed
prime--polar coefficient at the fixed lower wall. -/
def ccmFUCentralRectangularAffineRemainder (b t : ℝ) : ℝ :=
  rectangularPrimePolarSourceCoefficient (t / 2) (t / 2) -
    rectangularPrimePolarSourceCoefficient (b / 2) (b / 2) -
      2 * (t - b) * criticalMellinCompletedError b

/-- **FU--Suzuki central weld.** Every marked FU rectangular slice is exactly negative one half
of the affine-renormalized central two-edge prime--polar source. Fixed-wall memory is the true
zero-frequency completed source coefficient; no positive/negative region is separated. -/
theorem ccmThirdGradeCesaroRectangularPrimePolarSlice_eq_neg_half_centralAffineRemainder
    {b H t : ℝ} (hb : 0 < b) (hbt : b ≤ t) (htH : t ≤ H) :
    ccmThirdGradeCesaroRectangularPrimePolarSlice b H t =
      -(1 / 2 : ℝ) * ccmFUCentralRectangularAffineRemainder b t := by
  rw [ccmThirdGradeCesaroRectangularPrimePolarSlice_eq_completedErrorPrimitive
    hb hbt htH]
  rw [ccmFUCentralRectangularAffineRemainder,
    centralRectangularPrimePolarSource_eq_completedErrorPrimitive (hb.le.trans hbt),
    centralRectangularPrimePolarSource_eq_completedErrorPrimitive hb.le]
  have hE := intervalIntegrable_criticalMellinCompletedError_on_Icc hbt
  rw [intervalIntegral.integral_sub
    (continuous_const.intervalIntegrable b t) hE,
    intervalIntegral.integral_const]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_criticalMellinCompletedError_on_Icc hb.le)
    hE
  have hdiff :
      (∫ h in (0 : ℝ)..t, criticalMellinCompletedError h) -
          (∫ h in (0 : ℝ)..b, criticalMellinCompletedError h) =
        ∫ h in b..t, criticalMellinCompletedError h := by
    linarith
  rw [show (∫ h in (0 : ℝ)..t, criticalMellinCompletedError h) =
      (∫ h in (0 : ℝ)..b, criticalMellinCompletedError h) +
        ∫ h in b..t, criticalMellinCompletedError h by linarith]
  ring

end GaloisForLFunctions.RHTower

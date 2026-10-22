import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilThirdGradeRectangularFubiniCurrent

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

private theorem rectangularSlice_prime_cutoff
    {b H t : ℝ} (htH : t ≤ H) :
    (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        if b < Real.log k then
          criticalMellinAtomWeight k *
            ccmPositiveLagRectangularTriangle t (Real.log k)
        else 0) =
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp t⌋₊,
        if b < Real.log k then
          criticalMellinAtomWeight k *
            ccmPositiveLagRectangularTriangle t (Real.log k)
        else 0 := by
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    exact ⟨hk.1, hk.2.trans (Nat.floor_mono (Real.exp_le_exp.mpr htH))⟩
  · intro k hk hnot
    simp only [Finset.mem_Icc] at hk
    have hfloor : ⌊Real.exp t⌋₊ < k := by
      by_contra hle
      exact hnot (Finset.mem_Icc.mpr ⟨hk.1, by omega⟩)
    have hexp : Real.exp t < (k : ℝ) :=
      (Nat.floor_lt (Real.exp_pos t).le).mp hfloor
    have hkpos : (0 : ℝ) < k := (Real.exp_pos t).trans hexp
    have hlog : t < Real.log k := (Real.lt_log_iff_exp_lt hkpos).mpr hexp
    simp [ccmPositiveLagRectangularTriangle, max_eq_left (by linarith : t - Real.log k ≤ 0)]

private theorem rectangularSlice_polar_cutoff
    {b H t : ℝ} (hbt : b ≤ t) (htH : t ≤ H) :
    (∫ h in b..H,
        ccmPositiveLagRectangularTriangle t h * (2 * Real.cosh (h / 2))) =
      ∫ h in b..t, (t - h) * (2 * Real.cosh (h / 2)) := by
  let f : ℝ → ℝ := fun h =>
    ccmPositiveLagRectangularTriangle t h * (2 * Real.cosh (h / 2))
  have hf : Continuous f := by
    dsimp only [f]
    unfold ccmPositiveLagRectangularTriangle
    fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable b t) (hf.intervalIntegrable t H)]
  have hright : (∫ h in t..H, f h) = 0 := by
    calc
      (∫ h in t..H, f h) = ∫ _h in t..H, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro h hh
        rw [Set.uIcc_of_le htH] at hh
        simp [f, ccmPositiveLagRectangularTriangle,
          max_eq_left (sub_nonpos.mpr hh.1)]
      _ = 0 := by simp
  rw [hright, add_zero]
  apply intervalIntegral.integral_congr
  intro h hh
  rw [Set.uIcc_of_le hbt] at hh
  change max 0 (t - h) * (2 * Real.cosh (h / 2)) =
    (t - h) * (2 * Real.cosh (h / 2))
  rw [max_eq_right (sub_nonneg.mpr hh.2)]

private theorem rectangularSlice_eq_linearWeightedWindow
    {b H t : ℝ} (hbt : b ≤ t) (htH : t ≤ H) :
    ccmThirdGradeCesaroRectangularPrimePolarSlice b H t =
      ccmGuinandWeilPrimePolarWeightedWindow b t (fun h => t - h) := by
  unfold ccmThirdGradeCesaroRectangularPrimePolarSlice
    ccmGuinandWeilPrimePolarWeightedWindow
  rw [rectangularSlice_prime_cutoff htH,
    rectangularSlice_polar_cutoff hbt htH]
  apply congrArg₂ (· - ·)
  · apply Finset.sum_congr rfl
    intro k hk
    by_cases hbk : b < Real.log k
    · rw [if_pos hbk, if_pos hbk]
      have hkpos : (0 : ℝ) < k := by
        have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hk2)
      have hkexp : (k : ℝ) ≤ Real.exp t :=
        (Nat.le_floor_iff (Real.exp_pos t).le).mp (Finset.mem_Icc.mp hk).2
      have hklog : Real.log k ≤ t := (Real.log_le_iff_le_exp hkpos).mpr hkexp
      simp [ccmPositiveLagRectangularTriangle, max_eq_right (sub_nonneg.mpr hklog)]
    · simp [hbk]
  · rfl

/-- Every marked rectangular slice is exactly the first Volterra primitive of the anchored
completed prime-minus-polar error. Thus aperture mixing acts on one coherent source current, not
on independent positive Weil energies. -/
theorem ccmThirdGradeCesaroRectangularPrimePolarSlice_eq_completedErrorPrimitive
    {b H t : ℝ} (hb : 0 < b) (hbt : b ≤ t) (htH : t ≤ H) :
    ccmThirdGradeCesaroRectangularPrimePolarSlice b H t =
      ∫ h in b..t,
        (criticalMellinCompletedError b - criticalMellinCompletedError h) := by
  rw [rectangularSlice_eq_linearWeightedWindow hbt htH]
  have hflux := ccmGuinandWeilPrimePolarWeightedWindow_eq_completedErrorFlux
    hb hbt (F := fun h : ℝ => t - h) (F' := fun _ => (-1 : ℝ))
    (fun x hx => by simpa using (hasDerivAt_id x).const_sub t)
    (continuous_const.intervalIntegrable b t)
    continuous_const.continuousOn
  rw [hflux]
  simp only [sub_self, zero_mul, sub_zero]
  rw [show (fun h : ℝ => criticalMellinCompletedError h * (-1)) =
      fun h => -criticalMellinCompletedError h by funext h; ring,
    intervalIntegral.integral_neg]
  have hE := intervalIntegrable_criticalMellinCompletedError_on_Icc hbt
  calc
    (t - b) * criticalMellinCompletedError b +
        -(∫ h in b..t, criticalMellinCompletedError h) =
      (∫ h in b..t, criticalMellinCompletedError b) -
        ∫ h in b..t, criticalMellinCompletedError h := by
          rw [intervalIntegral.integral_const]
          ring
    _ = ∫ h in b..t,
        (criticalMellinCompletedError b - criticalMellinCompletedError h) := by
      rw [← intervalIntegral.integral_sub
        (continuous_const.intervalIntegrable b t) hE]

/-- Cross-aperture marked current in completed-error Volterra coordinates. The bulk is one
positive aperture mixture of causal first primitives and the forced endpoint atom is the full
first primitive at the moving wall. -/
theorem ccmThirdGradeCesaroMarkedRectangularPrimePolarCurrent_eq_volterraMixture
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    ccmThirdGradeCesaroMarkedRectangularPrimePolarCurrent b H =
      (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t *
        (∫ h in b..t,
          (criticalMellinCompletedError b - criticalMellinCompletedError h))) +
      (32 / H ^ 4) *
        (∫ h in b..H,
          (criticalMellinCompletedError b - criticalMellinCompletedError h)) := by
  rw [ccmThirdGradeCesaroMarkedRectangularPrimePolarCurrent_eq_fubini hb hbH]
  apply congrArg₂ (· + ·)
  · apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hbH] at ht
    change ccmThirdGradeCesaroRectangularMixDensity H t *
        ccmThirdGradeCesaroRectangularPrimePolarSlice b H t =
      ccmThirdGradeCesaroRectangularMixDensity H t *
        (∫ h in b..t,
          (criticalMellinCompletedError b - criticalMellinCompletedError h))
    rw [ccmThirdGradeCesaroRectangularPrimePolarSlice_eq_completedErrorPrimitive
      hb ht.1 ht.2]
  · rw [ccmThirdGradeCesaroRectangularPrimePolarSlice_eq_completedErrorPrimitive
      hb hbH le_rfl]

end GaloisForLFunctions.RHTower

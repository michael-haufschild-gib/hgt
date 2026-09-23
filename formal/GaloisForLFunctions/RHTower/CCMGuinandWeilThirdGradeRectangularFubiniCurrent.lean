import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeMarkedRectangularCurrent
import GaloisForLFunctions.RHTower.BoxFubini

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- One literal rectangular interval-head source slice, with prime and polar coefficients coupled
at the same marked aperture. The fixed outer wall makes the Fubini box explicit; triangles beyond
their marked aperture vanish identically. -/
def ccmThirdGradeCesaroRectangularPrimePolarSlice (b H t : ℝ) : ℝ :=
  (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
      if b < Real.log k then
        criticalMellinAtomWeight k * ccmPositiveLagRectangularTriangle t (Real.log k)
      else 0) -
    ∫ h in b..H,
      ccmPositiveLagRectangularTriangle t h * (2 * Real.cosh (h / 2))

private theorem continuousOn_rectangularMixDensity_mul_triangle_at
    {b H s : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    ContinuousOn (fun t => ccmThirdGradeCesaroRectangularMixDensity H t *
      ccmPositiveLagRectangularTriangle t s) (Set.Icc b H) := by
  have hH : 0 < H := hb.trans_le hbH
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt (hb.trans_le ht.1)
  have hdensity : ContinuousAt (ccmThirdGradeCesaroRectangularMixDensity H) t := by
    unfold ccmThirdGradeCesaroRectangularMixDensity
    exact (continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).div
      (continuousAt_const.mul (continuousAt_id.pow 5))
      (mul_ne_zero hH.ne' (pow_ne_zero 5 ht0))
  have htriangle : ContinuousAt (fun t => ccmPositiveLagRectangularTriangle t s) t := by
    unfold ccmPositiveLagRectangularTriangle
    fun_prop
  exact (hdensity.mul htriangle).continuousWithinAt

private def ccmThirdGradeCesaroClippedRectangularMixDensity (b H t : ℝ) : ℝ :=
  ccmThirdGradeCesaroRectangularMixDensity H (max b t)

private theorem continuous_clippedRectangularMixDensity
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    Continuous (ccmThirdGradeCesaroClippedRectangularMixDensity b H) := by
  have hH : 0 < H := hb.trans_le hbH
  unfold ccmThirdGradeCesaroClippedRectangularMixDensity
    ccmThirdGradeCesaroRectangularMixDensity
  have hmaxpos : ∀ t : ℝ, 0 < max b t := fun t => hb.trans_le (le_max_left b t)
  have hmax : Continuous (fun t : ℝ => max b t) := continuous_const.max continuous_id
  exact (continuous_const.mul (continuous_const.sub hmax)).div
    (continuous_const.mul (hmax.pow 5))
    (fun t => mul_ne_zero hH.ne' (pow_ne_zero 5 (ne_of_gt (hmaxpos t))))

private theorem clippedRectangularMixDensity_eq
    {b H t : ℝ} (hbt : b ≤ t) :
    ccmThirdGradeCesaroClippedRectangularMixDensity b H t =
      ccmThirdGradeCesaroRectangularMixDensity H t := by
  simp [ccmThirdGradeCesaroClippedRectangularMixDensity, max_eq_right hbt]

private theorem thirdGradeMarkedRectangular_prime_fubini
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        if b < Real.log k then
          criticalMellinAtomWeight k *
            ccmThirdGradeCesaroFixedRectangularMixture b H (Real.log k)
        else 0) =
      (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t *
        (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
          if b < Real.log k then
            criticalMellinAtomWeight k *
              ccmPositiveLagRectangularTriangle t (Real.log k)
          else 0)) +
      (32 / H ^ (4 : ℕ)) *
        (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
          if b < Real.log k then
            criticalMellinAtomWeight k *
              ccmPositiveLagRectangularTriangle H (Real.log k)
          else 0) := by
  let S := Finset.Icc 2 ⌊Real.exp H⌋₊
  let P : ℕ → ℝ → ℝ := fun k t => if b < Real.log k then
    criticalMellinAtomWeight k *
      (ccmThirdGradeCesaroRectangularMixDensity H t *
        ccmPositiveLagRectangularTriangle t (Real.log k))
    else 0
  let Q : ℕ → ℝ := fun k => if b < Real.log k then
    criticalMellinAtomWeight k *
      ccmPositiveLagRectangularTriangle H (Real.log k)
    else 0
  have hint : ∀ k ∈ S, IntervalIntegrable
      (P k) volume b H := by
    intro k hk
    by_cases hbk : b < Real.log k
    · have hc := continuousOn_rectangularMixDensity_mul_triangle_at
        (s := Real.log k) hb hbH
      have hcU : ContinuousOn (fun t =>
          ccmThirdGradeCesaroRectangularMixDensity H t *
            ccmPositiveLagRectangularTriangle t (Real.log k)) (Set.uIcc b H) := by
        simpa only [Set.uIcc_of_le hbH] using hc
      refine ((hcU.const_mul (criticalMellinAtomWeight k)).intervalIntegrable).congr ?_
      intro t ht
      simp [P, hbk]
    · simpa [P, hbk] using
        (continuous_const.intervalIntegrable b H :
          IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume b H)
  have hterm : ∀ k ∈ S,
      (if b < Real.log k then
        criticalMellinAtomWeight k *
          ccmThirdGradeCesaroFixedRectangularMixture b H (Real.log k)
      else 0) = (∫ t in b..H, P k t) + (32 / H ^ (4 : ℕ)) * Q k := by
    intro k hk
    by_cases hbk : b < Real.log k
    · rw [if_pos hbk]
      rw [ccmThirdGradeCesaroFixedRectangularMixture]
      rw [show (∫ t in b..H, P k t) = criticalMellinAtomWeight k *
          (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t *
            ccmPositiveLagRectangularTriangle t (Real.log k)) by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t ht
        simp [P, hbk]
        ]
      simp only [Q, if_pos hbk]
      ring
    · simp [P, Q, hbk]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  rw [← intervalIntegral.integral_finsetSum hint, ← Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply intervalIntegral.integral_congr
    intro t ht
    dsimp only [P]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hbk : b < Real.log k
    · simp [hbk]
      ring
    · simp [hbk]
  · rfl

private theorem thirdGradeMarkedRectangular_polar_fubini
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    (∫ h in b..H,
        ccmThirdGradeCesaroFixedRectangularMixture b H h *
          (2 * Real.cosh (h / 2))) =
      (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t *
        (∫ h in b..H,
          ccmPositiveLagRectangularTriangle t h * (2 * Real.cosh (h / 2)))) +
      (32 / H ^ (4 : ℕ)) *
        (∫ h in b..H,
          ccmPositiveLagRectangularTriangle H h * (2 * Real.cosh (h / 2))) := by
  let D : ℝ → ℝ := ccmThirdGradeCesaroClippedRectangularMixDensity b H
  let T : ℝ → ℝ → ℝ := fun t h => ccmPositiveLagRectangularTriangle t h
  let P : ℝ → ℝ := fun h => 2 * Real.cosh (h / 2)
  have hD : Continuous D := continuous_clippedRectangularMixDensity hb hbH
  have hT : Continuous (Function.uncurry T) := by
    dsimp only [T, Function.uncurry]
    unfold ccmPositiveLagRectangularTriangle
    fun_prop
  have hP : Continuous P := by
    dsimp only [P]
    fun_prop
  have hjoint : Continuous (Function.uncurry fun h t => D t * T t h * P h) := by
    have hTswap : Continuous (fun p : ℝ × ℝ => T p.2 p.1) := by
      dsimp only [T]
      unfold ccmPositiveLagRectangularTriangle
      fun_prop
    exact ((hD.comp continuous_snd).mul hTswap).mul
      (hP.comp continuous_fst)
  have hswap := _root_.RHTower.interval_integral_swap_of_continuous hbH hbH hjoint
  have hD_eq : ∀ t ∈ Set.uIcc b H,
      D t = ccmThirdGradeCesaroRectangularMixDensity H t := by
    intro t ht
    rw [Set.uIcc_of_le hbH] at ht
    exact clippedRectangularMixDensity_eq ht.1
  have hinner : ∀ h : ℝ,
      (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t * T t h) =
        ∫ t in b..H, D t * T t h := by
    intro h
    apply intervalIntegral.integral_congr
    intro t ht
    change ccmThirdGradeCesaroRectangularMixDensity H t * T t h = D t * T t h
    rw [hD_eq t ht]
  have hleftExpand :
      (∫ h in b..H,
          ccmThirdGradeCesaroFixedRectangularMixture b H h * P h) =
        (∫ h in b..H, (∫ t in b..H, D t * T t h) * P h) +
          ∫ h in b..H, (32 / H ^ (4 : ℕ)) * T H h * P h := by
    rw [← intervalIntegral.integral_add]
    · apply intervalIntegral.integral_congr
      intro h hh
      change (ccmThirdGradeCesaroFixedRectangularMixture b H h) * P h = _
      rw [ccmThirdGradeCesaroFixedRectangularMixture, hinner h]
      ring
    · have hcinner : Continuous (fun h => ∫ t in b..H, D t * T t h) := by
        apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        have hTswap : Continuous (fun p : ℝ × ℝ => T p.2 p.1) := by
          dsimp only [T]
          unfold ccmPositiveLagRectangularTriangle
          fun_prop
        exact (hD.comp continuous_snd).mul hTswap
      exact (hcinner.mul hP).intervalIntegrable _ _
    · exact ((continuous_const.mul
        (continuous_const.max (continuous_const.sub continuous_id))).mul hP).intervalIntegrable _ _
  have hleftSwap :
      (∫ h in b..H, (∫ t in b..H, D t * T t h) * P h) =
        ∫ t in b..H, D t * (∫ h in b..H, T t h * P h) := by
    calc
      _ = ∫ h in b..H, ∫ t in b..H, D t * T t h * P h := by
        apply intervalIntegral.integral_congr
        intro h hh
        change (∫ t in b..H, D t * T t h) * P h =
          ∫ t in b..H, D t * T t h * P h
        rw [intervalIntegral.integral_mul_const]
      _ = ∫ t in b..H, ∫ h in b..H, D t * T t h * P h := hswap
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro t ht
        change (∫ h in b..H, D t * T t h * P h) =
          D t * ∫ h in b..H, T t h * P h
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro h hh
        ring
  rw [hleftExpand, hleftSwap]
  apply congrArg₂ (· + ·)
  · apply intervalIntegral.integral_congr
    intro t ht
    change D t * (∫ h in b..H, T t h * P h) =
      ccmThirdGradeCesaroRectangularMixDensity H t *
        (∫ h in b..H, T t h * P h)
    rw [hD_eq t ht]
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro h hh
    ring

/-- Exact cross-aperture Fubini normal form. Cancellation across marked apertures stays inside one
signed direct integral; no per-slice absolute value or positivity assumption is introduced. -/
theorem ccmThirdGradeCesaroMarkedRectangularPrimePolarCurrent_eq_fubini
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    ccmThirdGradeCesaroMarkedRectangularPrimePolarCurrent b H =
      (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t *
        ccmThirdGradeCesaroRectangularPrimePolarSlice b H t) +
      (32 / H ^ (4 : ℕ)) * ccmThirdGradeCesaroRectangularPrimePolarSlice b H H := by
  rw [ccmThirdGradeCesaroMarkedRectangularPrimePolarCurrent,
    ccmGuinandWeilPrimePolarWeightedWindow]
  rw [thirdGradeMarkedRectangular_prime_fubini hb hbH,
    thirdGradeMarkedRectangular_polar_fubini hb hbH]
  unfold ccmThirdGradeCesaroRectangularPrimePolarSlice
  let D : ℝ → ℝ := ccmThirdGradeCesaroClippedRectangularMixDensity b H
  let P : ℝ → ℝ := fun t =>
    ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
      if b < Real.log k then
        criticalMellinAtomWeight k *
          ccmPositiveLagRectangularTriangle t (Real.log k)
      else 0
  let Q : ℝ → ℝ := fun t =>
    ∫ h in b..H, ccmPositiveLagRectangularTriangle t h * (2 * Real.cosh (h / 2))
  have hD : Continuous D := continuous_clippedRectangularMixDensity hb hbH
  have hD_eq : ∀ t ∈ Set.uIcc b H,
      D t = ccmThirdGradeCesaroRectangularMixDensity H t := by
    intro t ht
    rw [Set.uIcc_of_le hbH] at ht
    exact clippedRectangularMixDensity_eq ht.1
  have hP : Continuous P := by
    dsimp only [P]
    refine continuous_finsetSum _ fun k hk => ?_
    by_cases hbk : b < Real.log k
    · simp only [if_pos hbk]
      exact continuous_const.mul (by
        unfold ccmPositiveLagRectangularTriangle
        fun_prop)
    · simp only [if_neg hbk]
      exact continuous_const
  have hQ : Continuous Q := by
    dsimp only [Q]
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    unfold Function.uncurry ccmPositiveLagRectangularTriangle
    fun_prop
  have hPrimeInt : IntervalIntegrable
      (fun t => ccmThirdGradeCesaroRectangularMixDensity H t * P t) volume b H := by
    refine ((hD.mul hP).intervalIntegrable b H).congr ?_
    intro t ht
    change D t * P t = ccmThirdGradeCesaroRectangularMixDensity H t * P t
    rw [hD_eq t (Set.uIoc_subset_uIcc ht)]
  have hPolarInt : IntervalIntegrable
      (fun t => ccmThirdGradeCesaroRectangularMixDensity H t * Q t) volume b H := by
    refine ((hD.mul hQ).intervalIntegrable b H).congr ?_
    intro t ht
    change D t * Q t = ccmThirdGradeCesaroRectangularMixDensity H t * Q t
    rw [hD_eq t (Set.uIoc_subset_uIcc ht)]
  have hsub :
      (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t * P t) -
          (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t * Q t) =
        ∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t * (P t - Q t) := by
    rw [← intervalIntegral.integral_sub hPrimeInt hPolarInt]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  change ((∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t * P t) +
        (32 / H ^ (4 : ℕ)) * P H) -
      ((∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t * Q t) +
        (32 / H ^ (4 : ℕ)) * Q H) =
    (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t * (P t - Q t)) +
      (32 / H ^ (4 : ℕ)) * (P H - Q H)
  rw [← hsub]
  ring

end GaloisForLFunctions.RHTower

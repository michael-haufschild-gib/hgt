import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiSignedWindowMixture
import GaloisForLFunctions.HTGeometry.HyperbolicBounds

/-!
# Source-adaptive cofinal landing for positive Suzuki log chords

The finite connected Suzuki multiplier has quadratic clock defect.  We measure the exact finite
total variation of the literal triangular prime--polar source and choose a positive clock from that
variation.  The resulting schedule is explicit, tends to zero, and lands on the moving literal
signed windows with error at most `exp 1 / (2 * H_N^(2 : ℕ))`.  No cancellation estimate, compactness
selection, or Riemann-hypothesis input enters this convergence theorem.
-/

open Filter Topology MeasureTheory

namespace RHTower

noncomputable section

open GaloisForLFunctions.RHTower

theorem abs_multiplier_sub_one_le
    {ω h : ℝ} (hω : 0 < ω) (hh : 0 < h) :
    |shiftedEulerLogConnectedThirdMultiplier ω h - 1| ≤
      (ω * h) ^ (2 : ℕ) / 2 * Real.exp (ω * h) := by
  have hy : 0 < ω * h := mul_pos hω hh
  have hlow := one_le_shiftedEulerLogConnectedThirdMultiplier hω hh
  have hup := shiftedEulerLogConnectedThirdMultiplier_le_cosh hω hh
  have hcosh := HTGeometry.cosh_sub_one_le hy.le
  have hce := HTGeometry.cosh_le_exp_of_nonneg hy.le
  rw [abs_of_nonneg (sub_nonneg.mpr hlow)]
  calc
    shiftedEulerLogConnectedThirdMultiplier ω h - 1 ≤
        Real.cosh (ω * h) - 1 := sub_le_sub_right hup 1
    _ ≤ (ω * h) ^ (2 : ℕ) / 2 * Real.cosh (ω * h) := hcosh
    _ ≤ (ω * h) ^ (2 : ℕ) / 2 * Real.exp (ω * h) :=
      mul_le_mul_of_nonneg_left hce (by positivity)

def ccmGuinandWeilPrimePolarWeightedWindowVariation
    (b H : ℝ) (F : ℝ → ℝ) : ℝ :=
  (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
    if b < Real.log k then
      |criticalMellinAtomWeight k * F (Real.log k)|
    else 0) +
  ∫ h in b..H,
    |F h * (2 * Real.cosh (h / 2))|

theorem ccmGuinandWeilPrimePolarWeightedWindowVariation_nonneg
    {b H : ℝ} (hbH : b ≤ H) :
    0 ≤ ccmGuinandWeilPrimePolarWeightedWindowVariation b H F := by
  apply add_nonneg
  · exact Finset.sum_nonneg fun k hk => by
      split <;> positivity
  · exact intervalIntegral.integral_nonneg hbH fun h hh => abs_nonneg _

theorem abs_weightedWindow_sub_le_mul_variation
    {b H c : ℝ} (hbH : b ≤ H) {F G : ℝ → ℝ}
    (hF : ContinuousOn F (Set.Icc b H))
    (hG : ContinuousOn G (Set.Icc b H))
    (hprime : ∀ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
      b < Real.log k →
        |criticalMellinAtomWeight k * F (Real.log k) -
          criticalMellinAtomWeight k * G (Real.log k)| ≤
        c * |criticalMellinAtomWeight k * F (Real.log k)|)
    (hpolar : ∀ h ∈ Set.Icc b H,
      |F h * (2 * Real.cosh (h / 2)) -
        G h * (2 * Real.cosh (h / 2))| ≤
      c * |F h * (2 * Real.cosh (h / 2))|) :
    |ccmGuinandWeilPrimePolarWeightedWindow b H F -
        ccmGuinandWeilPrimePolarWeightedWindow b H G| ≤
      c * ccmGuinandWeilPrimePolarWeightedWindowVariation b H F := by
  let P : ℝ → ℝ := fun h => 2 * Real.cosh (h / 2)
  have hP : Continuous P := by dsimp only [P]; fun_prop
  have hFI : IntervalIntegrable (fun h => F h * P h) volume b H := by
    have hcF := hF.mul hP.continuousOn
    change ContinuousOn (fun h => F h * P h) (Set.Icc b H) at hcF
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hbH] using hcF
  have hGI : IntervalIntegrable (fun h => G h * P h) volume b H := by
    have hcG := hG.mul hP.continuousOn
    change ContinuousOn (fun h => G h * P h) (Set.Icc b H) at hcG
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hbH] using hcG
  have hsubI : IntervalIntegrable (fun h => F h * P h - G h * P h)
      volume b H := hFI.sub hGI
  have hbaseI : IntervalIntegrable (fun h => |F h * P h|) volume b H := hFI.abs
  have hmajorI : IntervalIntegrable (fun h => c * |F h * P h|) volume b H :=
    hbaseI.const_mul c
  have hsum :
      |∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        ((if b < Real.log k then criticalMellinAtomWeight k * F (Real.log k) else 0) -
          if b < Real.log k then criticalMellinAtomWeight k * G (Real.log k) else 0)| ≤
      c * ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        if b < Real.log k then
          |criticalMellinAtomWeight k * F (Real.log k)| else 0 := by
    calc
      |∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
          ((if b < Real.log k then criticalMellinAtomWeight k * F (Real.log k) else 0) -
            if b < Real.log k then criticalMellinAtomWeight k * G (Real.log k) else 0)| ≤
          ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
            |(if b < Real.log k then criticalMellinAtomWeight k * F (Real.log k) else 0) -
              if b < Real.log k then criticalMellinAtomWeight k * G (Real.log k) else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
          c * (if b < Real.log k then
            |criticalMellinAtomWeight k * F (Real.log k)| else 0) := by
        apply Finset.sum_le_sum
        intro k hk
        by_cases hbk : b < Real.log k
        · simpa only [hbk, if_true] using hprime k hk hbk
        · simp only [hbk, if_false, sub_self, abs_zero, mul_zero]
          exact le_rfl
      _ = c * ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
          if b < Real.log k then
            |criticalMellinAtomWeight k * F (Real.log k)| else 0 := by
        rw [Finset.mul_sum]
  have hpol :
      |(∫ h in b..H, F h * P h) - ∫ h in b..H, G h * P h| ≤
        c * ∫ h in b..H, |F h * P h| := by
    rw [← intervalIntegral.integral_sub hFI hGI]
    calc
      |∫ h in b..H, F h * P h - G h * P h| ≤
          ∫ h in b..H, |F h * P h - G h * P h| :=
        intervalIntegral.abs_integral_le_integral_abs hbH
      _ ≤ ∫ h in b..H, c * |F h * P h| := by
        apply intervalIntegral.integral_mono_on hbH hsubI.abs hmajorI
        intro h hh
        simpa only [P] using hpolar h hh
      _ = c * ∫ h in b..H, |F h * P h| :=
        intervalIntegral.integral_const_mul _ _
  rw [ccmGuinandWeilPrimePolarWeightedWindow,
    ccmGuinandWeilPrimePolarWeightedWindow]
  have hsumSub :
      (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
          if b < Real.log k then criticalMellinAtomWeight k * F (Real.log k) else 0) -
        (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
          (if b < Real.log k then criticalMellinAtomWeight k * G (Real.log k) else 0)) =
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        ((if b < Real.log k then criticalMellinAtomWeight k * F (Real.log k) else 0) -
          (if b < Real.log k then criticalMellinAtomWeight k * G (Real.log k) else 0)) := by
    rw [Finset.sum_sub_distrib]
  rw [ccmGuinandWeilPrimePolarWeightedWindowVariation]
  calc
    |((∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
          if b < Real.log k then criticalMellinAtomWeight k * F (Real.log k) else 0) -
        ∫ h in b..H, F h * P h) -
      ((∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
          if b < Real.log k then criticalMellinAtomWeight k * G (Real.log k) else 0) -
        ∫ h in b..H, G h * P h)| =
      |(∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        ((if b < Real.log k then criticalMellinAtomWeight k * F (Real.log k) else 0) -
          (if b < Real.log k then criticalMellinAtomWeight k * G (Real.log k) else 0))) -
        ((∫ h in b..H, F h * P h) - ∫ h in b..H, G h * P h)| := by
          rw [← hsumSub]
          ring
    _ ≤ |∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        ((if b < Real.log k then criticalMellinAtomWeight k * F (Real.log k) else 0) -
          (if b < Real.log k then criticalMellinAtomWeight k * G (Real.log k) else 0))| +
        |(∫ h in b..H, F h * P h) - ∫ h in b..H, G h * P h| := abs_sub _ _
    _ ≤ c * (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
          if b < Real.log k then
            |criticalMellinAtomWeight k * F (Real.log k)| else 0) +
        c * ∫ h in b..H, |F h * P h| := add_le_add hsum hpol
    _ = c * ((∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
          if b < Real.log k then
            |criticalMellinAtomWeight k * F (Real.log k)| else 0) +
        ∫ h in b..H, |F h * P h|) := by ring

theorem abs_positiveLogChordApprox_sub_literal_le_variation
    {ω b H : ℝ} (hω : 0 < ω) (hb : 0 < b) (hbH : b ≤ H) :
    |ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox b H ω -
        ccmGuinandWeilPrimePolarWeightedWindow b H
          (ccmGuinandWeilThirdGradeCesaroTriangularWeight H)| ≤
      ((ω * H) ^ (2 : ℕ) / 2 * Real.exp (ω * H)) *
        ccmGuinandWeilPrimePolarWeightedWindowVariation b H
          (ccmGuinandWeilThirdGradeCesaroTriangularWeight H) := by
  let T : ℝ → ℝ := ccmGuinandWeilThirdGradeCesaroTriangularWeight H
  let M : ℝ → ℝ := shiftedEulerLogConnectedThirdMultiplier ω
  let c : ℝ := (ω * H) ^ (2 : ℕ) / 2 * Real.exp (ω * H)
  have hH : 0 < H := hb.trans_le hbH
  have hgap : ∀ h ∈ Set.Icc b H, |M h - 1| ≤ c := by
    intro h hhmem
    have hh : 0 < h := hb.trans_le hhmem.1
    have hy : 0 ≤ ω * h := (mul_pos hω hh).le
    have hyH : ω * h ≤ ω * H := mul_le_mul_of_nonneg_left hhmem.2 hω.le
    have hsq : (ω * h) ^ (2 : ℕ) / 2 ≤ (ω * H) ^ (2 : ℕ) / 2 := by
      have hs := pow_le_pow_left₀ hy hyH 2
      linarith
    have hexp : Real.exp (ω * h) ≤ Real.exp (ω * H) :=
      Real.exp_le_exp.mpr hyH
    have hraw := abs_multiplier_sub_one_le hω hh
    dsimp only [M, c]
    exact hraw.trans (mul_le_mul hsq hexp (Real.exp_pos _).le (by positivity))
  have hT : ContinuousOn T (Set.Icc b H) := by
    intro h hhmem
    dsimp only [T]
    exact (hasDerivAt_ccmGuinandWeilThirdGradeCesaroTriangularWeight
      (ne_of_gt (hb.trans_le hhmem.1))).continuousAt.continuousWithinAt
  have hTM : ContinuousOn (fun h => T h * M h) (Set.Icc b H) := by
    intro h hhmem
    have hh : 0 < h := hb.trans_le hhmem.1
    have harg : ContinuousAt (fun x : ℝ => ω * x) h :=
      continuousAt_const.mul continuousAt_id
    have hsinh : ContinuousAt (fun x : ℝ => Real.sinh (ω * x)) h :=
      Real.continuous_sinh.continuousAt.comp harg
    have hratio : ContinuousAt
        (fun x : ℝ => Real.sinh (ω * x) / (ω * x)) h :=
      hsinh.div harg (mul_ne_zero hω.ne' hh.ne')
    have hm : ContinuousAt M h := by
      dsimp only [M, shiftedEulerLogConnectedThirdMultiplier]
      exact (continuousAt_const.mul (hratio.sub continuousAt_const)).div
        (harg.pow 2) (pow_ne_zero 2 (mul_ne_zero hω.ne' hh.ne'))
    exact (hT h hhmem).mul hm.continuousWithinAt
  have hbound := abs_weightedWindow_sub_le_mul_variation hbH hT hTM
    (fun k hk hbk => by
      have hkpos : (0 : ℝ) < k := by
        have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
        exact_mod_cast (show 0 < k by omega)
      have hkexp : (k : ℝ) ≤ Real.exp H :=
        (Nat.le_floor_iff (Real.exp_pos H).le).mp (Finset.mem_Icc.mp hk).2
      have hlogH : Real.log k ≤ H :=
        (Real.log_le_iff_le_exp hkpos).mpr hkexp
      have hlogmem : Real.log k ∈ Set.Icc b H := ⟨hbk.le, hlogH⟩
      have hg := hgap (Real.log k) hlogmem
      change |criticalMellinAtomWeight k * T (Real.log k) -
          criticalMellinAtomWeight k * (T (Real.log k) * M (Real.log k))| ≤
        c * |criticalMellinAtomWeight k * T (Real.log k)|
      rw [show criticalMellinAtomWeight k * T (Real.log k) -
          criticalMellinAtomWeight k * (T (Real.log k) * M (Real.log k)) =
        (criticalMellinAtomWeight k * T (Real.log k)) *
          (1 - M (Real.log k)) by ring, abs_mul, abs_sub_comm]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left hg (abs_nonneg
          (criticalMellinAtomWeight k * T (Real.log k))))
    (fun h hhmem => by
      have hg := hgap h hhmem
      change |T h * (2 * Real.cosh (h / 2)) -
          T h * M h * (2 * Real.cosh (h / 2))| ≤
        c * |T h * (2 * Real.cosh (h / 2))|
      rw [show T h * (2 * Real.cosh (h / 2)) -
          T h * M h * (2 * Real.cosh (h / 2)) =
        (T h * (2 * Real.cosh (h / 2))) * (1 - M h) by ring,
        abs_mul, abs_sub_comm]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left hg
          (abs_nonneg (T h * (2 * Real.cosh (h / 2)))))
  rw [ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox_eq_weightedWindow
    hω.ne' hb hbH]
  rw [abs_sub_comm]
  simpa only [T, M, c] using hbound

theorem adaptive_clock_algebra
    {H V : ℝ} (hH : 0 < H) (hV : 0 ≤ V) :
    ((1 / (H ^ (2 : ℕ) * (V + 1)) * H) ^ (2 : ℕ)) * V ≤ 1 / H ^ (2 : ℕ) := by
  have hV1 : 0 < V + 1 := by linarith
  have hden : 0 < H ^ (2 : ℕ) * (V + 1) ^ (2 : ℕ) := mul_pos (sq_pos_of_pos hH) (sq_pos_of_pos hV1)
  rw [show ((1 / (H ^ (2 : ℕ) * (V + 1)) * H) ^ (2 : ℕ)) * V =
      V / (H ^ (2 : ℕ) * (V + 1) ^ (2 : ℕ)) by
        field_simp [hH.ne', hV1.ne']]
  apply (div_le_iff₀ hden).2
  field_simp [hH.ne']
  nlinarith [sq_nonneg V]

def ccmFUSuzukiPositiveLogChordSourceAdaptiveClock (b H : ℝ) : ℝ :=
  let V := ccmGuinandWeilPrimePolarWeightedWindowVariation b H
    (ccmGuinandWeilThirdGradeCesaroTriangularWeight H)
  1 / (H ^ (2 : ℕ) * (V + 1))

theorem abs_positiveLogChordSourceAdaptiveApprox_sub_literal_le
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) (hH1 : 1 ≤ H) :
    let ω := ccmFUSuzukiPositiveLogChordSourceAdaptiveClock b H
    |ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox b H ω -
        ccmGuinandWeilPrimePolarWeightedWindow b H
          (ccmGuinandWeilThirdGradeCesaroTriangularWeight H)| ≤
      Real.exp 1 / (2 * H ^ (2 : ℕ)) := by
  dsimp only
  let V := ccmGuinandWeilPrimePolarWeightedWindowVariation b H
    (ccmGuinandWeilThirdGradeCesaroTriangularWeight H)
  let ω := ccmFUSuzukiPositiveLogChordSourceAdaptiveClock b H
  have hH : 0 < H := hb.trans_le hbH
  have hV : 0 ≤ V :=
    ccmGuinandWeilPrimePolarWeightedWindowVariation_nonneg hbH
  have hωdef : ω = 1 / (H ^ (2 : ℕ) * (V + 1)) := by rfl
  have hω : 0 < ω := by rw [hωdef]; positivity
  have hωH : ω * H ≤ 1 := by
    rw [hωdef]
    have hV1 : 1 ≤ V + 1 := by linarith
    have hden : 1 ≤ H * (V + 1) := by
      simpa only [one_mul] using
        mul_le_mul hH1 hV1 (by norm_num : (0 : ℝ) ≤ 1) hH.le
    rw [show 1 / (H ^ (2 : ℕ) * (V + 1)) * H = 1 / (H * (V + 1)) by
      field_simp [hH.ne']]
    exact (div_le_one (by positivity : 0 < H * (V + 1))).2 hden
  have hexp : Real.exp (ω * H) ≤ Real.exp 1 := Real.exp_le_exp.mpr hωH
  have halg : (ω * H) ^ (2 : ℕ) * V ≤ 1 / H ^ (2 : ℕ) := by
    rw [hωdef]
    exact adaptive_clock_algebra hH hV
  have hraw := abs_positiveLogChordApprox_sub_literal_le_variation hω hb hbH
  change |ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox b H ω -
        ccmGuinandWeilPrimePolarWeightedWindow b H
          (ccmGuinandWeilThirdGradeCesaroTriangularWeight H)| ≤
      ((ω * H) ^ (2 : ℕ) / 2 * Real.exp (ω * H)) * V at hraw
  calc
    |ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox b H ω -
        ccmGuinandWeilPrimePolarWeightedWindow b H
          (ccmGuinandWeilThirdGradeCesaroTriangularWeight H)| ≤
        ((ω * H) ^ (2 : ℕ) / 2 * Real.exp (ω * H)) * V := hraw
    _ = (Real.exp (ω * H) / 2) * ((ω * H) ^ (2 : ℕ) * V) := by ring
    _ ≤ (Real.exp 1 / 2) * (1 / H ^ (2 : ℕ)) :=
      mul_le_mul (by linarith) halg (by positivity) (by positivity)
    _ = Real.exp 1 / (2 * H ^ (2 : ℕ)) := by ring

theorem uniformlyBounded_sourceAdaptivePositiveLogChord_iff_literal
    {b : ℝ} (hb : 0 < b) :
    (∃ C : ℝ, ∀ H : ℝ, max b 1 ≤ H →
      |ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox b H
        (ccmFUSuzukiPositiveLogChordSourceAdaptiveClock b H)| ≤ C) ↔
    (∃ C : ℝ, ∀ H : ℝ, max b 1 ≤ H →
      |ccmGuinandWeilPrimePolarWeightedWindow b H
        (ccmGuinandWeilThirdGradeCesaroTriangularWeight H)| ≤ C) := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + Real.exp 1 / 2, ?_⟩
    intro H hBH
    have hbH : b ≤ H := (le_max_left b 1).trans hBH
    have hH1 : 1 ≤ H := (le_max_right b 1).trans hBH
    have herr := abs_positiveLogChordSourceAdaptiveApprox_sub_literal_le hb hbH hH1
    dsimp only at herr
    have hA := hC H hBH
    have htri := abs_sub_abs_le_abs_sub
      (ccmGuinandWeilPrimePolarWeightedWindow b H
        (ccmGuinandWeilThirdGradeCesaroTriangularWeight H))
      (ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox b H
        (ccmFUSuzukiPositiveLogChordSourceAdaptiveClock b H))
    have hrate : Real.exp 1 / (2 * H ^ (2 : ℕ)) ≤ Real.exp 1 / 2 := by
      have hH0 : 0 < H := lt_of_lt_of_le (by norm_num) hH1
      have hHsq : 1 ≤ H ^ (2 : ℕ) := by nlinarith
      apply (div_le_div_iff_of_pos_left (Real.exp_pos 1) (by positivity) (by positivity)).2
      nlinarith
    rw [abs_sub_comm] at herr
    linarith [htri]
  · rintro ⟨C, hC⟩
    refine ⟨C + Real.exp 1 / 2, ?_⟩
    intro H hBH
    have hbH : b ≤ H := (le_max_left b 1).trans hBH
    have hH1 : 1 ≤ H := (le_max_right b 1).trans hBH
    have herr := abs_positiveLogChordSourceAdaptiveApprox_sub_literal_le hb hbH hH1
    dsimp only at herr
    have hW := hC H hBH
    have htri := abs_sub_abs_le_abs_sub
      (ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox b H
        (ccmFUSuzukiPositiveLogChordSourceAdaptiveClock b H))
      (ccmGuinandWeilPrimePolarWeightedWindow b H
        (ccmGuinandWeilThirdGradeCesaroTriangularWeight H))
    have hrate : Real.exp 1 / (2 * H ^ (2 : ℕ)) ≤ Real.exp 1 / 2 := by
      have hH0 : 0 < H := lt_of_lt_of_le (by norm_num) hH1
      have hHsq : 1 ≤ H ^ (2 : ℕ) := by nlinarith
      apply (div_le_div_iff_of_pos_left (Real.exp_pos 1) (by positivity) (by positivity)).2
      nlinarith
    linarith [htri]

/-- Uniform boundedness of the actual source-adaptive positive Suzuki producer is already
RH-bearing.  The convergence landing loses only a fixed `exp 1 / 2` budget. -/
theorem riemannHypothesis_of_sourceAdaptivePositiveLogChord_uniformlyBounded
    (hbound : ∃ C : ℝ, ∀ H : ℝ, 1 ≤ H →
      |ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox 1 H
        (ccmFUSuzukiPositiveLogChordSourceAdaptiveClock 1 H)| ≤ C) :
    RiemannHypothesis := by
  have hb : (0 : ℝ) < 1 := by norm_num
  have hadaptive : ∃ C : ℝ, ∀ H : ℝ, max (1 : ℝ) 1 ≤ H →
      |ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox 1 H
        (ccmFUSuzukiPositiveLogChordSourceAdaptiveClock 1 H)| ≤ C := by
    simpa using hbound
  rcases (uniformlyBounded_sourceAdaptivePositiveLogChord_iff_literal hb).mp
      hadaptive with ⟨C, hC⟩
  have hanchored : CCMGuinandWeilThirdGradeCesaroAnchoredMomentBound 1 := by
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro H hH
    have hW := hC H (by simpa using hH.le)
    rw [← ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_eq_primePolarTriangularWindow
      hb hH.le] at hW
    exact hW.trans (le_max_left _ _)
  exact
    (ccmGuinandWeilThirdGradeCesaroAnchoredMomentBound_iff_and_riemannHypothesis hb).mp
      hanchored |>.2

def ccmFUSuzukiPositiveLogChordCofinalWall (b : ℝ) (N : ℕ) : ℝ :=
  b + (N : ℝ) + 1

def ccmFUSuzukiPositiveLogChordCofinalVariation (b : ℝ) (N : ℕ) : ℝ :=
  let H := ccmFUSuzukiPositiveLogChordCofinalWall b N
  ccmGuinandWeilPrimePolarWeightedWindowVariation b H
    (ccmGuinandWeilThirdGradeCesaroTriangularWeight H)

def ccmFUSuzukiPositiveLogChordAdaptiveClock (b : ℝ) (N : ℕ) : ℝ :=
  let H := ccmFUSuzukiPositiveLogChordCofinalWall b N
  let V := ccmFUSuzukiPositiveLogChordCofinalVariation b N
  1 / (H ^ (2 : ℕ) * (V + 1))

theorem ccmFUSuzukiPositiveLogChordAdaptiveClock_pos
    {b : ℝ} (hb : 0 < b) (N : ℕ) :
    0 < ccmFUSuzukiPositiveLogChordAdaptiveClock b N := by
  let H := ccmFUSuzukiPositiveLogChordCofinalWall b N
  let V := ccmFUSuzukiPositiveLogChordCofinalVariation b N
  have hbH : b ≤ H := by
    dsimp only [H, ccmFUSuzukiPositiveLogChordCofinalWall]
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hH : 0 < H := hb.trans_le hbH
  have hV : 0 ≤ V := by
    exact ccmGuinandWeilPrimePolarWeightedWindowVariation_nonneg hbH
  change 0 < 1 / (H ^ (2 : ℕ) * (V + 1))
  positivity

theorem abs_positiveLogChordAdaptiveCofinalApprox_sub_literal_le
    {b : ℝ} (hb : 0 < b) (N : ℕ) :
    let H := ccmFUSuzukiPositiveLogChordCofinalWall b N
    let ω := ccmFUSuzukiPositiveLogChordAdaptiveClock b N
    |ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox b H ω -
        ccmGuinandWeilPrimePolarWeightedWindow b H
          (ccmGuinandWeilThirdGradeCesaroTriangularWeight H)| ≤
      Real.exp 1 / (2 * H ^ (2 : ℕ)) := by
  dsimp only
  let H := ccmFUSuzukiPositiveLogChordCofinalWall b N
  let V := ccmFUSuzukiPositiveLogChordCofinalVariation b N
  let ω := ccmFUSuzukiPositiveLogChordAdaptiveClock b N
  have hbH : b ≤ H := by
    dsimp only [H, ccmFUSuzukiPositiveLogChordCofinalWall]
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hH : 0 < H := hb.trans_le hbH
  have hH1 : 1 ≤ H := by
    dsimp only [H, ccmFUSuzukiPositiveLogChordCofinalWall]
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hV : 0 ≤ V := by
    exact ccmGuinandWeilPrimePolarWeightedWindowVariation_nonneg hbH
  have hω : 0 < ω := ccmFUSuzukiPositiveLogChordAdaptiveClock_pos hb N
  have hωdef : ω = 1 / (H ^ (2 : ℕ) * (V + 1)) := by
    rfl
  have hωH : ω * H ≤ 1 := by
    rw [hωdef]
    have hV1 : 1 ≤ V + 1 := by linarith
    have hden : 1 ≤ H * (V + 1) := by
      simpa only [one_mul] using
        mul_le_mul hH1 hV1 (by norm_num : (0 : ℝ) ≤ 1) hH.le
    rw [show 1 / (H ^ (2 : ℕ) * (V + 1)) * H = 1 / (H * (V + 1)) by
      field_simp [hH.ne']]
    exact (div_le_one (by positivity : 0 < H * (V + 1))).2 hden
  have hexp : Real.exp (ω * H) ≤ Real.exp 1 := Real.exp_le_exp.mpr hωH
  have halg : (ω * H) ^ (2 : ℕ) * V ≤ 1 / H ^ (2 : ℕ) := by
    rw [hωdef]
    exact adaptive_clock_algebra hH hV
  have hraw := abs_positiveLogChordApprox_sub_literal_le_variation hω hb hbH
  change |ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox b H ω -
        ccmGuinandWeilPrimePolarWeightedWindow b H
          (ccmGuinandWeilThirdGradeCesaroTriangularWeight H)| ≤
      ((ω * H) ^ (2 : ℕ) / 2 * Real.exp (ω * H)) * V at hraw
  calc
    |ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox b H ω -
        ccmGuinandWeilPrimePolarWeightedWindow b H
          (ccmGuinandWeilThirdGradeCesaroTriangularWeight H)| ≤
        ((ω * H) ^ (2 : ℕ) / 2 * Real.exp (ω * H)) * V := hraw
    _ = (Real.exp (ω * H) / 2) * ((ω * H) ^ (2 : ℕ) * V) := by ring
    _ ≤ (Real.exp 1 / 2) * (1 / H ^ (2 : ℕ)) :=
      mul_le_mul (by linarith) halg (by positivity) (by positivity)
    _ = Real.exp 1 / (2 * H ^ (2 : ℕ)) := by ring

theorem tendsto_ccmFUSuzukiPositiveLogChordCofinalWall (b : ℝ) :
    Tendsto (ccmFUSuzukiPositiveLogChordCofinalWall b) atTop atTop := by
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have h := tendsto_atTop_add_const_right atTop (b + 1) hnat
  apply h.congr'
  exact Filter.Eventually.of_forall fun N => by
    simp only [ccmFUSuzukiPositiveLogChordCofinalWall]
    ring

theorem tendsto_ccmFUSuzukiPositiveLogChordAdaptiveClock
    {b : ℝ} (hb : 0 < b) :
    Tendsto (ccmFUSuzukiPositiveLogChordAdaptiveClock b) atTop (𝓝 0) := by
  let H : ℕ → ℝ := ccmFUSuzukiPositiveLogChordCofinalWall b
  have hHtop : Tendsto H atTop atTop :=
    tendsto_ccmFUSuzukiPositiveLogChordCofinalWall b
  have hinv : Tendsto (fun N => (H N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hHtop
  have hinvSq : Tendsto (fun N => ((H N)⁻¹) ^ (2 : ℕ)) atTop (𝓝 0) := by
    simpa using hinv.pow 2
  have honeDivSq : Tendsto (fun N => 1 / (H N) ^ (2 : ℕ)) atTop (𝓝 0) := by
    apply hinvSq.congr'
    exact Filter.Eventually.of_forall fun N => by
      simp only [one_div, inv_pow]
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun N =>
      (ccmFUSuzukiPositiveLogChordAdaptiveClock_pos hb N).le)
    (Filter.Eventually.of_forall fun N => ?_)
    honeDivSq
  let V := ccmFUSuzukiPositiveLogChordCofinalVariation b N
  have hbH : b ≤ H N := by
    dsimp only [H, ccmFUSuzukiPositiveLogChordCofinalWall]
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hHN : 0 < H N := hb.trans_le hbH
  have hV : 0 ≤ V :=
    ccmGuinandWeilPrimePolarWeightedWindowVariation_nonneg hbH
  change 1 / ((H N) ^ (2 : ℕ) * (V + 1)) ≤ 1 / (H N) ^ (2 : ℕ)
  apply one_div_le_one_div_of_le (sq_pos_of_pos hHN)
  nlinarith [mul_nonneg (sq_nonneg (H N)) hV]

theorem tendsto_positiveLogChordAdaptiveCofinalApprox_sub_literal
    {b : ℝ} (hb : 0 < b) :
    Tendsto (fun N : ℕ =>
      let H := ccmFUSuzukiPositiveLogChordCofinalWall b N
      let ω := ccmFUSuzukiPositiveLogChordAdaptiveClock b N
      ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox b H ω -
        ccmGuinandWeilPrimePolarWeightedWindow b H
          (ccmGuinandWeilThirdGradeCesaroTriangularWeight H))
      atTop (𝓝 0) := by
  let H : ℕ → ℝ := ccmFUSuzukiPositiveLogChordCofinalWall b
  have hHtop : Tendsto H atTop atTop :=
    tendsto_ccmFUSuzukiPositiveLogChordCofinalWall b
  have hinv : Tendsto (fun N => (H N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hHtop
  have hrate : Tendsto (fun N => Real.exp 1 / (2 * (H N) ^ (2 : ℕ)))
      atTop (𝓝 0) := by
    have hsq : Tendsto (fun N => ((H N)⁻¹) ^ (2 : ℕ)) atTop (𝓝 0) := by
      simpa using hinv.pow 2
    have hmul : Tendsto (fun N => (Real.exp 1 / 2) * ((H N)⁻¹) ^ (2 : ℕ))
        atTop (𝓝 0) := by
      simpa using hsq.const_mul (Real.exp 1 / 2)
    apply hmul.congr'
    exact Filter.Eventually.of_forall fun N => by
      have hbH : b ≤ H N := by
        dsimp only [H, ccmFUSuzukiPositiveLogChordCofinalWall]
        have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith
      have hHN : 0 < H N := hb.trans_le hbH
      field_simp [hHN.ne']
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun N => norm_nonneg _)
    (Filter.Eventually.of_forall fun N => ?_)
    hrate
  simpa only [Real.norm_eq_abs, H] using
    abs_positiveLogChordAdaptiveCofinalApprox_sub_literal_le hb N

end

end RHTower

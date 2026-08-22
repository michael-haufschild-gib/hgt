import GaloisForLFunctions.RHTower.CCMFUSuzukiPositiveConnectedLogChord
import GaloisForLFunctions.RHTower.BoxFubini

/-!
# Suzuki log chords as barycentres of completed signed windows

The connected finite-clock multiplier is a probability mixture of symmetric Mellin shifts.
This file proves that the mixture survives the literal prime-minus-polar readout: finite prime
sums commute with the mixing integral, while compact-box Fubini transports the polar integral.
Consequently the whole finite Suzuki producer, before any absolute-value estimate, is exactly a
convex barycentre of signed completed windows.  Prime and polar regions are never separated.
-/

open Filter Topology MeasureTheory

namespace RHTower

noncomputable section

open GaloisForLFunctions.RHTower

/-- A continuous parameter mixture commutes with the literal completed prime-minus-polar window.
This is a signed identity, not an estimate of the prime and polar channels separately. -/
theorem ccmGuinandWeilPrimePolarWeightedWindow_intervalMixture
    {b H : ℝ} (hbH : b ≤ H) {G : ℝ → ℝ → ℝ}
    (hG : Continuous (Function.uncurry G)) :
    ccmGuinandWeilPrimePolarWeightedWindow b H
        (fun h => ∫ t in (0 : ℝ)..1, G t h) =
      ∫ t in (0 : ℝ)..1,
        ccmGuinandWeilPrimePolarWeightedWindow b H (G t) := by
  have hGslice : ∀ h : ℝ, Continuous (fun t : ℝ => G t h) := by
    intro h
    exact hG.comp (continuous_id.prodMk continuous_const)
  have hGswap : Continuous (Function.uncurry (fun h t : ℝ => G t h)) :=
    hG.comp (continuous_snd.prodMk continuous_fst)
  have hpolarJoint : Continuous (Function.uncurry (fun h t : ℝ =>
      G t h * (2 * Real.cosh (h / 2)))) := by
    exact hGswap.mul ((by fun_prop : Continuous (fun h : ℝ =>
      2 * Real.cosh (h / 2))).comp continuous_fst)
  have hpolarSwap :
      (∫ h in b..H, ∫ t in (0 : ℝ)..1,
          G t h * (2 * Real.cosh (h / 2))) =
        ∫ t in (0 : ℝ)..1, ∫ h in b..H,
          G t h * (2 * Real.cosh (h / 2)) :=
    interval_integral_swap_of_continuous hbH (by norm_num) hpolarJoint
  have hprimeCont : Continuous (fun t : ℝ =>
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        if b < Real.log k then
          criticalMellinAtomWeight k * G t (Real.log k) else 0) := by
    apply _root_.continuous_finsetSum
    intro k hk
    by_cases hbk : b < Real.log k
    · simp only [hbk, if_true]
      exact (hGslice (Real.log k)).const_mul _
    · simp only [hbk, if_false]
      exact continuous_const
  have hprimeInt : IntervalIntegrable (fun t : ℝ =>
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        if b < Real.log k then
          criticalMellinAtomWeight k * G t (Real.log k) else 0)
      volume 0 1 := hprimeCont.intervalIntegrable 0 1
  have hpolarCont : Continuous (fun t : ℝ =>
      ∫ h in b..H, G t h * (2 * Real.cosh (h / 2))) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (hG.mul ((by fun_prop : Continuous (fun h : ℝ =>
        2 * Real.cosh (h / 2))).comp continuous_snd)) b H
  have hpolarInt : IntervalIntegrable (fun t : ℝ =>
      ∫ h in b..H, G t h * (2 * Real.cosh (h / 2))) volume 0 1 :=
    hpolarCont.intervalIntegrable 0 1
  rw [ccmGuinandWeilPrimePolarWeightedWindow]
  simp_rw [ccmGuinandWeilPrimePolarWeightedWindow]
  rw [intervalIntegral.integral_sub hprimeInt hpolarInt]
  congr 1
  · rw [intervalIntegral.integral_finsetSum (fun k hk => by
        by_cases hbk : b < Real.log k
        · simp only [hbk, if_true]
          exact ((hGslice (Real.log k)).const_mul _).intervalIntegrable 0 1
        · simp only [hbk, if_false]
          exact intervalIntegrable_const)]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hbk : b < Real.log k
    · simp only [hbk, if_true]
      rw [intervalIntegral.integral_const_mul]
    · simp only [hbk, if_false, intervalIntegral.integral_zero]
  · calc
      (∫ h in b..H,
          (∫ t in (0 : ℝ)..1, G t h) * (2 * Real.cosh (h / 2))) =
          ∫ h in b..H, ∫ t in (0 : ℝ)..1,
            G t h * (2 * Real.cosh (h / 2)) := by
              apply intervalIntegral.integral_congr
              intro h _
              symm
              exact intervalIntegral.integral_mul_const
                (a := (0 : ℝ)) (b := 1)
                (2 * Real.cosh (h / 2)) (fun t : ℝ => G t h)
      _ = ∫ t in (0 : ℝ)..1, ∫ h in b..H,
            G t h * (2 * Real.cosh (h / 2)) := hpolarSwap

/-- Scalar linearity of the completed signed window. -/
theorem ccmGuinandWeilPrimePolarWeightedWindow_const_mul
    (b H c : ℝ) (F : ℝ → ℝ) :
    ccmGuinandWeilPrimePolarWeightedWindow b H (fun h => c * F h) =
      c * ccmGuinandWeilPrimePolarWeightedWindow b H F := by
  have hpolar : (∫ h in b..H, c * F h * (2 * Real.cosh (h / 2))) =
      c * (∫ h in b..H, F h * (2 * Real.cosh (h / 2))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro h _
    ring
  have hprime :
      (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        if b < Real.log k then criticalMellinAtomWeight k *
          (c * F (Real.log k)) else 0) =
      c * (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        if b < Real.log k then criticalMellinAtomWeight k *
          F (Real.log k) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hbk : b < Real.log k
    · simp only [hbk, if_true]
      ring
    · simp only [hbk, if_false, mul_zero]
  rw [ccmGuinandWeilPrimePolarWeightedWindow,
    ccmGuinandWeilPrimePolarWeightedWindow]
  rw [hprime, hpolar]
  ring

/-- Two tests that agree on every active prime atom and throughout the polar interval have the
same completed signed readout.  Values outside the physical carrier are irrelevant. -/
theorem ccmGuinandWeilPrimePolarWeightedWindow_congr_on
    {b H : ℝ} (hbH : b ≤ H) {F G : ℝ → ℝ}
    (hprime : ∀ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
      b < Real.log k → F (Real.log k) = G (Real.log k))
    (hpolar : ∀ h ∈ Set.Icc b H, F h = G h) :
    ccmGuinandWeilPrimePolarWeightedWindow b H F =
      ccmGuinandWeilPrimePolarWeightedWindow b H G := by
  rw [ccmGuinandWeilPrimePolarWeightedWindow,
    ccmGuinandWeilPrimePolarWeightedWindow]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    by_cases hbk : b < Real.log k
    · simp only [hbk, if_true, hprime k hk hbk]
    · simp only [hbk, if_false]
  · apply intervalIntegral.integral_congr
    intro h hh
    have hmem : h ∈ Set.Icc b H := by
      simpa only [Set.uIcc_of_le hbH] using hh
    change F h * (2 * Real.cosh (h / 2)) =
      G h * (2 * Real.cosh (h / 2))
    rw [hpolar h hmem]

/-- Literal triangular completed window after a symmetric Mellin shift by `ξ`. -/
def ccmFUSuzukiSymmetricMellinShiftedTriangularWindow
    (b H ξ : ℝ) : ℝ :=
  ccmGuinandWeilPrimePolarWeightedWindow b H
    (fun h => ccmGuinandWeilThirdGradeCesaroTriangularWeight H h *
      Real.cosh (ξ * h))

/-- **Signed Suzuki barycentre law.**  Applying the common connected finite-clock multiplier to
the literal triangular prime-minus-polar window is exactly a probability mixture of symmetric
Mellin-shifted completed windows.  The identity retains cancellation across both source regions. -/
theorem ccmFUSuzukiMultiplierWeightedWindow_eq_symmetricShiftMixture
    {ω b H : ℝ} (hω : ω ≠ 0) (hb : 0 < b) (hbH : b ≤ H) :
    ccmGuinandWeilPrimePolarWeightedWindow b H
        (fun h => ccmGuinandWeilThirdGradeCesaroTriangularWeight H h *
          shiftedEulerLogConnectedThirdMultiplier ω h) =
      ∫ t in (0 : ℝ)..1, 3 * (1 - t) ^ 2 *
        ccmFUSuzukiSymmetricMellinShiftedTriangularWindow b H (t * ω) := by
  let G : ℝ → ℝ → ℝ := fun t h =>
    3 * (1 - t) ^ 2 *
      (ccmGuinandWeilThirdGradeCesaroTriangularWeight H (max b h) *
        Real.cosh ((t * ω) * max b h))
  have hmax : Continuous (fun h : ℝ => max b h) :=
    continuous_const.max continuous_id
  have hmax0 : ∀ h : ℝ, max b h ≠ 0 := by
    intro h
    exact ne_of_gt (hb.trans_le (le_max_left b h))
  have hweight : Continuous (fun h : ℝ =>
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H (max b h)) := by
    rw [show (fun h : ℝ =>
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H (max b h)) =
      fun h : ℝ => (32 / (max b h) ^ 3) * (1 - max b h / H) by
        funext h
        rfl]
    exact (continuous_const.div (hmax.pow 3)
      (fun h => pow_ne_zero 3 (hmax0 h))).mul
        (continuous_const.sub (hmax.div_const H))
  have hG : Continuous (Function.uncurry G) := by
    dsimp only [G]
    have hdensity : Continuous (fun p : ℝ × ℝ =>
        3 * (1 - p.1) ^ 2) := by fun_prop
    have hcosh : Continuous (fun p : ℝ × ℝ =>
        Real.cosh ((p.1 * ω) * max b p.2)) := by fun_prop
    exact hdensity.mul ((hweight.comp continuous_snd).mul hcosh)
  have hpoint : ∀ {h : ℝ}, b ≤ h →
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H h *
          shiftedEulerLogConnectedThirdMultiplier ω h =
        ∫ t in (0 : ℝ)..1, G t h := by
    intro h hbh
    rw [shiftedEulerLogConnectedThirdMultiplier_eq_coshMixture hω
      (ne_of_gt (hb.trans_le hbh))]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [G]
    rw [max_eq_right hbh]
    ring
  have hland :
      ccmGuinandWeilPrimePolarWeightedWindow b H
          (fun h => ccmGuinandWeilThirdGradeCesaroTriangularWeight H h *
            shiftedEulerLogConnectedThirdMultiplier ω h) =
        ccmGuinandWeilPrimePolarWeightedWindow b H
          (fun h => ∫ t in (0 : ℝ)..1, G t h) := by
    apply ccmGuinandWeilPrimePolarWeightedWindow_congr_on hbH
    · intro k hk hbk
      rw [hpoint hbk.le]
    · intro h hmem
      rw [hpoint hmem.1]
  calc
    ccmGuinandWeilPrimePolarWeightedWindow b H
        (fun h => ccmGuinandWeilThirdGradeCesaroTriangularWeight H h *
          shiftedEulerLogConnectedThirdMultiplier ω h) =
        ccmGuinandWeilPrimePolarWeightedWindow b H
          (fun h => ∫ t in (0 : ℝ)..1, G t h) := hland
    _ = ∫ t in (0 : ℝ)..1,
          ccmGuinandWeilPrimePolarWeightedWindow b H (G t) :=
      ccmGuinandWeilPrimePolarWeightedWindow_intervalMixture hbH hG
    _ = ∫ t in (0 : ℝ)..1, 3 * (1 - t) ^ 2 *
          ccmFUSuzukiSymmetricMellinShiftedTriangularWindow b H (t * ω) := by
      apply intervalIntegral.integral_congr
      intro t _
      change ccmGuinandWeilPrimePolarWeightedWindow b H
          (fun h => 3 * (1 - t) ^ 2 *
            (ccmGuinandWeilThirdGradeCesaroTriangularWeight H (max b h) *
              Real.cosh ((t * ω) * max b h))) =
        3 * (1 - t) ^ 2 *
          ccmFUSuzukiSymmetricMellinShiftedTriangularWindow b H (t * ω)
      rw [ccmGuinandWeilPrimePolarWeightedWindow_const_mul]
      apply congrArg (fun x : ℝ => 3 * (1 - t) ^ 2 * x)
      apply ccmGuinandWeilPrimePolarWeightedWindow_congr_on hbH
      · intro k hk hbk
        rw [max_eq_right hbk.le]
      · intro h hmem
        rw [max_eq_right hmem.1]

/-- The finite positive connected Suzuki producer itself is the signed Mellin-shift barycentre. -/
theorem ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox_eq_symmetricShiftMixture
    {ω b H : ℝ} (hω : ω ≠ 0) (hb : 0 < b) (hbH : b ≤ H) :
    ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox b H ω =
      ∫ t in (0 : ℝ)..1, 3 * (1 - t) ^ 2 *
        ccmFUSuzukiSymmetricMellinShiftedTriangularWindow b H (t * ω) := by
  rw [ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox_eq_weightedWindow
    hω hb hbH]
  exact ccmFUSuzukiMultiplierWeightedWindow_eq_symmetricShiftMixture hω hb hbH

end

end RHTower

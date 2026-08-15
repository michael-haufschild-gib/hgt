import GaloisForLFunctions.RHTower.GaussHarmonicDoubleDefectEnergy

/-!
# Full convergence of the cubic propagated error

The two smooth double-defect pieces and the hard triple-defect piece are assembled here into the
literal physical cubic outer vector and then into the propagated relative error.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions Filter Topology
open scoped ENNReal

noncomputable section

/-- Extract norm convergence from an ENNReal squared-norm majorant tending to zero. -/
theorem tendsto_norm_of_ofReal_sq_le
    {E : Type*} [SeminormedAddCommGroup E] {w : ℕ → E} {B : ℕ → ℝ≥0∞}
    (hB : Tendsto B atTop (nhds 0))
    (hw : ∀ n, ENNReal.ofReal (‖w n‖ ^ (2 : ℝ)) ≤ B n) :
    Tendsto (fun n => ‖w n‖) atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero] at hB
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hB (ENNReal.ofReal ((ε / 2) ^ 2)) (by
      simpa using pow_pos (half_pos hε) 2))
  refine ⟨N, fun n hn => ?_⟩
  have hofReal : ENNReal.ofReal (‖w n‖ ^ (2 : ℝ)) ≤
      ENNReal.ofReal ((ε / 2) ^ 2) := (hw n).trans (hN n hn)
  have hle : ‖w n‖ ^ (2 : ℝ) ≤ (ε / 2) ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hofReal
  have hnorm2 : ‖w n‖ ^ (2 : ℕ) ≤ (ε / 2) ^ 2 := by
    have hcast : ‖w n‖ ^ (2 : ℕ) = ‖w n‖ ^ (2 : ℝ) := by
      rw [← Real.rpow_natCast (‖w n‖) 2]
      norm_num
    rw [hcast]
    exact hle
  have hfinal : ‖w n‖ ≤ ε / 2 := by
    have h := Real.sqrt_le_sqrt hnorm2
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (half_pos hε).le] at h
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  linarith

/-- First physical smooth contribution vanishes along every escaping sequence. -/
theorem tendsto_norm_gaussCubicOuterDefectPart_firstSource_comp
    {m : ℕ} (hm2 : 2 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) {ι : ℕ → ℤ}
    (hι : Tendsto (fun n : ℕ => (ι n).natAbs) atTop atTop) :
    Tendsto (fun n : ℕ =>
      ‖gaussCubicOuterDefectPart (le_trans one_le_two hm2) k p hp (ι n)
        (gaussCubicFirstSource (le_trans one_le_two hm2) k p hp (ι n))‖)
      atTop (nhds 0) := by
  let C : ℝ := 8 * (p : ℝ) ^ 3
  have hC : 0 ≤ C := by simp only [C]; positivity
  have hB := tendsto_gaussHarmonicDoubleDefectBound_comp C hm2 k p hp hι
  refine tendsto_norm_of_ofReal_sq_le hB fun n => ?_
  have h := ofReal_norm_gaussMovingDefectVector_sq_le_harmonicDouble hC
    (le_trans one_le_two hm2) k p (ι n)
    (gaussPrimeScaleSqBlock hp
      (gaussCubicFirstSource (le_trans one_le_two hm2) k p hp (ι n)))
    (norm_fourierCoeff_gaussPrimeScaleSq_firstSource_le
      (le_trans one_le_two hm2) k p hp (ι n))
  simpa only [C, gaussCubicOuterDefectPart, gaussMovingDefectVector] using h

/-- Third physical smooth contribution vanishes along every escaping sequence. -/
theorem tendsto_norm_gaussCubicOuterDefectPart_thirdSource_comp
    {m : ℕ} (hm2 : 2 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) {ι : ℕ → ℤ}
    (hι : Tendsto (fun n : ℕ => (ι n).natAbs) atTop atTop) :
    Tendsto (fun n : ℕ =>
      ‖gaussCubicOuterDefectPart (le_trans one_le_two hm2) k p hp (ι n)
        (gaussCubicThirdSource (le_trans one_le_two hm2) k p hp (ι n))‖)
      atTop (nhds 0) := by
  let C : ℝ := 16 * (p : ℝ) ^ 2
  have hC : 0 ≤ C := by simp only [C]; positivity
  have hB := tendsto_gaussHarmonicDoubleDefectBound_comp C hm2 k p hp hι
  refine tendsto_norm_of_ofReal_sq_le hB fun n => ?_
  have h := ofReal_norm_gaussMovingDefectVector_sq_le_harmonicDouble hC
    (le_trans one_le_two hm2) k p (ι n)
    (gaussPrimeScaleSqBlock hp
      (gaussCubicThirdSource (le_trans one_le_two hm2) k p hp (ι n)))
    (norm_fourierCoeff_gaussPrimeScaleSq_thirdSource_le
      (le_trans one_le_two hm2) k p hp (ι n))
  simpa only [C, gaussCubicOuterDefectPart, gaussMovingDefectVector] using h

/-- Full literal cubic outer defect vanishes for the three-component Gauss source. -/
theorem tendsto_norm_gaussCubicOuterDefectVector_comp
    (k : Fin 3) (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) {ι : ℕ → ℤ}
    (hι : Tendsto (fun n : ℕ => (ι n).natAbs) atTop atTop) :
    Tendsto (fun n : ℕ =>
      ‖gaussCubicOuterDefectVector (by omega : 1 ≤ 3) k p hp (ι n)‖)
      atTop (nhds 0) := by
  have h1 := tendsto_norm_gaussCubicOuterDefectPart_firstSource_comp
    (by omega : 2 ≤ 3) k p hp hι
  have h2 := tendsto_norm_gaussCubicOuterDefectPart_doubleDefect_comp k p hp hι
  have h3 := tendsto_norm_gaussCubicOuterDefectPart_thirdSource_comp
    (by omega : 2 ≤ 3) k p hp hι
  have hsum := h1.add (h2.add h3)
  simp only [add_zero] at hsum
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hsum
  rw [gaussCubicOuterDefectVector_eq_three_parts]
  exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))

/-- The exact cubic propagated relative-error vector vanishes for `m = 3`. -/
theorem tendsto_norm_gaussCubicPropagatedRelativeErrorVector_comp
    (k : Fin 3) (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) {ι : ℕ → ℤ}
    (hι : Tendsto (fun n : ℕ => (ι n).natAbs) atTop atTop) :
    Tendsto (fun n : ℕ =>
      ‖gaussCubicPropagatedRelativeErrorVector (by omega : 1 ≤ 3) k p hp (ι n)‖)
      atTop (nhds 0) := by
  have hout := tendsto_norm_gaussCubicOuterDefectVector_comp k p hp hι
  have hold : Tendsto (fun n : ℕ =>
      ‖gaussPrincipalRelativeErrorVector (by omega : 1 ≤ 3) k p hp (ι n)‖)
      atTop (nhds 0) := by
    simpa only [gaussPrincipalRelativeErrorVector] using
      tendsto_norm_gaussPrincipalStep_one_sub_amplitude (by omega : 2 ≤ 3) k p hp hι
  have hdom := hout.add (hold.const_mul (Real.sqrt (p : ℝ)))
  simp only [mul_zero, add_zero] at hdom
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hdom
  exact norm_gaussCubicPropagatedRelativeErrorVector_le
    (by omega : 1 ≤ 3) k p hp (ι n)

/-- Cubic principal moment converges to the exact moving-amplitude cubic moment. -/
theorem tendsto_norm_inner_one_gaussPrincipalStep_cube_sub_movingAmplitude_cube
    (k : Fin 3) (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) {ι : ℕ → ℤ}
    (hι : Tendsto (fun n : ℕ => (ι n).natAbs) atTop atTop) :
    Tendsto (fun n : ℕ =>
      ‖(inner ℂ (fourierLp 2 0)
            ((gaussPrincipalStepBlock (by omega : 1 ≤ 3) k p hp (ι n) ^ 3)
              (fourierLp 2 0)) : ℂ) -
        inner ℂ (fourierLp 2 0)
          ((gaussMovingAmplitudeBlock hp
            ((gaussSamplePhase 3 p (ι n) : ℝ) : AddCircle (1 : ℝ)) ^ 3)
              (fourierLp 2 0))‖)
      atTop (nhds 0) := by
  have hs := tendsto_norm_gaussCubicSmoothShiftErrorVector
    (by omega : 1 ≤ 3) k p hp hι
  have hpv := tendsto_norm_gaussCubicPropagatedRelativeErrorVector_comp k p hp hι
  have hsum := hs.add hpv
  simp only [add_zero] at hsum
  have hconst : Tendsto (fun _ : ℕ =>
      2 * (Real.sqrt (p : ℝ) * (p : ℝ))) atTop
      (nhds (2 * (Real.sqrt (p : ℝ) * (p : ℝ)))) := tendsto_const_nhds
  have hfac := hsum.add hconst
  have hprod := hsum.mul hfac
  simp only [zero_add, zero_mul] at hprod
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hprod
  exact norm_inner_one_gaussPrincipalStep_cube_sub_movingAmplitude_cube_le_sharp
    (by omega : 1 ≤ 3) k p hp (ι n)

end

end RHTower

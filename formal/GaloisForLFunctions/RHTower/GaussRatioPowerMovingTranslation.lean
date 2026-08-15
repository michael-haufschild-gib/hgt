import GaloisForLFunctions.RHTower.GaussHigherRatioWeightedDefect
import GaloisForLFunctions.RHTower.GaussUniformTranslationL2

/-!
# Moving-translation estimates with propagated sampled-ratio weights

Vectors produced after `q` normalized Gauss layers carry `q` sampled-ratio factors in each Fourier
coefficient.  This module turns the higher ratio-weighted defect hierarchy into an operator-level
moving-translation theorem for exactly those propagated vectors.
-/

namespace RHTower

open Filter Topology MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-- Parseval transfer from the depth-`q` lattice bound to an arbitrary coefficientwise defect. -/
theorem tendsto_norm_of_gaussRatioPower_fourierDefect
    {m q : ℕ} (hq : q + 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    {ι : ℕ → ℤ} (hι : Tendsto (fun n : ℕ => (ι n).natAbs) atTop atTop)
    (u w : ℕ → Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) {A : ℝ}
    (hcoeff : ∀ (n : ℕ) (j : ℤ),
      ‖fourierCoeff ((w n : AddCircle (1 : ℝ) → ℂ)) j‖ =
        ‖fourierCoeff ((u n : AddCircle (1 : ℝ) → ℂ)) j‖ *
          ‖gaussSampleRatioDefect k p j (ι n)‖)
    (hu : ∀ (n : ℕ) (j : ℤ),
      ‖fourierCoeff ((u n : AddCircle (1 : ℝ) → ℂ)) j‖ ≤
        A / (1 + (j.natAbs : ℝ)) *
          (‖gaussSampleValue k p (ι n + j)‖ / ‖gaussSampleValue k p (ι n)‖) ^ q) :
    Tendsto (fun n : ℕ => ‖w n‖) atTop (nhds 0) := by
  have hdefect := tendsto_gaussTranslationL2RatioPowerDefectBound_comp hq k p A hι
  rw [ENNReal.tendsto_nhds_zero] at hdefect
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hdefect (ENNReal.ofReal ((ε / 2) ^ 2)) (by
    simpa using pow_pos (half_pos hε) 2))
  refine ⟨N, fun n hn => ?_⟩
  have hbound := hN n hn
  have hcongr : ∀ j : ℤ,
      ‖fourierCoeff ((w n : AddCircle (1 : ℝ) → ℂ)) j‖ ^ (2 : ℝ)
        = ‖fourierCoeff ((u n : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2 *
          ‖gaussSampleRatioDefect k p j (ι n)‖ ^ 2 := by
    intro j
    rw [hcoeff n j, Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
      ← Real.rpow_natCast (‖fourierCoeff ((u n : AddCircle (1 : ℝ) → ℂ)) j‖) 2,
      ← Real.rpow_natCast (‖gaussSampleRatioDefect k p j (ι n)‖) 2]
    norm_num
  have hsummable : Summable fun j : ℤ =>
      ‖fourierCoeff ((w n : AddCircle (1 : ℝ) → ℂ)) j‖ ^ (2 : ℝ) := by
    have hmem := lp.memℓp ((fourierBasis (T := (1 : ℝ))).repr (w n))
    have hs := hmem.summable (p := 2) (by norm_num)
    simp only [ENNReal.toReal_ofNat] at hs
    refine hs.congr fun j => ?_
    rw [fourierBasis_repr]
  have hsummable' : Summable fun j : ℤ =>
      ‖fourierCoeff ((u n : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2 *
        ‖gaussSampleRatioDefect k p j (ι n)‖ ^ 2 := hsummable.congr hcongr
  have hnormsq : ‖w n‖ ^ (2 : ℝ) =
      ∑' j : ℤ, ‖fourierCoeff ((u n : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2 *
        ‖gaussSampleRatioDefect k p j (ι n)‖ ^ 2 := by
    rw [norm_sq_eq_tsum_fourierCoeff (w n)]
    exact tsum_congr hcongr
  have hdom : (∑' j : ℤ, ENNReal.ofReal
        (‖fourierCoeff ((u n : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2 *
          ‖gaussSampleRatioDefect k p j (ι n)‖ ^ 2)) ≤
      gaussTranslationL2RatioPowerDefectBound k p q A (ι n) := by
    rw [gaussTranslationL2RatioPowerDefectBound]
    refine ENNReal.tsum_le_tsum fun j => ENNReal.ofReal_le_ofReal ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_
      (pow_nonneg (norm_nonneg (gaussSampleRatioDefect k p j (ι n))) 2)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (hu n j) 2
    calc
      ‖fourierCoeff ((u n : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2
          ≤ (A / (1 + (j.natAbs : ℝ)) *
            (‖gaussSampleValue k p (ι n + j)‖ /
              ‖gaussSampleValue k p (ι n)‖) ^ q) ^ 2 := h2
      _ = A ^ 2 / (1 + (j.natAbs : ℝ)) ^ 2 *
          (‖gaussSampleValue k p (ι n + j)‖ /
            ‖gaussSampleValue k p (ι n)‖) ^ (2 * q) := by
        set R : ℝ := ‖gaussSampleValue k p (ι n + j)‖ /
          ‖gaussSampleValue k p (ι n)‖ with hR
        have hd : (1 + (j.natAbs : ℝ)) ≠ 0 := by positivity
        rw [show 2 * q = q * 2 by omega, pow_mul]
        field_simp [hd]
  have hofReal : ENNReal.ofReal (‖w n‖ ^ (2 : ℝ)) ≤
      ENNReal.ofReal ((ε / 2) ^ 2) := by
    rw [hnormsq, ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsummable']
    exact hdom.trans hbound
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
    rwa [Real.sqrt_sq (norm_nonneg (w n)), Real.sqrt_sq (half_pos hε).le] at h
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg (w n))]
  linarith

/-- Conjugated normalized block: depth-`q` propagated vectors converge to their moving rotation. -/
theorem tendsto_norm_gaussShiftedBlockOf_sub_rotation_ratioPowerFamily
    {m q : ℕ} (hq : q + 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    {ι : ℕ → ℤ} (hι : Tendsto (fun n : ℕ => (ι n).natAbs) atTop atTop)
    (u : ℕ → Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) {A : ℝ}
    (hu : ∀ (n : ℕ) (j : ℤ),
      ‖fourierCoeff ((u n : AddCircle (1 : ℝ) → ℂ)) j‖ ≤
        A / (1 + (j.natAbs : ℝ)) *
          (‖gaussSampleValue k p (ι n + j)‖ / ‖gaussSampleValue k p (ι n)‖) ^ q) :
    Tendsto (fun n : ℕ =>
      ‖gaussShiftedBlockOf (by omega : 1 ≤ m) k p (ι n) (u n) -
        gaussRotationBlock ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) (u n)‖)
      atTop (nhds 0) := by
  let hm : 1 ≤ m := by omega
  let w : ℕ → Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) := fun n =>
    gaussShiftedBlockOf hm k p (ι n) (u n) -
      gaussRotationBlock ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) (u n)
  refine tendsto_norm_of_gaussRatioPower_fourierDefect hq k p hι u w ?_ hu
  intro n j
  have hsub : fourierCoeff ((w n : AddCircle (1 : ℝ) → ℂ)) j =
      fourierCoeff ((gaussShiftedBlockOf hm k p (ι n) (u n) : AddCircle (1 : ℝ) → ℂ)) j -
        fourierCoeff ((gaussRotationBlock
          ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) (u n) :
            AddCircle (1 : ℝ) → ℂ)) j := by
    simp only [w]
    rw [← fourierBasis_repr, ← fourierBasis_repr, ← fourierBasis_repr, map_sub]
    rfl
  rw [hsub, norm_fourierCoeff_shiftedBlockOf_sub_rotation hm k p]

/-- Unconjugated normalized block: same depth-`q` propagated moving-translation law. -/
theorem tendsto_norm_gaussShiftedBlockDiag_sub_rotationInv_ratioPowerFamily
    {m q : ℕ} (hq : q + 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    {ι : ℕ → ℤ} (hι : Tendsto (fun n : ℕ => (ι n).natAbs) atTop atTop)
    (u : ℕ → Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) {A : ℝ}
    (hu : ∀ (n : ℕ) (j : ℤ),
      ‖fourierCoeff ((u n : AddCircle (1 : ℝ) → ℂ)) j‖ ≤
        A / (1 + (j.natAbs : ℝ)) *
          (‖gaussSampleValue k p (ι n + j)‖ / ‖gaussSampleValue k p (ι n)‖) ^ q) :
    Tendsto (fun n : ℕ =>
      ‖gaussShiftedBlockDiag (by omega : 1 ≤ m) k p (ι n) (u n) -
        gaussRotationBlockInv
          ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) (u n)‖)
      atTop (nhds 0) := by
  let hm : 1 ≤ m := by omega
  let w : ℕ → Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) := fun n =>
    gaussShiftedBlockDiag hm k p (ι n) (u n) -
      gaussRotationBlockInv
        ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) (u n)
  refine tendsto_norm_of_gaussRatioPower_fourierDefect hq k p hι u w ?_ hu
  intro n j
  have hsub : fourierCoeff ((w n : AddCircle (1 : ℝ) → ℂ)) j =
      fourierCoeff ((gaussShiftedBlockDiag hm k p (ι n) (u n) : AddCircle (1 : ℝ) → ℂ)) j -
        fourierCoeff ((gaussRotationBlockInv
          ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) (u n) :
            AddCircle (1 : ℝ) → ℂ)) j := by
    simp only [w]
    rw [← fourierBasis_repr, ← fourierBasis_repr, ← fourierBasis_repr, map_sub]
    rfl
  rw [hsub, norm_fourierCoeff_shiftedBlockDiag_sub_rotationInv hm k p]

end

end RHTower

import GaloisForLFunctions.RHTower.GaussLowModeKernelBound

/-!
# The relative one-step error on the spike vanishes

The normalized shifted diagonal applied to the reciprocal-square transform of the lattice defect
tends to zero in `L²`.  The vector is split at the band `|j| ≤ n/4`.  The high modes carry defect
mass `O(log n / n)` and are multiplied by a ratio bounded by `(K n)^{1/2}`, so they contribute
`O(log n / n^{1/2})`.  The low modes are far from the spike, so their transform has coefficients
`O(log n / n)` there, and the spike carries only linear ratio mass, so they contribute
`O(log² n / n)`.  Off the spike the ratio is bounded by a constant and the whole vector is small
because the defect is.
-/

namespace RHTower

open Filter Topology MeasureTheory GaloisForLFunctions

open scoped ENNReal NNReal

noncomputable section

variable {m : ℕ}

/-! ## Coefficientwise bookkeeping -/

theorem fourierCoeff_sub_lp (u v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (j : ℤ) :
    fourierCoeff (((u - v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
        AddCircle (1 : ℝ) → ℂ)) j
      = fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j
        - fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) j := by
  rw [← fourierBasis_repr, ← fourierBasis_repr, ← fourierBasis_repr, map_sub]
  rfl

/-- The coefficients of the lattice defect vector. -/
theorem norm_fourierCoeff_defectVector (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (n : ℤ)
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (j : ℤ) :
    ‖fourierCoeff (((gaussShiftedBlockOf hm k p n u -
        gaussRotationBlock ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ)) u :
          Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) : AddCircle (1 : ℝ) → ℂ)) j‖
      = ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ * ‖gaussSampleRatioDefect k p j n‖ := by
  rw [fourierCoeff_sub_lp, norm_fourierCoeff_shiftedBlockOf_sub_rotation hm k p]

/-- Parseval in the form used for the truncation tail. -/
theorem ofReal_norm_sq_eq_tsum (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    ENNReal.ofReal (‖u‖ ^ (2 : ℝ))
      = ∑' j : ℤ, ENNReal.ofReal (‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2) := by
  have hcongr : ∀ j : ℤ, ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ (2 : ℝ)
      = ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2 := by
    intro j
    rw [← Real.rpow_natCast (‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖) 2]
    norm_num
  have hsummable : Summable fun j : ℤ =>
      ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ (2 : ℝ) := by
    have hmem := lp.memℓp ((fourierBasis (T := (1 : ℝ))).repr u)
    have hs := hmem.summable (p := 2) (by norm_num)
    simp only [ENNReal.toReal_ofNat] at hs
    refine hs.congr fun j => ?_
    rw [fourierBasis_repr]
  rw [norm_sq_eq_tsum_fourierCoeff u, tsum_congr hcongr,
    ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) (hsummable.congr hcongr)]

/-- The truncation does not increase the norm. -/
theorem norm_fourierTruncate_le (S : Finset ℤ)
    (w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    ‖fourierTruncate S w‖ ≤ ‖w‖ := by
  classical
  have hsq : ENNReal.ofReal (‖fourierTruncate S w‖ ^ (2 : ℝ))
      ≤ ENNReal.ofReal (‖w‖ ^ (2 : ℝ)) := by
    rw [ofReal_norm_sq_eq_tsum, ofReal_norm_sq_eq_tsum]
    refine ENNReal.tsum_le_tsum fun j => ?_
    rw [fourierCoeff_fourierTruncate]
    by_cases hj : j ∈ S
    · rw [if_pos hj]
    · rw [if_neg hj, norm_zero]
      simp
  have hle : ‖fourierTruncate S w‖ ^ (2 : ℝ) ≤ ‖w‖ ^ (2 : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hsq
  have hnat : ‖fourierTruncate S w‖ ^ (2 : ℕ) ≤ ‖w‖ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (‖fourierTruncate S w‖) 2, ← Real.rpow_natCast (‖w‖) 2]
    exact_mod_cast hle
  have h := Real.sqrt_le_sqrt hnat
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

/-- The truncation tail of the lattice defect vector. -/
theorem ofReal_norm_sq_sub_fourierTruncate_le (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    {K : ℝ} (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    {A : ℝ} (I J : ℕ)
    {w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))}
    (hw : ∀ j : ℤ, ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j‖
      ≤ (A / (1 + (j.natAbs : ℝ))) * ‖gaussSampleRatioDefect k p j (I : ℤ)‖) :
    ENNReal.ofReal (‖w - fourierTruncate (Finset.Icc (-(J : ℤ)) (J : ℤ)) w‖ ^ (2 : ℝ))
      ≤ ENNReal.ofReal (16 * A ^ 2 * (1 + K) / (1 + (J : ℝ))
          + 16 * K * A ^ 2 * (1 + Real.log (I : ℝ)) / (I : ℝ)) := by
  classical
  rw [ofReal_norm_sq_eq_tsum]
  refine le_trans (ENNReal.tsum_le_tsum ?_)
    (tsum_defect_highMode_le hm k p hK hKb A I J)
  intro j
  rw [fourierCoeff_sub_lp, fourierCoeff_fourierTruncate]
  by_cases hj : j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ)
  · rw [if_pos hj, sub_self, norm_zero]
    have hnot : ¬ J < j.natAbs := by
      rw [Finset.mem_Icc] at hj
      omega
    rw [if_neg hnot]
    simp
  · rw [if_neg hj, sub_zero]
    have hyes : J < j.natAbs := by
      rw [Finset.mem_Icc] at hj
      omega
    rw [if_pos hyes]
    refine ENNReal.ofReal_le_ofReal ?_
    have hb := hw j
    have hnn : (0 : ℝ) ≤ (A / (1 + (j.natAbs : ℝ))) * ‖gaussSampleRatioDefect k p j (I : ℤ)‖ :=
      le_trans (norm_nonneg _) hb
    have hsq := mul_self_le_mul_self (norm_nonneg _) hb
    calc ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2
        = ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j‖ *
            ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j‖ := by ring
      _ ≤ ((A / (1 + (j.natAbs : ℝ))) * ‖gaussSampleRatioDefect k p j (I : ℤ)‖) *
            ((A / (1 + (j.natAbs : ℝ))) * ‖gaussSampleRatioDefect k p j (I : ℤ)‖) := hsq
      _ = (A / (1 + (j.natAbs : ℝ))) ^ 2 * ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2 := by
          ring

end

end RHTower

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

/-! ## The two ratio-weighted norm bounds -/

theorem gaussShiftedBlockDiag_add (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (n : ℤ)
    (u v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    gaussShiftedBlockDiag hm k p n (u + v)
      = gaussShiftedBlockDiag hm k p n u + gaussShiftedBlockDiag hm k p n v := by
  rw [gaussShiftedBlockDiag, gaussShiftedBlockDiag, gaussShiftedBlockDiag]
  simp only [map_add, smul_add]

/-- The global ratio bound gives a norm bound with the square-root factor. -/
theorem norm_sq_gaussShiftedBlockDiag_le_global (hm : 2 ≤ m) (k : Fin m) (p : Nat.Primes)
    {K : ℝ} (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    (I : ℕ) (v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    ‖gaussShiftedBlockDiag (le_trans one_le_two hm) k p (I : ℤ) v‖ ^ (2 : ℝ)
      ≤ (1 + (K * (I : ℝ)) ^ (1 / 2 : ℝ)) * ‖v‖ ^ (2 : ℝ) := by
  have hpow : (0 : ℝ) ≤ (K * (I : ℝ)) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hc : (0 : ℝ) ≤ 1 + (K * (I : ℝ)) ^ (1 / 2 : ℝ) := by linarith
  have hvn : (0 : ℝ) ≤ ‖v‖ ^ (2 : ℝ) := Real.rpow_nonneg (norm_nonneg v) _
  have hsq : ENNReal.ofReal
      (‖gaussShiftedBlockDiag (le_trans one_le_two hm) k p (I : ℤ) v‖ ^ (2 : ℝ))
      ≤ ENNReal.ofReal ((1 + (K * (I : ℝ)) ^ (1 / 2 : ℝ)) * ‖v‖ ^ (2 : ℝ)) := by
    rw [norm_sq_gaussShiftedBlockDiag_eq_tsum]
    have hpoint : ∀ l : ℤ,
        ENNReal.ofReal (gaussShiftRatio k p (I : ℤ) l ^ 2 *
          ‖fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) l‖ ^ 2)
        ≤ ENNReal.ofReal (1 + (K * (I : ℝ)) ^ (1 / 2 : ℝ)) *
            ENNReal.ofReal (‖fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) l‖ ^ 2) := by
      intro l
      rw [← ENNReal.ofReal_mul hc]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (gaussShiftRatio_sq_le_global hm k p hK hKb I l) (by positivity))
    refine le_trans (ENNReal.tsum_le_tsum hpoint) ?_
    rw [ENNReal.tsum_mul_left, ← ofReal_norm_sq_eq_tsum, ← ENNReal.ofReal_mul hc]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hsq

/-- The split bound: a constant off the spike, the linear spike mass on it. -/
theorem norm_sq_gaussShiftedBlockDiag_spike_le (hm : 2 ≤ m) (k : Fin m) (p : Nat.Primes)
    {K : ℝ} (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    (I : ℕ) (v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) {ε : ℝ} (hε : 0 ≤ ε)
    (hv : ∀ l : ℤ, 2 * ((I : ℤ) + l).natAbs < I →
      ‖fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) l‖ ≤ ε) :
    ‖gaussShiftedBlockDiag (le_trans one_le_two hm) k p (I : ℤ) v‖ ^ (2 : ℝ)
      ≤ (1 + 2 * K) * ‖v‖ ^ (2 : ℝ) + ε ^ 2 * ((2 + 4 * K ^ (1 / 2 : ℝ)) * (I : ℝ)) := by
  classical
  have hKs : (0 : ℝ) ≤ K ^ (1 / 2 : ℝ) := Real.rpow_nonneg hK.le _
  have hvn : (0 : ℝ) ≤ ‖v‖ ^ (2 : ℝ) := Real.rpow_nonneg (norm_nonneg v) _
  have hsq : ENNReal.ofReal
      (‖gaussShiftedBlockDiag (le_trans one_le_two hm) k p (I : ℤ) v‖ ^ (2 : ℝ))
      ≤ ENNReal.ofReal ((1 + 2 * K) * ‖v‖ ^ (2 : ℝ))
        + ENNReal.ofReal (ε ^ 2 * ((2 + 4 * K ^ (1 / 2 : ℝ)) * (I : ℝ))) := by
    rw [norm_sq_gaussShiftedBlockDiag_eq_tsum]
    have hpoint : ∀ l : ℤ,
        ENNReal.ofReal (gaussShiftRatio k p (I : ℤ) l ^ 2 *
          ‖fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) l‖ ^ 2)
        ≤ ENNReal.ofReal (1 + 2 * K) *
            ENNReal.ofReal (‖fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) l‖ ^ 2)
          + (if 2 * ((I : ℤ) + l).natAbs < I then
              ENNReal.ofReal (ε ^ 2) *
                ENNReal.ofReal (gaussShiftRatio k p (I : ℤ) l ^ 2) else 0) := by
      intro l
      by_cases hsp : 2 * ((I : ℤ) + l).natAbs < I
      · rw [if_pos hsp]
        have hb := hv l hsp
        have hrn : (0 : ℝ) ≤ gaussShiftRatio k p (I : ℤ) l ^ 2 := by positivity
        have hcoeff : ‖fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) l‖ ^ 2 ≤ ε ^ 2 := by
          nlinarith [norm_nonneg (fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) l)]
        have hstep : gaussShiftRatio k p (I : ℤ) l ^ 2 *
            ‖fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) l‖ ^ 2
            ≤ ε ^ 2 * gaussShiftRatio k p (I : ℤ) l ^ 2 := by
          nlinarith [hrn, hcoeff]
        calc ENNReal.ofReal (gaussShiftRatio k p (I : ℤ) l ^ 2 *
              ‖fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) l‖ ^ 2)
            ≤ ENNReal.ofReal (ε ^ 2 * gaussShiftRatio k p (I : ℤ) l ^ 2) :=
              ENNReal.ofReal_le_ofReal hstep
          _ = ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal (gaussShiftRatio k p (I : ℤ) l ^ 2) :=
              ENNReal.ofReal_mul (by positivity)
          _ ≤ ENNReal.ofReal (1 + 2 * K) *
                ENNReal.ofReal (‖fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) l‖ ^ 2)
              + ENNReal.ofReal (ε ^ 2) *
                ENNReal.ofReal (gaussShiftRatio k p (I : ℤ) l ^ 2) := le_add_self
      · rw [if_neg hsp, add_zero]
        have hstep : gaussShiftRatio k p (I : ℤ) l ^ 2 *
            ‖fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) l‖ ^ 2
            ≤ (1 + 2 * K) * ‖fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) l‖ ^ 2 :=
          mul_le_mul_of_nonneg_right
            (gaussShiftRatio_sq_le_of_not_spike (le_trans one_le_two hm) k p hK hKb I l
              (by omega)) (by positivity)
        calc ENNReal.ofReal (gaussShiftRatio k p (I : ℤ) l ^ 2 *
              ‖fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) l‖ ^ 2)
            ≤ ENNReal.ofReal ((1 + 2 * K) *
                ‖fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) l‖ ^ 2) :=
              ENNReal.ofReal_le_ofReal hstep
          _ = ENNReal.ofReal (1 + 2 * K) *
                ENNReal.ofReal (‖fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) l‖ ^ 2) :=
              ENNReal.ofReal_mul (by positivity)
    refine le_trans (ENNReal.tsum_le_tsum hpoint) ?_
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ← ofReal_norm_sq_eq_tsum,
      ← ENNReal.ofReal_mul (by positivity)]
    refine add_le_add le_rfl ?_
    have hmove : ∀ l : ℤ, (if 2 * ((I : ℤ) + l).natAbs < I then
        ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal (gaussShiftRatio k p (I : ℤ) l ^ 2) else 0)
        = ENNReal.ofReal (ε ^ 2) * (if 2 * ((I : ℤ) + l).natAbs < I then
            ENNReal.ofReal (gaussShiftRatio k p (I : ℤ) l ^ 2) else 0) := by
      intro l
      by_cases h : 2 * ((I : ℤ) + l).natAbs < I
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [tsum_congr hmove, ENNReal.tsum_mul_left]
    refine le_trans (mul_le_mul_right (tsum_spike_gaussShiftRatio_sq_le hm k p hK hKb I) _) ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hsq
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hsq

/-! ## The two vanishing rates -/

theorem tendsto_one_add_log_div_sqrt_atTop_zero :
    Tendsto (fun I : ℕ => (1 + Real.log (I : ℝ)) / Real.sqrt (I : ℝ)) atTop (nhds 0) := by
  have hbase := tendsto_one_add_log_div_rpow_atTop_zero (t := 1 / 2) (by norm_num)
  refine hbase.congr fun I => ?_
  rw [Real.sqrt_eq_rpow]

theorem tendsto_const_mul_one_add_log_div_sqrt (C : ℝ) :
    Tendsto (fun I : ℕ => C * ((1 + Real.log (I : ℝ)) / Real.sqrt (I : ℝ))) atTop (nhds 0) := by
  have h := tendsto_one_add_log_div_sqrt_atTop_zero.const_mul C
  simpa using h

theorem tendsto_const_mul_one_add_log_div_sqrt_sq (C : ℝ) :
    Tendsto (fun I : ℕ => C * ((1 + Real.log (I : ℝ)) / Real.sqrt (I : ℝ)) ^ 2)
      atTop (nhds 0) := by
  have hsq := tendsto_one_add_log_div_sqrt_atTop_zero.pow 2
  have h := hsq.const_mul C
  simpa using h

/-! ## Elementary comparisons at the truncation scale -/

theorem log_shift_le (I : ℕ) (hI : 1 ≤ I) :
    1 + Real.log (((I / 4 : ℕ) : ℝ) + 2) ≤ 3 * (1 + Real.log (I : ℝ)) := by
  have hIR : (1 : ℝ) ≤ (I : ℝ) := by exact_mod_cast hI
  have hJ : ((I / 4 : ℕ) : ℝ) ≤ (I : ℝ) := by
    have : (I / 4 : ℕ) ≤ I := Nat.div_le_self I 4
    exact_mod_cast this
  have hle : ((I / 4 : ℕ) : ℝ) + 2 ≤ 3 * (I : ℝ) := by linarith
  have hpos : (0 : ℝ) < ((I / 4 : ℕ) : ℝ) + 2 := by positivity
  have hlog : Real.log (((I / 4 : ℕ) : ℝ) + 2) ≤ Real.log (3 * (I : ℝ)) :=
    Real.log_le_log hpos hle
  have hsplit : Real.log (3 * (I : ℝ)) = Real.log 3 + Real.log (I : ℝ) := by
    rw [Real.log_mul (by norm_num) (by linarith)]
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    linarith
  have hlogI : 0 ≤ Real.log (I : ℝ) := Real.log_nonneg hIR
  linarith [hlog, hsplit, hlog3, hlogI]

theorem sqrt_le_self_nat {I : ℕ} (hI : 1 ≤ I) : Real.sqrt (I : ℝ) ≤ (I : ℝ) := by
  have hIR : (1 : ℝ) ≤ (I : ℝ) := by exact_mod_cast hI
  have h1 : (1 : ℝ) ≤ Real.sqrt (I : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hIR
  have hsq : Real.sqrt (I : ℝ) * Real.sqrt (I : ℝ) = (I : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  nlinarith [h1, hsq]

theorem sqrt_scale_bound {D sK L : ℝ} (hD : 0 ≤ D) (hsK : 0 ≤ sK) (hL : 1 ≤ L) {I : ℕ}
    (hI : 1 ≤ I) :
    (1 + sK * Real.sqrt (I : ℝ)) * (D * L / (I : ℝ))
      ≤ (2 * (1 + sK) * D) * (L / Real.sqrt (I : ℝ)) := by
  have hIR : (1 : ℝ) ≤ (I : ℝ) := by exact_mod_cast hI
  have hIpos : (0 : ℝ) < (I : ℝ) := by linarith
  have hsI : (1 : ℝ) ≤ Real.sqrt (I : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hIR
  have hsIpos : (0 : ℝ) < Real.sqrt (I : ℝ) := by linarith
  have hsq : Real.sqrt (I : ℝ) * Real.sqrt (I : ℝ) = (I : ℝ) :=
    Real.mul_self_sqrt (le_of_lt hIpos)
  have hlhs : (1 + sK * Real.sqrt (I : ℝ)) * (D * L / (I : ℝ))
      = ((1 + sK * Real.sqrt (I : ℝ)) * (D * L)) / (I : ℝ) := by ring
  have hrhs : (2 * (1 + sK) * D) * (L / Real.sqrt (I : ℝ))
      = ((2 * (1 + sK) * D) * L) / Real.sqrt (I : ℝ) := by ring
  rw [hlhs, hrhs, div_le_div_iff₀ hIpos hsIpos]
  have hDL : 0 ≤ D * L := mul_nonneg hD (le_trans zero_le_one hL)
  nlinarith [hsq, hsI, hsK, hDL, mul_nonneg hDL hsK, mul_nonneg hDL hsIpos.le]

/-! ## The high-mode contribution -/

/-- The high modes of the defect are multiplied by a ratio of size `(K n)^{1/2}` but carry mass
`O(log n / n)`, so they contribute `O(log n / n^{1/2})`. -/
theorem norm_sq_shiftedDiag_symbol_highMode_le (hm : 2 ≤ m) (k : Fin m) (p : Nat.Primes)
    {c : AddCircle (1 : ℝ) → ℂ} (hc : Measurable c) (hC : ∀ x, ‖c x‖ ≤ 1)
    {K : ℝ} (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    {A : ℝ} {W : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))} {I : ℕ} (hI : 1 ≤ I)
    (hW : ∀ j : ℤ, ‖fourierCoeff ((W : AddCircle (1 : ℝ) → ℂ)) j‖
      ≤ (A / (1 + (j.natAbs : ℝ))) * ‖gaussSampleRatioDefect k p j (I : ℤ)‖) :
    ‖gaussShiftedBlockDiag (le_trans one_le_two hm) k p (I : ℤ)
        (MeasureTheory.lpBoundedMulCLM hc zero_le_one hC
          (W - fourierTruncate (Finset.Icc (-((I / 4 : ℕ) : ℤ)) ((I / 4 : ℕ) : ℤ)) W))‖ ^ (2 : ℝ)
      ≤ (2 * (1 + Real.sqrt K) * (64 * A ^ 2 * (1 + K) + 16 * K * A ^ 2)) *
          ((1 + Real.log (I : ℝ)) / Real.sqrt (I : ℝ)) := by
  have hm1 : 1 ≤ m := le_trans one_le_two hm
  set J : ℕ := I / 4 with hJdef
  set W2 : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    W - fourierTruncate (Finset.Icc (-(J : ℤ)) (J : ℤ)) W with hW2def
  set V2 : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    MeasureTheory.lpBoundedMulCLM hc zero_le_one hC W2 with hV2def
  have hIR : (1 : ℝ) ≤ (I : ℝ) := by exact_mod_cast hI
  have hIpos : (0 : ℝ) < (I : ℝ) := by linarith
  have hLlog : (0 : ℝ) ≤ Real.log (I : ℝ) := Real.log_nonneg hIR
  have hL : (1 : ℝ) ≤ 1 + Real.log (I : ℝ) := by linarith
  have hA2 : (0 : ℝ) ≤ A ^ 2 := sq_nonneg A
  have h1 := norm_sq_gaussShiftedBlockDiag_le_global hm k p hK hKb I V2
  have hnormV2 : ‖V2‖ ≤ ‖W2‖ := by
    have hop := (MeasureTheory.lpBoundedMulCLM hc zero_le_one hC).le_opNorm W2
    have hb := MeasureTheory.norm_lpBoundedMulCLM_le (p := 2) (μ := AddCircle.haarAddCircle (T := (1 : ℝ))) hc zero_le_one hC
    calc ‖V2‖ ≤ ‖MeasureTheory.lpBoundedMulCLM hc zero_le_one hC‖ * ‖W2‖ := hop
      _ ≤ 1 * ‖W2‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ = ‖W2‖ := one_mul _
  have h2 : ‖V2‖ ^ (2 : ℝ) ≤ ‖W2‖ ^ (2 : ℝ) :=
    Real.rpow_le_rpow (norm_nonneg _) hnormV2 (by norm_num)
  have hbnn : (0 : ℝ) ≤ 16 * A ^ 2 * (1 + K) / (1 + (J : ℝ))
      + 16 * K * A ^ 2 * (1 + Real.log (I : ℝ)) / (I : ℝ) := by
    have ha : (0 : ℝ) ≤ 16 * A ^ 2 * (1 + K) / (1 + (J : ℝ)) := by positivity
    have hb : (0 : ℝ) ≤ 16 * K * A ^ 2 * (1 + Real.log (I : ℝ)) / (I : ℝ) := by positivity
    linarith
  have h3 : ‖W2‖ ^ (2 : ℝ) ≤ 16 * A ^ 2 * (1 + K) / (1 + (J : ℝ))
      + 16 * K * A ^ 2 * (1 + Real.log (I : ℝ)) / (I : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff hbnn).mp
      (ofReal_norm_sq_sub_fourierTruncate_le hm1 k p hK hKb I J hW)
  have hfacnn : (0 : ℝ) ≤ 1 + (K * (I : ℝ)) ^ (1 / 2 : ℝ) := by
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ K * (I : ℝ) by positivity) (1 / 2 : ℝ)
    linarith
  have hchain : ‖gaussShiftedBlockDiag (le_trans one_le_two hm) k p (I : ℤ) V2‖ ^ (2 : ℝ)
      ≤ (1 + (K * (I : ℝ)) ^ (1 / 2 : ℝ)) *
        (16 * A ^ 2 * (1 + K) / (1 + (J : ℝ))
          + 16 * K * A ^ 2 * (1 + Real.log (I : ℝ)) / (I : ℝ)) :=
    h1.trans (mul_le_mul_of_nonneg_left (h2.trans h3) hfacnn)
  refine hchain.trans ?_
  have hsplit : (K * (I : ℝ)) ^ (1 / 2 : ℝ) = Real.sqrt K * Real.sqrt (I : ℝ) := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul hK.le]
  have hJR : (I : ℝ) ≤ 4 + 4 * (J : ℝ) := by
    have hnat : I ≤ 4 + 4 * J := by rw [hJdef]; omega
    exact_mod_cast hnat
  have hIle : (I : ℝ) ≤ 4 * (1 + (J : ℝ)) := by linarith
  have hii : 16 * A ^ 2 * (1 + K) / (1 + (J : ℝ)) ≤ 64 * A ^ 2 * (1 + K) / (I : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hIpos]
    nlinarith [mul_le_mul_of_nonneg_left hIle
      (show (0 : ℝ) ≤ 16 * A ^ 2 * (1 + K) by positivity)]
  have hiii : 16 * A ^ 2 * (1 + K) / (1 + (J : ℝ))
      + 16 * K * A ^ 2 * (1 + Real.log (I : ℝ)) / (I : ℝ)
      ≤ (64 * A ^ 2 * (1 + K) + 16 * K * A ^ 2) * (1 + Real.log (I : ℝ)) / (I : ℝ) := by
    have hstep : 64 * A ^ 2 * (1 + K) / (I : ℝ)
        ≤ 64 * A ^ 2 * (1 + K) * (1 + Real.log (I : ℝ)) / (I : ℝ) := by
      rw [div_le_div_iff₀ hIpos hIpos]
      nlinarith [mul_le_mul_of_nonneg_left hL
        (show (0 : ℝ) ≤ 64 * A ^ 2 * (1 + K) * (I : ℝ) by positivity)]
    have hsum : 64 * A ^ 2 * (1 + K) * (1 + Real.log (I : ℝ)) / (I : ℝ)
        + 16 * K * A ^ 2 * (1 + Real.log (I : ℝ)) / (I : ℝ)
        = (64 * A ^ 2 * (1 + K) + 16 * K * A ^ 2) * (1 + Real.log (I : ℝ)) / (I : ℝ) := by
      field_simp
    linarith [hii, hstep, hsum]
  have hDnn : (0 : ℝ) ≤ 64 * A ^ 2 * (1 + K) + 16 * K * A ^ 2 := by positivity
  have hsKnn : (0 : ℝ) ≤ Real.sqrt K := Real.sqrt_nonneg K
  calc (1 + (K * (I : ℝ)) ^ (1 / 2 : ℝ)) *
        (16 * A ^ 2 * (1 + K) / (1 + (J : ℝ))
          + 16 * K * A ^ 2 * (1 + Real.log (I : ℝ)) / (I : ℝ))
      ≤ (1 + Real.sqrt K * Real.sqrt (I : ℝ)) *
          ((64 * A ^ 2 * (1 + K) + 16 * K * A ^ 2) * (1 + Real.log (I : ℝ)) / (I : ℝ)) := by
        rw [hsplit] at hfacnn ⊢
        exact mul_le_mul_of_nonneg_left hiii hfacnn
    _ ≤ (2 * (1 + Real.sqrt K) * (64 * A ^ 2 * (1 + K) + 16 * K * A ^ 2)) *
          ((1 + Real.log (I : ℝ)) / Real.sqrt (I : ℝ)) :=
        sqrt_scale_bound hDnn hsKnn hL hI

/-! ## The low-mode contribution -/

/-- The low modes are separated from the spike, so the kernel makes their transform small there,
and the spike carries only linear ratio mass. -/
theorem norm_sq_shiftedDiag_symbol_lowMode_le (hm : 2 ≤ m) (k : Fin m) (p : Nat.Primes)
    {c : AddCircle (1 : ℝ) → ℂ} (hc : Measurable c) (hC : ∀ x, ‖c x‖ ≤ 1)
    (hreal : ∀ x, starRingEnd ℂ (c x) = c x) {Ak : ℝ}
    (hAk : ∀ x : ℤ, ‖fourierCoeff c x‖ ≤ Ak / (1 + (x.natAbs : ℝ)))
    {K : ℝ} (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    {A : ℝ} (hA : 0 ≤ A) {W : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))} {I : ℕ}
    (hI : 1 ≤ I)
    (hW : ∀ j : ℤ, ‖fourierCoeff ((W : AddCircle (1 : ℝ) → ℂ)) j‖
      ≤ (A / (1 + (j.natAbs : ℝ))) * ‖gaussSampleRatioDefect k p j (I : ℤ)‖) :
    ‖gaussShiftedBlockDiag (le_trans one_le_two hm) k p (I : ℤ)
        (MeasureTheory.lpBoundedMulCLM hc zero_le_one hC
          (fourierTruncate (Finset.Icc (-((I / 4 : ℕ) : ℤ)) ((I / 4 : ℕ) : ℤ)) W))‖ ^ (2 : ℝ)
      ≤ (1 + 2 * K) * ‖W‖ ^ (2 : ℝ)
        + ((24 * Ak * A * (5 + 3 * K)) ^ 2 * (2 + 4 * Real.sqrt K)) *
            ((1 + Real.log (I : ℝ)) / Real.sqrt (I : ℝ)) ^ 2 := by
  have hm1 : 1 ≤ m := le_trans one_le_two hm
  set J : ℕ := I / 4 with hJdef
  set W1 : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    fourierTruncate (Finset.Icc (-(J : ℤ)) (J : ℤ)) W with hW1def
  set V1 : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    MeasureTheory.lpBoundedMulCLM hc zero_le_one hC W1 with hV1def
  have hIR : (1 : ℝ) ≤ (I : ℝ) := by exact_mod_cast hI
  have hIpos : (0 : ℝ) < (I : ℝ) := by linarith
  have hLlog : (0 : ℝ) ≤ Real.log (I : ℝ) := Real.log_nonneg hIR
  have hL : (1 : ℝ) ≤ 1 + Real.log (I : ℝ) := by linarith
  have h4J : 4 * J ≤ I := by rw [hJdef]; omega
  set ε : ℝ := 24 * Ak * A * (5 + 3 * K) * ((1 + Real.log (I : ℝ)) / (I : ℝ)) with hεdef
  have hAk0 : (0 : ℝ) ≤ Ak := by
    have h0 := hAk 0
    simp only [Int.natAbs_zero, Nat.cast_zero, add_zero, div_one] at h0
    exact le_trans (norm_nonneg _) h0
  have hεnn : (0 : ℝ) ≤ ε := by
    rw [hεdef]
    have hlog : (0 : ℝ) ≤ (1 + Real.log (I : ℝ)) / (I : ℝ) := by positivity
    have : (0 : ℝ) ≤ 24 * Ak * A * (5 + 3 * K) := by positivity
    exact mul_nonneg this hlog
  have hspikebound : ∀ l : ℤ, 2 * ((I : ℤ) + l).natAbs < I →
      ‖fourierCoeff ((V1 : AddCircle (1 : ℝ) → ℂ)) l‖ ≤ ε := by
    intro l hl
    have hsep : ∀ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
        (I : ℝ) / 4 ≤ 1 + (((j - l).natAbs : ℕ) : ℝ) := by
      intro j hj
      have hnat := spike_lowBand_separation h4J hl hj
      have hc : ((I : ℕ) : ℝ) ≤ ((4 * (1 + (j - l).natAbs) : ℕ) : ℝ) := by exact_mod_cast hnat
      push_cast at hc
      linarith
    have hker := norm_fourierCoeff_symbol_truncate_le hc zero_le_one hC hreal hAk (Finset.Icc (-(J : ℤ)) (J : ℤ)) W l
      (D := (I : ℝ) / 4) (by positivity) hsep
    have hl1 := sum_norm_fourierCoeff_lowBand_le hm1 k p hK hKb hA h4J hW
    have hlog := log_shift_le I hI
    have hAK : (0 : ℝ) ≤ A * (5 + 3 * K) := by positivity
    have hcoef : (0 : ℝ) ≤ Ak / ((I : ℝ) / 4) := by positivity
    calc ‖fourierCoeff ((V1 : AddCircle (1 : ℝ) → ℂ)) l‖
        ≤ (Ak / ((I : ℝ) / 4)) *
            ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
              ‖fourierCoeff ((W : AddCircle (1 : ℝ) → ℂ)) j‖ := hker
      _ ≤ (Ak / ((I : ℝ) / 4)) * (A * (5 + 3 * K) * (2 * (1 + Real.log ((J : ℝ) + 2)))) :=
          mul_le_mul_of_nonneg_left hl1 hcoef
      _ ≤ (Ak / ((I : ℝ) / 4)) * (A * (5 + 3 * K) * (2 * (3 * (1 + Real.log (I : ℝ))))) := by
          refine mul_le_mul_of_nonneg_left ?_ hcoef
          refine mul_le_mul_of_nonneg_left ?_ hAK
          linarith [hlog]
      _ = ε := by
          rw [hεdef]
          field_simp
          ring
  have hmain := norm_sq_gaussShiftedBlockDiag_spike_le hm k p hK hKb I V1 hεnn hspikebound
  have hnormV1 : ‖V1‖ ≤ ‖W‖ := by
    have hop := (MeasureTheory.lpBoundedMulCLM hc zero_le_one hC).le_opNorm W1
    have hb := MeasureTheory.norm_lpBoundedMulCLM_le (p := 2) (μ := AddCircle.haarAddCircle (T := (1 : ℝ))) hc zero_le_one hC
    have h1 : ‖V1‖ ≤ ‖W1‖ := by
      calc ‖V1‖ ≤ ‖MeasureTheory.lpBoundedMulCLM hc zero_le_one hC‖ * ‖W1‖ := hop
        _ ≤ 1 * ‖W1‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
        _ = ‖W1‖ := one_mul _
    exact h1.trans (norm_fourierTruncate_le _ W)
  have hV1sq : ‖V1‖ ^ (2 : ℝ) ≤ ‖W‖ ^ (2 : ℝ) :=
    Real.rpow_le_rpow (norm_nonneg _) hnormV1 (by norm_num)
  have hsqrtK : K ^ (1 / 2 : ℝ) = Real.sqrt K := (Real.sqrt_eq_rpow K).symm
  have hsqI : Real.sqrt (I : ℝ) * Real.sqrt (I : ℝ) = (I : ℝ) :=
    Real.mul_self_sqrt (le_of_lt hIpos)
  have hIne : (I : ℝ) ≠ 0 := ne_of_gt hIpos
  have hR : ((1 + Real.log (I : ℝ)) / Real.sqrt (I : ℝ)) ^ 2
      = (1 + Real.log (I : ℝ)) ^ 2 / (I : ℝ) := by
    rw [div_pow, Real.sq_sqrt (le_of_lt hIpos)]
  have hlast : ε ^ 2 * ((2 + 4 * Real.sqrt K) * (I : ℝ))
      = ((24 * Ak * A * (5 + 3 * K)) ^ 2 * (2 + 4 * Real.sqrt K)) *
        ((1 + Real.log (I : ℝ)) / Real.sqrt (I : ℝ)) ^ 2 := by
    rw [hεdef, hR]
    field_simp
  rw [hsqrtK] at hmain
  refine hmain.trans ?_
  rw [hlast]
  have h2K : (0 : ℝ) ≤ 1 + 2 * K := by linarith
  exact add_le_add (mul_le_mul_of_nonneg_left hV1sq h2K) le_rfl

/-! ## The vanishing theorem -/

/-- **The relative one-step error on the spike vanishes.**  For `m ≥ 2` the normalized shifted
diagonal applied to the reciprocal-square transform of the lattice defect of a harmonically
decaying amplitude tends to zero in `L²`. -/
theorem tendsto_norm_gaussShiftedBlockDiag_symbol_defect_zero (hm : 2 ≤ m) (k : Fin m)
    (p : Nat.Primes) {c : AddCircle (1 : ℝ) → ℂ} (hc : Measurable c) (hC : ∀ x, ‖c x‖ ≤ 1)
    (hreal : ∀ x, starRingEnd ℂ (c x) = c x) {Ak : ℝ}
    (hAk : ∀ x : ℤ, ‖fourierCoeff c x‖ ≤ Ak / (1 + (x.natAbs : ℝ)))
    (g : ℕ → Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) {A : ℝ} (hA : 0 ≤ A)
    (hg : ∀ (I : ℕ) (j : ℤ),
      ‖fourierCoeff ((g I : AddCircle (1 : ℝ) → ℂ)) j‖ ≤ A / (1 + (j.natAbs : ℝ))) :
    Tendsto (fun I : ℕ =>
      ‖gaussShiftedBlockDiag (le_trans one_le_two hm) k p (I : ℤ)
        (MeasureTheory.lpBoundedMulCLM hc zero_le_one hC
          (gaussShiftedBlockOf (le_trans one_le_two hm) k p (I : ℤ) (g I) -
            gaussRotationBlock ((gaussSamplePhase m p (I : ℤ) : ℝ) : AddCircle (1 : ℝ)) (g I)))‖)
      atTop (nhds 0) := by
  classical
  have hm1 : 1 ≤ m := le_trans one_le_two hm
  obtain ⟨K, hK, hKb⟩ := exists_norm_gaussSampleValue_pow_ratio_bound hm1 k p
  set W : ℕ → Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) := fun I =>
    gaussShiftedBlockOf hm1 k p (I : ℤ) (g I) -
      gaussRotationBlock ((gaussSamplePhase m p (I : ℤ) : ℝ) : AddCircle (1 : ℝ)) (g I) with hWdef
  have hWbound : ∀ (I : ℕ) (j : ℤ), ‖fourierCoeff ((W I : AddCircle (1 : ℝ) → ℂ)) j‖
      ≤ (A / (1 + (j.natAbs : ℝ))) * ‖gaussSampleRatioDefect k p j (I : ℤ)‖ := by
    intro I j
    simp only [hWdef]
    rw [norm_fourierCoeff_defectVector hm1 k p (I : ℤ) (g I) j]
    exact mul_le_mul_of_nonneg_right (hg I j) (norm_nonneg _)
  have hι : Tendsto (fun n : ℕ => ((n : ℤ)).natAbs) atTop atTop := by
    have h : Tendsto (fun n : ℕ => n) atTop atTop := tendsto_id
    simpa using h
  have hWzero : Tendsto (fun I : ℕ => ‖W I‖) atTop (nhds 0) :=
    tendsto_norm_gaussShiftedBlockOf_sub_rotation_family hm1 k p hι g hg
  have hWsq : Tendsto (fun I : ℕ => ‖W I‖ ^ (2 : ℝ)) atTop (nhds 0) := by
    have h := hWzero.pow 2
    rw [show ((0 : ℝ) ^ 2) = 0 by norm_num] at h
    refine h.congr fun I => ?_
    rw [← Real.rpow_natCast (‖W I‖) 2]
    norm_num
  set C₁ : ℝ := (24 * Ak * A * (5 + 3 * K)) ^ 2 * (2 + 4 * Real.sqrt K) with hC₁
  set C₂ : ℝ := 2 * (1 + Real.sqrt K) * (64 * A ^ 2 * (1 + K) + 16 * K * A ^ 2) with hC₂
  set low : ℕ → ℝ := fun I => (1 + 2 * K) * ‖W I‖ ^ (2 : ℝ)
    + C₁ * ((1 + Real.log (I : ℝ)) / Real.sqrt (I : ℝ)) ^ 2 with hlow
  set high : ℕ → ℝ := fun I => C₂ * ((1 + Real.log (I : ℝ)) / Real.sqrt (I : ℝ)) with hhigh
  have hlowzero : Tendsto low atTop (nhds 0) := by
    have h1 := hWsq.const_mul (1 + 2 * K)
    rw [mul_zero] at h1
    have h2 := tendsto_const_mul_one_add_log_div_sqrt_sq C₁
    have := h1.add h2
    rw [add_zero] at this
    exact this
  have hhighzero : Tendsto high atTop (nhds 0) := tendsto_const_mul_one_add_log_div_sqrt C₂
  have hsqrtlow : Tendsto (fun I : ℕ => Real.sqrt (low I)) atTop (nhds 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hlowzero
    rw [Real.sqrt_zero] at h
    exact h
  have hsqrthigh : Tendsto (fun I : ℕ => Real.sqrt (high I)) atTop (nhds 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hhighzero
    rw [Real.sqrt_zero] at h
    exact h
  have hsum : Tendsto (fun I : ℕ => Real.sqrt (low I) + Real.sqrt (high I)) atTop (nhds 0) := by
    have := hsqrtlow.add hsqrthigh
    rw [add_zero] at this
    exact this
  refine squeeze_zero' (Filter.Eventually.of_forall fun I => norm_nonneg _) ?_ hsum
  filter_upwards [Filter.eventually_ge_atTop 1] with I hI
  set S : Finset ℤ := Finset.Icc (-((I / 4 : ℕ) : ℤ)) ((I / 4 : ℕ) : ℤ) with hS
  have hdecomp : W I = fourierTruncate S (W I) + (W I - fourierTruncate S (W I)) := by abel
  have hsplit :
      ‖gaussShiftedBlockDiag hm1 k p (I : ℤ) (MeasureTheory.lpBoundedMulCLM hc zero_le_one hC (W I))‖
        ≤ ‖gaussShiftedBlockDiag hm1 k p (I : ℤ)
              (MeasureTheory.lpBoundedMulCLM hc zero_le_one hC (fourierTruncate S (W I)))‖
          + ‖gaussShiftedBlockDiag hm1 k p (I : ℤ)
              (MeasureTheory.lpBoundedMulCLM hc zero_le_one hC (W I - fourierTruncate S (W I)))‖ := by
    conv_lhs => rw [hdecomp]
    rw [map_add, gaussShiftedBlockDiag_add hm1]
    exact norm_add_le _ _
  have hlowbd := norm_sq_shiftedDiag_symbol_lowMode_le hm k p hc hC hreal hAk hK hKb hA hI (hWbound I)
  have hhighbd := norm_sq_shiftedDiag_symbol_highMode_le hm k p hc hC hK hKb hI (hWbound I)
  have hlow' : ‖gaussShiftedBlockDiag hm1 k p (I : ℤ)
      (MeasureTheory.lpBoundedMulCLM hc zero_le_one hC (fourierTruncate S (W I)))‖ ≤ Real.sqrt (low I) := by
    have hnat : ‖gaussShiftedBlockDiag hm1 k p (I : ℤ)
        (MeasureTheory.lpBoundedMulCLM hc zero_le_one hC (fourierTruncate S (W I)))‖ ^ (2 : ℕ) ≤ low I := by
      rw [← Real.rpow_natCast _ 2]
      have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
      rw [hcast]
      exact hlowbd
    have h := Real.sqrt_le_sqrt hnat
    rwa [Real.sqrt_sq (norm_nonneg _)] at h
  have hhigh' : ‖gaussShiftedBlockDiag hm1 k p (I : ℤ)
      (MeasureTheory.lpBoundedMulCLM hc zero_le_one hC (W I - fourierTruncate S (W I)))‖ ≤ Real.sqrt (high I) := by
    have hnat : ‖gaussShiftedBlockDiag hm1 k p (I : ℤ)
        (MeasureTheory.lpBoundedMulCLM hc zero_le_one hC (W I - fourierTruncate S (W I)))‖ ^ (2 : ℕ) ≤ high I := by
      rw [← Real.rpow_natCast _ 2]
      have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
      rw [hcast]
      exact hhighbd
    have h := Real.sqrt_le_sqrt hnat
    rwa [Real.sqrt_sq (norm_nonneg _)] at h
  exact le_trans hsplit (add_le_add hlow' hhigh')

/-- **The reciprocal-square specialization.**  For `m ≥ 2` the normalized shifted diagonal applied
to the reciprocal-square transform of the lattice defect of a harmonically decaying amplitude tends
to zero in `L²`. -/
theorem tendsto_norm_gaussShiftedBlockDiag_invSq_defect_zero (hm : 2 ≤ m) (k : Fin m)
    (p : Nat.Primes) {P : ℝ} (hP : 1 < P)
    (g : ℕ → Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) {A : ℝ} (hA : 0 ≤ A)
    (hg : ∀ (I : ℕ) (j : ℤ),
      ‖fourierCoeff ((g I : AddCircle (1 : ℝ) → ℂ)) j‖ ≤ A / (1 + (j.natAbs : ℝ))) :
    Tendsto (fun I : ℕ =>
      ‖gaussShiftedBlockDiag (le_trans one_le_two hm) k p (I : ℤ)
        (gaussPrimeScaleInvSqBlock hP
          (gaussShiftedBlockOf (le_trans one_le_two hm) k p (I : ℤ) (g I) -
            gaussRotationBlock ((gaussSamplePhase m p (I : ℤ) : ℝ) : AddCircle (1 : ℝ)) (g I)))‖)
      atTop (nhds 0) :=
  tendsto_norm_gaussShiftedBlockDiag_symbol_defect_zero hm k p
    (measurable_gaussPrimeScaleInvSqCircle P) (norm_gaussPrimeScaleInvSqCircle_le hP)
    (gaussPrimeScaleInvSqCircle_conj P)
    (norm_fourierCoeff_gaussPrimeScaleInvSqCircle_le hP) g hA hg

/-- **The piecewise-exponential specialization.**  Every real symbol of modulus at most one that is
piecewise exponential — the algebra the prime-scale amplitudes generate — has harmonic Fourier
decay, so the one-step spike error vanishes for it as well. -/
theorem tendsto_norm_gaussShiftedBlockDiag_expPiecewise_defect_zero (hm : 2 ≤ m) (k : Fin m)
    (p : Nat.Primes) {α : ℝ} {n : ℕ} {t : ℕ → ℝ} {cc : ℕ → ℂ} {c : AddCircle (1 : ℝ) → ℂ}
    (hpw : IsExpPiecewise α n t cc c) (hc : Measurable c) (hC : ∀ x, ‖c x‖ ≤ 1)
    (hreal : ∀ x, starRingEnd ℂ (c x) = c x) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i, ‖cc i‖ ≤ M)
    (g : ℕ → Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) {A : ℝ} (hA : 0 ≤ A)
    (hg : ∀ (I : ℕ) (j : ℤ),
      ‖fourierCoeff ((g I : AddCircle (1 : ℝ) → ℂ)) j‖ ≤ A / (1 + (j.natAbs : ℝ))) :
    Tendsto (fun I : ℕ =>
      ‖gaussShiftedBlockDiag (le_trans one_le_two hm) k p (I : ℤ)
        (MeasureTheory.lpBoundedMulCLM (p := 2)
          (μ := AddCircle.haarAddCircle (T := (1 : ℝ))) hc zero_le_one hC
          (gaussShiftedBlockOf (le_trans one_le_two hm) k p (I : ℤ) (g I) -
            gaussRotationBlock ((gaussSamplePhase m p (I : ℤ) : ℝ) : AddCircle (1 : ℝ)) (g I)))‖)
      atTop (nhds 0) :=
  tendsto_norm_gaussShiftedBlockDiag_symbol_defect_zero hm k p hc hC hreal
    (norm_fourierCoeff_of_isExpPiecewise hpw hM0 hM) g hA hg

end

end RHTower

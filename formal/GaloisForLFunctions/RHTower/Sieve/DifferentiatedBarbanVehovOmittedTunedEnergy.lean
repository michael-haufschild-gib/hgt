import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovTunedMinLogAsymptotic

open Filter Topology

namespace RHTower.Sieve

noncomputable section

/-- Polynomial approximation to omitted-head energy. -/
def barbanVehovOmittedLongEnergyPolynomialMain
    (lam ell : ℝ) (M : ℕ) : ℝ :=
  (barbanVehovOmittedLongBasePolynomialMain M +
      2 * lam * barbanVehovOmittedLongCrossPolynomialMain ell M +
      lam ^ (2 : ℕ) * barbanVehovOmittedLongDerivativePolynomialMain ell M) /
    Real.log M ^ (2 : ℕ)

theorem barbanVehovOmittedLongEnergyPolynomialMain_eq_tunedRemainder
    {lam ell : ℝ} {M : ℕ} (hM : 0 < M) (htune : lam * ell = 1) :
    barbanVehovOmittedLongEnergyPolynomialMain lam ell M =
      lam ^ (2 : ℕ) * selbergOriginalTunedMinLogRemainder M / Real.log M ^ (2 : ℕ) := by
  rw [barbanVehovOmittedLongEnergyPolynomialMain,
    barbanVehovOmittedLongBasePolynomialMain_eq_originalBoundary,
    barbanVehovOmittedLongCrossPolynomialMain_eq_originalBoundary,
    barbanVehovOmittedLongDerivativePolynomialMain_eq_originalBoundary,
    selbergOriginalOmittedBaseBoundary_eq_minMonomial M hM,
    selbergOriginalOmittedCrossBoundary_eq_minMonomials ell M hM,
    selbergOriginalOmittedDerivativeBoundary_eq_minMonomials ell M hM]
  unfold selbergOriginalTunedMinLogRemainder
  rw [selbergOriginalMinLogMonomial_comm 1 2 1 M,
    selbergOriginalMinLogMonomial_comm 1 2 2 M]
  have hzero : 1 - lam * ell = 0 := by rw [htune]; ring
  calc
    _ = (lam ^ (2 : ℕ) *
          ((1 / 3 : ℝ) * selbergOriginalMinLogMonomial 1 1 3 M -
            selbergOriginalMinLogMonomial 2 1 2 M +
            selbergOriginalMinLogMonomial 2 2 1 M) +
          (1 - lam * ell) ^ (2 : ℕ) * selbergOriginalMinLogMonomial 1 1 1 M -
          2 * lam * (1 - lam * ell) * selbergOriginalMinLogMonomial 2 1 1 M +
          lam * (1 - lam * ell) * selbergOriginalMinLogMonomial 1 1 2 M) /
        Real.log M ^ (2 : ℕ) := by ring
    _ = _ := by rw [hzero]; ring

private theorem tendsto_nat_pow_fortyNine_atTop_omitted :
    Tendsto (fun N : ℕ => N ^ (49 : ℕ)) atTop atTop := by
  rw [tendsto_atTop]
  intro B
  filter_upwards [eventually_ge_atTop (max B 1)] with N hN
  have hBN : B ≤ N := (Nat.le_max_left B 1).trans hN
  have hN1 : 1 ≤ N := (Nat.le_max_right B 1).trans hN
  exact hBN.trans (by
    calc
      N ≤ N * N ^ (48 : ℕ) := Nat.le_mul_of_pos_right N (pow_pos hN1 48)
      _ = N ^ (49 : ℕ) := by ring)

/-- The omitted polynomial sector carries `7/12` of the full scale at reciprocal tuning. -/
theorem tendsto_barbanVehovOmittedLongEnergyPolynomialMain_fortyNine_reciprocal :
    Tendsto (fun N : ℕ =>
      barbanVehovOmittedLongEnergyPolynomialMain
        ((49 / 100 : ℝ) / (49 * Real.log N))
        (100 * Real.log N) (N ^ (49 : ℕ)))
      atTop (𝓝 ((7 / 12 : ℝ) * (49 / 100 : ℝ) ^ (2 : ℕ))) := by
  have hrem :=
    tendsto_selbergOriginalTunedMinLogRemainder_div_log_four_seven_twelfths.comp
      tendsto_nat_pow_fortyNine_atTop_omitted
  have hscaled := hrem.const_mul ((49 / 100 : ℝ) ^ (2 : ℕ))
  have hscaled' : Tendsto (fun N : ℕ =>
      (49 / 100 : ℝ) ^ (2 : ℕ) *
        (selbergOriginalTunedMinLogRemainder (N ^ (49 : ℕ)) /
          Real.log (((N ^ (49 : ℕ) : ℕ) : ℝ)) ^ (4 : ℕ)))
      atTop (𝓝 ((7 / 12 : ℝ) * (49 / 100 : ℝ) ^ (2 : ℕ))) := by
    simpa only [Function.comp_apply, mul_comm] using hscaled
  refine hscaled'.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
  have hM : 0 < N ^ (49 : ℕ) := pow_pos (by omega) 49
  have htune :
      ((49 / 100 : ℝ) / (49 * Real.log N)) * (100 * Real.log N) = 1 := by
    field_simp [hlog]
  rw [barbanVehovOmittedLongEnergyPolynomialMain_eq_tunedRemainder hM htune]
  rw [show (((N ^ (49 : ℕ) : ℕ) : ℝ)) = (N : ℝ) ^ (49 : ℕ) by norm_num,
    Real.log_pow]
  field_simp [hlog]
  ring

/-- Explicit aggregate error for the omitted-head polynomial approximation. -/
def barbanVehovOmittedFortyNineEnergyErrorConstant (r : ℝ) : ℝ :=
  3 + 38 * |r| + 113 * r ^ (2 : ℕ)

theorem abs_levinsonCriticalDetectorOmittedLongEnergy_fortyNine_sub_polynomialMain_le
    (r : ℝ) {N : ℕ} (hN : 8 ≤ N) :
    |RHTower.levinsonCriticalDetectorOmittedLongEnergy
          (r / (49 * Real.log N)) (N ^ (100 : ℕ)) (N ^ (49 : ℕ)) -
        barbanVehovOmittedLongEnergyPolynomialMain
          (r / (49 * Real.log N)) (100 * Real.log N) (N ^ (49 : ℕ))| ≤
      barbanVehovOmittedFortyNineEnergyErrorConstant r / (N : ℝ) ^ (2 : ℕ) := by
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
  have hM : 1 < N ^ (49 : ℕ) := by
    have hNpow : N ≤ N ^ (49 : ℕ) := by
      calc
        N ≤ N * N ^ (48 : ℕ) := Nat.le_mul_of_pos_right N (pow_pos hN0 48)
        _ = N ^ (49 : ℕ) := by ring
    exact (by omega : 1 < N).trans_le hNpow
  have hML : N ^ (49 : ℕ) ≤ N ^ (100 : ℕ) := by
    calc
      N ^ (49 : ℕ) ≤ N ^ (49 : ℕ) * N ^ (51 : ℕ) :=
        Nat.le_mul_of_pos_right _ (pow_pos hN0 51)
      _ = N ^ (100 : ℕ) := by ring
  have hlogM : Real.log (((N ^ (49 : ℕ) : ℕ) : ℝ)) = 49 * Real.log N := by
    rw [show (((N ^ (49 : ℕ) : ℕ) : ℝ)) = (N : ℝ) ^ (49 : ℕ) by norm_num,
      Real.log_pow]
    norm_num
  rw [RHTower.levinsonCriticalDetectorOmittedLongEnergy_eq_momentQuadratic
    (r / (49 * Real.log N)) (N ^ (100 : ℕ)) hM,
    levinsonCriticalDetectorOmittedLongBaseMoment_eq_lcm hM hML,
    levinsonCriticalDetectorOmittedLongCrossMoment_eq_lcm hM hML,
    levinsonCriticalDetectorOmittedLongDerivativeMoment_eq_lcm hM hML,
    barbanVehovOmittedLongEnergyPolynomialMain, hlogM]
  have hbase :=
    abs_barbanVehovOmittedLongBaseLcm_fortyNine_div_log_sq_sub_polynomial_le hN
  have hcross :=
    abs_barbanVehovOmittedLongCrossLcm_fortyNine_div_log_cube_sub_polynomial_le hN
  have hderiv :=
    abs_barbanVehovOmittedLongDerivativeLcm_fortyNine_div_log_four_sub_polynomial_le hN
  let eB :=
    barbanVehovOmittedLongBaseLcm (N ^ (100 : ℕ)) (N ^ (49 : ℕ)) /
        (49 * Real.log N) ^ (2 : ℕ) -
      barbanVehovOmittedLongBasePolynomialMain (N ^ (49 : ℕ)) /
        (49 * Real.log N) ^ (2 : ℕ)
  let eC :=
    barbanVehovOmittedLongCrossLcm (N ^ (100 : ℕ)) (N ^ (49 : ℕ)) /
        (49 * Real.log N) ^ (3 : ℕ) -
      barbanVehovOmittedLongCrossPolynomialMain (100 * Real.log N) (N ^ (49 : ℕ)) /
        (49 * Real.log N) ^ (3 : ℕ)
  let eD :=
    barbanVehovOmittedLongDerivativeLcm (N ^ (100 : ℕ)) (N ^ (49 : ℕ)) /
        (49 * Real.log N) ^ (4 : ℕ) -
      barbanVehovOmittedLongDerivativePolynomialMain (100 * Real.log N) (N ^ (49 : ℕ)) /
        (49 * Real.log N) ^ (4 : ℕ)
  have heq :
      (barbanVehovOmittedLongBaseLcm (N ^ (100 : ℕ)) (N ^ (49 : ℕ)) +
            2 * (r / (49 * Real.log N)) *
              barbanVehovOmittedLongCrossLcm (N ^ (100 : ℕ)) (N ^ (49 : ℕ)) +
            (r / (49 * Real.log N)) ^ (2 : ℕ) *
              barbanVehovOmittedLongDerivativeLcm (N ^ (100 : ℕ)) (N ^ (49 : ℕ))) /
          (49 * Real.log N) ^ (2 : ℕ) -
        (barbanVehovOmittedLongBasePolynomialMain (N ^ (49 : ℕ)) +
            2 * (r / (49 * Real.log N)) *
              barbanVehovOmittedLongCrossPolynomialMain
                (100 * Real.log N) (N ^ (49 : ℕ)) +
            (r / (49 * Real.log N)) ^ (2 : ℕ) *
              barbanVehovOmittedLongDerivativePolynomialMain
                (100 * Real.log N) (N ^ (49 : ℕ))) /
          (49 * Real.log N) ^ (2 : ℕ) =
        eB + 2 * r * eC + r ^ (2 : ℕ) * eD := by
    dsimp only [eB, eC, eD]
    field_simp [hlog]
    ring
  rw [heq]
  calc
    |eB + 2 * r * eC + r ^ (2 : ℕ) * eD| ≤
        |eB| + |2 * r * eC| + |r ^ (2 : ℕ) * eD| := by
      exact (abs_add_le (eB + 2 * r * eC) (r ^ (2 : ℕ) * eD)).trans
        (add_le_add (abs_add_le eB (2 * r * eC)) (le_refl _))
    _ = |eB| + 2 * |r| * |eC| + r ^ (2 : ℕ) * |eD| := by
      rw [abs_mul, abs_mul, abs_mul, abs_pow, sq_abs]
      norm_num
    _ ≤ 3 / (N : ℝ) ^ (2 : ℕ) + 2 * |r| * (19 / (N : ℝ) ^ (2 : ℕ)) +
          r ^ (2 : ℕ) * (113 / (N : ℝ) ^ (2 : ℕ)) := by
      dsimp only [eB, eC, eD] at hbase hcross hderiv ⊢
      gcongr
    _ = barbanVehovOmittedFortyNineEnergyErrorConstant r / (N : ℝ) ^ (2 : ℕ) := by
      rw [barbanVehovOmittedFortyNineEnergyErrorConstant]
      ring

/-- Actual omitted-head long energy has exact limiting mass `7ρ²/12`. -/
private theorem tendsto_const_div_nat_sq_omitted (c : ℝ) :
    Tendsto (fun N : ℕ => c / (N : ℝ) ^ (2 : ℕ)) atTop (𝓝 0) := by
  have hc : Tendsto (fun N : ℕ => c / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hone : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hmul := hc.mul hone
  rw [zero_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  field_simp [hNR]

theorem tendsto_levinsonCriticalDetectorOmittedLongEnergy_fortyNine_reciprocal :
    Tendsto (fun N : ℕ =>
      RHTower.levinsonCriticalDetectorOmittedLongEnergy
        ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ (100 : ℕ)) (N ^ (49 : ℕ)))
      atTop (𝓝 ((7 / 12 : ℝ) * (49 / 100 : ℝ) ^ (2 : ℕ))) := by
  let P : ℕ → ℝ := fun N =>
    barbanVehovOmittedLongEnergyPolynomialMain
      ((49 / 100 : ℝ) / (49 * Real.log N))
      (100 * Real.log N) (N ^ (49 : ℕ))
  have hP : Tendsto P atTop (𝓝 ((7 / 12 : ℝ) * (49 / 100 : ℝ) ^ (2 : ℕ))) :=
    tendsto_barbanVehovOmittedLongEnergyPolynomialMain_fortyNine_reciprocal
  have hbound : Tendsto (fun N : ℕ =>
      barbanVehovOmittedFortyNineEnergyErrorConstant (49 / 100 : ℝ) /
        (N : ℝ) ^ (2 : ℕ)) atTop (𝓝 0) := by
    exact tendsto_const_div_nat_sq_omitted _
  have habs : Tendsto (fun N : ℕ =>
      |RHTower.levinsonCriticalDetectorOmittedLongEnergy
          ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ (100 : ℕ)) (N ^ (49 : ℕ)) - P N|)
      atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hbound
    filter_upwards [eventually_ge_atTop 8] with N hN
    simpa only [P] using
      abs_levinsonCriticalDetectorOmittedLongEnergy_fortyNine_sub_polynomialMain_le
        (49 / 100 : ℝ) hN
  have herr : Tendsto (fun N : ℕ =>
      RHTower.levinsonCriticalDetectorOmittedLongEnergy
          ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ (100 : ℕ)) (N ^ (49 : ℕ)) - P N)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs, norm_zero] using habs
  simpa only [P, zero_add] using (herr.add hP).congr'
    (Eventually.of_forall fun N => by ring)

/-- The detector cutoff is asymptotically Pythagorean: included and omitted sectors become
orthogonal in harmonic coefficient energy. -/
theorem tendsto_levinsonCriticalDetector_full_sub_included_sub_omitted_fortyNine_zero :
    Tendsto (fun N : ℕ =>
      RHTower.levinsonCriticalDetectorFullLongEnergy
          ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ (100 : ℕ)) (N ^ (49 : ℕ)) -
        RHTower.levinsonCriticalDetectorLongEnergy
          ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ (100 : ℕ)) (N ^ (49 : ℕ)) -
        RHTower.levinsonCriticalDetectorOmittedLongEnergy
          ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ (100 : ℕ)) (N ^ (49 : ℕ)))
      atTop (𝓝 0) := by
  have h :=
    tendsto_levinsonCriticalDetectorFullLongEnergy_fortyNine_reciprocal.sub
      tendsto_levinsonCriticalDetectorLongEnergy_fortyNine_reciprocal
  have h' := h.sub
    tendsto_levinsonCriticalDetectorOmittedLongEnergy_fortyNine_reciprocal
  convert h' using 1
  norm_num

end

end RHTower.Sieve

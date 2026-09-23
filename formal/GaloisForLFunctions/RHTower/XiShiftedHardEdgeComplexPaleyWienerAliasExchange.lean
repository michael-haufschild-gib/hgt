import GaloisForLFunctions.RHTower.XiShiftedHardEdgeComplexPaleyWienerPeriodization
import GaloisForLFunctions.RHTower.XiShiftedReciprocalHankelDisproof

/-!
# Weighted Xi-divisor exchange for complex hard-edge periodization

Uniform pointwise alias decay cannot be summed over the infinite Xi divisor.  The missing
mechanism is the shifted reciprocal weight already present in the hard-edge trace: after mass
renormalization it supplies an absolutely summable reciprocal-square atom.  This file proves the
resulting divisor exchange directly, with an explicit `O(a⁻²)` majorant and no zero-location
hypothesis.
-/

open scoped BigOperators SchwartzMap FourierTransform

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Literal compact-lattice sample at one multiplicity-labelled Xi spectral point. -/
def routeUXiComplexHardEdgeSample
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (q : XiZeroCopy) : ℂ :=
  ((routeUHardEdgeMesh r : ℝ) : ℂ) *
    ∑' k : ℤ,
      Complex.exp
          (Complex.I * routeUComplexHardEdgePhase r (xiSpectralPoint q) *
            (((routeUHardEdgeMesh r) * (k : ℝ) : ℝ) : ℂ)) *
        SchwartzMap.compactSupportApproximation n f
          (routeUHardEdgeMesh r * (k : ℝ))

/-- Central entire Fourier value at the complex Cayley phase of one Xi spectral point. -/
def routeUXiComplexHardEdgeCentral
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (q : XiZeroCopy) : ℂ :=
  routeUComplexPositiveFourierExtension n f
    (routeUComplexHardEdgePhase r (xiSpectralPoint q))

/-- Mass-renormalized shifted reciprocal weight occurring in the hard-edge Xi trace. -/
def routeUXiHardEdgeResolventWeight (r : ℝ) (q : XiZeroCopy) : ℂ :=
  (((routeUHardEdgeMass r) ^ (2 : ℕ) : ℝ) : ℂ) *
    xiShiftedReciprocalSquare ((routeUHardEdgeMass r) ^ (2 : ℕ)) q

/-- Weighted error made by replacing the squared lattice sample by its central entire value. -/
def routeUXiComplexHardEdgeAliasSquareErrorTerm
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (q : XiZeroCopy) : ℂ :=
  routeUXiHardEdgeResolventWeight r q *
    (routeUXiComplexHardEdgeSample n f r q ^ (2 : ℕ) -
      routeUXiComplexHardEdgeCentral n f r q ^ (2 : ℕ))

/-- Divisor-independent coefficient in the reciprocal-square majorant for alias exchange. -/
def routeUXiComplexHardEdgeAliasSquareMajorantCoefficient
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) : ℝ :=
  (routeUHardEdgeMass r) ^ (2 : ℕ) *
      (routeUComplexHardEdgeUniformAliasTailConstant n f 1 *
        (routeUComplexHardEdgeUniformAliasTailConstant n f 1 +
          2 * routeUComplexTiltUniformDecay n f 0)) /
    routeUHardEdgeAliasPeriod r ^ (4 : ℕ)

theorem routeUXiComplexHardEdgeAliasSquareMajorantCoefficient_nonneg
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) :
    0 ≤ routeUXiComplexHardEdgeAliasSquareMajorantCoefficient n f r := by
  rw [routeUXiComplexHardEdgeAliasSquareMajorantCoefficient]
  exact div_nonneg
    (mul_nonneg (sq_nonneg _)
      (mul_nonneg
        (routeUComplexHardEdgeUniformAliasTailConstant_nonneg n f 1)
        (add_nonneg
          (routeUComplexHardEdgeUniformAliasTailConstant_nonneg n f 1)
          (mul_nonneg (by norm_num)
            (routeUComplexTiltUniformDecay_nonneg n f 0)))))
    (pow_nonneg (le_of_lt (routeUHardEdgeAliasPeriod_pos r)) 4)

theorem routeUXiComplexHardEdgeSample_eq_central_add_aliasTail
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (q : XiZeroCopy) :
    routeUXiComplexHardEdgeSample n f r q =
      routeUXiComplexHardEdgeCentral n f r q +
        routeUComplexHardEdgeAliasTail n f r
          (routeUComplexHardEdgePhase r (xiSpectralPoint q)) := by
  simpa only [routeUXiComplexHardEdgeSample, routeUXiComplexHardEdgeCentral] using
    routeU_complex_hardEdge_periodization_phase_eq_extension_add_tail
      n f r (xiSpectralPoint q)

theorem norm_routeUXiComplexHardEdgeCentral_le
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (q : XiZeroCopy) :
    ‖routeUXiComplexHardEdgeCentral n f r q‖ ≤
      routeUComplexTiltUniformDecay n f 0 := by
  simpa only [routeUXiComplexHardEdgeCentral, pow_zero, Nat.mul_zero, one_mul] using
    routeUComplexPositiveFourierExtension_uniform_decay n f
      (abs_routeUComplexHardEdgePhase_xiSpectralPoint_im_lt_one r q).le 0

theorem one_le_routeUHardEdgeAliasPeriod (r : ℝ) :
    1 ≤ routeUHardEdgeAliasPeriod r := by
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hmass : (1 : ℝ) ≤ routeUHardEdgeMass r := by
    simp [routeUHardEdgeMass]
  rw [routeUHardEdgeAliasPeriod]
  nlinarith [mul_nonneg (sub_nonneg.mpr hpi) (sub_nonneg.mpr hmass)]

theorem norm_routeUXiComplexHardEdgeAliasSquare_sub_le
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (q : XiZeroCopy) :
    ‖routeUXiComplexHardEdgeSample n f r q ^ (2 : ℕ) -
        routeUXiComplexHardEdgeCentral n f r q ^ (2 : ℕ)‖ ≤
      routeUComplexHardEdgeUniformAliasTailConstant n f 1 *
          (routeUComplexHardEdgeUniformAliasTailConstant n f 1 +
            2 * routeUComplexTiltUniformDecay n f 0) /
        routeUHardEdgeAliasPeriod r ^ (4 : ℕ) := by
  let T : ℂ := routeUComplexHardEdgeAliasTail n f r
    (routeUComplexHardEdgePhase r (xiSpectralPoint q))
  let C : ℂ := routeUXiComplexHardEdgeCentral n f r q
  let D : ℝ := routeUComplexHardEdgeUniformAliasTailConstant n f 1
  let B : ℝ := routeUComplexTiltUniformDecay n f 0
  let L : ℝ := routeUHardEdgeAliasPeriod r
  have hD : 0 ≤ D := routeUComplexHardEdgeUniformAliasTailConstant_nonneg n f 1
  have hB : 0 ≤ B := routeUComplexTiltUniformDecay_nonneg n f 0
  have hL : 1 ≤ L := one_le_routeUHardEdgeAliasPeriod r
  have hT : ‖T‖ ≤ D / L ^ (4 : ℕ) := by
    simpa only [T, D, L,
      GaloisForLFunctions.RHTower.ccmRationalArchimedeanDecayExponent] using
      norm_routeUComplexHardEdgeAliasTail_xiSpectralPoint_le n f r q 1
  have hTcoarse : ‖T‖ ≤ D :=
    hT.trans (div_le_self hD (one_le_pow₀ hL))
  have hC : ‖C‖ ≤ B := by
    simpa only [C, B] using norm_routeUXiComplexHardEdgeCentral_le n f r q
  have hsum : ‖T + C + C‖ ≤ D + 2 * B := by
    calc
      ‖T + C + C‖ ≤ ‖T + C‖ + ‖C‖ := norm_add_le (T + C) C
      _ ≤ (‖T‖ + ‖C‖) + ‖C‖ :=
        by linarith [norm_add_le T C]
      _ ≤ D + B + B := by gcongr
      _ = D + 2 * B := by ring
  rw [routeUXiComplexHardEdgeSample_eq_central_add_aliasTail]
  change ‖(C + T) ^ (2 : ℕ) - C ^ (2 : ℕ)‖ ≤ D * (D + 2 * B) / L ^ (4 : ℕ)
  rw [show (C + T) ^ (2 : ℕ) - C ^ (2 : ℕ) = T * (T + C + C) by ring, norm_mul]
  calc
    ‖T‖ * ‖T + C + C‖ ≤ (D / L ^ (4 : ℕ)) * (D + 2 * B) := by
      exact mul_le_mul hT hsum (norm_nonneg _) (by positivity)
    _ = D * (D + 2 * B) / L ^ (4 : ℕ) := by ring

theorem norm_routeUXiHardEdgeResolventWeight_le
    (r : ℝ) (q : XiZeroCopy) :
    ‖routeUXiHardEdgeResolventWeight r q‖ ≤
      (routeUHardEdgeMass r) ^ (2 : ℕ) * ‖xiZeroCopyReciprocalSquare q‖ := by
  rw [routeUXiHardEdgeResolventWeight, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  gcongr
  exact norm_xiShiftedReciprocalSquare_le (sq_nonneg _) q

/-- **Weighted Xi alias majorant.**  Uniform sampling error becomes summable only after retaining
the native mass-renormalized reciprocal weight of the hard-edge divisor packet. -/
theorem norm_routeUXiComplexHardEdgeAliasSquareErrorTerm_le
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (q : XiZeroCopy) :
    ‖routeUXiComplexHardEdgeAliasSquareErrorTerm n f r q‖ ≤
      routeUXiComplexHardEdgeAliasSquareMajorantCoefficient n f r *
        ‖xiZeroCopyReciprocalSquare q‖ := by
  rw [routeUXiComplexHardEdgeAliasSquareErrorTerm, norm_mul]
  calc
    ‖routeUXiHardEdgeResolventWeight r q‖ *
        ‖routeUXiComplexHardEdgeSample n f r q ^ (2 : ℕ) -
          routeUXiComplexHardEdgeCentral n f r q ^ (2 : ℕ)‖ ≤
      ((routeUHardEdgeMass r) ^ (2 : ℕ) * ‖xiZeroCopyReciprocalSquare q‖) *
        (routeUComplexHardEdgeUniformAliasTailConstant n f 1 *
            (routeUComplexHardEdgeUniformAliasTailConstant n f 1 +
              2 * routeUComplexTiltUniformDecay n f 0) /
          routeUHardEdgeAliasPeriod r ^ (4 : ℕ)) := by
      exact mul_le_mul
        (norm_routeUXiHardEdgeResolventWeight_le r q)
        (norm_routeUXiComplexHardEdgeAliasSquare_sub_le n f r q)
        (norm_nonneg _) (by positivity)
    _ = routeUXiComplexHardEdgeAliasSquareMajorantCoefficient n f r *
        ‖xiZeroCopyReciprocalSquare q‖ := by
      rw [routeUXiComplexHardEdgeAliasSquareMajorantCoefficient]
      ring

theorem summable_routeUXiComplexHardEdgeAliasSquareErrorTerm
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) :
    Summable (routeUXiComplexHardEdgeAliasSquareErrorTerm n f r) := by
  apply Summable.of_norm_bounded
    ((summable_xiZeroCopyReciprocalSquare_pow 0).norm.mul_left
      (routeUXiComplexHardEdgeAliasSquareMajorantCoefficient n f r))
  intro q
  simpa using norm_routeUXiComplexHardEdgeAliasSquareErrorTerm_le n f r q

/-- Quantitative infinite-divisor alias exchange. -/
theorem norm_tsum_routeUXiComplexHardEdgeAliasSquareErrorTerm_le
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) :
    ‖∑' q : XiZeroCopy,
        routeUXiComplexHardEdgeAliasSquareErrorTerm n f r q‖ ≤
      routeUXiComplexHardEdgeAliasSquareMajorantCoefficient n f r *
        ∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ := by
  let A : ℝ := routeUXiComplexHardEdgeAliasSquareMajorantCoefficient n f r
  have hErr := summable_routeUXiComplexHardEdgeAliasSquareErrorTerm n f r
  have hBase : Summable (fun q : XiZeroCopy =>
      ‖xiZeroCopyReciprocalSquare q‖) := by
    simpa using (summable_xiZeroCopyReciprocalSquare_pow 0).norm
  have hMajor : Summable (fun q : XiZeroCopy =>
      A * ‖xiZeroCopyReciprocalSquare q‖) := hBase.mul_left A
  calc
    ‖∑' q : XiZeroCopy,
        routeUXiComplexHardEdgeAliasSquareErrorTerm n f r q‖ ≤
      ∑' q : XiZeroCopy,
        ‖routeUXiComplexHardEdgeAliasSquareErrorTerm n f r q‖ :=
        norm_tsum_le_tsum_norm hErr.norm
    _ ≤ ∑' q : XiZeroCopy, A * ‖xiZeroCopyReciprocalSquare q‖ :=
      hErr.norm.tsum_le_tsum
        (fun q => norm_routeUXiComplexHardEdgeAliasSquareErrorTerm_le n f r q)
        hMajor
    _ = A * ∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ :=
      tsum_mul_left

/-- The explicit reciprocal-square majorant coefficient vanishes along the cofinal integral
hard-edge scale. -/
theorem tendsto_routeUXiComplexHardEdgeAliasSquareMajorantCoefficient_natCast_zero
    (n : ℕ) (f : SchwartzMap ℝ ℂ) :
    Filter.Tendsto
      (fun k : ℕ =>
        routeUXiComplexHardEdgeAliasSquareMajorantCoefficient n f (k : ℝ))
      Filter.atTop (nhds 0) := by
  let K : ℝ :=
    routeUComplexHardEdgeUniformAliasTailConstant n f 1 *
      (routeUComplexHardEdgeUniformAliasTailConstant n f 1 +
        2 * routeUComplexTiltUniformDecay n f 0)
  have hmass : Filter.Tendsto (fun k : ℕ => 1 + (k : ℝ))
      Filter.atTop Filter.atTop := by
    simpa only [add_comm] using
      Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop
  have hmassSq : Filter.Tendsto (fun k : ℕ => (1 + (k : ℝ)) ^ (2 : ℕ))
      Filter.atTop Filter.atTop := by
    simpa only [pow_two] using hmass.atTop_mul_atTop₀ hmass
  have hden : Filter.Tendsto
      (fun k : ℕ => Real.pi ^ (4 : ℕ) * (1 + (k : ℝ)) ^ (2 : ℕ))
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (pow_pos Real.pi_pos 4) hmassSq
  have hlim : Filter.Tendsto
      (fun k : ℕ => K / (Real.pi ^ (4 : ℕ) * (1 + (k : ℝ)) ^ (2 : ℕ)))
      Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  apply hlim.congr'
  filter_upwards with k
  rw [routeUXiComplexHardEdgeAliasSquareMajorantCoefficient,
    routeUHardEdgeAliasPeriod, routeUHardEdgeMass]
  simp only [abs_of_nonneg (show 0 ≤ (k : ℝ) by positivity)]
  change K / (Real.pi ^ (4 : ℕ) * (1 + (k : ℝ)) ^ (2 : ℕ)) =
    (1 + (k : ℝ)) ^ (2 : ℕ) * K /
      (Real.pi * (1 + (k : ℝ))) ^ (4 : ℕ)
  field_simp [Real.pi_ne_zero, show (1 + (k : ℝ)) ≠ 0 by positivity]

/-- **Premise-free infinite-divisor alias exchange.**  The full Xi-weighted squared lattice
sampling error tends to zero.  This is the alias component of complex HEPW.14. -/
theorem tendsto_tsum_routeUXiComplexHardEdgeAliasSquareErrorTerm_natCast_zero
    (n : ℕ) (f : SchwartzMap ℝ ℂ) :
    Filter.Tendsto
      (fun k : ℕ =>
        ∑' q : XiZeroCopy,
          routeUXiComplexHardEdgeAliasSquareErrorTerm n f (k : ℝ) q)
      Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let S : ℝ := ∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖
  have hright : Filter.Tendsto
      (fun k : ℕ =>
        routeUXiComplexHardEdgeAliasSquareMajorantCoefficient n f (k : ℝ) * S)
      Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_routeUXiComplexHardEdgeAliasSquareMajorantCoefficient_natCast_zero n f).mul
        (tendsto_const_nhds (x := S))
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun k => norm_nonneg _)
    (Filter.Eventually.of_forall fun k => ?_) hright
  simpa only [S] using
    norm_tsum_routeUXiComplexHardEdgeAliasSquareErrorTerm_le n f (k : ℝ)

end RHTower

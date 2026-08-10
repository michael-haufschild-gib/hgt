import GaloisForLFunctions.RHTower.GaussTranslationL2Convergence

/-!
# The moving-translation estimate for a general amplitude

Equation (9) holds with the prime-scale amplitude replaced by any `L²` vector whose Fourier
coefficients decay like `A/(1+|j|)`, with a rate depending only on `A`.  This is the uniform form
the iterated principal action of §4 consumes: the amplitudes produced by finitely many products of
translates of `b` and `b^{-1}` all share one decay constant.

The moving target is expressed by the rotation multiplier `e_(-j)(δ)` on the Fourier side, which
is the unitary implementing translation by `δ`.
-/

namespace RHTower

open Filter Topology MeasureTheory

noncomputable section

/-! ## The rotation multiplier -/

/-- Rotation by `δ`: the unitary Fourier multiplier with symbol `e_(-j)(δ)`. -/
def gaussRotationBlock (δ : AddCircle (1 : ℝ)) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  conjugateOperator (fourierBasis (T := (1 : ℝ))).repr.toContinuousLinearEquiv
    (GaloisForLFunctions.lpDiagonalCLM (fun j : ℤ => fourier (-j) δ) zero_le_one
      (fun j => le_of_eq (norm_fourier_eq_one (-j) δ)))

theorem fourierCoeff_gaussRotationBlock (δ : AddCircle (1 : ℝ))
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (l : ℤ) :
    fourierCoeff ((gaussRotationBlock δ u : AddCircle (1 : ℝ) → ℂ)) l
      = fourier (-l) δ * fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) l := by
  have hrepr : (fourierBasis (T := (1 : ℝ))).repr (gaussRotationBlock δ u)
      = GaloisForLFunctions.lpDiagonalCLM (fun j : ℤ => fourier (-j) δ) zero_le_one
          (fun j => le_of_eq (norm_fourier_eq_one (-j) δ))
          ((fourierBasis (T := (1 : ℝ))).repr u) := by
    rw [gaussRotationBlock, conjugateOperator]
    simp
  rw [← fourierBasis_repr, ← fourierBasis_repr, hrepr]
  exact GaloisForLFunctions.lpDiagonalCLM_apply _ _ _ _ _

/-! ## The shifted block of a general amplitude -/

/-- The normalized shifted block carrying an amplitude `u`. -/
def gaussShiftedBlockOf {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (n : ℤ)
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  (starRingEnd ℂ (gaussSampleValue k p n))⁻¹ •
    fourierMulBlock (-n) (gaussDiagonalBlockStar hm k p (fourierMulBlock n u))

theorem fourierCoeff_gaussShiftedBlockOf {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (n : ℤ) (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (j : ℤ) :
    fourierCoeff ((gaussShiftedBlockOf hm k p n u : AddCircle (1 : ℝ) → ℂ)) j
      = (starRingEnd ℂ (gaussSampleValue k p n))⁻¹ *
        (starRingEnd ℂ (gaussSampleValue k p (n + j)) *
          fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j) := by
  have hsmul : ((gaussShiftedBlockOf hm k p n u : AddCircle (1 : ℝ) → ℂ))
      =ᵐ[AddCircle.haarAddCircle] fun z =>
        (starRingEnd ℂ (gaussSampleValue k p n))⁻¹ *
          ((fourierMulBlock (-n)
            (gaussDiagonalBlockStar hm k p (fourierMulBlock n u)) :
              AddCircle (1 : ℝ) → ℂ) z) := by
    filter_upwards [Lp.coeFn_smul (starRingEnd ℂ (gaussSampleValue k p n))⁻¹
      (fourierMulBlock (-n) (gaussDiagonalBlockStar hm k p (fourierMulBlock n u)))] with z hz
    rw [gaussShiftedBlockOf, hz, Pi.smul_apply, smul_eq_mul]
  rw [fourierCoeff_congr_ae hsmul j, fourierCoeff_smul, fourierCoeff_fourierMulBlock,
    fourierCoeff_gaussDiagonalBlockStar, fourierCoeff_fourierMulBlock,
    show j - -n = n + j from by ring, show n + j - n = j from by ring]

/-! ## The uniform estimate -/

theorem norm_fourierCoeff_shiftedBlockOf_sub_rotation {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) (n j : ℤ) (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    ‖fourierCoeff ((gaussShiftedBlockOf hm k p n u : AddCircle (1 : ℝ) → ℂ)) j -
        fourierCoeff ((gaussRotationBlock
          ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ)) u :
            AddCircle (1 : ℝ) → ℂ)) j‖
      = ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ * ‖gaussSampleRatioDefect k p j n‖ := by
  rw [fourierCoeff_gaussShiftedBlockOf, fourierCoeff_gaussRotationBlock]
  have hrot : fourier (-j) ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ))
      = starRingEnd ℂ (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) *
        ((gaussSamplePhase m p n : ℝ) : ℂ))) := by
    rw [fourier_coe_apply, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal, map_intCast]
    push_cast
    ring
  rw [hrot, gaussSampleRatioDefect]
  by_cases hd : gaussSampleValue k p n = 0
  · rw [hd]
    simp only [map_zero, inv_zero, zero_mul, div_zero, zero_sub, zero_mul]
    rw [norm_neg, norm_mul, norm_neg, RCLike.norm_conj]
    ring
  · have hconj : starRingEnd ℂ (gaussSampleValue k p n) ≠ 0 := by simpa using hd
    have hexpand :
        (starRingEnd ℂ (gaussSampleValue k p n))⁻¹ *
            (starRingEnd ℂ (gaussSampleValue k p (n + j)) *
              fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j) -
          starRingEnd ℂ (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) *
            ((gaussSamplePhase m p n : ℝ) : ℂ))) *
            fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j
          = fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j *
            starRingEnd ℂ (gaussSampleValue k p (n + j) / gaussSampleValue k p n -
              Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) *
                ((gaussSamplePhase m p n : ℝ) : ℂ))) := by
      rw [map_sub, map_div₀]
      field_simp
    rw [hexpand, norm_mul, RCLike.norm_conj]

/-- **Equation (9), uniform form.**  For every amplitude whose Fourier coefficients decay like
`A/(1+|j|)`, the normalized shifted block converges in `L²(ℝ/ℤ)` to its rotation, with a rate
depending only on `A`. -/
theorem tendsto_norm_gaussShiftedBlockOf_sub_rotation {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) {A : ℝ}
    (hu : ∀ j : ℤ, ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ≤ A / (1 + (j.natAbs : ℝ))) :
    Tendsto (fun n : ℕ =>
      ‖gaussShiftedBlockOf hm k p (n : ℤ) u -
        gaussRotationBlock ((gaussSamplePhase m p (n : ℤ) : ℝ) : AddCircle (1 : ℝ)) u‖)
      atTop (nhds 0) := by
  have hdefect := tendsto_gaussTranslationL2Defect_of_decay hm k p hu
  rw [ENNReal.tendsto_nhds_zero] at hdefect
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hdefect (ENNReal.ofReal ((ε / 2) ^ 2)) (by
    simpa using pow_pos (half_pos hε) 2))
  refine ⟨N, fun n hn => ?_⟩
  have hbound := hN n hn
  set w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussShiftedBlockOf hm k p (n : ℤ) u -
      gaussRotationBlock ((gaussSamplePhase m p (n : ℤ) : ℝ) : AddCircle (1 : ℝ)) u with hw
  have hcoeff : ∀ j : ℤ,
      ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j‖
        = ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ *
          ‖gaussSampleRatioDefect k p j (n : ℤ)‖ := by
    intro j
    have hsub : fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j
        = fourierCoeff ((gaussShiftedBlockOf hm k p (n : ℤ) u : AddCircle (1 : ℝ) → ℂ)) j -
          fourierCoeff ((gaussRotationBlock
            ((gaussSamplePhase m p (n : ℤ) : ℝ) : AddCircle (1 : ℝ)) u :
              AddCircle (1 : ℝ) → ℂ)) j := by
      rw [← fourierBasis_repr, ← fourierBasis_repr, ← fourierBasis_repr, hw, map_sub]
      rfl
    rw [hsub, norm_fourierCoeff_shiftedBlockOf_sub_rotation hm k p]
  have hcongr : ∀ j : ℤ,
      ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j‖ ^ (2 : ℝ)
        = ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2 *
          ‖gaussSampleRatioDefect k p j (n : ℤ)‖ ^ 2 := by
    intro j
    rw [hcoeff j, Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
      ← Real.rpow_natCast (‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖) 2,
      ← Real.rpow_natCast (‖gaussSampleRatioDefect k p j (n : ℤ)‖) 2]
    norm_num
  have hsummable : Summable fun j : ℤ =>
      ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j‖ ^ (2 : ℝ) := by
    have hmem := lp.memℓp ((fourierBasis (T := (1 : ℝ))).repr w)
    have hs := hmem.summable (p := 2) (by norm_num)
    simp only [ENNReal.toReal_ofNat] at hs
    refine hs.congr fun j => ?_
    rw [fourierBasis_repr]
  have hsummable' : Summable fun j : ℤ =>
      ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2 *
        ‖gaussSampleRatioDefect k p j (n : ℤ)‖ ^ 2 := hsummable.congr hcongr
  have hnormsq : ‖w‖ ^ (2 : ℝ)
      = ∑' j : ℤ, ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2 *
        ‖gaussSampleRatioDefect k p j (n : ℤ)‖ ^ 2 := by
    rw [norm_sq_eq_tsum_fourierCoeff w]
    exact tsum_congr hcongr
  have hofReal : ENNReal.ofReal (‖w‖ ^ (2 : ℝ)) ≤ ENNReal.ofReal ((ε / 2) ^ 2) := by
    rw [hnormsq, ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsummable']
    exact hbound
  have hle : ‖w‖ ^ (2 : ℝ) ≤ (ε / 2) ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hofReal
  have hnorm2 : ‖w‖ ^ (2 : ℕ) ≤ (ε / 2) ^ 2 := by
    have hcast : ‖w‖ ^ (2 : ℕ) = ‖w‖ ^ (2 : ℝ) := by
      rw [← Real.rpow_natCast (‖w‖) 2]
      norm_num
    rw [hcast]
    exact hle
  have hfinal : ‖w‖ ≤ ε / 2 := by
    have h := Real.sqrt_le_sqrt hnorm2
    rwa [Real.sqrt_sq (norm_nonneg w), Real.sqrt_sq (half_pos hε).le] at h
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg w)]
  linarith

/-! ## The unconjugated block -/

/-- Inverse rotation by `δ`: the unitary Fourier multiplier with symbol `e_j(δ)`. -/
def gaussRotationBlockInv (δ : AddCircle (1 : ℝ)) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  conjugateOperator (fourierBasis (T := (1 : ℝ))).repr.toContinuousLinearEquiv
    (GaloisForLFunctions.lpDiagonalCLM (fun j : ℤ => fourier j δ) zero_le_one
      (fun j => le_of_eq (norm_fourier_eq_one j δ)))

theorem fourierCoeff_gaussRotationBlockInv (δ : AddCircle (1 : ℝ))
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (l : ℤ) :
    fourierCoeff ((gaussRotationBlockInv δ u : AddCircle (1 : ℝ) → ℂ)) l
      = fourier l δ * fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) l := by
  have hrepr : (fourierBasis (T := (1 : ℝ))).repr (gaussRotationBlockInv δ u)
      = GaloisForLFunctions.lpDiagonalCLM (fun j : ℤ => fourier j δ) zero_le_one
          (fun j => le_of_eq (norm_fourier_eq_one j δ))
          ((fourierBasis (T := (1 : ℝ))).repr u) := by
    rw [gaussRotationBlockInv, conjugateOperator]
    simp
  rw [← fourierBasis_repr, ← fourierBasis_repr, hrepr]
  exact GaloisForLFunctions.lpDiagonalCLM_apply _ _ _ _ _

/-- The normalized shifted block built from the unconjugated diagonal. -/
def gaussShiftedBlockDiag {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (n : ℤ)
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  (gaussSampleValue k p n)⁻¹ •
    fourierMulBlock (-n) (gaussDiagonalBlock hm k p (fourierMulBlock n u))

theorem fourierCoeff_gaussShiftedBlockDiag {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (n : ℤ) (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (j : ℤ) :
    fourierCoeff ((gaussShiftedBlockDiag hm k p n u : AddCircle (1 : ℝ) → ℂ)) j
      = (gaussSampleValue k p n)⁻¹ *
        (gaussSampleValue k p (n + j) *
          fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j) := by
  have hsmul : ((gaussShiftedBlockDiag hm k p n u : AddCircle (1 : ℝ) → ℂ))
      =ᵐ[AddCircle.haarAddCircle] fun z =>
        (gaussSampleValue k p n)⁻¹ *
          ((fourierMulBlock (-n)
            (gaussDiagonalBlock hm k p (fourierMulBlock n u)) :
              AddCircle (1 : ℝ) → ℂ) z) := by
    filter_upwards [Lp.coeFn_smul (gaussSampleValue k p n)⁻¹
      (fourierMulBlock (-n) (gaussDiagonalBlock hm k p (fourierMulBlock n u)))] with z hz
    rw [gaussShiftedBlockDiag, hz, Pi.smul_apply, smul_eq_mul]
  rw [fourierCoeff_congr_ae hsmul j, fourierCoeff_smul, fourierCoeff_fourierMulBlock,
    fourierCoeff_gaussDiagonalBlock, fourierCoeff_fourierMulBlock,
    show j - -n = n + j from by ring, show n + j - n = j from by ring]

theorem norm_fourierCoeff_shiftedBlockDiag_sub_rotationInv {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) (n j : ℤ) (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    ‖fourierCoeff ((gaussShiftedBlockDiag hm k p n u : AddCircle (1 : ℝ) → ℂ)) j -
        fourierCoeff ((gaussRotationBlockInv
          ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ)) u :
            AddCircle (1 : ℝ) → ℂ)) j‖
      = ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ * ‖gaussSampleRatioDefect k p j n‖ := by
  rw [fourierCoeff_gaussShiftedBlockDiag, fourierCoeff_gaussRotationBlockInv]
  have hrot : fourier j ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) *
        ((gaussSamplePhase m p n : ℝ) : ℂ)) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [hrot, gaussSampleRatioDefect]
  by_cases hd : gaussSampleValue k p n = 0
  · rw [hd]
    simp only [inv_zero, zero_mul, div_zero, zero_sub, zero_mul]
    rw [norm_neg, norm_mul, norm_neg]
    ring
  · have hexpand :
        (gaussSampleValue k p n)⁻¹ *
            (gaussSampleValue k p (n + j) * fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j) -
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) *
            ((gaussSamplePhase m p n : ℝ) : ℂ)) *
            fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j
          = fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j *
            (gaussSampleValue k p (n + j) / gaussSampleValue k p n -
              Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) *
                ((gaussSamplePhase m p n : ℝ) : ℂ))) := by
      field_simp
    rw [hexpand, norm_mul]

/-- **Equation (9) for the unconjugated diagonal.** -/
theorem tendsto_norm_gaussShiftedBlockDiag_sub_rotationInv {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) {A : ℝ}
    (hu : ∀ j : ℤ, ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ≤ A / (1 + (j.natAbs : ℝ))) :
    Tendsto (fun n : ℕ =>
      ‖gaussShiftedBlockDiag hm k p (n : ℤ) u -
        gaussRotationBlockInv ((gaussSamplePhase m p (n : ℤ) : ℝ) : AddCircle (1 : ℝ)) u‖)
      atTop (nhds 0) := by
  have hdefect := tendsto_gaussTranslationL2Defect_of_decay hm k p hu
  rw [ENNReal.tendsto_nhds_zero] at hdefect
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hdefect (ENNReal.ofReal ((ε / 2) ^ 2)) (by
    simpa using pow_pos (half_pos hε) 2))
  refine ⟨N, fun n hn => ?_⟩
  have hbound := hN n hn
  set w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussShiftedBlockDiag hm k p (n : ℤ) u -
      gaussRotationBlockInv ((gaussSamplePhase m p (n : ℤ) : ℝ) : AddCircle (1 : ℝ)) u with hw
  have hcoeff : ∀ j : ℤ,
      ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j‖
        = ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ *
          ‖gaussSampleRatioDefect k p j (n : ℤ)‖ := by
    intro j
    have hsub : fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j
        = fourierCoeff ((gaussShiftedBlockDiag hm k p (n : ℤ) u : AddCircle (1 : ℝ) → ℂ)) j -
          fourierCoeff ((gaussRotationBlockInv
            ((gaussSamplePhase m p (n : ℤ) : ℝ) : AddCircle (1 : ℝ)) u :
              AddCircle (1 : ℝ) → ℂ)) j := by
      rw [← fourierBasis_repr, ← fourierBasis_repr, ← fourierBasis_repr, hw, map_sub]
      rfl
    rw [hsub, norm_fourierCoeff_shiftedBlockDiag_sub_rotationInv hm k p]
  have hcongr : ∀ j : ℤ,
      ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j‖ ^ (2 : ℝ)
        = ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2 *
          ‖gaussSampleRatioDefect k p j (n : ℤ)‖ ^ 2 := by
    intro j
    rw [hcoeff j, Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
      ← Real.rpow_natCast (‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖) 2,
      ← Real.rpow_natCast (‖gaussSampleRatioDefect k p j (n : ℤ)‖) 2]
    norm_num
  have hsummable : Summable fun j : ℤ =>
      ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j‖ ^ (2 : ℝ) := by
    have hmem := lp.memℓp ((fourierBasis (T := (1 : ℝ))).repr w)
    have hs := hmem.summable (p := 2) (by norm_num)
    simp only [ENNReal.toReal_ofNat] at hs
    refine hs.congr fun j => ?_
    rw [fourierBasis_repr]
  have hsummable' : Summable fun j : ℤ =>
      ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2 *
        ‖gaussSampleRatioDefect k p j (n : ℤ)‖ ^ 2 := hsummable.congr hcongr
  have hnormsq : ‖w‖ ^ (2 : ℝ)
      = ∑' j : ℤ, ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2 *
        ‖gaussSampleRatioDefect k p j (n : ℤ)‖ ^ 2 := by
    rw [norm_sq_eq_tsum_fourierCoeff w]
    exact tsum_congr hcongr
  have hofReal : ENNReal.ofReal (‖w‖ ^ (2 : ℝ)) ≤ ENNReal.ofReal ((ε / 2) ^ 2) := by
    rw [hnormsq, ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsummable']
    exact hbound
  have hle : ‖w‖ ^ (2 : ℝ) ≤ (ε / 2) ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hofReal
  have hnorm2 : ‖w‖ ^ (2 : ℕ) ≤ (ε / 2) ^ 2 := by
    have hcast : ‖w‖ ^ (2 : ℕ) = ‖w‖ ^ (2 : ℝ) := by
      rw [← Real.rpow_natCast (‖w‖) 2]
      norm_num
    rw [hcast]
    exact hle
  have hfinal : ‖w‖ ≤ ε / 2 := by
    have h := Real.sqrt_le_sqrt hnorm2
    rwa [Real.sqrt_sq (norm_nonneg w), Real.sqrt_sq (half_pos hε).le] at h
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg w)]
  linarith

end

end RHTower

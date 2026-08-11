import GaloisForLFunctions.RHTower.GaussShiftedBlockCoefficients
import GaloisForLFunctions.RHTower.GaussSampleTranslationL2
import GaloisForLFunctions.HTGeometry.FourierCircleTruncation

/-!
# The moving-translation estimate in `L²(ℝ/ℤ)`

Equation (9) in its literal form: the normalized shifted block converges in `L²(ℝ/ℤ)` to the
moving translate of the prime-scale amplitude,

`(conj d_n)^{-1} e_(-n) D* B e_n - b(· - δ_n) → 0`.

Coefficientwise the difference is `b̂(j)·(conj(d_(n+j))/conj(d_n) - e^{-2π i j δ_n})`, whose squared
`ℓ²` norm is exactly the quantity `tendsto_gaussTranslationL2Defect` sends to zero; Parseval for
the Fourier basis converts the two statements into each other.
-/

namespace RHTower

open Filter Topology MeasureTheory

noncomputable section

/-! ## The moving translate as an `L²` vector -/

/-- The translate `b(· - δ)` of the prime-scale amplitude on the circle. -/
def gaussPrimeScaleTranslate (p : ℝ) (δ : AddCircle (1 : ℝ)) : AddCircle (1 : ℝ) → ℂ :=
  fun z => gaussPrimeScaleCircle p (z - δ)

theorem measurable_gaussPrimeScaleTranslate (p : ℝ) (δ : AddCircle (1 : ℝ)) :
    Measurable (gaussPrimeScaleTranslate p δ) :=
  (measurable_gaussPrimeScaleCircle p).comp (measurable_sub_const δ)

theorem norm_gaussPrimeScaleTranslate_le {p : ℝ} (hp : 1 < p) (δ : AddCircle (1 : ℝ))
    (z : AddCircle (1 : ℝ)) : ‖gaussPrimeScaleTranslate p δ z‖ ≤ Real.sqrt p :=
  norm_gaussPrimeScaleCircle_le hp _

theorem memLp_gaussPrimeScaleTranslate {p : ℝ} (hp : 1 < p) (δ : AddCircle (1 : ℝ)) :
    MemLp (gaussPrimeScaleTranslate p δ) 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  MemLp.of_bound (measurable_gaussPrimeScaleTranslate p δ).aestronglyMeasurable (Real.sqrt p)
    (Filter.Eventually.of_forall (norm_gaussPrimeScaleTranslate_le hp δ))

/-- The moving translate, as an element of `L²(ℝ/ℤ)`. -/
def gaussPrimeScaleTranslateLp {p : ℝ} (hp : 1 < p) (δ : AddCircle (1 : ℝ)) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  (memLp_gaussPrimeScaleTranslate hp δ).toLp _

theorem fourierCoeff_gaussPrimeScaleTranslateLp {p : ℝ} (hp : 1 < p) (δ : AddCircle (1 : ℝ))
    (j : ℤ) :
    fourierCoeff ((gaussPrimeScaleTranslateLp hp δ : AddCircle (1 : ℝ) → ℂ)) j
      = fourier (-j) δ * gaussPrimeScaleFourierCoefficient p j := by
  rw [gaussPrimeScaleTranslateLp,
    fourierCoeff_congr_ae (MemLp.coeFn_toLp (memLp_gaussPrimeScaleTranslate hp δ)) j]
  exact fourierCoeff_gaussPrimeScaleCircle_translate hp j δ

/-! ## Parseval for the Fourier basis -/

theorem norm_sq_eq_tsum_fourierCoeff (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    ‖u‖ ^ (2 : ℝ) = ∑' j : ℤ, ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ (2 : ℝ) :=
  GaloisForLFunctions.norm_sq_eq_tsum_fourierCoeff u

/-! ## The `L²` convergence -/

/-- The coefficientwise difference is the `ℓ²` summand of the estimate. -/
theorem norm_fourierCoeff_shiftedBlock_sub_translate {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) (n j : ℤ) :
    ‖fourierCoeff ((gaussShiftedBlock hm k p n : AddCircle (1 : ℝ) → ℂ)) j -
        fourierCoeff
          ((gaussPrimeScaleTranslateLp hp
            ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ)) : AddCircle (1 : ℝ) → ℂ)) j‖
      = ‖gaussPrimeScaleFourierCoefficient (p : ℝ) j‖ * ‖gaussSampleRatioDefect k p j n‖ := by
  rw [fourierCoeff_gaussShiftedBlock, fourierCoeff_gaussPrimeScaleTranslateLp]
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
  · have hconj : starRingEnd ℂ (gaussSampleValue k p n) ≠ 0 := by
      simpa using hd
    have hexpand :
        (starRingEnd ℂ (gaussSampleValue k p n))⁻¹ *
            (starRingEnd ℂ (gaussSampleValue k p (n + j)) *
              gaussPrimeScaleFourierCoefficient (p : ℝ) j) -
          starRingEnd ℂ (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) *
            ((gaussSamplePhase m p n : ℝ) : ℂ))) *
            gaussPrimeScaleFourierCoefficient (p : ℝ) j
          = gaussPrimeScaleFourierCoefficient (p : ℝ) j *
            starRingEnd ℂ (gaussSampleValue k p (n + j) / gaussSampleValue k p n -
              Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) *
                ((gaussSamplePhase m p n : ℝ) : ℂ))) := by
      rw [map_sub, map_div₀]
      field_simp
    rw [hexpand, norm_mul, RCLike.norm_conj]

/-- **Equation (9).**  The normalized shifted block converges in `L²(ℝ/ℤ)` to the moving translate
of the prime-scale amplitude. -/
theorem tendsto_norm_gaussShiftedBlock_sub_translate {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) :
    Tendsto (fun n : ℕ =>
      ‖gaussShiftedBlock hm k p (n : ℤ) -
        gaussPrimeScaleTranslateLp hp
          ((gaussSamplePhase m p (n : ℤ) : ℝ) : AddCircle (1 : ℝ))‖) atTop (nhds 0) := by
  have hdefect := tendsto_gaussTranslationL2Defect hm k p
  rw [ENNReal.tendsto_nhds_zero] at hdefect
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hdefect (ENNReal.ofReal ((ε / 2) ^ 2)) (by
    simpa using pow_pos (half_pos hε) 2))
  refine ⟨N, fun n hn => ?_⟩
  have hbound := hN n hn
  set u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussShiftedBlock hm k p (n : ℤ) -
      gaussPrimeScaleTranslateLp hp ((gaussSamplePhase m p (n : ℤ) : ℝ) : AddCircle (1 : ℝ))
    with hu
  have hcoeff : ∀ j : ℤ,
      ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖
        = ‖gaussPrimeScaleFourierCoefficient (p : ℝ) j‖ *
          ‖gaussSampleRatioDefect k p j (n : ℤ)‖ := by
    intro j
    have hsub : fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j
        = fourierCoeff ((gaussShiftedBlock hm k p (n : ℤ) : AddCircle (1 : ℝ) → ℂ)) j -
          fourierCoeff ((gaussPrimeScaleTranslateLp hp
            ((gaussSamplePhase m p (n : ℤ) : ℝ) : AddCircle (1 : ℝ)) :
              AddCircle (1 : ℝ) → ℂ)) j := by
      rw [← fourierBasis_repr, ← fourierBasis_repr, ← fourierBasis_repr, hu, map_sub]
      rfl
    rw [hsub, norm_fourierCoeff_shiftedBlock_sub_translate hm k p hp]
  have hcongr : ∀ j : ℤ,
      ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ (2 : ℝ)
        = ‖gaussPrimeScaleFourierCoefficient (p : ℝ) j‖ ^ 2 *
          ‖gaussSampleRatioDefect k p j (n : ℤ)‖ ^ 2 := by
    intro j
    rw [hcoeff j, Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
      ← Real.rpow_natCast (‖gaussPrimeScaleFourierCoefficient (p : ℝ) j‖) 2,
      ← Real.rpow_natCast (‖gaussSampleRatioDefect k p j (n : ℤ)‖) 2]
    norm_num
  have hsummable : Summable fun j : ℤ =>
      ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ (2 : ℝ) := by
    have hmem := lp.memℓp ((fourierBasis (T := (1 : ℝ))).repr u)
    have hs := hmem.summable (p := 2) (by norm_num)
    simp only [ENNReal.toReal_ofNat] at hs
    refine hs.congr fun j => ?_
    rw [fourierBasis_repr]
  have hsummable' : Summable fun j : ℤ =>
      ‖gaussPrimeScaleFourierCoefficient (p : ℝ) j‖ ^ 2 *
        ‖gaussSampleRatioDefect k p j (n : ℤ)‖ ^ 2 := hsummable.congr hcongr
  have hnormsq : ‖u‖ ^ (2 : ℝ)
      = ∑' j : ℤ, ‖gaussPrimeScaleFourierCoefficient (p : ℝ) j‖ ^ 2 *
        ‖gaussSampleRatioDefect k p j (n : ℤ)‖ ^ 2 := by
    rw [norm_sq_eq_tsum_fourierCoeff u]
    exact tsum_congr hcongr
  have hofReal : ENNReal.ofReal (‖u‖ ^ (2 : ℝ)) ≤ ENNReal.ofReal ((ε / 2) ^ 2) := by
    rw [hnormsq, ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsummable']
    exact hbound
  have hle : ‖u‖ ^ (2 : ℝ) ≤ (ε / 2) ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hofReal
  have hnorm2 : ‖u‖ ^ (2 : ℕ) ≤ (ε / 2) ^ 2 := by
    have hcast : ‖u‖ ^ (2 : ℕ) = ‖u‖ ^ (2 : ℝ) := by
      rw [← Real.rpow_natCast (‖u‖) 2]
      norm_num
    rw [hcast]
    exact hle
  have hfinal : ‖u‖ ≤ ε / 2 := by
    have h := Real.sqrt_le_sqrt hnorm2
    rwa [Real.sqrt_sq (norm_nonneg u), Real.sqrt_sq (half_pos hε).le] at h
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg u)]
  linarith

end

end RHTower

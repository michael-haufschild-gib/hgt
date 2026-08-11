import GaloisForLFunctions.RHTower.GaussIterate
import GaloisForLFunctions.RHTower.GaussScaleAmplitudeIntegral
import GaloisForLFunctions.HTGeometry.FourierCircleTruncation

/-!
# The diagonal of the iterated principal action

Pairing the iterated principal action against the exponential monomial it acts on turns the `L²`
statement into the scalar law

`⟪e_n, G^r e_n⟫ = (p |d_n|²)^r · A_r(δ_n) + o(1)`,

where `A_r(δ) = ∫₀¹ a_δ(x)^r dx` is the exact period average of the `r`-th power of the moving
amplitude.  The pairing is legitimate because `‖e_n‖ = 1`, so Cauchy–Schwarz turns the vanishing
`L²` error into a vanishing scalar error; and the period average of the iterated amplitude is the
zeroth Fourier coefficient, which the two-piece description evaluates in closed form.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions Filter Topology

noncomputable section

/-! ## Fourier coefficients as inner products -/

theorem inner_fourierLp_eq_fourierCoeff (n : ℤ)
    (v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    inner ℂ (fourierLp 2 n) v = fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) n :=
  GaloisForLFunctions.inner_fourierLp_eq_fourierCoeff n v

theorem norm_fourierLp_eq_one (n : ℤ) :
    ‖(fourierLp (T := (1 : ℝ)) 2 n : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))‖ = 1 :=
  GaloisForLFunctions.norm_fourierLp_eq_one n

/-- The exponential monomial is the constant function twisted by itself. -/
theorem fourierMulBlock_fourierLp_zero (n : ℤ) :
    fourierMulBlock n (fourierLp 2 0)
      = (fourierLp 2 n : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) := by
  refine Lp.ext ?_
  refine (MeasureTheory.lpBoundedMulCLM_coeFn _ _ _ _).trans ?_
  refine Filter.EventuallyEq.trans ?_ (coeFn_fourierLp (T := (1 : ℝ)) 2 n).symm
  filter_upwards [coeFn_fourierLp_zero] with z hz
  rw [hz, mul_one]

/-! ## The period average of the iterated amplitude -/

theorem gaussMovingAmplitudeCircle_coe {p s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hx0 : 0 < x) (hx1 : x < 1) (hne : x ≠ 1 - s) :
    gaussMovingAmplitudeCircle p ((s : ℝ) : AddCircle (1 : ℝ)) ((x : ℝ) : AddCircle (1 : ℝ))
      = ((gaussMovingAmplitude p s x : ℝ) : ℂ) := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hxs : x + s < 1 := by linarith
    rw [gaussMovingAmplitudeCircle_of_lt hs0 hx0 hxs.le,
      gaussMovingAmplitude_of_lt_one hx0.le hs0 hxs]
  · have hxs : 1 < x + s := by linarith
    rw [gaussMovingAmplitudeCircle_of_ge hs1 hx0 hx1.le hxs,
      gaussMovingAmplitude_of_one_le hx0.le hx1 hs1.le hxs.le]

/-- **The period average of the `r`-th power of the moving amplitude** is the closed form. -/
theorem fourierCoeff_gaussAmplitudePow_zero {p s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (r : ℕ) :
    fourierCoeff (fun z => gaussMovingAmplitudeCircle p ((s : ℝ) : AddCircle (1 : ℝ)) z ^ r) 0
      = ((gaussAmplitudeSegment p r s : ℝ) : ℂ) := by
  have hc : fourierCoeff
        (fun z => gaussMovingAmplitudeCircle p ((s : ℝ) : AddCircle (1 : ℝ)) z ^ r) 0
      = ∫ x in (0 : ℝ)..1,
          gaussMovingAmplitudeCircle p ((s : ℝ) : AddCircle (1 : ℝ))
            ((x : ℝ) : AddCircle (1 : ℝ)) ^ r := by
    rw [fourierCoeff_eq_intervalIntegral _ 0 0]
    simp
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc (0 : ℝ) 1 →
      gaussMovingAmplitudeCircle p ((s : ℝ) : AddCircle (1 : ℝ))
          ((x : ℝ) : AddCircle (1 : ℝ)) ^ r
        = ((gaussMovingAmplitude p s x ^ r : ℝ) : ℂ) := by
    have hnull1 : (volume : Measure ℝ) {(1 - s)} = 0 := measure_singleton _
    have hnull2 : (volume : Measure ℝ) {(1 : ℝ)} = 0 := measure_singleton _
    filter_upwards [compl_mem_ae_iff.mpr hnull1, compl_mem_ae_iff.mpr hnull2]
      with x hxa hxb hmem
    rw [Set.uIoc_of_le zero_le_one] at hmem
    have hx0 : 0 < x := hmem.1
    have hxlt : x < 1 := lt_of_le_of_ne hmem.2 (by simpa using hxb)
    have hne : x ≠ 1 - s := by simpa using hxa
    rw [gaussMovingAmplitudeCircle_coe hs0 hs1 hx0 hxlt hne, ← Complex.ofReal_pow]
  rw [hc, intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_ofReal,
    intervalIntegral_gaussMovingAmplitude_pow p r hs0 hs1.le]

theorem fourierCoeff_gaussAmplitudeIterate_zero {p : ℝ} (hp : 1 < p) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1) (r : ℕ) :
    fourierCoeff (((gaussMovingAmplitudeBlock hp ((s : ℝ) : AddCircle (1 : ℝ)) ^ r)
        (fourierLp 2 0) : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
          AddCircle (1 : ℝ) → ℂ) 0
      = ((gaussAmplitudeSegment p r s : ℝ) : ℂ) := by
  rw [fourierCoeff_congr_ae
    (coeFn_gaussAmplitudePow hp ((s : ℝ) : AddCircle (1 : ℝ)) r) 0]
  exact fourierCoeff_gaussAmplitudePow_zero hs0 hs1 r

/-! ## Equation (11) -/

/-- **The diagonal of the iterated principal action.**  Pairing `G^r e_n` against `e_n` gives the
`r`-th power of the step scalar times the exact period average of the `r`-th power of the moving
amplitude, up to an error that vanishes. -/
theorem tendsto_gaussIterateInner {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) {ι : ℕ → ℤ}
    (hι : Tendsto (fun n : ℕ => (ι n).natAbs) atTop atTop) (r : ℕ) :
    Tendsto (fun n : ℕ =>
      ‖(inner ℂ (fourierLp 2 (ι n))
            ((gaussQuasiInnerG hm k p ^ r) (fourierLp 2 (ι n))) : ℂ) -
          ((((p : ℝ) : ℂ) *
              (starRingEnd ℂ (gaussSampleValue k p (ι n)) *
                gaussSampleValue k p (ι n))) ^ r) *
            ((gaussAmplitudeSegment (p : ℝ) r
              (Int.fract (gaussSamplePhase m p (ι n))) : ℝ) : ℂ)‖)
      atTop (nhds 0) := by
  refine squeeze_zero_norm' ?_ (tendsto_gaussIterate hm k p hp hι r)
  filter_upwards with n
  set s : ℝ := Int.fract (gaussSamplePhase m p (ι n)) with hs
  have hs0 : 0 ≤ s := Int.fract_nonneg _
  have hs1 : s < 1 := Int.fract_lt_one _
  have hδ : ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ))
      = ((s : ℝ) : AddCircle (1 : ℝ)) := (coe_fract_eq _).symm
  set σ : ℂ := ((p : ℝ) : ℂ) *
    (starRingEnd ℂ (gaussSampleValue k p (ι n)) * gaussSampleValue k p (ι n)) with hσ
  set g : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    (gaussMovingAmplitudeBlock hp ((s : ℝ) : AddCircle (1 : ℝ)) ^ r) (fourierLp 2 0) with hg
  have hinner : (inner ℂ (fourierLp 2 (ι n)) (fourierMulBlock (ι n) g) : ℂ)
      = ((gaussAmplitudeSegment (p : ℝ) r s : ℝ) : ℂ) := by
    rw [inner_fourierLp_eq_fourierCoeff, fourierCoeff_fourierMulBlock, sub_self,
      fourierCoeff_gaussAmplitudeIterate_zero hp hs0 hs1 r]
  have hpair : (inner ℂ (fourierLp 2 (ι n))
        ((gaussQuasiInnerG hm k p ^ r) (fourierLp 2 (ι n))) : ℂ) -
        (σ ^ r) * ((gaussAmplitudeSegment (p : ℝ) r s : ℝ) : ℂ)
      = inner ℂ (fourierLp 2 (ι n))
          ((gaussQuasiInnerG hm k p ^ r) (fourierMulBlock (ι n) (fourierLp 2 0)) -
            (σ ^ r) • fourierMulBlock (ι n) g) := by
    rw [inner_sub_right, inner_smul_right, fourierMulBlock_fourierLp_zero, hinner]
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hδ, hpair]
  refine le_trans (norm_inner_le_norm _ _) ?_
  rw [norm_fourierLp_eq_one, one_mul]

end

end RHTower

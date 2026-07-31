import Mathlib

/-!
# Polynomially weighted wave traces of a discrete frequency family

A conjugation-stable family of nonzero complex frequencies, bounded away from the origin,
of finite horizontal width and with summable inverse squares, carries for every real
polynomial `P` the wave trace
`H_P(t) = ∑ sin (gamma * t) * P (gamma ^ (-2)) / gamma ^ 3`.

The series converges normally on compact time intervals, defines a real continuous function
of exponential order at most the horizontal width, and depends linearly on `P`. A finite
family of monomial weights therefore assembles into a vector path whose linear observables
are again wave traces, which is exactly the reduction used to feed convex recurrence.
-/

open Complex Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Elementary bounds -/

theorem norm_csin_le_exp_abs_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin]
  rw [norm_div, norm_mul, Complex.norm_I, mul_one]
  have h1 : ‖Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)‖ ≤
      ‖Complex.exp (-z * Complex.I)‖ + ‖Complex.exp (z * Complex.I)‖ := norm_sub_le _ _
  have h2 : ‖Complex.exp (-z * Complex.I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have h3 : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have h4 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (le_abs_self _)
  have h5 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  rw [h2, h3] at h1
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnorm2]
  linarith

/-- Uniform bound of a real polynomial evaluated on a complex ball. -/
def polyBallBound (P : Polynomial ℝ) (R : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (P.natDegree + 1), |P.coeff k| * R ^ k

theorem polyBallBound_nonneg (P : Polynomial ℝ) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ polyBallBound P R :=
  Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (pow_nonneg hR k)

theorem norm_aeval_le_polyBallBound (P : Polynomial ℝ) {R : ℝ}
    {w : ℂ} (hw : ‖w‖ ≤ R) :
    ‖Polynomial.aeval w P‖ ≤ polyBallBound P R := by
  rw [Polynomial.aeval_eq_sum_range]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Algebra.smul_def, norm_mul, norm_pow]
  refine mul_le_mul ?_ (pow_le_pow_left₀ (norm_nonneg w) hw k) (by positivity) (by positivity)
  simp [Complex.norm_real]

/-! ## Admissible spectra -/

/-- A conjugation-stable discrete frequency family of finite width with summable inverse
squares. -/
structure WaveSpectrum (G : Type*) where
  /-- The frequencies. -/
  gamma : G → ℂ
  /-- Index involution realizing complex conjugation of frequencies. -/
  invol : G → G
  invol_invol : ∀ g, invol (invol g) = g
  gamma_invol : ∀ g, gamma (invol g) = (starRingEnd ℂ) (gamma g)
  /-- Uniform lower bound on the modulus. -/
  lower : ℝ
  lower_pos : 0 < lower
  lower_le : ∀ g, lower ≤ ‖gamma g‖
  /-- Uniform bound on the horizontal width. -/
  width : ℝ
  width_nonneg : 0 ≤ width
  im_le : ∀ g, |(gamma g).im| ≤ width
  summable_inv_sq : Summable fun g => ‖gamma g‖⁻¹ ^ 2

namespace WaveSpectrum

variable {G : Type*} (S : WaveSpectrum G)

theorem gamma_ne_zero (g : G) : S.gamma g ≠ 0 := by
  intro h
  have := S.lower_le g
  rw [h, norm_zero] at this
  linarith [S.lower_pos]

theorem norm_gamma_pos (g : G) : 0 < ‖S.gamma g‖ :=
  lt_of_lt_of_le S.lower_pos (S.lower_le g)

theorem summable_inv_cube : Summable fun g => ‖S.gamma g‖⁻¹ ^ 3 := by
  refine Summable.of_nonneg_of_le (fun g => by positivity)
    (fun g => ?_) (S.summable_inv_sq.mul_left S.lower⁻¹)
  have hg : 0 < ‖S.gamma g‖ := S.norm_gamma_pos g
  have hle : S.lower ≤ ‖S.gamma g‖ := S.lower_le g
  have hinv : ‖S.gamma g‖⁻¹ ≤ S.lower⁻¹ := by
    gcongr
    exact S.lower_pos
  calc ‖S.gamma g‖⁻¹ ^ 3 = ‖S.gamma g‖⁻¹ * ‖S.gamma g‖⁻¹ ^ 2 := by ring
    _ ≤ S.lower⁻¹ * ‖S.gamma g‖⁻¹ ^ 2 := by
        exact mul_le_mul_of_nonneg_right hinv (by positivity)

theorem norm_inv_gamma_sq_le (g : G) : ‖(S.gamma g ^ 2)⁻¹‖ ≤ S.lower⁻¹ ^ 2 := by
  rw [norm_inv, norm_pow]
  have hg : 0 < ‖S.gamma g‖ := S.norm_gamma_pos g
  have hle : S.lower ≤ ‖S.gamma g‖ := S.lower_le g
  rw [← inv_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  gcongr
  exact S.lower_pos

/-! ## The wave trace -/

/-- One term of the polynomially weighted wave trace. -/
def traceTerm (P : Polynomial ℝ) (t : ℝ) (g : G) : ℂ :=
  Complex.sin (S.gamma g * t) * Polynomial.aeval ((S.gamma g ^ 2)⁻¹) P / S.gamma g ^ 3

/-- Polynomially weighted wave trace of the spectrum. -/
def waveTrace (P : Polynomial ℝ) (t : ℝ) : ℂ :=
  ∑' g, S.traceTerm P t g

theorem norm_traceTerm_le (P : Polynomial ℝ) (t : ℝ) (g : G) :
    ‖S.traceTerm P t g‖ ≤
      (Real.exp (S.width * |t|) * polyBallBound P (S.lower⁻¹ ^ 2)) * ‖S.gamma g‖⁻¹ ^ 3 := by
  rw [traceTerm, norm_div, norm_mul, norm_pow]
  have hsin : ‖Complex.sin (S.gamma g * t)‖ ≤ Real.exp (S.width * |t|) := by
    refine le_trans (norm_csin_le_exp_abs_im _) (Real.exp_le_exp.mpr ?_)
    have him : (S.gamma g * (t : ℂ)).im = (S.gamma g).im * t := by
      simp [Complex.mul_im]
    rw [him, abs_mul]
    exact mul_le_mul_of_nonneg_right (S.im_le g) (abs_nonneg t)
  have hpoly : ‖Polynomial.aeval ((S.gamma g ^ 2)⁻¹) P‖ ≤ polyBallBound P (S.lower⁻¹ ^ 2) :=
    norm_aeval_le_polyBallBound P (S.norm_inv_gamma_sq_le g)
  have hg : 0 < ‖S.gamma g‖ := S.norm_gamma_pos g
  rw [div_le_iff₀ (by positivity)]
  have hmul :
      ‖Complex.sin (S.gamma g * t)‖ * ‖Polynomial.aeval ((S.gamma g ^ 2)⁻¹) P‖ ≤
        Real.exp (S.width * |t|) * polyBallBound P (S.lower⁻¹ ^ 2) :=
    mul_le_mul hsin hpoly (norm_nonneg _)
      (Real.exp_nonneg _)
  calc ‖Complex.sin (S.gamma g * t)‖ * ‖Polynomial.aeval ((S.gamma g ^ 2)⁻¹) P‖
      ≤ Real.exp (S.width * |t|) * polyBallBound P (S.lower⁻¹ ^ 2) := hmul
    _ = (Real.exp (S.width * |t|) * polyBallBound P (S.lower⁻¹ ^ 2)) *
          ‖S.gamma g‖⁻¹ ^ 3 * ‖S.gamma g‖ ^ 3 := by
        field_simp

theorem summable_traceTerm (P : Polynomial ℝ) (t : ℝ) :
    Summable fun g => S.traceTerm P t g := by
  refine Summable.of_norm_bounded
    ((S.summable_inv_cube).mul_left
      (Real.exp (S.width * |t|) * polyBallBound P (S.lower⁻¹ ^ 2))) ?_
  intro g
  exact S.norm_traceTerm_le P t g

/-- The wave trace obeys the exponential-order bound set by the horizontal width. -/
theorem norm_waveTrace_le (P : Polynomial ℝ) (t : ℝ) :
    ‖S.waveTrace P t‖ ≤
      (Real.exp (S.width * |t|) * polyBallBound P (S.lower⁻¹ ^ 2)) *
        ∑' g, ‖S.gamma g‖⁻¹ ^ 3 := by
  refine le_trans (norm_tsum_le_tsum_norm ?_) ?_
  · exact (S.summable_traceTerm P t).norm
  · rw [← tsum_mul_left]
    exact ((S.summable_traceTerm P t).norm).tsum_le_tsum (fun g => S.norm_traceTerm_le P t g)
      ((S.summable_inv_cube).mul_left _)


/-! ## Reality -/

theorem conj_traceTerm (P : Polynomial ℝ) (t : ℝ) (g : G) :
    (starRingEnd ℂ) (S.traceTerm P t g) = S.traceTerm P t (S.invol g) := by
  rw [traceTerm, traceTerm, S.gamma_invol, map_div₀, map_mul, map_pow]
  congr 1
  congr 1
  · rw [← Complex.sin_conj, map_mul]
    congr 1
    simp
  · have hw : Complex.conjAe ((S.gamma g ^ 2)⁻¹) = ((starRingEnd ℂ) (S.gamma g) ^ 2)⁻¹ := by
      simp [map_inv₀, map_pow]
    rw [← hw, Polynomial.aeval_algHom_apply]
    simp

/-- The wave trace of a real polynomial weight is real: conjugation of the frequency family
is realized by the index involution. -/
theorem conj_waveTrace (P : Polynomial ℝ) (t : ℝ) :
    (starRingEnd ℂ) (S.waveTrace P t) = S.waveTrace P t := by
  have hcont : Continuous (starRingEnd ℂ) := Complex.continuous_conj
  have hmap : (starRingEnd ℂ) (∑' g, S.traceTerm P t g) =
      ∑' g, (starRingEnd ℂ) (S.traceTerm P t g) := by
    exact (Complex.conjLIE.toLinearIsometry.toContinuousLinearMap.map_tsum
      (S.summable_traceTerm P t))
  rw [waveTrace, hmap]
  simp_rw [S.conj_traceTerm P t]
  exact (Function.Involutive.toPerm S.invol S.invol_invol).tsum_eq _

theorem waveTrace_im (P : Polynomial ℝ) (t : ℝ) : (S.waveTrace P t).im = 0 := by
  have h := S.conj_waveTrace P t
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

/-- Real form of the wave trace. -/
def realWaveTrace (P : Polynomial ℝ) (t : ℝ) : ℝ := (S.waveTrace P t).re

theorem ofReal_realWaveTrace (P : Polynomial ℝ) (t : ℝ) :
    ((S.realWaveTrace P t : ℝ) : ℂ) = S.waveTrace P t := by
  apply Complex.ext <;> simp [realWaveTrace, S.waveTrace_im]

/-! ## Linearity in the polynomial weight -/

theorem traceTerm_add (P Q : Polynomial ℝ) (t : ℝ) (g : G) :
    S.traceTerm (P + Q) t g = S.traceTerm P t g + S.traceTerm Q t g := by
  simp only [traceTerm, map_add]
  ring

theorem traceTerm_smul (a : ℝ) (P : Polynomial ℝ) (t : ℝ) (g : G) :
    S.traceTerm (a • P) t g = (a : ℂ) * S.traceTerm P t g := by
  simp only [traceTerm, map_smul, Complex.real_smul]
  ring

theorem waveTrace_add (P Q : Polynomial ℝ) (t : ℝ) :
    S.waveTrace (P + Q) t = S.waveTrace P t + S.waveTrace Q t := by
  rw [waveTrace, waveTrace, waveTrace]
  simp_rw [S.traceTerm_add]
  exact (S.summable_traceTerm P t).tsum_add (S.summable_traceTerm Q t)

theorem waveTrace_smul (a : ℝ) (P : Polynomial ℝ) (t : ℝ) :
    S.waveTrace (a • P) t = (a : ℂ) * S.waveTrace P t := by
  rw [waveTrace, waveTrace]
  simp_rw [S.traceTerm_smul]
  exact tsum_mul_left

theorem realWaveTrace_add (P Q : Polynomial ℝ) (t : ℝ) :
    S.realWaveTrace (P + Q) t = S.realWaveTrace P t + S.realWaveTrace Q t := by
  simp [realWaveTrace, S.waveTrace_add]

theorem realWaveTrace_smul (a : ℝ) (P : Polynomial ℝ) (t : ℝ) :
    S.realWaveTrace (a • P) t = a * S.realWaveTrace P t := by
  simp [realWaveTrace, S.waveTrace_smul]

theorem realWaveTrace_sum {ι : Type*} (u : Finset ι) (Q : ι → Polynomial ℝ) (t : ℝ) :
    S.realWaveTrace (∑ i ∈ u, Q i) t = ∑ i ∈ u, S.realWaveTrace (Q i) t := by
  classical
  induction u using Finset.induction with
  | empty => simp [realWaveTrace, waveTrace, traceTerm]
  | insert i u hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, S.realWaveTrace_add, ih]

end WaveSpectrum

end

end GaloisForLFunctions.HTGeometry

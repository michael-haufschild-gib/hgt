import GaloisForLFunctions.HTGeometry.MassBesselDeepTimeCarrier

/-!
# The deep-time carrier estimate, uniform over a logarithmic shell

At a spectral point `σ + iu` with `u` large, every frequency of a logarithmic shell has the same
massive radiation profile to within a relative error controlled by `x²/u`.  The three factors of
the distortion — the ratio of the shell root to the spectral point, the ratio of their principal
square roots, and the exponential of the root defect — are each near one, and the Schläfli
remainder is smaller than the profile by a full power of the spectral height.

Consequently the carriers of a whole shell are aligned: their weighted sum cannot cancel.
-/

open Complex

namespace HTGeometry

noncomputable section

/-! ## The spectral point -/

/-- The spectral point of the aperture. -/
def apertureSpectralPoint (σ u : ℝ) : ℂ := (σ : ℂ) + (u : ℂ) * Complex.I

@[simp] theorem spectralPoint_re (σ u : ℝ) : (apertureSpectralPoint σ u).re = σ := by
  simp [apertureSpectralPoint]

@[simp] theorem spectralPoint_im (σ u : ℝ) : (apertureSpectralPoint σ u).im = u := by
  simp [apertureSpectralPoint]

theorem norm_sq_eq_re_add_im (z : ℂ) : ‖z‖ ^ (2 : ℕ) = z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem norm_spectralPoint_sq (σ u : ℝ) : ‖apertureSpectralPoint σ u‖ ^ (2 : ℕ) = σ ^ (2 : ℕ) + u ^ (2 : ℕ) := by
  rw [norm_sq_eq_re_add_im, spectralPoint_re, spectralPoint_im]

theorem le_norm_spectralPoint (σ u : ℝ) : u ≤ ‖apertureSpectralPoint σ u‖ := by
  nlinarith [norm_spectralPoint_sq σ u, norm_nonneg (apertureSpectralPoint σ u), sq_nonneg σ,
    sq_nonneg (‖apertureSpectralPoint σ u‖ - u), sq_nonneg (‖apertureSpectralPoint σ u‖ + u)]

theorem norm_spectralPoint_le {σ u : ℝ} (hσ : 0 < σ) (hσu : σ ≤ u) :
    ‖apertureSpectralPoint σ u‖ ≤ 2 * u := by
  nlinarith [norm_spectralPoint_sq σ u, norm_nonneg (apertureSpectralPoint σ u), hσ, hσu]

/-! ## Size of the shell root -/

theorem norm_add_ge_sub (A B : ℂ) : ‖A‖ - ‖B‖ ≤ ‖A + B‖ := by
  have h : ‖A‖ ≤ ‖A + B‖ + ‖B‖ := by
    have := norm_sub_le (A + B) B
    simpa using this
  linarith

theorem norm_massBesselRoot_sq_ge {t : ℂ} (htre : 0 < t.re) (htim : 0 < t.im) (x : ℝ) :
    ‖t‖ ^ (2 : ℕ) - x ^ (2 : ℕ) ≤ ‖massBesselRoot t x‖ ^ (2 : ℕ) := by
  have hsq : ‖massBesselRoot t x‖ ^ (2 : ℕ) = ‖t ^ (2 : ℕ) + (x : ℂ) ^ (2 : ℕ)‖ := by
    rw [← norm_pow, massBesselRoot_sq htre htim]
  rw [hsq]
  have hx : ‖((x : ℂ)) ^ (2 : ℕ)‖ = x ^ (2 : ℕ) := by
    rw [← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have ht : ‖t ^ (2 : ℕ)‖ = ‖t‖ ^ (2 : ℕ) := norm_pow t 2
  have := norm_add_ge_sub (t ^ (2 : ℕ)) ((x : ℂ) ^ (2 : ℕ))
  rw [ht, hx] at this
  exact this

/-! ## The uniform shell estimate -/

/-- **The deep-time carrier estimate, uniform over a shell.**  At the spectral point `σ + iu` the
carrier of the frequency `x` agrees with the deep-time profile up to a relative error of order
`x²/u` and an absolute error of order `1/u`. -/
theorem norm_massBesselCarrier_sub_leading_le_shell {a σ u x : ℝ}
    (ha : 0 < a) (hσ : 0 < σ) (hu : 1 ≤ u) (hσu : σ ≤ u)
    (hx2 : 2 * x ^ (2 : ℕ) ≤ u) (hxσ : 4 * x ^ (2 : ℕ) ≤ σ * u) (hax : 2 * a * x ^ (2 : ℕ) ≤ u) :
    ‖massBesselCarrier a (apertureSpectralPoint σ u) x - massBesselLeading a (apertureSpectralPoint σ u)‖
      ≤ (12 + 2 * a) * (x ^ (2 : ℕ) / u) * ‖massBesselLeading a (apertureSpectralPoint σ u)‖
        + 8 * Real.exp (-(a * σ / 2)) * Real.sqrt (2 * Real.pi / (a * σ)) / u := by
  set t : ℂ := apertureSpectralPoint σ u with htdef
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  have htre : 0 < t.re := by rw [htdef, spectralPoint_re]; exact hσ
  have htim : 0 < t.im := by rw [htdef, spectralPoint_im]; exact hu0
  set z : ℂ := massBesselRoot t x with hzdef
  have hzre : 0 < z.re := massBesselRoot_re_pos htre htim x
  -- the root defect
  have hδ : ‖z - t‖ ≤ x ^ (2 : ℕ) / u := by
    have := norm_massBesselRoot_sub_le htre htim x
    rw [htdef, spectralPoint_im] at this
    exact this
  have hδ0 : (0 : ℝ) ≤ x ^ (2 : ℕ) / u := by positivity
  -- size of the root
  have hnormt : u ≤ ‖t‖ := by rw [htdef]; exact le_norm_spectralPoint σ u
  have hnormt2 : ‖t‖ ≤ 2 * u := by rw [htdef]; exact norm_spectralPoint_le hσ hσu
  have hzsq : u ^ (2 : ℕ) / 2 ≤ ‖z‖ ^ (2 : ℕ) := by
    have h := norm_massBesselRoot_sq_ge htre htim x
    rw [← hzdef] at h
    nlinarith [hnormt, hu0, hx2, hu]
  have hznorm : u / 2 ≤ ‖z‖ := by
    nlinarith [hzsq, norm_nonneg z, hu0]
  have hzpos : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le (by positivity) hznorm
  -- the three distortion bounds
  have hα : ‖z - t‖ / ‖z‖ ≤ 2 * x ^ (2 : ℕ) / u ^ (2 : ℕ) := by
    rw [div_le_iff₀ hzpos]
    have hbig : 2 * x ^ (2 : ℕ) / u ^ (2 : ℕ) * (u / 2) = x ^ (2 : ℕ) / u := by
      field_simp
    calc ‖z - t‖ ≤ x ^ (2 : ℕ) / u := hδ
      _ = 2 * x ^ (2 : ℕ) / u ^ (2 : ℕ) * (u / 2) := hbig.symm
      _ ≤ 2 * x ^ (2 : ℕ) / u ^ (2 : ℕ) * ‖z‖ := by
          refine mul_le_mul_of_nonneg_left hznorm (by positivity)
  have hcstre : Real.sqrt (u / 2) ≤ (csqrt t).re := by
    rw [csqrt_re, csqrtRe]
    refine Real.sqrt_le_sqrt ?_
    have : u ≤ ‖t‖ + σ := by linarith
    linarith
  have hcstrepos : (0 : ℝ) < Real.sqrt (u / 2) := Real.sqrt_pos.2 (by positivity)
  have hcszn : Real.sqrt (u / 2) ≤ ‖csqrt z‖ := by
    rw [norm_csqrt hzre]
    exact Real.sqrt_le_sqrt hznorm
  have hβ : ‖csqrt t - csqrt z‖ / ‖csqrt z‖ ≤ 2 * x ^ (2 : ℕ) / u ^ (2 : ℕ) := by
    have hsqrtsq : Real.sqrt (u / 2) * Real.sqrt (u / 2) = u / 2 :=
      Real.mul_self_sqrt (by positivity)
    have hlip : ‖csqrt t - csqrt z‖ ≤ ‖t - z‖ / (csqrt t).re := norm_csqrt_sub_le htre hzre
    have htz : ‖t - z‖ = ‖z - t‖ := by
      rw [← norm_neg]
      congr 1
      ring
    rw [htz] at hlip
    have hstep : ‖csqrt t - csqrt z‖ ≤ (x ^ (2 : ℕ) / u) / Real.sqrt (u / 2) := by
      refine le_trans hlip ?_
      gcongr
    have hkey : (x ^ (2 : ℕ) / u) / Real.sqrt (u / 2) ≤ 2 * x ^ (2 : ℕ) / u ^ (2 : ℕ) * Real.sqrt (u / 2) := by
      rw [div_le_iff₀ hcstrepos, mul_assoc, hsqrtsq]
      have hval : 2 * x ^ (2 : ℕ) / u ^ (2 : ℕ) * (u / 2) = x ^ (2 : ℕ) / u := by
        field_simp
      rw [hval]
    rw [div_le_iff₀ (lt_of_lt_of_le hcstrepos hcszn)]
    calc ‖csqrt t - csqrt z‖ ≤ (x ^ (2 : ℕ) / u) / Real.sqrt (u / 2) := hstep
      _ ≤ 2 * x ^ (2 : ℕ) / u ^ (2 : ℕ) * Real.sqrt (u / 2) := hkey
      _ ≤ 2 * x ^ (2 : ℕ) / u ^ (2 : ℕ) * ‖csqrt z‖ := mul_le_mul_of_nonneg_left hcszn (by positivity)
  have hβ1 : 2 * x ^ (2 : ℕ) / u ^ (2 : ℕ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [hx2, hu, hu0]
  have hγ : 2 * (a * ‖z - t‖) ≤ 2 * a * x ^ (2 : ℕ) / u := by
    have := mul_le_mul_of_nonneg_left hδ (by positivity : (0:ℝ) ≤ 2 * a)
    calc 2 * (a * ‖z - t‖) = 2 * a * ‖z - t‖ := by ring
      _ ≤ 2 * a * (x ^ (2 : ℕ) / u) := by
          exact mul_le_mul_of_nonneg_left hδ (by positivity)
      _ = 2 * a * x ^ (2 : ℕ) / u := by ring
  have hγ1 : 2 * a * x ^ (2 : ℕ) / u ≤ 1 := by
    rw [div_le_one hu0]
    linarith [hax]
  have hexpsmall : a * ‖z - t‖ ≤ 1 := by
    nlinarith [hγ, hγ1, norm_nonneg (z - t), ha]
  -- the assembled bound
  have hmain := norm_massBesselCarrier_sub_leading_le ha htre htim x hα hβ hβ1 hγ hγ1 hexpsmall
  refine le_trans hmain ?_
  refine add_le_add ?_ ?_
  · rw [mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have h1 : 4 * (2 * x ^ (2 : ℕ) / u ^ (2 : ℕ)) + 2 * (2 * x ^ (2 : ℕ) / u ^ (2 : ℕ)) = 12 * x ^ (2 : ℕ) / u ^ (2 : ℕ) := by ring
    rw [h1]
    have h2 : 12 * x ^ (2 : ℕ) / u ^ (2 : ℕ) ≤ 12 * (x ^ (2 : ℕ) / u) := by
      rw [div_le_iff₀ (by positivity)]
      have : x ^ (2 : ℕ) / u * u = x ^ (2 : ℕ) := by field_simp
      nlinarith [hu, sq_nonneg x, hu0, this]
    have h3 : 2 * a * x ^ (2 : ℕ) / u = 2 * a * (x ^ (2 : ℕ) / u) := by ring
    rw [h3]
    have : (12 + 2 * a) * (x ^ (2 : ℕ) / u) = 12 * (x ^ (2 : ℕ) / u) + 2 * a * (x ^ (2 : ℕ) / u) := by ring
    rw [this]
    linarith
  · -- the Schläfli remainder
    have hzrege : σ / 2 ≤ z.re := by
      have hre : |(z - t).re| ≤ ‖z - t‖ := Complex.abs_re_le_norm _
      rw [Complex.sub_re] at hre
      have habs := abs_le.mp hre
      have hxu : x ^ (2 : ℕ) / u ≤ σ / 4 := by
        rw [div_le_div_iff₀ hu0 (by norm_num)]
        linarith [hxσ]
      have htrez : t.re = σ := by rw [htdef, spectralPoint_re]
      rw [htrez] at habs
      linarith [habs.1, hδ, hxu]
    have hzrepos : (0 : ℝ) < z.re := lt_of_lt_of_le (by positivity) hzrege
    have hrem := norm_massBesselRemainder_le ha htre htim x
    rw [← hzdef] at hrem
    have hexple : Real.exp (-(a * z.re)) ≤ Real.exp (-(a * σ / 2)) := by
      refine Real.exp_le_exp.2 ?_
      nlinarith [hzrege, ha]
    have hsqle : Real.sqrt (Real.pi / (a * z.re)) ≤ Real.sqrt (2 * Real.pi / (a * σ)) := by
      refine Real.sqrt_le_sqrt ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : a * (σ / 2) ≤ a * z.re := mul_le_mul_of_nonneg_left hzrege ha.le
      nlinarith [h1, Real.pi_pos]
    have hfac : Real.exp (-(a * z.re)) * Real.sqrt (Real.pi / (a * z.re))
        ≤ Real.exp (-(a * σ / 2)) * Real.sqrt (2 * Real.pi / (a * σ)) :=
      mul_le_mul hexple hsqle (Real.sqrt_nonneg _) (Real.exp_pos _).le
    have hnum : 2 * a * ‖t‖ * ‖massBesselRemainder a t x‖
        ≤ 2 * a * (2 * u) *
          (Real.exp (-(a * σ / 2)) * Real.sqrt (2 * Real.pi / (a * σ)) / (a * ‖z‖)) := by
      refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
      · exact mul_le_mul_of_nonneg_left hnormt2 (by positivity)
      · refine le_trans hrem ?_
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hfac (by positivity)
    have hstep : 2 * a * ‖t‖ * ‖massBesselRemainder a t x‖ / ‖z‖
        ≤ 2 * a * (2 * u) *
          (Real.exp (-(a * σ / 2)) * Real.sqrt (2 * Real.pi / (a * σ)) / (a * ‖z‖)) / ‖z‖ := by
      have hinv : (0 : ℝ) ≤ (‖z‖)⁻¹ := by positivity
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hnum hinv
    refine le_trans hstep ?_
    have hkey : 2 * a * (2 * u) *
        (Real.exp (-(a * σ / 2)) * Real.sqrt (2 * Real.pi / (a * σ)) / (a * ‖z‖)) / ‖z‖
        = 4 * u * (Real.exp (-(a * σ / 2)) * Real.sqrt (2 * Real.pi / (a * σ))) / ‖z‖ ^ (2 : ℕ) := by
      field_simp
      ring
    have hrhs : 8 * Real.exp (-(a * σ / 2)) * Real.sqrt (2 * Real.pi / (a * σ)) / u
        = 8 * (Real.exp (-(a * σ / 2)) * Real.sqrt (2 * Real.pi / (a * σ))) / u := by ring
    rw [hkey, hrhs]
    set K : ℝ := Real.exp (-(a * σ / 2)) * Real.sqrt (2 * Real.pi / (a * σ)) with hKdef
    have hK0 : (0 : ℝ) ≤ K := by
      rw [hKdef]
      positivity
    clear_value K
    rw [div_le_div_iff₀ (pow_pos hzpos 2) hu0]
    have h8K : (0 : ℝ) ≤ 8 * K := by linarith
    have h8 : 8 * K * (u ^ (2 : ℕ) / 2) ≤ 8 * K * ‖z‖ ^ (2 : ℕ) := mul_le_mul_of_nonneg_left hzsq h8K
    linarith [h8]

end

end HTGeometry

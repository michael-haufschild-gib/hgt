import Mathlib

/-!
# The realization defect of one depth mode

The logarithm of the modulus of `1 − x e^{−iθ}` expands into the harmonic ladder
`−∑_r x^r cos(rθ)/r`, so the *defect* of a single depth mode — the loss of modulus caused by the
phase `θ` — is the manifestly nonnegative statistic `∑_r x^r (1 − cos(rθ))/r`.  This is the local
form of the modulus budget: each depth `j` contributes with `x = q^j`, and each harmonic `r`
contributes the weight `q^{jr}/r`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

/-- The phase factor of a mode. -/
noncomputable def modePhase (θ : ℝ) : ℂ := Complex.exp ((-θ : ℝ) * Complex.I)

theorem norm_modePhase (θ : ℝ) : ‖modePhase θ‖ = 1 := by
  rw [modePhase, Complex.norm_exp]
  simp

theorem re_pow_ofReal_mul_modePhase (x θ : ℝ) (n : ℕ) :
    (((x : ℂ) * modePhase θ) ^ n).re = x ^ n * Real.cos ((n : ℝ) * θ) := by
  have hpow : ((x : ℂ) * modePhase θ) ^ n
      = ((x ^ n : ℝ) : ℂ) * Complex.exp (((-((n : ℝ) * θ) : ℝ) : ℂ) * Complex.I) := by
    rw [mul_pow, modePhase, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  rw [hpow, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.ofReal_re, Complex.ofReal_im,
    Real.cos_neg]
  ring

theorem div_natCast_re (w : ℂ) (n : ℕ) : (w / (n : ℂ)).re = w.re / (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hnR : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [Complex.div_re]
    simp [Complex.normSq_apply]
    field_simp

/-- **The harmonic expansion of the log-modulus.** -/
theorem hasSum_log_norm_one_sub (x θ : ℝ) (hx : ‖(x : ℂ) * modePhase θ‖ < 1) :
    HasSum (fun n : ℕ => x ^ n * Real.cos ((n : ℝ) * θ) / (n : ℝ))
      (-Real.log ‖1 - (x : ℂ) * modePhase θ‖) := by
  have h := Complex.hasSum_taylorSeries_neg_log hx
  have hre := Complex.hasSum_re h
  rw [Complex.neg_re, Complex.log_re] at hre
  refine hre.congr_fun fun n => ?_
  rw [div_natCast_re, re_pow_ofReal_mul_modePhase]

theorem norm_ofReal_mul_modePhase (x θ : ℝ) : ‖(x : ℂ) * modePhase θ‖ = |x| := by
  rw [norm_mul, norm_modePhase, mul_one, Complex.norm_real, Real.norm_eq_abs]

@[simp] theorem modePhase_zero : modePhase 0 = 1 := by
  rw [modePhase]
  simp

/-- **The defect of one depth mode.**  The phase `θ` costs exactly the harmonic ladder
`∑_r x^r (1 − cos rθ)/r`, whose terms are all nonnegative. -/
theorem hasSum_modeDefect {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (θ : ℝ) :
    HasSum (fun n : ℕ => x ^ n * (1 - Real.cos ((n : ℝ) * θ)) / (n : ℝ))
      (Real.log ‖1 - (x : ℂ) * modePhase θ‖ - Real.log (1 - x)) := by
  have hnorm : ∀ φ : ℝ, ‖(x : ℂ) * modePhase φ‖ < 1 := by
    intro φ
    rw [norm_ofReal_mul_modePhase, abs_of_nonneg hx0]
    exact hx1
  have h0 := hasSum_log_norm_one_sub x 0 (hnorm 0)
  have hθ := hasSum_log_norm_one_sub x θ (hnorm θ)
  have hzero : Real.log ‖1 - (x : ℂ) * modePhase 0‖ = Real.log (1 - x) := by
    rw [modePhase_zero, mul_one]
    congr 1
    rw [show (1 : ℂ) - (x : ℂ) = (((1 - x : ℝ)) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [hzero] at h0
  have hsub := h0.sub hθ
  have hval : -Real.log (1 - x) - -Real.log ‖1 - (x : ℂ) * modePhase θ‖
      = Real.log ‖1 - (x : ℂ) * modePhase θ‖ - Real.log (1 - x) := by ring
  rw [hval] at hsub
  refine hsub.congr_fun fun n => ?_
  rw [mul_zero, Real.cos_zero]
  ring

theorem modeDefect_term_nonneg {x : ℝ} (hx0 : 0 ≤ x) (θ : ℝ) (n : ℕ) :
    0 ≤ x ^ n * (1 - Real.cos ((n : ℝ) * θ)) / (n : ℝ) := by
  have h1 : (0 : ℝ) ≤ 1 - Real.cos ((n : ℝ) * θ) := by
    have := Real.cos_le_one ((n : ℝ) * θ)
    linarith
  positivity

/-- The defect of one depth mode is nonnegative. -/
theorem modeDefect_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (θ : ℝ) :
    0 ≤ Real.log ‖1 - (x : ℂ) * modePhase θ‖ - Real.log (1 - x) :=
  (hasSum_modeDefect hx0 hx1 θ).nonneg (modeDefect_term_nonneg hx0 θ)

end GaloisForLFunctions.HTGeometry

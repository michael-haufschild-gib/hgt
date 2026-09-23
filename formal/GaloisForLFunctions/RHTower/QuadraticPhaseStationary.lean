import GaloisForLFunctions.RHTower.FresnelIntegral

/-!
# The quadratic phase integral

The local model of a nondegenerate stationary point is the pure quadratic phase.  For `μ > 0`,

```text
∫_{-R}^{R} exp(i μ t²/2) dt = √(2π/μ) · e^{iπ/4} + O(1/(μR)),
```

with the explicit constant `8`.  The scaling `t = x √(2/μ)` reduces this to the Fresnel integral
`∫_0^∞ exp(i x²) dx = (√π/2) e^{iπ/4}`, whose truncation error is `2/R`.

Reversing the sign of the phase conjugates both the value and the phase `e^{iπ/4} ↦ e^{-iπ/4}`.
-/

noncomputable section

open Complex MeasureTheory Set

namespace GaloisForLFunctions.RHTower

/-- The pure quadratic phase kernel with curvature `μ`. -/
def quadPhase (μ t : ℝ) : ℂ := Complex.exp (Complex.ofReal (μ * t ^ (2 : ℕ) / 2) * Complex.I)

theorem continuous_quadPhase (μ : ℝ) : Continuous (quadPhase μ) := by
  unfold quadPhase
  fun_prop

theorem quadPhase_neg (μ t : ℝ) : quadPhase μ (-t) = quadPhase μ t := by
  simp [quadPhase]

/-- The quadratic phase integral is twice its half-line part. -/
theorem integral_quadPhase_symm (μ R : ℝ) :
    (∫ t in (-R : ℝ)..R, quadPhase μ t) = 2 * ∫ t in (0 : ℝ)..R, quadPhase μ t := by
  have hcont := continuous_quadPhase μ
  have hI : ∀ a b : ℝ, IntervalIntegrable (quadPhase μ) MeasureTheory.volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have h1 : (∫ t in (-R : ℝ)..0, quadPhase μ t) = ∫ t in (0 : ℝ)..R, quadPhase μ t := by
    have h := intervalIntegral.integral_comp_neg (a := (-R : ℝ)) (b := 0)
      (f := fun t : ℝ => quadPhase μ t)
    simpa [quadPhase_neg] using h
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hI (-R) 0) (hI 0 R)
  rw [← h2, h1]
  ring

/-- The scaling `t = x √(2/μ)` turns the quadratic phase into the Fresnel phase. -/
theorem integral_quadPhase_scale {μ : ℝ} (hμ : 0 < μ) (R : ℝ) :
    (∫ t in (0 : ℝ)..R, quadPhase μ t)
      = (Complex.ofReal (Real.sqrt (μ / 2)))⁻¹ *
          ∫ x in (0 : ℝ)..(Real.sqrt (μ / 2) * R), Complex.exp ((x ^ (2 : ℕ) : ℝ) * Complex.I) := by
  have hc : Real.sqrt (μ / 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hcsq : (Real.sqrt (μ / 2)) ^ (2 : ℕ) = μ / 2 := Real.sq_sqrt (by positivity)
  have hshape : ∀ t : ℝ, quadPhase μ t
      = (fun x : ℝ => Complex.exp ((x ^ (2 : ℕ) : ℝ) * Complex.I)) (Real.sqrt (μ / 2) * t) := by
    intro t
    have hsq : (Real.sqrt (μ / 2) * t) ^ (2 : ℕ) = μ * t ^ (2 : ℕ) / 2 := by
      rw [mul_pow, hcsq]
      ring
    simp only [quadPhase, hsq]
  have h := intervalIntegral.integral_comp_mul_left
    (f := fun x : ℝ => Complex.exp ((x ^ (2 : ℕ) : ℝ) * Complex.I)) (a := 0) (b := R) hc
  rw [intervalIntegral.integral_congr (fun t _ => hshape t), h, mul_zero, Complex.real_smul]
  norm_num

/-- **The quadratic phase integral.**  For `μ > 0` the symmetric truncation is within `8/(μR)` of
`√(2π/μ) e^{iπ/4}`. -/
theorem norm_integral_quadPhase_sub_le {μ R : ℝ} (hμ : 0 < μ) (hR : 0 < R) :
    ‖(∫ t in (-R : ℝ)..R, quadPhase μ t)
        - Complex.ofReal (Real.sqrt (2 * Real.pi / μ))
            * Complex.exp (Complex.ofReal (Real.pi / 4) * Complex.I)‖
      ≤ 8 / (μ * R) := by
  have hμ0 : μ ≠ 0 := hμ.ne'
  have hR0 : R ≠ 0 := hR.ne'
  have hcpos : 0 < Real.sqrt (μ / 2) := Real.sqrt_pos.mpr (by positivity)
  have hS : 0 < Real.sqrt (μ / 2) * R := by positivity
  have hcsq : (Real.sqrt (μ / 2)) ^ (2 : ℕ) = μ / 2 := Real.sq_sqrt (by positivity)
  have hc2 : Real.sqrt (μ / 2) * Real.sqrt (μ / 2) = μ / 2 := by
    rw [← sq]; exact hcsq
  have hfres := norm_integral_fresnel_sub_le hS
  have hval : (2 : ℂ) * (Complex.ofReal (Real.sqrt (μ / 2)))⁻¹ * fresnelValue
      = Complex.ofReal (Real.sqrt (2 * Real.pi / μ))
          * Complex.exp (Complex.ofReal (Real.pi / 4) * Complex.I) := by
    rw [fresnelValue_eq]
    have hsplit : Real.sqrt (2 * Real.pi / μ)
        = (Real.sqrt (μ / 2))⁻¹ * Real.sqrt Real.pi := by
      rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
      congr 1
      field_simp
    rw [hsplit]
    push_cast
    ring
  rw [integral_quadPhase_symm, integral_quadPhase_scale hμ, ← hval]
  have hfactor : (2 : ℂ) * ((Complex.ofReal (Real.sqrt (μ / 2)))⁻¹ *
        ∫ x in (0 : ℝ)..(Real.sqrt (μ / 2) * R), Complex.exp ((x ^ (2 : ℕ) : ℝ) * Complex.I))
      - (2 : ℂ) * (Complex.ofReal (Real.sqrt (μ / 2)))⁻¹ * fresnelValue
      = ((2 : ℂ) * (Complex.ofReal (Real.sqrt (μ / 2)))⁻¹) *
        ((∫ x in (0 : ℝ)..(Real.sqrt (μ / 2) * R), Complex.exp ((x ^ (2 : ℕ) : ℝ) * Complex.I))
          - fresnelValue) := by
    ring
  rw [hfactor, norm_mul]
  have hnorm : ‖(2 : ℂ) * (Complex.ofReal (Real.sqrt (μ / 2)))⁻¹‖ = 2 / Real.sqrt (μ / 2) := by
    have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos, h2]
    ring
  rw [hnorm]
  have hbound : 2 / Real.sqrt (μ / 2) * ‖(∫ x in (0 : ℝ)..(Real.sqrt (μ / 2) * R),
        Complex.exp ((x ^ (2 : ℕ) : ℝ) * Complex.I)) - fresnelValue‖
      ≤ 2 / Real.sqrt (μ / 2) * (2 / (Real.sqrt (μ / 2) * R)) :=
    mul_le_mul_of_nonneg_left hfres (by positivity)
  refine hbound.trans (le_of_eq ?_)
  have hstep : 2 / Real.sqrt (μ / 2) * (2 / (Real.sqrt (μ / 2) * R))
      = 4 / (Real.sqrt (μ / 2) * Real.sqrt (μ / 2) * R) := by
    field_simp
    ring
  rw [hstep, hc2]
  field_simp
  ring

/-- **The reversed quadratic phase integral.**  Conjugating the phase conjugates the value. -/
theorem norm_integral_quadPhase_conj_sub_le {μ R : ℝ} (hμ : 0 < μ) (hR : 0 < R) :
    ‖(∫ t in (-R : ℝ)..R, Complex.exp (Complex.ofReal (-(μ * t ^ (2 : ℕ) / 2)) * Complex.I))
        - Complex.ofReal (Real.sqrt (2 * Real.pi / μ))
            * Complex.exp (Complex.ofReal (-(Real.pi / 4)) * Complex.I)‖
      ≤ 8 / (μ * R) := by
  have hconj : ∀ t : ℝ, Complex.exp (Complex.ofReal (-(μ * t ^ (2 : ℕ) / 2)) * Complex.I)
      = (starRingEnd ℂ) (quadPhase μ t) := by
    intro t
    rw [quadPhase, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 1
    push_cast
    ring
  have hint : (∫ t in (-R : ℝ)..R, Complex.exp (Complex.ofReal (-(μ * t ^ (2 : ℕ) / 2)) * Complex.I))
      = (starRingEnd ℂ) (∫ t in (-R : ℝ)..R, quadPhase μ t) := by
    rw [← intervalIntegral.intervalIntegral_conj]
    exact intervalIntegral.integral_congr fun t _ => hconj t
  have hexp : Complex.exp (Complex.ofReal (-(Real.pi / 4)) * Complex.I)
      = (starRingEnd ℂ) (Complex.exp (Complex.ofReal (Real.pi / 4) * Complex.I)) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 1
    push_cast
    ring
  have hvalconj : Complex.ofReal (Real.sqrt (2 * Real.pi / μ))
      * Complex.exp (Complex.ofReal (-(Real.pi / 4)) * Complex.I)
      = (starRingEnd ℂ) (Complex.ofReal (Real.sqrt (2 * Real.pi / μ))
          * Complex.exp (Complex.ofReal (Real.pi / 4) * Complex.I)) := by
    rw [map_mul, Complex.conj_ofReal, ← hexp]
  rw [hint, hvalconj, ← map_sub, RCLike.norm_conj]
  exact norm_integral_quadPhase_sub_le hμ hR

end GaloisForLFunctions.RHTower

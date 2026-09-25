import GaloisForLFunctions.RHTower.SelbergEisensteinCuspScattering
import GaloisForLFunctions.RHTower.SelbergPoincareContinuation

open Complex MeasureTheory UpperHalfPlane
open scoped MatrixGroups FourierTransform

/-!
# The scattering entry `φ_{∞,σ∞}(s)` of `Γ(N)`

Scaling `x = yt` gives `∫_ℝ (y/(x²+y²))^s dx = y^{1-s} C(s)`, `C(s) = ∫_ℝ (1+t²)^{-s} dt` (`integral_ker0_scale`). With
the row-count series `D_σ` this puts the constant term of `E_∞` at the cusp `σ∞` in the form
`∫_0^N E_∞(σ(x+iy), s) dx = N · count₀ · y^s + φ_{∞,σ∞}(s) · y^{1-s}` for `Re s > 1` (`integral_poincare_cusp_phi`),
with `φ_{∞,σ∞} = D_σ · C` holomorphic on `Re s > 1/2`, `s ≠ 1` (`differentiableAt_phiσ`).
-/

namespace GaloisForLFunctions.RHTower.SelbergEisensteinScatteringEntry
open GaloisForLFunctions.RHTower.SelbergPoincareKernel GaloisForLFunctions.RHTower.SelbergEisensteinCuspSlice
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspConstant GaloisForLFunctions.RHTower.SelbergEisensteinCuspScattering
  GaloisForLFunctions.RHTower.SelbergMaassMean GaloisForLFunctions.RHTower.SelbergPoincare

theorem wt_scale {y : ℝ} (hy : 0 < y) (t : ℝ) : wt y (y * t) = y⁻¹ * wt 1 t := by
  unfold wt; field_simp

/-- **Scaling of the kernel integral**: `∫_ℝ (y/(x²+y²))^s dx = y^{1-s} ∫_ℝ (1+t²)^{-s} dt`. -/
theorem integral_ker0_scale {y : ℝ} (hy : 0 < y) (s : ℂ) :
    ∫ x, ker 0 y s x = ((y : ℝ) : ℂ) ^ (1 - s) * ∫ t, ker 0 1 s t := by
  have h := Measure.integral_comp_mul_left (ker 0 y s) y
  rw [abs_inv, abs_of_pos hy] at h
  have hscale : ∀ t, ker 0 y s (y * t) = (((y⁻¹ : ℝ) : ℂ)) ^ s * ker 0 1 s t := by
    intro t
    rw [ker0_eq y hy, ker0_eq 1 one_pos, wt_scale hy, ofReal_mul,
      mul_cpow_ofReal_nonneg (inv_pos.mpr hy).le (wt_pos one_pos t).le]
  simp_rw [hscale] at h
  rw [integral_const_mul] at h
  have hy0 : ((y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have harg : ((y : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hy.le]; exact Real.pi_ne_zero.symm
  have e : ∫ x, ker 0 y s x = (y : ℂ) * ((((y⁻¹ : ℝ) : ℂ)) ^ s * ∫ t, ker 0 1 s t) := by
    rw [h, Complex.real_smul, ← mul_assoc, ofReal_inv, mul_inv_cancel₀ hy0, one_mul]
  rw [e, ofReal_inv, inv_cpow _ _ harg, cpow_sub _ _ hy0, cpow_one]
  field_simp

variable (N : ℕ) [NeZero N] (σ : SL(2, ℤ))

/-- **The constant term of `E_∞` at `σ∞`** (`Re s > 1`):
`(1/N)·∫_0^N E_∞(σ(x+iy), s) dx · N = N · count₀ · y^s + D_σ(s) · C(s) · y^{1-s}`, `C(s) = ∫_ℝ (1+t²)^{-s} dt`. -/
theorem integral_poincare_cusp_eq {s : ℂ} (hs : 1 < s.re) {y : ℝ} (hy : 0 < y) :
    ∫ x in (0 : ℝ)..N, poincare N 0 s (σ • ofComplex (point x y)) =
      (N : ℂ) * ((y : ℝ) : ℂ) ^ s * (count0 N σ : ℂ) +
        Dσ N σ s * (∫ t, ker 0 1 s t) * ((y : ℝ) : ℂ) ^ (1 - s) := by
  rw [integral_poincare_cusp (N := N) (σ := σ) hs hy, tsum_weight_eq_Dσ N σ hs, integral_ker0_scale hy]
  ring

/-- **The scattering entry `φ_{∞,σ∞}(s) = D_σ(s) · ∫_ℝ (1+t²)^{-s} dt`**. -/
noncomputable def phiσ (s : ℂ) : ℂ := Dσ N σ s * ∫ t, ker 0 1 s t

theorem differentiableAt_integral_ker {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (fun s => ∫ t, ker 0 1 s t) s := by
  have h := GaloisForLFunctions.RHTower.SelbergPoincareContinuation.differentiableAt_fourier_ker
    (β := 0) (y := 1) le_rfl one_pos hs 0
  simpa [Real.fourier_eq] using h

/-- **Continuation of the scattering entry**: `φ_{∞,σ∞}` is holomorphic on `Re s > 1/2`, `s ≠ 1`. -/
theorem differentiableAt_phiσ {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) : DifferentiableAt ℂ (phiσ N σ) s :=
  (differentiableAt_Dσ N σ hs hs1).mul (differentiableAt_integral_ker hs)

theorem integral_poincare_cusp_phi {s : ℂ} (hs : 1 < s.re) {y : ℝ} (hy : 0 < y) :
    ∫ x in (0 : ℝ)..N, poincare N 0 s (σ • ofComplex (point x y)) =
      (N : ℂ) * ((y : ℝ) : ℂ) ^ s * (count0 N σ : ℂ) + phiσ N σ s * ((y : ℝ) : ℂ) ^ (1 - s) := by
  rw [integral_poincare_cusp_eq N σ hs hy, phiσ]

end GaloisForLFunctions.RHTower.SelbergEisensteinScatteringEntry

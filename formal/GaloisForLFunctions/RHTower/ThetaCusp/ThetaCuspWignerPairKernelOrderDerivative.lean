import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspWignerRadialGammaProductRule
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspWignerPairOrientationAntisymmetry

/-!
# The universal kernel's order derivative

The log-scale pair kernel is exactly the order derivative of the exponential pair kernel, shifted
by `log 2π`:

```text
d/dσ [ Kernel σ y ] = LogKernel σ y - log (2π) · Kernel σ y .
```

Consequently the archimedean `(1,1)` orientation current — the Hedenmalm gate with trivial
Dirichlet weight — is the difference of that order derivative at `σ = a + 1/2` and at `1/2 - a`.
The gate for this term is therefore a convexity question for `τ ↦ Kernel τ y` across the critical
abscissa.
-/

open Real MeasureTheory Set

namespace RHTower

noncomputable section

theorem hasDerivAt_const_rpow {b : ℝ} (hb : 0 < b) (σ : ℝ) :
    HasDerivAt (fun τ : ℝ => b ^ τ) (b ^ σ * Real.log b) σ := by
  have hfun : (fun τ : ℝ => b ^ τ) = fun τ : ℝ => Real.exp (Real.log b * τ) := by
    funext τ; rw [Real.rpow_def_of_pos hb]
  rw [hfun]
  have hinner : HasDerivAt (fun τ : ℝ => Real.log b * τ) (Real.log b) σ := by
    simpa using (hasDerivAt_id σ).const_mul (Real.log b)
  have h := (Real.hasDerivAt_exp (Real.log b * σ)).comp σ hinner
  refine h.congr_deriv ?_
  rw [← Real.rpow_def_of_pos hb]

/-- **The log-scale pair kernel is the order derivative of the exponential pair kernel.** -/
theorem hasDerivAt_thetaCuspWignerPairKernel {σ : ℝ} (hσ : 0 < σ) (y : ℝ) :
    HasDerivAt (fun τ : ℝ => thetaCuspWignerPairKernel τ y)
      (thetaCuspWignerPairLogKernel σ y -
        Real.log (2 * Real.pi) * thetaCuspWignerPairKernel σ y) σ := by
  have hP : (0 : ℝ) < 2 * Real.pi := by positivity
  have hC : (0 : ℝ) < Real.cosh y := Real.cosh_pos y
  have hCi : (0 : ℝ) < 1 / Real.cosh y := by positivity
  have h2 : (0 : ℝ) < σ + 2 := by linarith
  have hne : ∀ m : ℕ, σ + 2 ≠ -(m : ℝ) := by
    intro m hm
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith [hm ▸ h2]
  -- the four factors
  have hA : HasDerivAt (fun τ : ℝ => (2 * Real.pi) ^ (-τ))
      (-((2 * Real.pi) ^ (-σ) * Real.log (2 * Real.pi))) σ := by
    have hneg : HasDerivAt (fun τ : ℝ => -τ) (-1) σ := by simpa using (hasDerivAt_neg σ)
    have h := (hasDerivAt_const_rpow hP (-σ)).comp σ hneg
    refine h.congr_deriv ?_
    simp
  have hB : HasDerivAt (fun τ : ℝ => Real.Gamma (τ + 2)) (deriv Real.Gamma (σ + 2)) σ := by
    have hinner : HasDerivAt (fun τ : ℝ => τ + 2) 1 σ := (hasDerivAt_id σ).add_const 2
    simpa [Function.comp_def] using
      (Real.differentiableAt_Gamma hne).hasDerivAt.comp σ hinner
  have hD : HasDerivAt (fun τ : ℝ => (1 / Real.cosh y) ^ (τ + 2))
      ((1 / Real.cosh y) ^ (σ + 2) * Real.log (1 / Real.cosh y)) σ := by
    have hinner : HasDerivAt (fun τ : ℝ => τ + 2) 1 σ := (hasDerivAt_id σ).add_const 2
    have h := (hasDerivAt_const_rpow hCi (σ + 2)).comp σ hinner
    refine h.congr_deriv ?_
    simp
  have hE : HasDerivAt (fun τ : ℝ => thetaCuspWignerRadialQ τ (Real.cosh y))
      (thetaCuspWignerRadialQDeriv σ (Real.cosh y)) σ := by
    have hCsq : (Real.cosh y) ^ (2 : ℕ) ≠ 0 := by positivity
    have hpoly : HasDerivAt
        (fun τ : ℝ => ((τ + 2) * (τ + 3)) * ((Real.cosh y) ^ (2 : ℕ))⁻¹ - 6 * (τ + 2) + 9)
        ((2 * σ + 5) * ((Real.cosh y) ^ (2 : ℕ))⁻¹ - 6) σ := by
      have h1 : HasDerivAt (fun τ : ℝ => (τ + 2) * (τ + 3))
          (1 * (σ + 3) + (σ + 2) * 1) σ :=
        ((hasDerivAt_id σ).add_const 2).mul ((hasDerivAt_id σ).add_const 3)
      have h2' := (h1.mul_const (((Real.cosh y) ^ (2 : ℕ))⁻¹)).sub
        (((hasDerivAt_id σ).add_const 2).const_mul (6 : ℝ))
      have h3 := h2'.add_const (9 : ℝ)
      refine h3.congr_deriv ?_
      ring
    refine hpoly.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
    · rw [thetaCuspWignerRadialQDeriv, div_eq_mul_inv]
    · filter_upwards with τ
      rw [thetaCuspWignerRadialQ, div_eq_mul_inv]
  -- assemble
  have hprod := ((hA.mul hB).div_const 2).mul (hD.mul hE)
  have hlog : Real.log (1 / Real.cosh y) = -Real.log (Real.cosh y) := by
    rw [Real.log_div one_ne_zero hC.ne', Real.log_one, zero_sub]
  refine hprod.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · simp only [Pi.mul_apply]
    rw [thetaCuspWignerPairLogKernel, thetaCuspWignerPairKernel,
      thetaCuspWignerRadialLogWeight_eq_product_rule hσ hC, hlog]
    ring
  · filter_upwards with τ
    simp only [Pi.mul_apply]
    rw [thetaCuspWignerPairKernel]

/-- The order derivative of the universal kernel, as a `deriv`. -/
theorem deriv_thetaCuspWignerPairKernel {σ : ℝ} (hσ : 0 < σ) (y : ℝ) :
    deriv (fun τ : ℝ => thetaCuspWignerPairKernel τ y) σ =
      thetaCuspWignerPairLogKernel σ y -
        Real.log (2 * Real.pi) * thetaCuspWignerPairKernel σ y :=
  (hasDerivAt_thetaCuspWignerPairKernel hσ y).deriv

/-- **The archimedean orientation current is a difference of order derivatives.**  For the
`(1,1)` pair the Dirichlet weight is trivial, so the Hedenmalm gate reduces to comparing the
order derivative of the universal kernel at `σ = a + 1/2` and at `1 − σ = 1/2 − a`. -/
theorem thetaCuspPairOrientationCurrent_one_one {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (t : ℝ) :
    thetaCuspPairOrientationCurrent a 1 1 t =
      (1 / 2) * deriv (fun τ : ℝ => thetaCuspWignerPairKernel τ (2 * t)) (a + 1 / 2) -
        (1 / 2) * deriv (fun τ : ℝ => thetaCuspWignerPairKernel τ (2 * t)) (1 / 2 - a) := by
  have hp : (0 : ℝ) < a + 1 / 2 := by linarith
  have hq : (0 : ℝ) < 1 / 2 - a := by linarith
  rw [thetaCuspPairOrientationCurrent_eq_kernels ha0 ha Nat.one_pos Nat.one_pos t,
    deriv_thetaCuspWignerPairKernel hp, deriv_thetaCuspWignerPairKernel hq]
  norm_num

end

end RHTower

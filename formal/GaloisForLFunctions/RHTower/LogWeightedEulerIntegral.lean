import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianDigammaGauss
import GaloisForLFunctions.HTGeometry.BarnesMellinRepresentation

/-!
# The log-weighted Euler integral

The Mellin derivative of the Gamma integral is the log-weighted Euler integral, and a positive
rate rescales it by `C^{-σ}` while subtracting `Γ(σ) log C`:

```text
∫₀^∞ s^(σ-1) (log s) e^(-C s) ds = C^(-σ) (Γ'(σ) - Γ(σ) log C) .
```

The `log C` term is the only place where the rate enters outside a power, and it is what turns a
Dirichlet weight into its logarithmic derivative after summation.
-/

open Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

theorem integrableOn_rpow_mul_log_mul_exp_neg_Ioi {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ => t ^ (σ - 1) * Real.log t * Real.exp (-t)) (Ioi 0) := by
  have hC := Complex.integrableOn_gammaIntegral_log_kernel (s := (σ : ℂ))
    (by simpa using hσ)
  have hcongr : IntegrableOn
      (fun t : ℝ => ((t ^ (σ - 1) * Real.log t * Real.exp (-t) : ℝ) : ℂ)) (Ioi 0) := by
    refine hC.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht0 : (0 : ℝ) < t := ht
    have hcast : (t : ℂ) ^ ((σ : ℂ) - 1) = ((t ^ (σ - 1) : ℝ) : ℂ) := by
      rw [show ((σ : ℂ) - 1) = (((σ - 1 : ℝ)) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow ht0.le]
    show (t : ℂ) ^ ((σ : ℂ) - 1) * ((Real.log t : ℂ) * (Real.exp (-t) : ℂ)) =
      ((t ^ (σ - 1) * Real.log t * Real.exp (-t) : ℝ) : ℂ)
    rw [hcast]
    push_cast
    ring
  exact hcongr.re

/-- **The log-weighted Euler integral is the derivative of `Γ`.** -/
theorem integral_rpow_mul_log_mul_exp_neg_Ioi {σ : ℝ} (hσ : 0 < σ) :
    (∫ t in Ioi (0 : ℝ), t ^ (σ - 1) * Real.log t * Real.exp (-t)) = deriv Real.Gamma σ := by
  have hre : (0 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  have hd := Complex.hasDerivAt_GammaIntegral hre
  have hcong : (∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ ((σ : ℂ) - 1) * ((Real.log t : ℂ) * (Real.exp (-t) : ℂ))) =
      (((∫ t in Ioi (0 : ℝ), t ^ (σ - 1) * Real.log t * Real.exp (-t) : ℝ)) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    have hcast : (t : ℂ) ^ ((σ : ℂ) - 1) = ((t ^ (σ - 1) : ℝ) : ℂ) := by
      rw [show ((σ : ℂ) - 1) = (((σ - 1 : ℝ)) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow ht0.le]
    rw [hcast]
    push_cast
    ring
  rw [hcong] at hd
  have hGamma : HasDerivAt Complex.Gamma
      (((∫ t in Ioi (0 : ℝ), t ^ (σ - 1) * Real.log t * Real.exp (-t) : ℝ)) : ℂ) (σ : ℂ) := by
    refine hd.congr_of_eventuallyEq ?_
    have hopen : IsOpen {s : ℂ | 0 < s.re} :=
      Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
    filter_upwards [hopen.mem_nhds hre] with s hs
    exact Complex.Gamma_eq_integral hs
  have hreal : HasDerivAt (fun x : ℝ => (Complex.Gamma (x : ℂ)).re)
      ((((∫ t in Ioi (0 : ℝ), t ^ (σ - 1) * Real.log t * Real.exp (-t) : ℝ)) : ℂ)).re σ := by
    simpa using hGamma.real_of_complex
  have hfun : (fun x : ℝ => (Complex.Gamma (x : ℂ)).re) = Real.Gamma := by
    funext x
    rw [Complex.Gamma_ofReal, Complex.ofReal_re]
  rw [hfun, Complex.ofReal_re] at hreal
  exact hreal.deriv.symm

/-- **Rate scaling of the log-weighted Euler integral.** -/
theorem integral_rpow_mul_log_mul_exp_neg_mul_Ioi {σ C : ℝ} (hσ : 0 < σ) (hC : 0 < C) :
    (∫ s in Ioi (0 : ℝ), s ^ (σ - 1) * Real.log s * Real.exp (-(C * s))) =
      (1 / C) ^ σ * (deriv Real.Gamma σ - Real.Gamma σ * Real.log C) := by
  set g : ℝ → ℝ := fun x => x ^ (σ - 1) * Real.log x * Real.exp (-x) with hg
  have hbase : IntegrableOn g (Ioi 0) := integrableOn_rpow_mul_log_mul_exp_neg_Ioi hσ
  have hscaled : IntegrableOn (fun s : ℝ => g (C * s)) (Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff g 0 hC).mpr (by simpa using hbase)
    simpa using h
  have hpow : IntegrableOn (fun s : ℝ => s ^ (σ - 1) * Real.exp (-(C * s))) (Ioi 0) :=
    GaloisForLFunctions.HTGeometry.integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith) hC
  have hCpow : C ^ (1 - σ) * C ^ (σ - 1) = 1 := by
    rw [← Real.rpow_add hC, show 1 - σ + (σ - 1) = (0 : ℝ) by ring, Real.rpow_zero]
  have hpt : ∀ s ∈ Ioi (0 : ℝ), s ^ (σ - 1) * Real.log s * Real.exp (-(C * s)) =
      C ^ (1 - σ) * g (C * s) -
        Real.log C * (s ^ (σ - 1) * Real.exp (-(C * s))) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    show s ^ (σ - 1) * Real.log s * Real.exp (-(C * s)) =
      C ^ (1 - σ) * ((C * s) ^ (σ - 1) * Real.log (C * s) * Real.exp (-(C * s))) -
        Real.log C * (s ^ (σ - 1) * Real.exp (-(C * s)))
    rw [Real.mul_rpow hC.le hs0.le, Real.log_mul hC.ne' hs0.ne']
    linear_combination
      (-(s ^ (σ - 1) * (Real.log C + Real.log s) * Real.exp (-(C * s)))) * hCpow
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_sub (hscaled.const_mul _) (hpow.const_mul _), integral_const_mul, integral_const_mul,
    integral_comp_mul_left_Ioi g 0 hC, mul_zero,
    Real.integral_rpow_mul_exp_neg_mul_Ioi hσ hC,
    show (∫ x in Ioi (0 : ℝ), g x) = deriv Real.Gamma σ from
      integral_rpow_mul_log_mul_exp_neg_Ioi hσ]
  have hinv : C ^ (1 - σ) * C⁻¹ = (1 / C) ^ σ := by
    rw [one_div, Real.inv_rpow hC.le, ← Real.rpow_neg hC.le,
      show C⁻¹ = C ^ (-1 : ℝ) by rw [Real.rpow_neg_one], ← Real.rpow_add hC]
    congr 1
    ring
  rw [smul_eq_mul, ← mul_assoc, hinv]
  ring

end

end RHTower

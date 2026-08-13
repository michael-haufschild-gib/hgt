import GaloisForLFunctions.RHTower.DeningerFloquetMeasureEnergy
import GaloisForLFunctions.RHTower.DeningerSourceModulation
import GaloisForLFunctions.RHTower.XiShiftedHardEdgePolynomialGaussianExponentialSchwartz

/-!
# Gaussian concentration at a frequency node

For every real frequency `ξ₀` and every width `σ > 0` the source contains the cochain whose
half-density trivialization is `√σ e^{2πiξ₀t}e^{-πσt²}`.  Its Mellin sample is the Gaussian

`𝓕(e^{t/2}h)(ξ) = e^{-π(ξ-ξ₀)²/σ}`,

which equals `1` at `ξ₀` and concentrates there as `σ → 0`.  This is the analytic input that makes
the Mellin sampling map have dense range in `L²(μ_Fl)`: the atoms of the arithmetic lattice measure
are separately approximable.

* `deningerGaussSource` : the Gaussian `e^{-πσt²}` as a source cochain.
* `deningerFloquetAtom` : **the concentrating cochain at `(ξ₀, σ)`.**
* `deningerFloquetSample_atom` : **its Mellin sample is `e^{-π(ξ-ξ₀)²/σ}`.**
-/

namespace RHTower

open SchwartzMap MeasureTheory Complex
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped FourierTransform ContDiff

noncomputable section

/-- Pulling a constant out of the Fourier transform. -/
theorem deningerFourier_const_mul (c : ℂ) (g : ℝ → ℂ) (w : ℝ) :
    𝓕 (fun x : ℝ => c * g x) w = c * 𝓕 g w := by
  rw [Real.fourier_eq', Real.fourier_eq', ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul]
  ring

/-! ## The Gaussian source cochain -/

/-- The Gaussian `e^{-πσt²}` as an element of the exponentially decreasing source. -/
def deningerGaussSource (σ : ℝ) (hσ : 0 < σ) : DeningerExpSchwartz :=
  ⟨schwartzDilate (polyGaussSchwartz 1) (Real.sqrt_pos.2 hσ).ne',
    schwartzDilate_mem_deningerExpSchwartz (polyGaussSchwartz_mem_deningerExpSchwartz 1)
      (Real.sqrt_pos.2 hσ).ne'⟩

theorem deningerGaussSource_apply (σ : ℝ) (hσ : 0 < σ) (t : ℝ) :
    ((deningerGaussSource σ hσ : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
      = ((Real.exp (-(Real.pi * σ * t ^ 2)) : ℝ) : ℂ) := by
  show schwartzDilate (polyGaussSchwartz 1) (Real.sqrt_pos.2 hσ).ne' t = _
  rw [schwartzDilate_apply, polyGaussSchwartz_apply, gaussReal]
  have hsq : (Real.sqrt σ * t) ^ 2 = σ * t ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hσ.le]
  rw [hsq]
  simp only [Polynomial.eval_one, one_mul]
  congr 2
  ring

/-! ## The concentrating atom -/

/-- **The concentrating cochain at frequency `ξ₀` and width `σ`.** -/
def deningerFloquetAtom (ξ₀ σ : ℝ) (hσ : 0 < σ) : DeningerExpSchwartz :=
  ((Real.sqrt σ : ℝ) : ℂ) •
    deningerExpMul (-(1 / 2 : ℝ)) (deningerModulate ξ₀ (deningerGaussSource σ hσ))

/-- The half-density trivialization of the atom is a modulated Gaussian. -/
theorem deningerHalfDensityLift_atom (ξ₀ σ : ℝ) (hσ : 0 < σ) :
    ((((deningerHalfDensityLift (deningerFloquetAtom ξ₀ σ hσ)) : DeningerExpSchwartz) :
        𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = fun x : ℝ => ((Real.sqrt σ : ℝ) : ℂ) *
          Complex.exp (-(Real.pi : ℂ) * (σ : ℂ) * (x : ℂ) ^ 2
            + 2 * (Real.pi : ℂ) * (Complex.I * (ξ₀ : ℂ)) * (x : ℂ)) := by
  funext x
  rw [deningerHalfDensityLift_apply]
  show ((Real.exp (x / 2) : ℝ) : ℂ) * (((Real.sqrt σ : ℝ) : ℂ) *
      ((deningerExpMul (-(1 / 2 : ℝ))
        (deningerModulate ξ₀ (deningerGaussSource σ hσ)) : DeningerExpSchwartz) :
          𝓢(ℝ, ℂ)) x) = _
  rw [deningerExpMul_apply, deningerModulate_apply, deningerGaussSource_apply]
  have hexp : ((Real.exp (x / 2) : ℝ) : ℂ) * ((Real.exp (-(1 / 2 : ℝ) * x) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add,
      show x / 2 + -(1 / 2 : ℝ) * x = 0 by ring, Real.exp_zero, Complex.ofReal_one]
  have hg : ((Real.exp (-(Real.pi * σ * x ^ 2)) : ℝ) : ℂ)
      = Complex.exp (-(Real.pi : ℂ) * (σ : ℂ) * (x : ℂ) ^ 2) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hg, Complex.exp_add]
  have hmod : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (ξ₀ : ℂ) * (x : ℂ))
      = Complex.exp (2 * (Real.pi : ℂ) * (Complex.I * (ξ₀ : ℂ)) * (x : ℂ)) := by
    congr 1
    ring
  rw [hmod]
  linear_combination (((Real.sqrt σ : ℝ) : ℂ)
    * Complex.exp (2 * (Real.pi : ℂ) * (Complex.I * (ξ₀ : ℂ)) * (x : ℂ))
    * Complex.exp (-(Real.pi : ℂ) * (σ : ℂ) * (x : ℂ) ^ 2)) * hexp

/-- **The Mellin sample of the atom is the Gaussian `e^{-π(ξ-ξ₀)²/σ}`.** -/
theorem deningerFloquetSample_atom (ξ₀ σ : ℝ) (hσ : 0 < σ) (ξ : ℝ) :
    deningerFloquetSample (deningerFloquetAtom ξ₀ σ hσ) ξ
      = ((Real.exp (-(Real.pi * (ξ - ξ₀) ^ 2 / σ)) : ℝ) : ℂ) := by
  have hb : 0 < ((σ : ℂ)).re := by simpa using hσ
  rw [deningerFloquetSample, deningerHalfDensityLift_atom, deningerFourier_const_mul,
    congrFun (fourier_gaussian_pi' (b := (σ : ℂ)) hb (Complex.I * (ξ₀ : ℂ))) ξ]
  have hsqrt : ((σ : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt σ : ℝ) : ℂ) := by
    have h1 : ((1 : ℂ) / 2) = (((1 / 2 : ℝ)) : ℂ) := by norm_num
    rw [h1, ← Complex.ofReal_cpow hσ.le, ← Real.sqrt_eq_rpow]
  have hsq : ((ξ : ℂ) + Complex.I * (Complex.I * (ξ₀ : ℂ))) ^ 2 = (((ξ - ξ₀ : ℝ)) : ℂ) ^ 2 := by
    have hI : Complex.I * (Complex.I * (ξ₀ : ℂ)) = -(ξ₀ : ℂ) := by
      rw [← mul_assoc, Complex.I_mul_I]
      ring
    rw [hI]
    push_cast
    ring
  have harg : -(Real.pi : ℂ) / (σ : ℂ) * (((ξ - ξ₀ : ℝ)) : ℂ) ^ 2
      = ((-(Real.pi * (ξ - ξ₀) ^ 2 / σ) : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [hsqrt, hsq, harg, ← Complex.ofReal_exp]
  have hsqrtne : ((Real.sqrt σ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hσ).ne'
  field_simp

end

end RHTower

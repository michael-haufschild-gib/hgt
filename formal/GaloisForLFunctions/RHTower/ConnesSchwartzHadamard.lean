import GaloisForLFunctions.RHTower.ConnesSchwartzAntideriv
import GaloisForLFunctions.RHTower.ConnesTraceMainTerm

/-!
# Hadamard division on the Schwartz space

A Schwartz function on `ℝ` vanishing at the origin is `x` times a Schwartz function.  This is the
structural step of the last §V identification of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

No parametric-integral smoothness theorem is needed: on the Fourier side the statement becomes
"a Schwartz function of zero integral is the derivative of a Schwartz function", which is
`connesAntideriv`, and the dictionary `𝓕(x·ψ) = (i/2π)(𝓕ψ)'` (mathlib's `Real.deriv_fourier`)
plus Fourier inversion transport it back.
-/

open MeasureTheory Set Filter Topology FourierTransform
open scoped FourierTransform SchwartzMap

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The constant `-2πi` of the Fourier dictionary. -/
def connesHadamardConst : ℂ := -(2 * (Real.pi : ℂ) * Complex.I)

theorem connesHadamardConst_ne_zero : connesHadamardConst ≠ 0 := by
  intro h
  rw [connesHadamardConst, neg_eq_zero] at h
  rcases mul_eq_zero.mp h with h1 | h2
  · rcases mul_eq_zero.mp h1 with h3 | h4
    · norm_num at h3
    · exact Real.pi_ne_zero (by exact_mod_cast h4)
  · exact Complex.I_ne_zero h2

theorem connes_fourierCLM_coe (g : 𝓢(ℝ, ℂ)) :
    ((SchwartzMap.fourierTransformCLM ℂ g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = 𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
  simp only [SchwartzMap.fourierTransformCLM_apply]
  exact SchwartzMap.fourier_coe g

/-- Fourier inversion turns the vanishing of `φ` at the origin into the vanishing of the total
mass of `𝓕φ`. -/
theorem connes_fourier_total_mass_zero (φ : 𝓢(ℝ, ℂ)) (h0 : (φ : ℝ → ℂ) 0 = 0) :
    (∫ t : ℝ, ((SchwartzMap.fourierTransformCLM ℂ φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t) = 0 := by
  rw [connes_fourierCLM_coe, connes_integral_fourier_eq_zero_value φ, h0]

/-- The Schwartz primitive of `𝓕φ`. -/
def connesHadamardPrimitive (φ : 𝓢(ℝ, ℂ)) (h0 : (φ : ℝ → ℂ) 0 = 0) : 𝓢(ℝ, ℂ) :=
  connesAntideriv (SchwartzMap.fourierTransformCLM ℂ φ) (connes_fourier_total_mass_zero φ h0)

theorem connes_deriv_hadamardPrimitive (φ : 𝓢(ℝ, ℂ)) (h0 : (φ : ℝ → ℂ) 0 = 0) :
    deriv ((connesHadamardPrimitive φ h0 : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = 𝓕 ((φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
  rw [connesHadamardPrimitive, connes_deriv_connesAntideriv, connes_fourierCLM_coe]

/-- The Hadamard quotient `φ(x)/x`, as a Schwartz map. -/
def connesHadamardQuotient (φ : 𝓢(ℝ, ℂ)) (h0 : (φ : ℝ → ℂ) 0 = 0) : 𝓢(ℝ, ℂ) :=
  𝓕⁻ (connesHadamardConst • connesHadamardPrimitive φ h0)

theorem connes_fourier_hadamardQuotient (φ : 𝓢(ℝ, ℂ)) (h0 : (φ : ℝ → ℂ) 0 = 0) :
    𝓕 ((connesHadamardQuotient φ h0 : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = fun x : ℝ => connesHadamardConst * (connesHadamardPrimitive φ h0 : ℝ → ℂ) x := by
  have h : (𝓕 (connesHadamardQuotient φ h0) : 𝓢(ℝ, ℂ))
      = connesHadamardConst • connesHadamardPrimitive φ h0 := by
    rw [connesHadamardQuotient, fourier_fourierInv_eq]
  have h2 := congrArg (fun f : 𝓢(ℝ, ℂ) => (f : ℝ → ℂ)) h
  simp only [SchwartzMap.fourier_coe] at h2
  funext x
  rw [h2]
  simp

theorem connes_integrable_id_smul (ψ : 𝓢(ℝ, ℂ)) :
    Integrable (fun x : ℝ => x • (ψ : ℝ → ℂ) x) volume := by
  refine (ψ.integrable_pow_mul volume 1).mono ?_ ?_
  · exact (continuous_id.smul ψ.continuous).aestronglyMeasurable
  · filter_upwards with y
    have h1 : ‖y • (ψ : ℝ → ℂ) y‖ = ‖y‖ ^ (1 : ℕ) * ‖(ψ : ℝ → ℂ) y‖ := by
      rw [norm_smul, pow_one]
    rw [h1]
    exact Real.le_norm_self _

/-- The Fourier transform intertwines multiplication by the scalar with the scalar. -/
theorem connes_fourier_const_smul (c : ℂ) (φ : 𝓢(ℝ, ℂ)) :
    𝓕 (((c • φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = fun y : ℝ => c * 𝓕 ((φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y := by
  have h : (𝓕 (c • φ) : 𝓢(ℝ, ℂ)) = c • (𝓕 φ : 𝓢(ℝ, ℂ)) := fourier_smul c φ
  have h2 := congrArg (fun f : 𝓢(ℝ, ℂ) => (f : ℝ → ℂ)) h
  simp only [SchwartzMap.fourier_coe] at h2
  funext y
  rw [h2]
  simp [SchwartzMap.fourier_coe]

/-- **Hadamard division on the Schwartz space.**  A Schwartz function vanishing at the origin is
`x` times a Schwartz function. -/
theorem connes_schwartz_hadamard (φ : 𝓢(ℝ, ℂ)) (h0 : (φ : ℝ → ℂ) 0 = 0) (x : ℝ) :
    (φ : ℝ → ℂ) x
      = (x : ℂ) * ((connesHadamardQuotient φ h0 : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x := by
  set ψ : 𝓢(ℝ, ℂ) := connesHadamardQuotient φ h0 with hψdef
  set Bs : 𝓢(ℝ, ℂ) := connesHadamardConst • φ with hBsdef
  have hfψ : 𝓕 ((ψ : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = fun y : ℝ => connesHadamardConst * ((connesHadamardPrimitive φ h0 : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y :=
    connes_fourier_hadamardQuotient φ h0
  have hderiv : deriv (𝓕 ((ψ : 𝓢(ℝ, ℂ)) : ℝ → ℂ))
      = fun y : ℝ => connesHadamardConst * 𝓕 ((φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y := by
    rw [hfψ]
    funext y
    rw [deriv_const_mul _
      ((connesHadamardPrimitive φ h0).differentiable.differentiableAt),
      connes_deriv_hadamardPrimitive]
  have hdf := Real.deriv_fourier (f := ((ψ : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) ψ.integrable
    (connes_integrable_id_smul ψ)
  rw [hderiv] at hdf
  -- `hdf : (fun y => c * 𝓕 φ y) = 𝓕 (fun y => (-2πI y) • ψ y)`
  have hBcoe : ((Bs : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = fun y : ℝ => connesHadamardConst * (φ : ℝ → ℂ) y := by
    funext y
    simp [hBsdef]
  have hFB : 𝓕 ((Bs : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = fun y : ℝ => connesHadamardConst * 𝓕 ((φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y :=
    connes_fourier_const_smul connesHadamardConst φ
  have hAB : 𝓕 (fun y : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) • (ψ : ℝ → ℂ) y)
      = 𝓕 ((Bs : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
    rw [hFB, ← hdf]
  have hAint : Integrable
      (fun y : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) • (ψ : ℝ → ℂ) y) volume := by
    have h := (connes_integrable_id_smul ψ).const_mul (-2 * (Real.pi : ℂ) * Complex.I)
    refine h.congr (Filter.Eventually.of_forall fun y => ?_)
    simp [smul_eq_mul]
    ring
  have hAcont : Continuous
      (fun y : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) • (ψ : ℝ → ℂ) y) := by
    exact (Continuous.mul continuous_const Complex.continuous_ofReal).smul ψ.continuous
  have hFAint : Integrable
      (𝓕 (fun y : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) • (ψ : ℝ → ℂ) y)) volume := by
    rw [hAB]
    have h : Integrable ((SchwartzMap.fourierTransformCLM ℂ Bs : 𝓢(ℝ, ℂ)) : ℝ → ℂ) :=
      (SchwartzMap.fourierTransformCLM ℂ Bs).integrable
    rwa [connes_fourierCLM_coe] at h
  have hFBint : Integrable (𝓕 ((Bs : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) volume := by
    have h : Integrable ((SchwartzMap.fourierTransformCLM ℂ Bs : 𝓢(ℝ, ℂ)) : ℝ → ℂ) :=
      (SchwartzMap.fourierTransformCLM ℂ Bs).integrable
    rwa [connes_fourierCLM_coe] at h
  have hfun : (fun y : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) • (ψ : ℝ → ℂ) y)
      = ((Bs : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
    rw [← hAcont.fourierInv_fourier_eq hAint hFAint, hAB,
      Bs.continuous.fourierInv_fourier_eq Bs.integrable hFBint]
  have hpt := congrFun hfun x
  rw [hBcoe] at hpt
  have hpt2 : (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) • ((ψ : ℝ → ℂ) x)
      = connesHadamardConst * (φ : ℝ → ℂ) x := hpt
  have hc : connesHadamardConst ≠ 0 := connesHadamardConst_ne_zero
  have hpt' : connesHadamardConst * ((x : ℂ) * (ψ : ℝ → ℂ) x)
      = connesHadamardConst * (φ : ℝ → ℂ) x := by
    rw [← hpt2]
    simp only [connesHadamardConst, smul_eq_mul]
    ring
  have := mul_left_cancel₀ hc hpt'
  exact this.symm

end

end GaloisForLFunctions.RHTower

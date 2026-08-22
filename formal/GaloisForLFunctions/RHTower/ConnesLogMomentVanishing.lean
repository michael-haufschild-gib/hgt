import GaloisForLFunctions.RHTower.ConnesSchwartzHadamard
import GaloisForLFunctions.RHTower.ConnesSgnPrincipalValue
import GaloisForLFunctions.RHTower.ConnesLogFullLine
import GaloisForLFunctions.RHTower.ConnesArchPrincipalValue

/-!
# The log moment of a Schwartz function vanishing at the origin

Steps 1 and 2 of the §V route of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068,

combined through Hadamard division.  For a Schwartz `φ` with `φ(0) = 0`,

  `−∫_ℝ 𝓕φ(u) log|u| du = ∫_ℝ φ(x) d^*x`,

with Connes' multiplicative Haar density `d^*x = dx/(2|x|)`.  Both sides are absolutely convergent
here, so no regularization enters; the `δ`-coefficient of the general formula is invisible on this
subspace, which is exactly why it has to be fixed separately by the Gaussian.
-/

open MeasureTheory Set Filter Topology FourierTransform
open scoped FourierTransform SchwartzMap

namespace GaloisForLFunctions.RHTower

noncomputable section

theorem connes_fourier_smul_fun (c : ℂ) (φ : 𝓢(ℝ, ℂ)) :
    𝓕 (fun x : ℝ => c * (φ : ℝ → ℂ) x)
      = fun y : ℝ => c * 𝓕 ((φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y := by
  have h := connes_fourier_const_smul c φ
  have hcoe : (((c • φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = fun x : ℝ => c * (φ : ℝ → ℂ) x := by
    funext x
    simp
  rwa [hcoe] at h

/-- The derivative of the Fourier transform of the Hadamard quotient. -/
theorem connes_deriv_fourier_hadamardQuotient (φ : 𝓢(ℝ, ℂ)) (h0 : (φ : ℝ → ℂ) 0 = 0) :
    deriv ((SchwartzMap.fourierTransformCLM ℂ (connesHadamardQuotient φ h0) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = fun u : ℝ => connesHadamardConst * 𝓕 ((φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u := by
  set ψ : 𝓢(ℝ, ℂ) := connesHadamardQuotient φ h0 with hψ
  rw [connes_fourierCLM_coe]
  rw [Real.deriv_fourier (f := ((ψ : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) ψ.integrable
    (connes_integrable_id_smul ψ)]
  have hAeq : (fun x : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) • (ψ : ℝ → ℂ) x)
      = fun x : ℝ => connesHadamardConst * (φ : ℝ → ℂ) x := by
    funext x
    rw [connes_schwartz_hadamard φ h0 x, ← hψ]
    simp only [connesHadamardConst, smul_eq_mul]
    ring
  rw [hAeq]
  exact connes_fourier_smul_fun connesHadamardConst φ

/-- The pointwise identity behind the passage from the sign pairing to the multiplicative Haar
integral. -/
theorem connes_sign_haar_pointwise (φ : 𝓢(ℝ, ℂ)) (h0 : (φ : ℝ → ℂ) 0 = 0) (x : ℝ) :
    (φ : ℝ → ℂ) x * ((connesRealMultHaarDensity x : ℝ) : ℂ)
      = (Real.sign x : ℂ) * ((connesHadamardQuotient φ h0 : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x / 2 := by
  set ψ : 𝓢(ℝ, ℂ) := connesHadamardQuotient φ h0 with hψ
  rw [connes_schwartz_hadamard φ h0 x, ← hψ, connesRealMultHaarDensity]
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hx0 : (x : ℂ) ≠ 0 := by
      simpa using ne_of_lt hx
    rw [Real.sign_of_neg hx, abs_of_neg hx]
    push_cast
    field_simp
  · subst hx
    simp
  · have hx0 : (x : ℂ) ≠ 0 := by
      simpa using ne_of_gt hx
    rw [Real.sign_of_pos hx, abs_of_pos hx]
    push_cast
    field_simp

/-- **Steps 1 + 2 of the §V route, combined.**  For a Schwartz function vanishing at the origin the
Fourier log moment is the multiplicative Haar integral. -/
theorem connes_logMoment_of_zero (φ : 𝓢(ℝ, ℂ)) (h0 : (φ : ℝ → ℂ) 0 = 0) :
    (- ∫ u : ℝ, 𝓕 ((φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ))
      = ∫ x : ℝ, (φ : ℝ → ℂ) x * ((connesRealMultHaarDensity x : ℝ) : ℂ) := by
  set ψ : 𝓢(ℝ, ℂ) := connesHadamardQuotient φ h0 with hψ
  set Fψ : 𝓢(ℝ, ℂ) := SchwartzMap.fourierTransformCLM ℂ ψ with hFψ
  have hπ : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  -- step 2 applied to the Fourier transform of the Hadamard quotient
  have ha' : connesHadamardConst
        * (∫ u : ℝ, 𝓕 ((φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ))
      = - connesPVinv ((Fψ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
    rw [← connes_log_fullline Fψ, hFψ, connes_deriv_fourier_hadamardQuotient φ h0,
      ← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    ring
  -- step 1 applied to the Hadamard quotient
  have hs' : (∫ x : ℝ, (Real.sign x : ℂ) * (ψ : ℝ → ℂ) x)
      = (Complex.I / (Real.pi : ℂ)) * connesPVinv ((Fψ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
    rw [hFψ, connes_fourierCLM_coe]
    exact connes_sgn_pv_pairing ψ
  -- the pointwise comparison of the two right-hand sides
  have hRS : (∫ x : ℝ, (φ : ℝ → ℂ) x * ((connesRealMultHaarDensity x : ℝ) : ℂ))
      = (∫ x : ℝ, (Real.sign x : ℂ) * (ψ : ℝ → ℂ) x) / 2 := by
    rw [← MeasureTheory.integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (φ : ℝ → ℂ) x * ((connesRealMultHaarDensity x : ℝ) : ℂ)
        = (Real.sign x : ℂ) * (ψ : ℝ → ℂ) x / 2
    rw [hψ]
    exact connes_sign_haar_pointwise φ h0 x
  -- the algebra
  have hPX : connesPVinv ((Fψ : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = -(connesHadamardConst
          * (∫ u : ℝ, 𝓕 ((φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ))) := by
    rw [ha']
    ring
  have hSpi : (Real.pi : ℂ) * (∫ x : ℝ, (Real.sign x : ℂ) * (ψ : ℝ → ℂ) x)
      = -2 * (Real.pi : ℂ)
        * (∫ u : ℝ, 𝓕 ((φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ)) := by
    have h1 : (Real.pi : ℂ) * (∫ x : ℝ, (Real.sign x : ℂ) * (ψ : ℝ → ℂ) x)
        = Complex.I * connesPVinv ((Fψ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
      rw [hs']
      field_simp
    rw [h1, hPX, connesHadamardConst]
    linear_combination (2 * (Real.pi : ℂ)
      * (∫ u : ℝ, 𝓕 ((φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ)))
      * Complex.I_sq
  have hSX : (∫ x : ℝ, (Real.sign x : ℂ) * (ψ : ℝ → ℂ) x)
      = -2 * (∫ u : ℝ, 𝓕 ((φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ)) := by
    refine mul_left_cancel₀ hπ ?_
    rw [hSpi]
    ring
  rw [hRS, hSX]
  ring

end

end GaloisForLFunctions.RHTower

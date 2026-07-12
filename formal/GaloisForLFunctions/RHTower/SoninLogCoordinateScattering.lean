import GaloisForLFunctions.RHTower.EvenL2LogUnitary
import GaloisForLFunctions.RHTower.ConstrainedProlateOperator
import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry

/-!
# The true Sonin Fourier constraint in logarithmic coordinates

Normalized dilations become translations under the exact even logarithmic
unitary, but the Sonin Fourier transform does not become the ordinary Fourier
transform in that coordinate.  Its conjugate is an involutive scattering
operator which reverses translations.

The distinction is forced by the orbital-length commutator.  Multiplication by
`log |x|` has scalar commutator `-log p` with normalized dilation by `p`, whereas
ordinary position has an `x`-dependent commutator and cannot produce any scalar
orbital length.  Thus a Sonin realization of the Euler logarithm must carry the
Mellin-scattering/Burnol conductor channel; the ordinary-position two-edge
Fourier-cutoff calculation is not that channel.
-/

open Complex

namespace RHTower

noncomputable section

/-- The original Fourier involution conjugated through the exact even
logarithmic-coordinate unitary. -/
def soninLogFourierScattering : SoninL2 →L[ℂ] SoninL2 :=
  logEvenUnitary.toLinearIsometry.toContinuousLinearMap ∘L
    evenFourierTransform ∘L
      logEvenUnitary.symm.toLinearIsometry.toContinuousLinearMap

@[simp] theorem soninLogFourierScattering_apply (g : SoninL2) :
    soninLogFourierScattering g =
      logEvenUnitary (evenFourierTransform (logEvenUnitary.symm g)) := rfl

/-- Original Fourier inversion sends physical dilation by `p` to dilation by
`p⁻¹`, also on the even carrier. -/
theorem evenFourierTransform_evenDilation
    (p : ℝ) (hp : 0 < p) (f : evenSubspace) :
    evenFourierTransform (evenDilationUnitary p hp f) =
      evenDilationUnitary p⁻¹ (inv_pos.mpr hp) (evenFourierTransform f) := by
  apply Subtype.ext
  exact fourierUnitary_dilation p hp f

/-- The logarithmic-coordinate Sonin Fourier scattering is an involution. -/
@[simp] theorem soninLogFourierScattering_involutive (g : SoninL2) :
    soninLogFourierScattering (soninLogFourierScattering g) = g := by
  change logEvenUnitary
      (evenFourierTransform
        (logEvenUnitary.symm
          (logEvenUnitary
            (evenFourierTransform (logEvenUnitary.symm g))))) = g
  rw [logEvenUnitary.symm_apply_apply, evenFourierTransform_involutive,
    logEvenUnitary.apply_symm_apply]

/-- The native logarithmic Sonin scattering reverses additive translations.
This is the exact conjugate of `Fourier · dilation(p) = dilation(p⁻¹) · Fourier`. -/
theorem soninLogFourierScattering_additiveTranslation
    (p : ℝ) (hp : 0 < p) (g : SoninL2) :
    soninLogFourierScattering
        (MellinL2.additiveTranslationUnitary (Real.log p) g) =
      MellinL2.additiveTranslationUnitary (-Real.log p)
        (soninLogFourierScattering g) := by
  let f : evenSubspace := logEvenUnitary.symm g
  have hforward := logEvenUnitary_evenDilation p hp f
  have hfg : logEvenUnitary f = g := logEvenUnitary.apply_symm_apply g
  rw [hfg] at hforward
  rw [← hforward]
  simp only [soninLogFourierScattering_apply,
    logEvenUnitary.symm_apply_apply]
  rw [evenFourierTransform_evenDilation]
  rw [logEvenUnitary_evenDilation]
  rw [Real.log_inv]

/-- Pointwise logarithmic-position multiplier on a common function core. -/
def logPositionFunction (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Real.log |x| : ℂ) * f x

/-- Pointwise normalized physical dilation. -/
def normalizedDilationFunction (p : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Real.sqrt p : ℂ) * f (p * x)

/-- Exact orbital-length commutator.  Away from the null point `x=0`,
`[log|x|, U_p] = -log(p) U_p`. -/
theorem logPosition_normalizedDilation_commutator
    (p : ℝ) (hp : 0 < p) (f : ℝ → ℂ) {x : ℝ} (hx : x ≠ 0) :
    logPositionFunction (normalizedDilationFunction p f) x -
        normalizedDilationFunction p (logPositionFunction f) x =
      -(Real.log p : ℂ) * normalizedDilationFunction p f x := by
  have habsx : 0 < |x| := abs_pos.mpr hx
  have habs : |p * x| = p * |x| := by rw [abs_mul, abs_of_pos hp]
  rw [logPositionFunction, normalizedDilationFunction,
    normalizedDilationFunction, logPositionFunction, habs,
    Real.log_mul hp.ne' habsx.ne']
  push_cast
  ring

/-- Ordinary position, the multiplier used by the finite-edge Fourier
commutator, has an `x`-dependent dilation commutator. -/
def ordinaryPositionFunction (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) * f x

theorem ordinaryPosition_normalizedDilation_commutator
    (p : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    ordinaryPositionFunction (normalizedDilationFunction p f) x -
        normalizedDilationFunction p (ordinaryPositionFunction f) x =
      ((1 - p) * x : ℝ) * normalizedDilationFunction p f x := by
  simp [ordinaryPositionFunction, normalizedDilationFunction]
  ring

/-- For a nontrivial dilation, ordinary position cannot have any scalar
commutator even on the constant pointwise test.  It therefore cannot supply the
Euler orbital length `log p`. -/
theorem ordinaryPosition_commutator_not_scalar
    (p : ℝ) (hp : 0 < p) (hp1 : p ≠ 1) :
    ¬ ∃ c : ℂ, ∀ x : ℝ,
      ordinaryPositionFunction (normalizedDilationFunction p (fun _ => 1)) x -
          normalizedDilationFunction p (ordinaryPositionFunction (fun _ => 1)) x =
        c * normalizedDilationFunction p (fun _ => 1) x := by
  rintro ⟨c, h⟩
  have h0 := h 0
  have hsqrt : (Real.sqrt p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr hp)
  have hc : c = 0 := by
    simpa [ordinaryPositionFunction, normalizedDilationFunction, hsqrt] using
      (mul_eq_zero.mp (by
        simpa [ordinaryPositionFunction, normalizedDilationFunction] using h0)).resolve_right hsqrt
  have h1 := h 1
  rw [hc] at h1
  simp [ordinaryPositionFunction, normalizedDilationFunction] at h1
  norm_cast at h1
  exact hp1 (by nlinarith [Real.sqrt_pos.2 hp])

end

end RHTower

import GaloisForLFunctions.RHTower.PoleVanishingWeilTraceCertificate
import GaloisForLFunctions.HTGeometry.FourierTranslationModulation

/-!
# The trace certificate across the entry of the prime 2

For an aperture `b` with `log 2 ≤ 2b < log 3` the restricted Weil form contains exactly one prime
term, the translation by `L = log 2`.  On the pole-vanishing subspace it is a Fourier multiplier:

`Q_b(f) = ∫ (W(ξ) - √2 log 2 · cos(2π L ξ)) |𝓕 f(ξ)|² dξ`,

because `Re ⟨f(· + h), f⟩ = ∫ cos(2π h ξ) |𝓕 f(ξ)|² dξ` (translation is modulation on the Fourier
side).  A translation by the full diameter `2b` has null overlap on the aperture, so
`∫ cos(2π · 2b · ξ) |𝓕 f|² = 0` and the term `√2 log 2 · cos(2π · 2b · ξ)` may be added for free:

`Q_b(f) = ∫ (W(ξ) - √2 log 2 · (cos(2π L ξ) - cos(2π · 2b · ξ))) |𝓕 f(ξ)|² dξ`.

The difference of cosines is `2 sin(π(2b + L)ξ) sin(π(2b - L)ξ)`: it is small at frequencies below
`1/(2b - L)` and nonpositive on `[1/(2b+L), 2/(2b+L)]`.  This is the positive-definite (Krein)
extension freedom of the compressed Weil kernel: only lags in `[-2b, 2b]` are seen by the form.

The grid certificate of `PoleVanishingWeilTraceCertificate` is restated for a general symbol.
-/

open MeasureTheory Complex Set
open scoped FourierTransform InnerProduct

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-! ## Translation pairings as Fourier multipliers -/

theorem logTranslationCLM_eq_translateL2 (h : ℝ) (f : SoninL2) :
    logTranslationCLM h f = translateL2 h f := by
  apply Lp.ext
  filter_upwards [logTranslationCLM_ae h f, coeFn_translateL2 h f] with x h1 h2
  rw [h1, h2]

/-- **Translation pairing on the Fourier side.**  For a form-domain vector with aperture
realization `f`, `Re ⟨f(· + h), f⟩ = ∫ cos(2π h ξ) ‖u(ξ)‖² dξ`. -/
theorem re_inner_logTranslation_eq_integral_cos (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (h : ℝ) :
    (inner ℂ (logTranslationCLM h (ccmArchimedeanFormToAperture a u).1)
        (ccmArchimedeanFormToAperture a u).1).re =
      ∫ ξ : ℝ, Real.cos (2 * Real.pi * h * ξ) * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 := by
  set f : SoninL2 := (ccmArchimedeanFormToAperture a u).1 with hf
  have hF : fourierUnitary f = ccmArchimedeanWeightedToL2 u.1 :=
    fourierUnitary_ccmArchimedeanFourierToTime u.1
  have hmod : fourierUnitary (translateL2 h f) = modulationMul h (fourierUnitary f) :=
    fourierTransform_translateL2 h f
  rw [logTranslationCLM_eq_translateL2, ← fourierUnitary.inner_map_map, hmod, hF,
    MeasureTheory.L2.inner_def]
  have hre : (∫ ξ : ℝ, inner ℂ ((modulationMul h (ccmArchimedeanWeightedToL2 u.1) :
      SoninL2) ξ) ((ccmArchimedeanWeightedToL2 u.1 : SoninL2) ξ)).re =
      ∫ ξ : ℝ, (inner ℂ ((modulationMul h (ccmArchimedeanWeightedToL2 u.1) : SoninL2) ξ)
        ((ccmArchimedeanWeightedToL2 u.1 : SoninL2) ξ)).re := by
    rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm]
    · rfl
    · exact (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) _ _)
  rw [hre]
  apply integral_congr_ae
  filter_upwards [coeFn_modulationMul h (ccmArchimedeanWeightedToL2 u.1),
    ccmArchimedeanWeightedToL2_coeFn u.1] with ξ hm hw
  rw [hm, hw, RCLike.inner_apply]
  unfold modulationSymbol
  rw [map_mul, ← Complex.exp_conj]
  have hconj : (starRingEnd ℂ) (((2 * Real.pi * (h * ξ) : ℝ) : ℂ) * I) =
      ((-(2 * Real.pi * (h * ξ)) : ℝ) : ℂ) * I := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [hconj, mul_comm, ← mul_assoc, mul_assoc, Complex.conj_mul']
  rw [show ((‖(u.1 : ℝ → ℂ) ξ‖ : ℂ) ^ 2) = (((‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 : ℝ)) : ℂ) by push_cast; ring,
    Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

end RHTower

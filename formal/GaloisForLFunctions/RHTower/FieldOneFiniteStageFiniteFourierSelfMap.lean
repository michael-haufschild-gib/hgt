import GaloisForLFunctions.RHTower.FieldOneFiniteStageFiniteFourierPlancherel
import GaloisForLFunctions.RHTower.FieldOnePadicProductBruhatFourierSelfMap

/-!
# The finite-stage Fourier transform maps Bruhat–Schwartz functions to themselves

For a finite set `S` of primes, the Fourier transform on `∏_{p ∈ S} ℚ_p` (with the self-dual
Haar measure and the standard additive character) sends a compactly supported locally constant
function to another such function. This module packages the transform as a map of the
Bruhat–Schwartz space to itself, transported from the `p`-adic product model, and shows that it
is `ℂ`-linear.

## Main results

- `fieldOneFiniteStageFiniteBruhatFourierBruhat`: the Fourier transform as a self-map of
  `FieldOneFiniteStageFiniteBruhatSchwartz S`.
- `fieldOneFiniteStageFiniteBruhatFourierBruhat_apply`: its values are `f̂(y)`.
- `fieldOneFiniteStageFiniteBruhatFourier_integrand_integrable`: the Fourier integrand
  `x ↦ ψ(-x y) f(x)` is integrable.
- `fieldOneFiniteStageFiniteBruhatFourierLinear`: the Fourier transform as a `ℂ`-linear map.

## Hypotheses

All results are unconditional.
-/

namespace GaloisForLFunctions.RHTower
noncomputable section
open IsDedekindDomain MeasureTheory Set TopologicalSpace
open scoped BigOperators

/-- The Fourier transform on `∏_{p ∈ S} ℚ_p` as a map from compactly supported locally constant functions to
compactly supported locally constant functions. -/
def fieldOneFiniteStageFiniteBruhatFourierBruhat
    (S : Finset (HeightOneSpectrum ℤ))
    (f : FieldOneFiniteStageFiniteBruhatSchwartz S) :
    FieldOneFiniteStageFiniteBruhatSchwartz S := by
  classical
  let p : ↑S → ℕ := fun v => Rat.HeightOneSpectrum.primesEquiv v.1
  let e := fieldOneFiniteStagePadicProductAddEquiv S
  let Fp := fieldOnePadicProductBruhatFourierBruhat p
    (fieldOneFiniteStageFiniteBruhatToPadicProduct S f)
  let F' : LocallyConstant (FieldOneFiniteStageFinitePart S) ℂ :=
    LocallyConstant.comap ⟨fun y => e y, e.continuous⟩ Fp.1
  refine ⟨F', ?_⟩
  exact Fp.2.comp_homeomorph e.toHomeomorph

/-- The Bruhat-valued Fourier transform takes the values `f̂(y)` of the integral Fourier transform. -/
@[simp] theorem fieldOneFiniteStageFiniteBruhatFourierBruhat_apply
    (S : Finset (HeightOneSpectrum ℤ))
    (f : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (y : FieldOneFiniteStageFinitePart S) :
    (fieldOneFiniteStageFiniteBruhatFourierBruhat S f).1 y =
      fieldOneFiniteStageFiniteBruhatFourier S f y := by
  classical
  change fieldOnePadicProductBruhatFourier
      (fun v : ↑S => (Rat.HeightOneSpectrum.primesEquiv v.1 : ℕ))
      (fieldOneFiniteStageFiniteBruhatToPadicProduct S f)
      (fieldOneFiniteStagePadicProductAddEquiv S y) = _
  exact (fieldOneFiniteStageFiniteBruhatFourier_eq_padic S f y).symm

/-- For a Bruhat–Schwartz function `f` and any `y`, the Fourier integrand `x ↦ ψ(-x y) f(x)` is integrable
for the self-dual Haar measure. -/
theorem fieldOneFiniteStageFiniteBruhatFourier_integrand_integrable
    (S : Finset (HeightOneSpectrum ℤ))
    (f : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (y : FieldOneFiniteStageFinitePart S) :
    Integrable (fun x => fieldOneFiniteStageFiniteStandardAddChar S
        (fun v => -(x v * y v)) * f.1 x)
      (Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1) := by
  classical
  apply (f.1.continuous.integrable_of_hasCompactSupport f.2).bdd_mul (c := 1)
  · apply Continuous.aestronglyMeasurable
    apply continuous_finsetProd
    intro v _
    have harg : Continuous (fun x : FieldOneFiniteStageFinitePart S =>
        -(x v * y v)) :=
      continuous_neg.comp ((continuous_apply v).mul continuous_const)
    have hpadic :=
      (fieldOnePadicStandardAddChar_isLocallyConstant
        (Rat.HeightOneSpectrum.primesEquiv v.1)).continuous.comp
        ((fieldOneLocalPadicContinuousAddEquiv v.1).continuous.comp harg)
    exact hpadic.congr fun x => by
      symm
      exact fieldOneLocalStandardAddChar_eq_padic v.1 (-(x v * y v))
  · filter_upwards [] with x
    rw [fieldOneFiniteStageFiniteStandardAddChar, norm_prod]
    simp [fieldOneLocalStandardAddChar]

/-- The finite-stage Fourier transform as a `ℂ`-linear endomorphism of the Bruhat–Schwartz space. -/
def fieldOneFiniteStageFiniteBruhatFourierLinear
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageFiniteBruhatSchwartz S →ₗ[ℂ]
      FieldOneFiniteStageFiniteBruhatSchwartz S where
  toFun := fieldOneFiniteStageFiniteBruhatFourierBruhat S
  map_add' f g := by
    apply Subtype.ext
    apply LocallyConstant.ext
    intro y
    change (fieldOneFiniteStageFiniteBruhatFourierBruhat S (f + g)).1 y =
      (fieldOneFiniteStageFiniteBruhatFourierBruhat S f).1 y +
        (fieldOneFiniteStageFiniteBruhatFourierBruhat S g).1 y
    rw [fieldOneFiniteStageFiniteBruhatFourierBruhat_apply,
      fieldOneFiniteStageFiniteBruhatFourierBruhat_apply, fieldOneFiniteStageFiniteBruhatFourierBruhat_apply]
    change (∫ x, fieldOneFiniteStageFiniteStandardAddChar S
        (fun v => -(x v * y v)) * (f.1 x + g.1 x)
          ∂(Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1)) =
      fieldOneFiniteStageFiniteBruhatFourier S f y +
        fieldOneFiniteStageFiniteBruhatFourier S g y
    simp_rw [mul_add]
    rw [integral_add (fieldOneFiniteStageFiniteBruhatFourier_integrand_integrable S f y)
      (fieldOneFiniteStageFiniteBruhatFourier_integrand_integrable S g y)]
    rfl
  map_smul' c f := by
    apply Subtype.ext
    apply LocallyConstant.ext
    intro y
    change (fieldOneFiniteStageFiniteBruhatFourierBruhat S (c • f)).1 y =
      c * (fieldOneFiniteStageFiniteBruhatFourierBruhat S f).1 y
    rw [fieldOneFiniteStageFiniteBruhatFourierBruhat_apply, fieldOneFiniteStageFiniteBruhatFourierBruhat_apply]
    change (∫ x, fieldOneFiniteStageFiniteStandardAddChar S
        (fun v => -(x v * y v)) * (c * f.1 x)
          ∂(Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1)) =
      c * fieldOneFiniteStageFiniteBruhatFourier S f y
    simp_rw [show ∀ x : FieldOneFiniteStageFinitePart S,
      fieldOneFiniteStageFiniteStandardAddChar S (fun v => -(x v * y v)) *
          (c * f.1 x) =
        c * (fieldOneFiniteStageFiniteStandardAddChar S
          (fun v => -(x v * y v)) * f.1 x) by
      intro x
      ring]
    rw [integral_const_mul]
    rfl

end
end GaloisForLFunctions.RHTower


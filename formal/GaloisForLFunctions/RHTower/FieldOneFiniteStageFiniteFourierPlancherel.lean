import GaloisForLFunctions.RHTower.FieldOneFiniteStagePadicProductTransport
import GaloisForLFunctions.RHTower.FieldOnePadicProductBruhatFourierPlancherel

/-!
# Plancherel theorem for the finite part of the stage-`S` adeles of `ℚ`

For a finite set `S` of primes, the finite part of the stage-`S` adeles is `∏_{p ∈ S} ℚ_p`,
realized through the adic completions of `ℚ`. It carries the product of the self-dual additive
Haar measures (each giving `ℤ_p` mass `1`) and the standard additive character
`ψ(x) = ∏_{p ∈ S} ψ_p(x_p)`. This module defines the Fourier transform
`f̂(y) = ∫ ψ(-x y) f(x) dx` of a compactly supported locally constant function `f`. It identifies
this transform with the Fourier transform on the literal product of `p`-adic fields `ℚ_p`, and
deduces Plancherel: `∫ |f̂|² = ∫ |f|²`.

## Main results

- `fieldOneFiniteStageFiniteStandardAddChar`: the product character `∏_{p ∈ S} ψ_p(x_p)`.
- `fieldOneFiniteStageFiniteBruhatFourier`: the Fourier transform on `∏_{p ∈ S} ℚ_p`.
- `fieldOneFiniteStageFiniteBruhatFourier_eq_padic`: it agrees with the Fourier transform on
  the `p`-adic product model under the canonical additive equivalence.
- `fieldOneFiniteStageFiniteBruhatFourier_plancherel`: `∫ |f̂(y)|² dy = ∫ |f(x)|² dx`.

## Hypotheses

Unconditional for every finite set `S` of primes and every compactly supported locally constant
function `f`.
-/

namespace GaloisForLFunctions.RHTower
noncomputable section
open IsDedekindDomain MeasureTheory Set TopologicalSpace
open scoped BigOperators

/-- The standard additive character on `∏_{p ∈ S} ℚ_p`: the product of the local standard characters. -/
def fieldOneFiniteStageFiniteStandardAddChar
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageFinitePart S) : ℂ :=
  ∏ v : ↑S, fieldOneLocalStandardAddChar v.1 (x v)

/-- The product character agrees with the standard character of the literal `p`-adic product model. -/
theorem fieldOneFiniteStageFiniteStandardAddChar_eq_padic
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageFinitePart S) :
    fieldOneFiniteStageFiniteStandardAddChar S x =
      fieldOnePadicProductStandardAddChar
        (fun v : ↑S => Rat.HeightOneSpectrum.primesEquiv v.1)
        (fieldOneFiniteStagePadicProductAddEquiv S x) := by
  apply Finset.prod_congr rfl
  intro v _
  exact fieldOneLocalStandardAddChar_eq_padic v.1 (x v)

/-- Fourier transform `f̂(y) = ∫ ψ(-x y) f(x) dx` of a Bruhat–Schwartz function on `∏_{p ∈ S} ℚ_p`, with the
product of self-dual Haar measures. -/
def fieldOneFiniteStageFiniteBruhatFourier
    (S : Finset (HeightOneSpectrum ℤ))
    (f : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (y : FieldOneFiniteStageFinitePart S) : ℂ :=
  ∫ x, fieldOneFiniteStageFiniteStandardAddChar S (fun v => -(x v * y v)) * f.1 x
    ∂(Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1)

set_option backward.isDefEq.respectTransparency false in
/-- The stage-`S` finite Fourier transform equals the Fourier transform on the literal `p`-adic product,
transported along the canonical additive equivalence. -/
theorem fieldOneFiniteStageFiniteBruhatFourier_eq_padic
    (S : Finset (HeightOneSpectrum ℤ))
    (f : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (y : FieldOneFiniteStageFinitePart S) :
    fieldOneFiniteStageFiniteBruhatFourier S f y =
      fieldOnePadicProductBruhatFourier
        (fun v : ↑S => Rat.HeightOneSpectrum.primesEquiv v.1)
        (fieldOneFiniteStageFiniteBruhatToPadicProduct S f)
        (fieldOneFiniteStagePadicProductAddEquiv S y) := by
  classical
  let e := fieldOneFiniteStagePadicProductAddEquiv S
  let μ := Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1
  let p : ↑S → ℕ := fun v => Rat.HeightOneSpectrum.primesEquiv v.1
  let ν := fieldOnePadicProductUnitBallNormalizedHaar p
  change (∫ x, fieldOneFiniteStageFiniteStandardAddChar S
      (fun v => -(x v * y v)) * f.1 x ∂μ) =
    ∫ z, fieldOnePadicProductStandardAddChar p
      (fun v => -(z v * e y v)) *
        (fieldOneFiniteStageFiniteBruhatToPadicProduct S f).1 z ∂ν
  rw [show ν = Measure.map (fun x => e x) μ by
    exact (fieldOneFiniteStageSelfDualHaar_map_padicProduct S).symm]
  dsimp only [p] at *
  have hemb : MeasurableEmbedding
      (fun x : FieldOneFiniteStageFinitePart S =>
        (e x : FieldOnePadicProduct
          (fun v : ↑S => (Rat.HeightOneSpectrum.primesEquiv v.1 : ℕ)))) := by
    exact e.measurableEmbedding
  rw [hemb.integral_map]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [fieldOneFiniteStageFiniteStandardAddChar_eq_padic]
  have harg : e (fun v => -(x v * y v)) =
      (fun v => -(e x v * e y v)) := by
    funext v
    change fieldOneLocalPadicContinuousAddEquiv v.1 (-(x v * y v)) =
      -(fieldOneLocalPadicContinuousAddEquiv v.1 (x v) *
        fieldOneLocalPadicContinuousAddEquiv v.1 (y v))
    change Rat.HeightOneSpectrum.adicCompletion.padicEquiv v.1
        (-(x v * y v)) =
      -(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v.1 (x v) *
        Rat.HeightOneSpectrum.adicCompletion.padicEquiv v.1 (y v))
    rw [map_neg, map_mul]
  rw [harg]
  rw [fieldOneFiniteStageFiniteBruhatToPadicProduct_apply]
  rw [show (fieldOneFiniteStagePadicProductAddEquiv S).symm (e x) = x by
    exact e.symm_apply_apply x]

set_option backward.isDefEq.respectTransparency false in
/-- Plancherel on `∏_{p ∈ S} ℚ_p`: for every compactly supported locally constant `f`,
`∫ |f̂(y)|² dy = ∫ |f(x)|² dx` with respect to the self-dual Haar measure. -/
theorem fieldOneFiniteStageFiniteBruhatFourier_plancherel
    (S : Finset (HeightOneSpectrum ℤ))
    (f : FieldOneFiniteStageFiniteBruhatSchwartz S) :
    ∫ y, Complex.normSq (fieldOneFiniteStageFiniteBruhatFourier S f y)
        ∂(Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1) =
      ∫ x, Complex.normSq (f.1 x)
        ∂(Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1) := by
  classical
  let e := fieldOneFiniteStagePadicProductAddEquiv S
  let μ := Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1
  let p : ↑S → ℕ := fun v => Rat.HeightOneSpectrum.primesEquiv v.1
  let ν := fieldOnePadicProductUnitBallNormalizedHaar p
  have hpl := fieldOnePadicProductBruhatFourier_plancherel p
    (fieldOneFiniteStageFiniteBruhatToPadicProduct S f)
  change (∫ y, Complex.normSq (fieldOneFiniteStageFiniteBruhatFourier S f y) ∂μ) =
    ∫ x, Complex.normSq (f.1 x) ∂μ
  change (∫ y, Complex.normSq
      (fieldOnePadicProductBruhatFourier p
        (fieldOneFiniteStageFiniteBruhatToPadicProduct S f) y) ∂ν) =
    ∫ x, Complex.normSq
      ((fieldOneFiniteStageFiniteBruhatToPadicProduct S f).1 x) ∂ν at hpl
  rw [show ν = Measure.map (fun x => e x) μ by
    exact (fieldOneFiniteStageSelfDualHaar_map_padicProduct S).symm] at hpl
  dsimp only [p] at *
  have hemb : MeasurableEmbedding
      (fun x : FieldOneFiniteStageFinitePart S =>
        (e x : FieldOnePadicProduct
          (fun v : ↑S => (Rat.HeightOneSpectrum.primesEquiv v.1 : ℕ)))) := by
    exact e.measurableEmbedding
  rw [hemb.integral_map, hemb.integral_map] at hpl
  have hesymm : ∀ x : FieldOneFiniteStageFinitePart S,
      (fieldOneFiniteStagePadicProductAddEquiv S).symm (e x) = x := by
    intro x
    exact e.symm_apply_apply x
  simpa only [fieldOneFiniteStageFiniteBruhatFourier_eq_padic,
    fieldOneFiniteStageFiniteBruhatToPadicProduct_apply,
    hesymm] using hpl

end
end GaloisForLFunctions.RHTower


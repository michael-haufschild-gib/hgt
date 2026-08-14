import GaloisForLFunctions.RHTower.FieldOneFiniteStagePadicProductTransport
import GaloisForLFunctions.RHTower.FieldOnePadicProductBruhatFourierPlancherel

namespace GaloisForLFunctions.RHTower
noncomputable section
open IsDedekindDomain MeasureTheory Set TopologicalSpace
open scoped BigOperators

def fieldOneFiniteStageFiniteStandardAddChar
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageFinitePart S) : ℂ :=
  ∏ v : ↑S, fieldOneLocalStandardAddChar v.1 (x v)

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

def fieldOneFiniteStageFiniteBruhatFourier
    (S : Finset (HeightOneSpectrum ℤ))
    (f : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (y : FieldOneFiniteStageFinitePart S) : ℂ :=
  ∫ x, fieldOneFiniteStageFiniteStandardAddChar S (fun v => -(x v * y v)) * f.1 x
    ∂(Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1)

set_option backward.isDefEq.respectTransparency false in
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


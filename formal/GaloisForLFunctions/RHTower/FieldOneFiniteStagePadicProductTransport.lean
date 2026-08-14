import GaloisForLFunctions.RHTower.FieldOneLocalBruhatFourierSelfMap
import GaloisForLFunctions.RHTower.FieldOneFiniteStageConnesMarcolliFourierCore
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Canonical p-adic product model of a rational finite stage

Every nonarchimedean factor of `A_{ℚ,S}` is transported through the canonical
continuous equivalence to literal `ℚ_p`.  The product equivalence maps the
source finite-stage Haar measure exactly to the product of unit-ball-normalized
p-adic Haar measures and carries the literal finite Bruhat space with it.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain MeasureTheory Set TopologicalSpace

/-- Canonical continuous additive equivalence from the rational finite part
to the dependent product of literal p-adic fields. -/
def fieldOneFiniteStagePadicProductAddEquiv
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageFinitePart S ≃ₜ+
      ((v : ↑S) → ℚ_[Rat.HeightOneSpectrum.primesEquiv v.1]) :=
  { toAddEquiv := AddEquiv.piCongrRight fun v =>
      (fieldOneLocalPadicContinuousAddEquiv v.1).toAddEquiv
    continuous_toFun := continuous_pi fun v =>
      (fieldOneLocalPadicContinuousAddEquiv v.1).continuous.comp
        (continuous_apply v)
    continuous_invFun := continuous_pi fun v =>
      (fieldOneLocalPadicContinuousAddEquiv v.1).symm.continuous.comp
        (continuous_apply v) }

/-- Exact transport of the finite-stage source Haar measure to the product of
literal unit-ball-normalized p-adic Haar measures. -/
theorem fieldOneFiniteStageSelfDualHaar_map_padicProduct
    (S : Finset (HeightOneSpectrum ℤ)) :
    Measure.map (fun x => fieldOneFiniteStagePadicProductAddEquiv S x)
        (Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1) =
      Measure.pi fun v : ↑S =>
        fieldOnePadicUnitBallNormalizedHaar
          (Rat.HeightOneSpectrum.primesEquiv v.1) := by
  change Measure.map
      (fun x v => fieldOneLocalPadicContinuousAddEquiv v.1 (x v))
      (Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1) =
    Measure.pi fun v : ↑S =>
      fieldOnePadicUnitBallNormalizedHaar
        (Rat.HeightOneSpectrum.primesEquiv v.1)
  rw [Measure.pi_map_pi]
  · congr 1
    funext v
    exact fieldOneLocalSelfDualHaar_map_padic v.1
  · intro v
    exact
      (fieldOneLocalPadicContinuousAddEquiv v.1).measurable.aemeasurable

/-- Transport a literal finite-stage Bruhat function to the dependent product
of literal p-adic fields. -/
def fieldOneFiniteStageFiniteBruhatToPadicProduct
    (S : Finset (HeightOneSpectrum ℤ))
    (f : FieldOneFiniteStageFiniteBruhatSchwartz S) :
    compactlySupportedLocallyConstant
      ((v : ↑S) → ℚ_[Rat.HeightOneSpectrum.primesEquiv v.1]) := by
  let e := fieldOneFiniteStagePadicProductAddEquiv S
  let f' : LocallyConstant
      ((v : ↑S) → ℚ_[Rat.HeightOneSpectrum.primesEquiv v.1]) ℂ :=
    LocallyConstant.comap ⟨fun y => e.symm y, e.symm.continuous⟩ f.1
  refine ⟨f', ?_⟩
  exact f.2.comp_homeomorph e.symm.toHomeomorph

@[simp]
theorem fieldOneFiniteStageFiniteBruhatToPadicProduct_apply
    (S : Finset (HeightOneSpectrum ℤ))
    (f : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (y : (v : ↑S) → ℚ_[Rat.HeightOneSpectrum.primesEquiv v.1]) :
    (fieldOneFiniteStageFiniteBruhatToPadicProduct S f).1 y =
      f.1 ((fieldOneFiniteStagePadicProductAddEquiv S).symm y) :=
  rfl

end

end GaloisForLFunctions.RHTower

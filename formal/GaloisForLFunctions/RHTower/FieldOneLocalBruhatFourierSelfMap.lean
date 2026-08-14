import GaloisForLFunctions.RHTower.FieldOneLocalBruhatFourierPlancherel
import GaloisForLFunctions.RHTower.FieldOnePadicBruhatFourierSelfMap

/-!
# Local Fourier preservation on rational height-one completions

The exact p-adic Bruhat self-map transports through the canonical continuous
algebra equivalence at every rational height-one completion.  Thus the source
local Fourier integral preserves compact support and local constancy on the
literal completion, with no abstract automorphism premise.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain MeasureTheory Set TopologicalSpace

/-- The local source Fourier integral is locally constant on every rational
height-one completion. -/
theorem fieldOneLocalBruhatFourier_isLocallyConstant
    (v : HeightOneSpectrum ℤ)
    (f : compactlySupportedLocallyConstant (v.adicCompletion ℚ)) :
    IsLocallyConstant (fieldOneLocalBruhatFourier v f) := by
  let e := fieldOneLocalPadicContinuousAddEquiv v
  have h := fieldOnePadicBruhatFourier_isLocallyConstant
    (Rat.HeightOneSpectrum.primesEquiv v)
    (fieldOneLocalBruhatToPadic v f)
  have hc : IsLocallyConstant (fun y : v.adicCompletion ℚ =>
      fieldOnePadicBruhatFourier
        (Rat.HeightOneSpectrum.primesEquiv v)
        (fieldOneLocalBruhatToPadic v f) (e y)) :=
    h.comp_continuous e.continuous
  rw [show fieldOneLocalBruhatFourier v f = (fun y =>
      fieldOnePadicBruhatFourier
        (Rat.HeightOneSpectrum.primesEquiv v)
        (fieldOneLocalBruhatToPadic v f) (e y)) by
    funext y
    exact fieldOneLocalBruhatFourier_eq_padic v f y]
  exact hc

/-- The local source Fourier integral has compact support on every rational
height-one completion. -/
theorem fieldOneLocalBruhatFourier_hasCompactSupport
    (v : HeightOneSpectrum ℤ)
    (f : compactlySupportedLocallyConstant (v.adicCompletion ℚ)) :
    HasCompactSupport (fieldOneLocalBruhatFourier v f) := by
  let e := fieldOneLocalPadicContinuousAddEquiv v
  have h := fieldOnePadicBruhatFourier_hasCompactSupport
    (Rat.HeightOneSpectrum.primesEquiv v)
    (fieldOneLocalBruhatToPadic v f)
  have hc : HasCompactSupport (fun y : v.adicCompletion ℚ =>
      fieldOnePadicBruhatFourier
        (Rat.HeightOneSpectrum.primesEquiv v)
        (fieldOneLocalBruhatToPadic v f) (e y)) :=
    h.comp_homeomorph e.toHomeomorph
  rw [show fieldOneLocalBruhatFourier v f = (fun y =>
      fieldOnePadicBruhatFourier
        (Rat.HeightOneSpectrum.primesEquiv v)
        (fieldOneLocalBruhatToPadic v f) (e y)) by
    funext y
    exact fieldOneLocalBruhatFourier_eq_padic v f y]
  exact hc

/-- Literal local Fourier transform as a self-map of the rational-completion
Bruhat space. -/
def fieldOneLocalBruhatFourierBruhat
    (v : HeightOneSpectrum ℤ)
    (f : compactlySupportedLocallyConstant (v.adicCompletion ℚ)) :
    compactlySupportedLocallyConstant (v.adicCompletion ℚ) :=
  ⟨⟨fieldOneLocalBruhatFourier v f,
      fieldOneLocalBruhatFourier_isLocallyConstant v f⟩,
    fieldOneLocalBruhatFourier_hasCompactSupport v f⟩

@[simp]
theorem fieldOneLocalBruhatFourierBruhat_apply
    (v : HeightOneSpectrum ℤ)
    (f : compactlySupportedLocallyConstant (v.adicCompletion ℚ))
    (y : v.adicCompletion ℚ) :
    (fieldOneLocalBruhatFourierBruhat v f).1 y =
      fieldOneLocalBruhatFourier v f y :=
  rfl

end

end GaloisForLFunctions.RHTower

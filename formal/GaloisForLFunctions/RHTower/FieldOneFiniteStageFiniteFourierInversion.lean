import GaloisForLFunctions.RHTower.FieldOneFiniteStageFiniteFourierSelfMap
import GaloisForLFunctions.RHTower.FieldOnePadicProductBruhatFourierInversion

/-!
# Fourier inversion on the finite nonarchimedean part of a rational stage

The canonical local-completion equivalence transports product p-adic Fourier
inversion to the literal finite part of `A_{ℚ,S}`.  The resulting Bruhat
Fourier transform is bundled as a linear equivalence.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain MeasureTheory Set TopologicalSpace
open scoped BigOperators

/-- Transporting the literal finite-stage Fourier transform through the
canonical p-adic product equivalence gives the product p-adic transform. -/
theorem fieldOneFiniteStageFiniteBruhatToPadicProduct_fourier
    (S : Finset (HeightOneSpectrum ℤ))
    [DecidableEq ↑S]
    (f : FieldOneFiniteStageFiniteBruhatSchwartz S) :
    fieldOneFiniteStageFiniteBruhatToPadicProduct S
        (fieldOneFiniteStageFiniteBruhatFourierBruhat S f) =
      fieldOnePadicProductBruhatFourierBruhat
        (fun v : ↑S => (Rat.HeightOneSpectrum.primesEquiv v.1 : ℕ))
        (fieldOneFiniteStageFiniteBruhatToPadicProduct S f) := by
  classical
  apply Subtype.ext
  apply LocallyConstant.ext
  intro y
  rw [fieldOneFiniteStageFiniteBruhatToPadicProduct_apply]
  rw [fieldOneFiniteStageFiniteBruhatFourierBruhat_apply]
  rw [fieldOneFiniteStageFiniteBruhatFourier_eq_padic]
  simp

/-- Exact Fourier-square reflection on the finite nonarchimedean Bruhat
space of a rational finite stage. -/
theorem fieldOneFiniteStageFiniteBruhatFourier_fourier
    (S : Finset (HeightOneSpectrum ℤ))
    (f : FieldOneFiniteStageFiniteBruhatSchwartz S) :
    ∀ y,
      fieldOneFiniteStageFiniteBruhatFourier S
          (fieldOneFiniteStageFiniteBruhatFourierBruhat S f) y =
        f.1 (-y) := by
  classical
  intro y
  rw [fieldOneFiniteStageFiniteBruhatFourier_eq_padic]
  rw [fieldOneFiniteStageFiniteBruhatToPadicProduct_fourier]
  rw [fieldOnePadicProductBruhatFourier_fourier]
  simp [fieldOneFiniteStageFiniteBruhatToPadicProduct_apply]

/-- The literal finite nonarchimedean Bruhat Fourier transform is a linear
equivalence.  Its inverse is its third power. -/
def fieldOneFiniteStageFiniteBruhatFourierLinearEquiv
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageFiniteBruhatSchwartz S ≃ₗ[ℂ]
      FieldOneFiniteStageFiniteBruhatSchwartz S where
  toLinearMap := fieldOneFiniteStageFiniteBruhatFourierLinear S
  invFun f := fieldOneFiniteStageFiniteBruhatFourierLinear S
    (fieldOneFiniteStageFiniteBruhatFourierLinear S
      (fieldOneFiniteStageFiniteBruhatFourierLinear S f))
  left_inv f := by
    change fieldOneFiniteStageFiniteBruhatFourierLinear S
      (fieldOneFiniteStageFiniteBruhatFourierLinear S
        (fieldOneFiniteStageFiniteBruhatFourierLinear S
          (fieldOneFiniteStageFiniteBruhatFourierLinear S f))) = f
    apply Subtype.ext
    apply LocallyConstant.ext
    intro y
    have hsquare (a : FieldOneFiniteStageFiniteBruhatSchwartz S)
        (x : FieldOneFiniteStageFinitePart S) :
        (fieldOneFiniteStageFiniteBruhatFourierLinear S
          (fieldOneFiniteStageFiniteBruhatFourierLinear S a)).1 x =
            a.1 (-x) := by
      change (fieldOneFiniteStageFiniteBruhatFourierBruhat S
        (fieldOneFiniteStageFiniteBruhatFourierBruhat S a)).1 x = a.1 (-x)
      rw [fieldOneFiniteStageFiniteBruhatFourierBruhat_apply]
      exact fieldOneFiniteStageFiniteBruhatFourier_fourier S a x
    calc
      _ = (fieldOneFiniteStageFiniteBruhatFourierLinear S
            (fieldOneFiniteStageFiniteBruhatFourierLinear S f)).1 (-y) :=
        hsquare
          (fieldOneFiniteStageFiniteBruhatFourierLinear S
            (fieldOneFiniteStageFiniteBruhatFourierLinear S f)) y
      _ = f.1 (-(-y)) := hsquare f (-y)
      _ = f.1 y := by simp
  right_inv f := by
    change fieldOneFiniteStageFiniteBruhatFourierLinear S
      (fieldOneFiniteStageFiniteBruhatFourierLinear S
        (fieldOneFiniteStageFiniteBruhatFourierLinear S
          (fieldOneFiniteStageFiniteBruhatFourierLinear S f))) = f
    apply Subtype.ext
    apply LocallyConstant.ext
    intro y
    have hsquare (a : FieldOneFiniteStageFiniteBruhatSchwartz S)
        (x : FieldOneFiniteStageFinitePart S) :
        (fieldOneFiniteStageFiniteBruhatFourierLinear S
          (fieldOneFiniteStageFiniteBruhatFourierLinear S a)).1 x =
            a.1 (-x) := by
      change (fieldOneFiniteStageFiniteBruhatFourierBruhat S
        (fieldOneFiniteStageFiniteBruhatFourierBruhat S a)).1 x = a.1 (-x)
      rw [fieldOneFiniteStageFiniteBruhatFourierBruhat_apply]
      exact fieldOneFiniteStageFiniteBruhatFourier_fourier S a x
    calc
      _ = (fieldOneFiniteStageFiniteBruhatFourierLinear S
            (fieldOneFiniteStageFiniteBruhatFourierLinear S f)).1 (-y) :=
        hsquare
          (fieldOneFiniteStageFiniteBruhatFourierLinear S
            (fieldOneFiniteStageFiniteBruhatFourierLinear S f)) y
      _ = f.1 (-(-y)) := hsquare f (-y)
      _ = f.1 y := by simp

@[simp] theorem fieldOneFiniteStageFiniteBruhatFourierLinearEquiv_apply
    (S : Finset (HeightOneSpectrum ℤ))
    (f : FieldOneFiniteStageFiniteBruhatSchwartz S) :
    fieldOneFiniteStageFiniteBruhatFourierLinearEquiv S f =
      fieldOneFiniteStageFiniteBruhatFourierBruhat S f :=
  rfl

end

end GaloisForLFunctions.RHTower

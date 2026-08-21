import GaloisForLFunctions.HTGeometry.SeibergWitten.Orientation

/-!
# Hodge self-duality in the flat oriented four-model

Mathlib's current exterior-algebra library has no Hodge-star construction for real two-forms.
This module gives the canonical six-coordinate realization of `Λ²(ℝ⁴)`, in the oriented basis
`01, 02, 03, 12, 13, 23`.  Its Hodge star has the standard coordinate rule
`[ω₃₄, -ω₂₄, ω₂₃, ω₁₄, -ω₁₃, ω₁₂]` and squares to the identity.

The result is the algebraic Hodge layer needed to distinguish the self-dual curvature component
in Seiberg--Witten equations.  It is deliberately a finite-coordinate model rather than a full
development of exterior forms on arbitrary manifolds.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.SeibergWitten

/-- Six real coefficients of a two-form on the oriented Euclidean four-model. -/
abbrev FlatFourTwoForms := Fin 6 → ℝ

/-- The Euclidean Hodge star on two-form coordinates ordered as `01, 02, 03, 12, 13, 23`. -/
def flatFourHodgeStar : HodgeStar FlatFourTwoForms where
  toLinearMap :=
    { toFun := fun omega => ![omega 5, -omega 4, omega 3, omega 2, -omega 1, omega 0]
      map_add' := by
        intro omega eta
        ext i
        fin_cases i <;> simp [add_comm]
      map_smul' := by
        intro scalar omega
        ext i
        fin_cases i <;> simp }
  sq := by
    apply LinearMap.ext
    intro omega
    ext i
    fin_cases i <;> simp

/-- Every self-dual two-form is fixed by the algebraic self-dual projection. -/
theorem HodgeStar.selfDualPart_eq_of_isSelfDual
    {TwoForms : Type*} [AddCommGroup TwoForms] [Module ℝ TwoForms]
    (star : HodgeStar TwoForms) (omega : TwoForms) (hSelfDual : star.isSelfDual omega) :
    star.selfDualPart omega = omega := by
  unfold HodgeStar.selfDualPart
  rw [hSelfDual]
  calc
    (2 : ℝ)⁻¹ • (omega + omega) = (2 : ℝ)⁻¹ • ((2 : ℝ) • omega) := by rw [two_smul]
    _ = ((2 : ℝ)⁻¹ * 2) • omega := by rw [smul_smul]
    _ = omega := by rw [inv_mul_cancel₀ two_ne_zero, one_smul]

/-- The three self-dual coordinate directions in the oriented Euclidean four-model. -/
def flatSelfDualTwoForm (a b c : ℝ) : FlatFourTwoForms :=
  ![a, b, c, c, -b, a]

/-- The standard three anti-self-dual coordinate directions. -/
def flatAntiSelfDualTwoForm (a b c : ℝ) : FlatFourTwoForms :=
  ![a, b, c, -c, b, -a]

/-- The displayed three-plane is exactly self-dual for the Euclidean Hodge star. -/
theorem flatSelfDualTwoForm_isSelfDual (a b c : ℝ) :
    flatFourHodgeStar.isSelfDual (flatSelfDualTwoForm a b c) := by
  unfold HodgeStar.isSelfDual
  ext i
  fin_cases i <;> simp [flatFourHodgeStar, flatSelfDualTwoForm]

/-- The self-dual projection fixes every form in the displayed self-dual three-plane. -/
theorem flatSelfDualTwoForm_selfDualPart (a b c : ℝ) :
    flatFourHodgeStar.selfDualPart (flatSelfDualTwoForm a b c) =
      flatSelfDualTwoForm a b c :=
  flatFourHodgeStar.selfDualPart_eq_of_isSelfDual _
    (flatSelfDualTwoForm_isSelfDual a b c)

/-- The displayed complementary three-plane is anti-self-dual. -/
theorem flatAntiSelfDualTwoForm_isAntiSelfDual (a b c : ℝ) :
    flatFourHodgeStar.toLinearMap (flatAntiSelfDualTwoForm a b c) =
      -(flatAntiSelfDualTwoForm a b c) := by
  ext i
  fin_cases i <;> simp [flatFourHodgeStar, flatAntiSelfDualTwoForm]

/-- The self-dual projection kills every anti-self-dual coordinate form. -/
theorem flatAntiSelfDualTwoForm_selfDualPart_eq_zero (a b c : ℝ) :
    flatFourHodgeStar.selfDualPart (flatAntiSelfDualTwoForm a b c) = 0 := by
  unfold HodgeStar.selfDualPart
  rw [flatAntiSelfDualTwoForm_isAntiSelfDual]
  simp

end GaloisForLFunctions.HTGeometry.SeibergWitten

import GaloisForLFunctions.RHTower.DirichletCharacterTwist
import GaloisForLFunctions.RHTower.SelbergClass.Basic

/-!
# Arithmetic hypotheses for the degree-two twist frontier

This module records the exact arithmetic data in the theorem of Kaczorowski--Perelli on degree and
internal shift under primitive Dirichlet twists.  These definitions are data and propositions, not
surrogate theorem interfaces: membership in the extended Selberg class remains the concrete
analytic structure from `SelbergClass.Basic`.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- A polynomial in `p⁻s`, written in the normalization used for inverse local factors. -/
def selbergLocalInversePolynomialValue {order : ℕ} (p : ℕ)
    (A : Fin (order + 1) → ℂ) (s : ℂ) : ℂ :=
  ∑ j, A j / (p : ℂ) ^ ((j : ℕ) * s)

/-- `F` splits polynomially at `p`: deleting coefficients at multiples of `p` is multiplication by
a nonzero finite inverse-local-factor polynomial. -/
def ExtendedSelbergClass.SplitsPolynomiallyAt (F : ExtendedSelbergClass) (p : ℕ) : Prop :=
  p.Prime ∧ ∃ order : ℕ, ∃ A : Fin (order + 1) → ℂ,
    A ⟨order, Nat.lt_succ_self order⟩ ≠ 0 ∧
      ∀ s : ℂ, 1 < s.re →
        LSeries (characterLevelDepletion p F.coeff) s =
          selbergLocalInversePolynomialValue p A s * F s

/-- Saturation modulo `D`: every reduced class contains a nonzero coefficient coprime to every
prescribed positive modulus. -/
def ExtendedSelbergClass.SaturatedModulo {D : ℕ} [NeZero D]
    (F : ExtendedSelbergClass) : Prop :=
  ∀ M : ℕ, M ≠ 0 → ∀ a : ZMod D, IsUnit a →
    ∃ ν : ℕ, 0 < ν ∧ (ν : ZMod D) = a ∧ ν.Coprime M ∧ F.coeff ν ≠ 0

theorem ExtendedSelbergClass.SaturatedModulo.exists_nonzero_coeff_in_reduced_class
    {D : ℕ} [NeZero D] {F : ExtendedSelbergClass}
    (hF : F.SaturatedModulo (D := D)) (a : ZMod D) (ha : IsUnit a) :
    ∃ ν : ℕ, 0 < ν ∧ (ν : ZMod D) = a ∧ F.coeff ν ≠ 0 := by
  obtain ⟨ν, hν, hmod, _, hcoeff⟩ := hF 1 one_ne_zero a ha
  exact ⟨ν, hν, hmod, hcoeff⟩

/-- `G` has exactly the coefficientwise Dirichlet-character twist of `F`. -/
def ExtendedSelbergClass.IsCoefficientTwistOf {q : ℕ}
    (G F : ExtendedSelbergClass) (χ : DirichletCharacter ℂ q) : Prop :=
  G.coeff = dirichletCharacterTwist χ F.coeff

/-- A concrete gamma presentation of `F` has integer conductor `q`.  Presentation invariance must
be proved before this can be promoted to an intrinsic predicate. -/
def ExtendedSelbergClass.HasIntegerConductor
    (F : ExtendedSelbergClass) (q : ℕ) : Prop :=
  F.presentationConductor = q

end

end RHTower

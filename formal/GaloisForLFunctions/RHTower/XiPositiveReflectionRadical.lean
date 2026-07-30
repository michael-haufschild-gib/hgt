import GaloisForLFunctions.RHTower.BornTemperatureFactorType
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# Positive reflection radical

A positive `C⋆` realization cannot retain a nonzero element whose adjoint is
algebraically orthogonal to it.  In particular, if functional-equation
reflection exchanges two orthogonal divisor atoms, every `⋆`-homomorphism to a
`C⋆`-algebra kills those atoms.  A positive realization which conserves every
reduced `Xi` divisor atom therefore implies the Riemann hypothesis.

This file proves the unconditional algebraic mechanism and its exact RH
reduction.  It does not construct the conservative source realization.
-/

namespace HTGeometry

/-- If reflection sends `x` to an orthogonal partner `y`, then `x` vanishes in
every `C⋆`-algebra. -/
theorem cstar_eq_zero_of_star_eq_orthogonal
    {B : Type*} [NonUnitalNormedRing B] [StarRing B] [CStarRing B]
    {x y : B} (hstar : star x = y) (horth : y * x = 0) :
    x = 0 := by
  rw [← CStarRing.star_mul_self_eq_zero_iff x]
  rw [hstar, horth]

/-- Every `⋆`-homomorphism to a `C⋆`-algebra kills a star-isotropic source
element. -/
theorem starAlgHom_kills_star_isotropic
    {A B : Type*}
    [Semiring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    [NormedRing B] [StarRing B] [CStarRing B] [Algebra ℂ B] [StarModule ℂ B]
    (π : A →⋆ₐ[ℂ] B) {x : A} (hx : star x * x = 0) :
    π x = 0 := by
  rw [← CStarRing.star_mul_self_eq_zero_iff (π x)]
  rw [← map_star π x, ← map_mul, hx, map_zero]

/-- A reflected pair of orthogonal source elements lies in the kernel of every
positive `C⋆` realization. -/
theorem starAlgHom_kills_swapped_orthogonal
    {A B : Type*}
    [Semiring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    [NormedRing B] [StarRing B] [CStarRing B] [Algebra ℂ B] [StarModule ℂ B]
    (π : A →⋆ₐ[ℂ] B) {x y : A}
    (hstar : star x = y) (horth : y * x = 0) :
    π x = 0 := by
  apply starAlgHom_kills_star_isotropic π
  rw [hstar, horth]

/-- A nonzero reflected orthogonal atom obstructs every faithful positive
`C⋆` realization. -/
theorem no_injective_starAlgHom_of_swapped_orthogonal
    {A B : Type*}
    [Semiring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    [NormedRing B] [StarRing B] [CStarRing B] [Algebra ℂ B] [StarModule ℂ B]
    (π : A →⋆ₐ[ℂ] B) {x y : A}
    (hx : x ≠ 0) (hstar : star x = y) (horth : y * x = 0) :
    ¬ Function.Injective π := by
  intro hπ
  apply hx
  apply hπ
  simpa using starAlgHom_kills_swapped_orthogonal π hstar horth

end HTGeometry

namespace RHTower

/-- **Positive reflected-divisor reduction to RH.**  Suppose a source algebra
has atoms indexed before specialization, functional-equation reflection sends
each atom to its reflected partner, distinct reflected atoms are orthogonal,
and a positive `C⋆` realization retains the atom at every `Xi` zero.  Then every
`Xi` zero is fixed by reflection, hence RH holds.

The load-bearing open premise is `hsurvive`: the theorem classifies what a
conservative positive divisor realization would force, but does not construct
one. -/
theorem riemannHypothesis_of_positive_reflected_divisor_atoms
    {A B : Type*}
    [Semiring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    [NormedRing B] [StarRing B] [CStarRing B] [Algebra ℂ B] [StarModule ℂ B]
    (atom : ℂ → A) (π : A →⋆ₐ[ℂ] B)
    (hstar : ∀ ρ : ℂ, star (atom ρ) = atom (1 - starRingEnd ℂ ρ))
    (horth : ∀ ρ : ℂ, 1 - starRingEnd ℂ ρ ≠ ρ →
      atom (1 - starRingEnd ℂ ρ) * atom ρ = 0)
    (hsurvive : ∀ ρ : ℂ, xi ρ = 0 → π (atom ρ) ≠ 0) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_xiZero_reflection_fixed]
  intro ρ hρ
  by_contra hnotfixed
  apply hsurvive ρ hρ
  exact HTGeometry.starAlgHom_kills_swapped_orthogonal π
    (hstar ρ) (horth ρ hnotfixed)

end RHTower

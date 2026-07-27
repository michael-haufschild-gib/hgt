import Mathlib.Data.Finsupp.Basic

/-!
# Real Arakelov divisor endpoint

The finite divisor coordinates are a finitely supported family and the
archimedean coordinate records the negative weighted sum.  This file
proves the exact algebraic core: principal divisors are precisely the
kernel of total degree, the principal map is injective, and total degree
is surjective.
-/

namespace GaloisForLFunctions.RHTower

section ArakelovEndpoint

variable {P R : Type*} [CommRing R]

/-- Weighted degree of a finitely supported finite-place divisor. -/
def deningerFiniteDivisorWeight
    (weight : P → R) (d : P →₀ R) : R :=
  d.sum fun p c => c * weight p

/-- Principal Arakelov divisor: finite coordinates plus compensating
archimedean coordinate. -/
def deningerArakelovPrincipal
    (weight : P → R) (d : P →₀ R) : (P →₀ R) × R :=
  (d, -deningerFiniteDivisorWeight weight d)

/-- Total Arakelov degree. -/
def deningerArakelovDegree
    (weight : P → R) (x : (P →₀ R) × R) : R :=
  deningerFiniteDivisorWeight weight x.1 + x.2

/-- Every principal Arakelov divisor has degree zero. -/
theorem deningerArakelovDegree_principal
    (weight : P → R) (d : P →₀ R) :
    deningerArakelovDegree weight
      (deningerArakelovPrincipal weight d) = 0 := by
  simp [deningerArakelovDegree, deningerArakelovPrincipal]

/-- Finite coordinates make the principal-divisor map injective. -/
theorem deningerArakelovPrincipal_injective
    (weight : P → R) :
    Function.Injective (deningerArakelovPrincipal weight) := by
  intro d e h
  exact congrArg Prod.fst h

/-- Principal divisors are exactly the kernel of Arakelov degree. -/
theorem deningerArakelovDegree_eq_zero_iff
    (weight : P → R) (x : (P →₀ R) × R) :
    deningerArakelovDegree weight x = 0 ↔
      ∃ d : P →₀ R, deningerArakelovPrincipal weight d = x := by
  constructor
  · intro h
    refine ⟨x.1, ?_⟩
    apply Prod.ext
    · rfl
    · exact neg_eq_iff_add_eq_zero.mpr h
  · rintro ⟨d, rfl⟩
    exact deningerArakelovDegree_principal weight d

/-- The archimedean coordinate makes total degree surjective. -/
theorem deningerArakelovDegree_surjective
    (weight : P → R) :
    Function.Surjective (deningerArakelovDegree weight) := by
  intro r
  refine ⟨(0, r), ?_⟩
  simp [deningerArakelovDegree, deningerFiniteDivisorWeight]

end ArakelovEndpoint

end GaloisForLFunctions.RHTower

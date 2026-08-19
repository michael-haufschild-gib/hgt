import GaloisForLFunctions.HTGeometry.IntegralExtensionKrullDim
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field

/-!
# Noether normalization computes the Krull dimension

Over an injective integral extension the Krull dimension is unchanged, and the polynomial ring in
`s` variables over a field has dimension `s`, so a Noether normalization reads off the dimension of
any finitely generated algebra over a field:

```text
ringKrullDim_eq_of_noetherNormalization    dim R = s for any Noether normalization by s variables
exists_ringKrullDim_eq_of_finiteType       ** every f.g. algebra over a field has finite dimension **
```

Since the fraction field of a domain finite over `MvPolynomial (Fin s) k` is algebraic over
`k(X_0,…,X_{s-1})`, this is the statement that Krull dimension equals transcendence degree.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Noether normalization computes the Krull dimension.**  A finitely generated algebra over a
field has Krull dimension equal to the number of variables in any Noether normalization. -/
theorem ringKrullDim_eq_of_noetherNormalization
    {k R : Type*} [Field k] [CommRing R] [Nontrivial R] [Algebra k R]
    {s : ℕ} (g : MvPolynomial (Fin s) k →ₐ[k] R)
    (hinj : Function.Injective g) (hint : g.toRingHom.IsIntegral) :
    ringKrullDim R = (s : ℕ∞) := by
  letI : Algebra (MvPolynomial (Fin s) k) R := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) R := ⟨fun x => hint x⟩
  have hker : RingHom.ker (algebraMap (MvPolynomial (Fin s) k) R) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp hinj
  rw [← ringKrullDim_eq_of_isIntegral (MvPolynomial (Fin s) k) R hker,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field k]
  simp

/-- Every finitely generated algebra over a field has finite Krull dimension. -/
theorem exists_ringKrullDim_eq_of_finiteType
    (k R : Type*) [Field k] [CommRing R] [Nontrivial R] [Algebra k R]
    [Algebra.FiniteType k R] :
    ∃ s : ℕ, ringKrullDim R = (s : ℕ∞) := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k R
  exact ⟨s, ringKrullDim_eq_of_noetherNormalization g hinj hint⟩

end GaloisForLFunctions.HTGeometry

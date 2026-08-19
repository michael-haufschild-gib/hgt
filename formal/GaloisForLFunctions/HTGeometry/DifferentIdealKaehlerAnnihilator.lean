import GaloisForLFunctions.HTGeometry.DifferentIdealMonogenic
import GaloisForLFunctions.HTGeometry.MonogenicKaehlerAnnihilator
import GaloisForLFunctions.HTGeometry.DedekindOrderMonogenic
import GaloisForLFunctions.HTGeometry.ConductorAdjoinTop

/-!
# The Dedekind different is the Kähler different

For a Dedekind order `B` over a local domain `A` with characteristic-zero residue field, a single
element generates: `B = A[x]`.  The two classical descriptions of the ramification ideal then
coincide, because both are computed by the derivative of the minimal polynomial of that generator:

```text
differentIdeal A B = span {p'(x)} = Module.annihilator B (Ω[B⁄A])
```

The left identity is `DifferentIdealMonogenic.differentIdeal_eq_span_aeval_derivative` (the
conductor is the unit ideal), the right one is
`MonogenicKaehlerAnnihilator.annihilator_kaehler_monogenic`.  The generator is supplied by
`DedekindOrderMonogenic.exists_adjoin_eq_top_of_dedekind_finite`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial IsLocalRing

/-- In a tower whose bottom fraction field embeds in the top field, the structure map of the
integral layer is injective. -/
theorem algebraMap_injective_of_fractionTower (A K : Type*) {L B : Type*}
    [CommRing A] [Field K] [CommRing B] [Field L]
    [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [IsDomain A] [IsFractionRing A K] :
    Function.Injective (algebraMap A B) := by
  have h1 : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  rw [IsScalarTower.algebraMap_eq A B L] at h1
  exact Function.Injective.of_comp h1

/-- The fibre of a finite algebra over a local ring is a finite-dimensional residue algebra. -/
instance residueQuotient_finite (A : Type*) {B : Type*} [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] : Module.Finite (ResidueField A) (B ⧸ maxExt A B) := by
  have : Module.Finite A (B ⧸ maxExt A B) := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ A (maxExt A B)).toLinearMap Ideal.Quotient.mk_surjective
  exact Module.Finite.of_restrictScalars_finite A (ResidueField A) (B ⧸ maxExt A B)

/-- **The Dedekind different is the Kähler different.**  For a Dedekind order over a local domain
with characteristic-zero residue field, the different ideal is exactly the annihilator of the
module of relative differentials. -/
theorem differentIdeal_eq_annihilator_kaehler (A K : Type*) {L B : Type*}
    [CommRing A] [Field K] [CommRing B] [Field L]
    [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsIntegrallyClosed A] [IsIntegralClosure B A L] [IsFractionRing B L]
    [IsDedekindDomain B] [Module.IsTorsionFree A B]
    [IsLocalRing A] [CharZero (ResidueField A)] [Module.Finite A B]
    (h𝔞 : maxExt A B ≠ ⊥) :
    differentIdeal A B = Module.annihilator B (Ω[B⁄A]) := by
  have hinj : Function.Injective (algebraMap A B) :=
    algebraMap_injective_of_fractionTower A K (L := L) (B := B)
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  haveI : NoZeroSMulDivisors A B := ⟨fun {c x} h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (hinj (by simpa using h))
    · exact Or.inr h⟩
  obtain ⟨x, hx⟩ := exists_adjoin_eq_top_of_dedekind_finite (S := A) (B := B) h𝔞
  have hint : IsIntegral A x := Algebra.IsIntegral.isIntegral x
  have h0 : IsIntegral A (algebraMap B L x) := hint.map (IsScalarTower.toAlgHom A B L)
  have halg : IsAlgebraic K (algebraMap B L x) :=
    (IsIntegral.tower_top (A := K) h0).isAlgebraic
  have hfield : Algebra.adjoin K ({algebraMap B L x} : Set L) = ⊤ :=
    adjoin_fraction_eq_top halg hx
  have hcond : conductor A x = ⊤ := conductor_eq_top_of_adjoin_eq_top hx
  rw [differentIdeal_eq_span_aeval_derivative A K x hfield hcond,
    annihilator_kaehler_monogenic hint hx]

end GaloisForLFunctions.HTGeometry

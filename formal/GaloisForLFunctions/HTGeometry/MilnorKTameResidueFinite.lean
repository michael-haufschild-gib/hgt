import GaloisForLFunctions.HTGeometry.MilnorKTameDedekind
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

/-!
# Finiteness of the residue fields at the finite places

The valuation subring at a height-one prime of a Dedekind domain is the localization at that prime,
so its residue field is the residue field of the prime, which is a fraction field of `R ⧸ v.asIdeal`.
That quotient is already a field, because a nonzero prime of a Dedekind domain is maximal, and a
fraction field of a field is that field.  Hence the residue field at a finite place is finite
whenever `R ⧸ v.asIdeal` is — which is the defining finiteness of a number ring.

Combined with the tame-kernel reduction this makes the torsion of `K_2^M` of the fraction field
depend on nothing but the torsion of the tame kernel.

* `algebraMap_surjective_of_isFractionRing_of_isUnit` : a fraction field of a field is that field.
* `finite_residueField_valuationSubring` : **the residue field at a finite place is finite.**
* `milnorKDegTwo_torsion_of_tameKernel_of_finiteResidue` : **torsion of the tame kernel forces
  torsion of `K_2^M`**, with no side hypothesis beyond finiteness of the residue rings.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDedekindDomain IsLocalRing

section ResidueFinite

/-- **A fraction field of a ring in which every nonzero element is a unit is that ring.** -/
theorem algebraMap_surjective_of_isFractionRing_of_isUnit
    {A F : Type*} [CommRing A] [Nontrivial A] [Field F] [Algebra A F] [IsFractionRing A F]
    (hA : ∀ a : A, a ≠ 0 → IsUnit a) : Function.Surjective (algebraMap A F) := by
  intro x
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective (A := A) x
  obtain ⟨u, hu⟩ := hA b (nonZeroDivisors.ne_zero hb)
  refine ⟨a * ((u⁻¹ : Aˣ) : A), ?_⟩
  have hinv : algebraMap A F ((u⁻¹ : Aˣ) : A) = (algebraMap A F b)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, ← hu, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  rw [map_mul, hinv, ← div_eq_mul_inv, hx]

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The residue field at a finite place is finite** when the residue ring of the prime is.  The
valuation subring is the localization at the prime, so its residue field is a fraction field of
`R ⧸ v.asIdeal`, and that quotient is already a field. -/
instance finite_residueField_valuationSubring (v : HeightOneSpectrum R)
    [Finite (R ⧸ v.asIdeal)] : Finite (ResidueField ((v.valuation K).valuationSubring)) := by
  haveI : v.asIdeal.IsPrime := v.isPrime
  haveI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  haveI : Finite (Ideal.ResidueField v.asIdeal) :=
    Finite.of_surjective (algebraMap (R ⧸ v.asIdeal) (Ideal.ResidueField v.asIdeal))
      (algebraMap_surjective_of_isFractionRing_of_isUnit (fun a ha => by
        obtain ⟨b, hb⟩ :=
          ((Ideal.Quotient.maximal_ideal_iff_isField_quotient v.asIdeal).1
            inferInstance).mul_inv_cancel ha
        exact ⟨⟨a, b, hb, by rw [mul_comm]; exact hb⟩, rfl⟩))
  have e₁ : Localization.AtPrime v.asIdeal ≃ₐ[R] (HeightOneSpectrum.valuationSubringAtPrime K v) :=
    IsLocalization.algEquiv v.asIdeal.primeCompl _ _
  have e₂ : (HeightOneSpectrum.valuationSubringAtPrime K v) ≃+*
      ((v.valuation K).valuationSubring) :=
    RingEquiv.subringCongr
      (congrArg ValuationSubring.toSubring
        (HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring v))
  exact Finite.of_equiv (Ideal.ResidueField v.asIdeal)
    ((ResidueField.mapEquiv e₁.toRingEquiv).trans (ResidueField.mapEquiv e₂)).toEquiv

/-- **Torsion of the tame kernel forces torsion of `K_2^M`**, with the finiteness of the residue
fields discharged: only the residue rings of the primes are required to be finite, which holds for
every number ring. -/
theorem milnorKDegTwo_torsion_of_tameKernel_of_finiteResidue
    [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)]
    (htame : ∀ y ∈ tameKernel (fun v : HeightOneSpectrum R => tameDataAtPlace K v),
      y ∈ torsionAddSubgroup (MilnorKDeg K 2))
    (x : MilnorKDeg K 2) : x ∈ torsionAddSubgroup (MilnorKDeg K 2) :=
  milnorKDegTwo_torsion_of_tameKernelAtPlaces_torsion K htame x

end ResidueFinite

section NumberFieldCase

open NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The residue rings of a number ring are finite. -/
instance finite_quotient_asIdeal (v : HeightOneSpectrum (RingOfIntegers K)) :
    Finite (RingOfIntegers K ⧸ v.asIdeal) :=
  v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot

/-- **For a number field, torsion of the tame kernel forces torsion of `K_2^M`.**  Every side
condition is discharged: the residue rings of a number ring are finite, hence so are the residue
fields at the finite places, and a fixed class has trivial tame symbol at almost every place. -/
theorem milnorKDegTwo_torsion_of_tameKernel_numberField
    (htame : ∀ y ∈ tameKernel (fun v : HeightOneSpectrum (RingOfIntegers K) =>
        tameDataAtPlace K v), y ∈ torsionAddSubgroup (MilnorKDeg K 2))
    (x : MilnorKDeg K 2) : x ∈ torsionAddSubgroup (MilnorKDeg K 2) :=
  milnorKDegTwo_torsion_of_tameKernel_of_finiteResidue K htame x

end NumberFieldCase

end GaloisForLFunctions.HTGeometry

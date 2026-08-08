import GaloisForLFunctions.HTGeometry.ValuationSubringComapDVR
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Discreteness of valuation rings in finite extensions

A valuation ring of a finite separable extension which lies over a discrete valuation ring is
itself discrete.  We identify it with the localization of the integral closure at its contracted
maximal ideal and transport the DVR structure across that ring equivalence.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 3000000

open IsDiscreteValuationRing IsLocalRing

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- A valuation ring in a finite separable extension lying over a DVR is again a DVR. -/
theorem valuationSubring_isDiscreteValuationRing_of_finiteExtension
    (O : ValuationSubring F) (A : ValuationSubring E)
    [IsDiscreteValuationRing O] [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (hcomap : A.comap (algebraMap F E) = O) : IsDiscreteValuationRing A := by
  classical
  subst O
  let O := A.comap (algebraMap F E)
  let ψ := valuationSubringComapInclusion (algebraMap F E) A
  let S := integralClosure O E
  have hbase (x : O) : algebraMap O E x ∈ A := by
    change algebraMap F E (x : F) ∈ A
    exact x.property
  have hSA : S.toSubring ≤ A.toSubring := by
    letI : IsIntegrallyClosedIn A.toSubring E := by
      rw [Subring.isIntegrallyClosedIn_iff]
      intro x hx
      have hclosed :=
        Subring.isIntegrallyClosed_iff.mp (inferInstance : IsIntegrallyClosed A)
      exact hclosed hx
    exact (Subring.integralClosure_le_iff (T := A.toSubring)).mpr hbase
  let ι : S →+* A := Subring.inclusion hSA
  let P : Ideal S := (maximalIdeal A).comap ι
  letI : P.IsPrime := Ideal.comap_isPrime ι (maximalIdeal A)
  letI : IsDedekindDomain S := integralClosure.isDedekindDomain O F E
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let s : S := algebraMap O S π
  have hs0 : s ≠ 0 := by
    simpa [s] using (FaithfulSMul.algebraMap_injective O S).ne hπ.ne_zero
  have hιs : ι s = ψ π := by
    apply Subtype.ext
    change algebraMap O E π = algebraMap F E (π : F)
    exact IsScalarTower.algebraMap_apply O F E π
  have hsP : s ∈ P := by
    change ι s ∈ maximalIdeal A
    rw [hιs, mem_maximalIdeal]
    simpa only [mem_nonunits_iff, isUnit_map_iff] using hπ.not_isUnit
  have hP0 : P ≠ ⊥ := P.ne_bot_iff.mpr ⟨s, hsP, hs0⟩
  let R := Localization.AtPrime P
  letI : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hP0 R
  have hden (y : P.primeCompl) : IsUnit (ι (y : S)) := by
    by_contra hy
    apply y.property
    change ι (y : S) ∈ maximalIdeal A
    rw [mem_maximalIdeal]
    exact hy
  let φ : R →+* A := IsLocalization.lift hden
  have hφbase (x : S) : φ (algebraMap S R x) = ι x := by
    simp [φ]
  letI : IsLocalHom φ := by
    apply ((local_hom_TFAE φ).out 3 0).mp
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P]
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change φ (algebraMap S R x) ∈ maximalIdeal A
    rw [hφbase]
    exact hx
  let g : A →+* E := A.subtype
  letI : Algebra R E := (g.comp φ).toAlgebra
  have hSE : ∀ x : S, algebraMap S E x = algebraMap R E (algebraMap S R x) := by
    intro x
    change (x : E) = g (φ (algebraMap S R x))
    rw [hφbase]
    rfl
  letI : IsScalarTower S R E := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact hSE x)
  letI : IsFractionRing S E :=
    integralClosure.isFractionRing_of_finite_extension F E
  letI : IsFractionRing R E :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl R E
  have hcomp : g.comp φ = algebraMap R E := rfl
  have hcompbij : Function.Bijective (g.rangeRestrict.comp φ) :=
    bijective_rangeRestrict_comp_of_valuationRing (R := R) (S := A) (K := E) φ g hcomp
  have hφinj : Function.Injective φ := by
    intro x y hxy
    apply hcompbij.1
    exact congrArg g.rangeRestrict hxy
  have hφsurj : Function.Surjective φ := by
    intro a
    obtain ⟨x, hx⟩ := hcompbij.2 (g.rangeRestrict a)
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change g (φ x) = g a
    exact congrArg (fun z : g.range => (z : E)) hx
  let e : R ≃+* A := RingEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e

end

end GaloisForLFunctions.HTGeometry

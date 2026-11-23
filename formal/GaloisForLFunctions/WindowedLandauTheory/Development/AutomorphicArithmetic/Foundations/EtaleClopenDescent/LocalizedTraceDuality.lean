import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LocalKaehlerBasis
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LocalTopFormCoefficient
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CodifferentMembership
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FractionFieldLocalMembership
import Mathlib.RingTheory.Localization.AsSubring

/-! Over the normalization of a discrete valuation ring, trace duality
is equivalent to regularity of a rational top form on the local charts. -/

noncomputable section

open KaehlerDifferential IsLocalRing GlobalTheory.SchemeCohomology
open scoped GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

/-- The prime localization realized as a subalgebra of the fraction field. -/
abbrev primeLocalizationInField {T : Type*} [CommRing T] [IsDomain T]
    (E : Type*) [Field E] [Algebra T E] [IsFractionRing T E] (Q : Ideal T) [Q.IsPrime] :
    Subalgebra T E :=
  Localization.subalgebra.ofField E Q.primeCompl Q.primeCompl_le_nonZeroDivisors

variable {k B A T F E : Type} [Field k]
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero (ResidueField A)]
  [CommRing T] [IsDedekindDomain T] [Field F] [Field E] [CommRing B]
  [Algebra A F] [Algebra A T] [Algebra A E] [Algebra T E] [Algebra F E]
  [IsScalarTower A F E] [IsScalarTower A T E]
  [IsFractionRing A F] [IsFractionRing T E] [IsIntegralClosure T A E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E] [Module.Finite A T] [Module.IsTorsionFree A T]
  [Algebra k A] [Algebra k T] [Algebra k E] [Algebra k B] [Algebra B T] [Algebra B E]
  [IsScalarTower k A E] [IsScalarTower k T E] [IsScalarTower k B E] [IsScalarTower B T E]
  [Algebra.Smooth k B] [Algebra.FormallyEtale B T]

include B in
/-- Integrality of the trace pairing is equivalent to regularity of the
corresponding rational top form over every maximal ideal of the normalization. -/
theorem trace_dual_iff_topForm_regular_at_maximal {d : ℕ}
    (u : Fin d → A) (a : Module.Basis (Fin d) A Ω[A⁄k]) (ha : ∀ i, a i = D k A (u i))
    (bE : Module.Basis (Fin d) E Ω[E⁄k]) (z : E) :
    (∀ t : T, Algebra.trace F E (z * algebraMap T E t) ∈ (algebraMap A F).range) ↔
      ∀ (Q : Ideal T) [Q.IsMaximal],
        z • exteriorPower.ιMulti E d (fun i => D k E (algebraMap A E (u i))) ∈
          LinearMap.range
            (algebraFormPullback k ((primeLocalizationInField E Q).restrictScalars k) E d) := by
  let w := z • exteriorPower.ιMulti E d (fun i => D k E (algebraMap A E (u i)))
  have hloc (Q : Ideal T) [Q.IsMaximal] :
      w ∈ LinearMap.range
          (algebraFormPullback k ((primeLocalizationInField E Q).restrictScalars k) E d) ↔
        ∀ y ∈ differentIdeal A T, z * algebraMap T E y ∈
          (algebraMap (primeLocalizationInField E Q) E).range := by
    let C := primeLocalizationInField E Q
    letI : Algebra k C := (C.restrictScalars k).algebra
    letI : Algebra A C := (C.restrictScalars A).algebra
    letI : Algebra B C := (C.restrictScalars B).algebra
    letI : IsScalarTower k C E := .of_algebraMap_eq fun _ => rfl
    letI : IsScalarTower A C E := .of_algebraMap_eq fun _ => rfl
    letI : IsScalarTower A T C := .of_algebraMap_eq fun x =>
      Subtype.ext (IsScalarTower.algebraMap_apply A T E x)
    letI : IsScalarTower B T C := .of_algebraMap_eq fun x =>
      Subtype.ext (IsScalarTower.algebraMap_apply B T E x)
    letI : IsScalarTower k A C := .of_algebraMap_eq fun x =>
      Subtype.ext (IsScalarTower.algebraMap_apply k A E x)
    letI : IsScalarTower k B C := .of_algebraMap_eq fun x =>
      Subtype.ext (IsScalarTower.algebraMap_apply k B E x)
    letI : IsLocalization Q.primeCompl C := inferInstanceAs (IsLocalization Q.primeCompl (primeLocalizationInField E Q))
    letI : IsLocalRing C := IsLocalization.AtPrime.isLocalRing C Q
    letI : Algebra.FormallyEtale T C := .of_isLocalization Q.primeCompl
    letI : Algebra.FormallyEtale B C := Algebra.FormallyEtale.comp B T C
    obtain ⟨b⟩ := nonempty_kaehler_basis_of_fraction_basis (B := B) (C := C) bE
    exact coordinateTopForm_regular_iff_different (F := F) Q.primeCompl u a ha b z
  constructor
  · intro h Q _
    apply (hloc Q).mpr
    intro y hy
    obtain ⟨t, ht⟩ := (trace_mem_range_iff_mul_different z).mp h y hy
    exact ⟨algebraMap T (primeLocalizationInField E Q) t,
      (IsScalarTower.algebraMap_apply T (primeLocalizationInField E Q) E t).symm.trans ht⟩
  · intro h
    refine (trace_mem_range_iff_mul_different z).mpr fun y hy => ?_
    refine mem_algebraMap_range_of_forall_maximal _ fun Q _ => ?_
    let C := primeLocalizationInField E Q
    obtain ⟨c, hc⟩ := (hloc Q).mp (h Q) y hy
    obtain ⟨⟨t, s⟩, hcs⟩ := IsLocalization.surj Q.primeCompl c
    refine ⟨s, s.property, t, ?_⟩
    have he := congrArg (algebraMap C E) hcs
    rwa [map_mul, hc, ← IsScalarTower.algebraMap_apply T C E,
      ← IsScalarTower.algebraMap_apply T C E, mul_comm (z * algebraMap T E y)] at he

end GlobalTheory.PD

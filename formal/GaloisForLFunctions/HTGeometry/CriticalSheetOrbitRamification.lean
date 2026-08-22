import GaloisForLFunctions.HTGeometry.ValuationInertiaIntermediateBase
import GaloisForLFunctions.HTGeometry.CriticalSchurInertiaRamificationIndex
import GaloisForLFunctions.HTGeometry.CriticalSheetStabilizerInertia

/-!
# The orbit of a sheet is the ramification index of its place

The general orbit formula of `ValuationInertiaIntermediateBase`, instantiated on the critical
horizon.

```text
criticalNormalClosure_isGalois
charZero_residueField_of_ringHom      a prime residue field of a char-zero algebra is char zero
criticalIntermediateCentre_charZero
natCard_criticalSchurInertiaGroup_eq_intermediate_mul
    ** |I| = e(Q_M / 𝔪_A) · |W.inertiaSubgroup M| **, for every intermediate field `M`
natCard_criticalSchurInertiaGroup_eq_sheet_mul
    ** |I| = e(Q_σ / 𝔪_A) · |Stab_I(σ)| **, for every geometric sheet `σ`
```

So the `I`-orbit of a sheet has exactly `e(Q_σ / 𝔪_A)` elements, where `Q_σ` is the place the sheet
cuts out on the integral closure of the observation Schur DVR in the field the sheet generates.
This is the statement the collision count of the card consumes: a sheet is moved by inertia exactly
when its place ramifies, and the size of its orbit is the ramification index.

The characteristic-zero input is deliberately routed through an abstract lemma: a ring hom from a
characteristic-zero field into `B` makes every prime residue field of `B` characteristic zero, and a
field maps injectively into any nontrivial ring.  Building the four-step composite directly inside
the horizon's types exhausts the elaborator.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsLocalRing
open scoped Pointwise

set_option synthInstance.maxHeartbeats 3000000
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}

/-- The critical normal closure is Galois over the observation field. -/
theorem criticalNormalClosure_isGalois (hm : 0 < m) (hn : 0 < n) :
    IsGalois (criticalObservationField K m n) (criticalNormalClosure K m n) := by
  haveI : FiniteDimensional (criticalObservationField K m n) (criticalSourceField K m n) :=
    criticalSourceField_finiteDimensional_criticalObservationField K hm hn
  haveI : IsScalarTower (criticalObservationField K m n) (criticalSourceField K m n)
      (criticalSourceAlgebraicClosure K m n) :=
    AlgebraicClosure.instIsScalarTower (criticalSourceField K m n)
  haveI : Algebra.IsAlgebraic (criticalObservationField K m n)
      (criticalSourceAlgebraicClosure K m n) :=
    Algebra.IsAlgebraic.trans (criticalObservationField K m n) (criticalSourceField K m n)
      (criticalSourceAlgebraicClosure K m n)
  haveI : Normal (criticalObservationField K m n) (criticalSourceAlgebraicClosure K m n) :=
    { splits' _ := IsAlgClosed.splits _ }
  haveI : FiniteDimensional (criticalObservationField K m n) (criticalNormalClosure K m n) :=
    criticalNormalClosure_finiteDimensional K hm hn
  haveI : Normal (criticalObservationField K m n) (criticalNormalClosure K m n) :=
    normalClosure.normal (criticalObservationField K m n) (criticalSourceField K m n)
      (criticalSourceAlgebraicClosure K m n)
  infer_instance

/-- A prime residue field of a ring receiving a characteristic-zero field has characteristic
zero. -/
theorem charZero_residueField_of_ringHom {B : Type*} [CommRing B] (Q : Ideal B) [Q.IsPrime]
    {k : Type*} [Field k] [CharZero k] (φ : k →+* B) : CharZero Q.ResidueField :=
  (RingHom.charZero_iff (ϕ := (algebraMap (B ⧸ Q) Q.ResidueField).comp
    ((Ideal.Quotient.mk Q).comp φ)) (RingHom.injective _)).mp inferInstance

/-- Residue fields of primes of the intermediate base have characteristic zero. -/
theorem criticalIntermediateCentre_charZero (hm : 0 < m) (hn : 0 < n)
    (M : IntermediateField (criticalObservationField K m n) (criticalNormalClosure K m n))
    (Q : Ideal (integralClosure (CriticalSchurNormalBaseRing K hm hn) M)) [Q.IsPrime] :
    CharZero Q.ResidueField :=
  charZero_residueField_of_ringHom Q
    ((algebraMap (CriticalSchurNormalBaseRing K hm hn)
      (integralClosure (CriticalSchurNormalBaseRing K hm hn) M)).comp
      (criticalObservationSchurConstantBaseMap K hm hn))

/-- **The orbit formula on the critical horizon.**  The Schur inertia group is the inertia group of
an intermediate field times the ramification index of the place that field cuts out. -/
theorem natCard_criticalSchurInertiaGroup_eq_intermediate_mul (hm : 0 < m) (hn : 0 < n)
    (M : IntermediateField (criticalObservationField K m n) (criticalNormalClosure K m n)) :
    Nat.card (criticalSchurInertiaGroup K hm hn)
      = (ValuationInertia.intermediateCentre M
          (criticalNormalClosureSchurValuationSubring K hm hn)
          (criticalSchurNormalBase_algebraMap_mem K hm hn)).ramificationIdx
            (CriticalSchurNormalBaseRing K hm hn)
        * Nat.card ((criticalNormalClosureSchurValuationSubring K hm hn).inertiaSubgroup M) := by
  haveI : FiniteDimensional (criticalObservationField K m n) (criticalNormalClosure K m n) :=
    criticalNormalClosure_finiteDimensional K hm hn
  haveI := criticalNormalClosure_isGalois K hm hn
  haveI := criticalIntermediateCentre_charZero K hm hn M
    (ValuationInertia.intermediateCentre M
      (criticalNormalClosureSchurValuationSubring K hm hn)
      (criticalSchurNormalBase_algebraMap_mem K hm hn))
  exact ValuationInertia.natCard_inertiaSubgroup_eq_intermediate_mul
    M (criticalNormalClosureSchurValuationSubring K hm hn)
    (criticalSchurNormalBase_algebraMap_mem K hm hn)
    (IsLocalRing.maximalIdeal (CriticalSchurNormalBaseRing K hm hn))
    (ValuationSubring.ne_top_of_isDiscreteValuationRing _)
    (IsDiscreteValuationRing.not_a_field _)
    (criticalSchurNormalBase_centre K hm hn)

/-- **The orbit of a sheet has as many elements as the ramification index of the place it sits
over.**  Stated as the orbit–stabiliser product, with the stabiliser written out. -/
theorem natCard_criticalSchurInertiaGroup_eq_sheet_mul (hm : 0 < m) (hn : 0 < n)
    (σ : criticalGeometricSheet K m n) :
    Nat.card (criticalSchurInertiaGroup K hm hn)
      = (ValuationInertia.intermediateCentre (AlgHom.fieldRange σ)
          (criticalNormalClosureSchurValuationSubring K hm hn)
          (criticalSchurNormalBase_algebraMap_mem K hm hn)).ramificationIdx
            (CriticalSchurNormalBaseRing K hm hn)
        * Nat.card {g : (criticalNormalClosureSchurValuationSubring K hm hn).inertiaSubgroup
            (criticalObservationField K m n) //
            criticalSchurInertiaAction K hm hn g σ = σ} := by
  rw [natCard_sheetStabilizer_eq_natCard_inertiaSubgroup K m n hm hn σ]
  exact natCard_criticalSchurInertiaGroup_eq_intermediate_mul K hm hn (AlgHom.fieldRange σ)

end

end GaloisForLFunctions.HTGeometry

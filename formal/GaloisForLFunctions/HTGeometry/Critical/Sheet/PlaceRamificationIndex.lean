import GaloisForLFunctions.HTGeometry.Critical.Sheet.SchurPlacePullback
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.Critical.Sheet.OrbitRamification
import GaloisForLFunctions.HTGeometry.RamificationIdxTransport
import GaloisForLFunctions.HTGeometry.Critical.Schur.SourceRamificationIndex

/-!
# The ramification index of the place a sheet cuts out

A sheet is an isomorphism of the source field onto its own field range inside the normal closure,
so it carries the integral closure of the observation Schur DVR in the source field isomorphically
onto the integral closure in that range.  When the sheet cuts out the source Schur place, that
isomorphism matches the two centres, and the ramification index — invariant along an algebra
isomorphism — is the one already computed for the source Schur place: exactly two.

```text
isUnit_valuationSubring_iff       invertibility inside a valuation subring
criticalSheetToRange, criticalSheetFieldEquiv, criticalSheetBaseEquiv
criticalSheetIntegralClosureEquiv   transport of the integral closure along a sheet
mem_criticalSchurSourceIntegralClosurePrime_iff
criticalSheetIntermediateCentre_comap
criticalSheetRamificationIdx_eq_two  ** e(Q_σ) = 2 for a sheet over the source Schur place **
```

The matching of centres is elementwise: a sheet with the given place inverts an element of the
source exactly when the image is invertible upstairs, which is the definition of the pullback.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsLocalRing

set_option synthInstance.maxHeartbeats 3000000
set_option maxHeartbeats 8000000
set_option maxSynthPendingDepth 3

/-- An element of a valuation subring is a unit exactly when it has an inverse inside. -/
theorem isUnit_valuationSubring_iff {L : Type*} [Field L] (W : ValuationSubring L)
    {z : L} (hz : z ∈ W) :
    IsUnit (⟨z, hz⟩ : W) ↔ ∃ w, ∃ _ : w ∈ W, z * w = 1 := by
  constructor
  · intro hu
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hu
    exact ⟨(v : L), v.2, congrArg Subtype.val hv⟩
  · rintro ⟨w, hw, hzw⟩
    exact isUnit_iff_exists_inv.mpr ⟨⟨w, hw⟩, Subtype.ext hzw⟩

variable (K : Type*) [Field K] [CharZero K] {m n : ℕ}

/-- A sheet, corestricted to its own field range. -/
def criticalSheetToRange (σ : criticalGeometricSheet K m n) :
    criticalSourceField K m n →ₐ[criticalObservationField K m n] ↥(AlgHom.fieldRange σ) where
  toFun x := ⟨σ x, AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩⟩
  map_one' := Subtype.ext (map_one σ)
  map_mul' _ _ := Subtype.ext (map_mul σ _ _)
  map_zero' := Subtype.ext (map_zero σ)
  map_add' _ _ := Subtype.ext (map_add σ _ _)
  commutes' r := Subtype.ext (σ.commutes r)

/-- A sheet is an isomorphism onto its field range. -/
def criticalSheetFieldEquiv (σ : criticalGeometricSheet K m n) :
    criticalSourceField K m n ≃ₐ[criticalObservationField K m n] ↥(AlgHom.fieldRange σ) :=
  AlgEquiv.ofBijective (criticalSheetToRange K σ)
    ⟨fun x y hxy => σ.toRingHom.injective (congrArg Subtype.val hxy),
      fun y => by
        obtain ⟨x, hx⟩ := AlgHom.mem_fieldRange.mp y.2
        exact ⟨x, Subtype.ext hx⟩⟩

@[simp] theorem coe_criticalSheetFieldEquiv (σ : criticalGeometricSheet K m n)
    (x : criticalSourceField K m n) :
    ((criticalSheetFieldEquiv K σ x : ↥(AlgHom.fieldRange σ)) : criticalNormalClosure K m n)
      = σ x := rfl

variable [IsAlgClosed K]

/-- The same isomorphism, over the observation Schur base ring. -/
def criticalSheetBaseEquiv (hm : 0 < m) (hn : 0 < n) (σ : criticalGeometricSheet K m n) :
    criticalSourceField K m n ≃ₐ[CriticalSchurNormalBaseRing K hm hn]
      ↥(AlgHom.fieldRange σ) :=
  AlgEquiv.restrictScalars (CriticalSchurNormalBaseRing K hm hn)
    (S := criticalObservationField K m n) (criticalSheetFieldEquiv K σ)

/-- Transport of the integral closure along a sheet. -/
def criticalSheetIntegralClosureEquiv (hm : 0 < m) (hn : 0 < n)
    (σ : criticalGeometricSheet K m n) :
    CriticalSchurSourceIntegralClosure K hm hn ≃ₐ[CriticalSchurNormalBaseRing K hm hn]
      integralClosure (CriticalSchurNormalBaseRing K hm hn) ↥(AlgHom.fieldRange σ) where
  toFun x := ⟨criticalSheetBaseEquiv K hm hn σ x,
    x.2.map (criticalSheetFieldEquiv K σ).toAlgHom⟩
  invFun y := ⟨(criticalSheetBaseEquiv K hm hn σ).symm y,
    y.2.map (criticalSheetFieldEquiv K σ).symm.toAlgHom⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  commutes' r := Subtype.ext ((criticalSheetBaseEquiv K hm hn σ).commutes r)

@[simp] theorem coe_criticalSheetIntegralClosureEquiv (hm : 0 < m) (hn : 0 < n)
    (σ : criticalGeometricSheet K m n) (x : CriticalSchurSourceIntegralClosure K hm hn) :
    ((criticalSheetIntegralClosureEquiv K hm hn σ x :
        integralClosure (CriticalSchurNormalBaseRing K hm hn) ↥(AlgHom.fieldRange σ)) :
      criticalNormalClosure K m n)
      = σ (x : criticalSourceField K m n) := rfl

/-- Membership in the source Schur prime is failure of invertibility at the source Schur place. -/
theorem mem_criticalSchurSourceIntegralClosurePrime_iff (hm : 0 < m) (hn : 0 < n)
    (y : CriticalSchurSourceIntegralClosure K hm hn) :
    y ∈ criticalSchurSourceIntegralClosurePrime K hm hn ↔
      ¬ IsUnit (⟨(y : criticalSourceField K m n),
        criticalSchurSourceIntegralClosure_mem_upper K hm hn y⟩ :
          criticalSchurSourceValuationSubring K hm hn) := by
  show criticalSchurSourceIntegralClosureToUpper K hm hn y
    ∈ IsLocalRing.maximalIdeal (criticalSchurSourceValuationSubring K hm hn) ↔ _
  rw [IsLocalRing.mem_maximalIdeal]
  rfl

/-- **A sheet cutting out the source Schur place pulls the intermediate centre back to the source
Schur prime.** -/
theorem criticalSheetIntermediateCentre_comap (hm : 0 < m) (hn : 0 < n)
    {σ : criticalGeometricSheet K m n}
    (hplace : criticalSheetPullbackValuation K hm hn σ
      = criticalSchurSourceValuationSubring K hm hn) :
    Ideal.comap (criticalSheetIntegralClosureEquiv K hm hn σ :
        CriticalSchurSourceIntegralClosure K hm hn →+*
          integralClosure (CriticalSchurNormalBaseRing K hm hn) ↥(AlgHom.fieldRange σ))
      (ValuationInertia.intermediateCentre (AlgHom.fieldRange σ)
        (criticalNormalClosureSchurValuationSubring K hm hn)
        (criticalSchurNormalBase_algebraMap_mem K hm hn))
      = criticalSchurSourceIntegralClosurePrime K hm hn := by
  have hmem : ∀ y : criticalSourceField K m n,
      y ∈ criticalSchurSourceValuationSubring K hm hn ↔
        σ y ∈ criticalNormalClosureSchurValuationSubring K hm hn := by
    intro y
    rw [← hplace]
    exact Iff.rfl
  refine Ideal.ext fun x => ?_
  refine Iff.trans (ValuationInertia.mem_intermediateCentre_iff (AlgHom.fieldRange σ)
    (criticalNormalClosureSchurValuationSubring K hm hn)
    (criticalSchurNormalBase_algebraMap_mem K hm hn)
    (criticalSheetIntegralClosureEquiv K hm hn σ x)) ?_
  refine Iff.trans ?_ (mem_criticalSchurSourceIntegralClosurePrime_iff K hm hn x).symm
  refine not_congr ?_
  rw [isUnit_valuationSubring_iff, isUnit_valuationSubring_iff]
  constructor
  · rintro ⟨w, hw, hzw⟩
    have hzw' : σ (x : criticalSourceField K m n) * w = 1 := hzw
    have hx0 : (x : criticalSourceField K m n) ≠ 0 := by
      intro h0
      rw [h0, map_zero, zero_mul] at hzw'
      exact zero_ne_one hzw'
    refine ⟨(x : criticalSourceField K m n)⁻¹, ?_, mul_inv_cancel₀ hx0⟩
    rw [hmem, map_inv₀]
    have hw' : (σ (x : criticalSourceField K m n))⁻¹ = w :=
      inv_eq_of_mul_eq_one_right hzw' 
    rw [hw']
    exact hw
  · rintro ⟨w, hw, hzw⟩
    refine ⟨σ w, (hmem w).mp hw, ?_⟩
    show σ (x : criticalSourceField K m n) * σ w = 1
    rw [← map_mul, hzw, map_one]

/-- **The ramification index of the place a sheet cuts out is exactly two**, whenever that place is
the source Schur place. -/
theorem criticalSheetRamificationIdx_eq_two (hm : 0 < m) (hn : 0 < n)
    [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]
    {σ : criticalGeometricSheet K m n}
    (hplace : criticalSheetPullbackValuation K hm hn σ
      = criticalSchurSourceValuationSubring K hm hn) :
    (ValuationInertia.intermediateCentre (AlgHom.fieldRange σ)
        (criticalNormalClosureSchurValuationSubring K hm hn)
        (criticalSchurNormalBase_algebraMap_mem K hm hn)).ramificationIdx
      (CriticalSchurNormalBaseRing K hm hn) = 2 := by
  haveI : FiniteDimensional (criticalObservationField K m n) (criticalNormalClosure K m n) :=
    criticalNormalClosure_finiteDimensional K hm hn
  haveI := criticalNormalClosure_isGalois K hm hn
  haveI : IsDedekindDomain (integralClosure (CriticalSchurNormalBaseRing K hm hn)
      ↥(AlgHom.fieldRange σ)) :=
    IsIntegralClosure.isDedekindDomain (CriticalSchurNormalBaseRing K hm hn)
      (criticalObservationField K m n) ↥(AlgHom.fieldRange σ) _
  haveI : Module.IsTorsionFree (CriticalSchurNormalBaseRing K hm hn)
      (integralClosure (CriticalSchurNormalBaseRing K hm hn) ↥(AlgHom.fieldRange σ)) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (ValuationInertia.injective_algebraMap_intermediateBase
        (A := CriticalSchurNormalBaseRing K hm hn)
        (F := criticalObservationField K m n) (AlgHom.fieldRange σ))
  haveI := ValuationInertia.liesOver_intermediateCentre (AlgHom.fieldRange σ)
    (criticalNormalClosureSchurValuationSubring K hm hn)
    (criticalSchurNormalBase_algebraMap_mem K hm hn)
    (IsLocalRing.maximalIdeal (CriticalSchurNormalBaseRing K hm hn))
    (criticalSchurNormalBase_centre K hm hn)
  have hp : IsLocalRing.maximalIdeal (CriticalSchurNormalBaseRing K hm hn) ≠ ⊥ :=
    IsDiscreteValuationRing.not_a_field _
  have hmapeq : ValuationInertia.intermediateCentre (AlgHom.fieldRange σ)
        (criticalNormalClosureSchurValuationSubring K hm hn)
        (criticalSchurNormalBase_algebraMap_mem K hm hn)
      = Ideal.map (criticalSheetIntegralClosureEquiv K hm hn σ :
          CriticalSchurSourceIntegralClosure K hm hn →+*
            integralClosure (CriticalSchurNormalBaseRing K hm hn) ↥(AlgHom.fieldRange σ))
        (criticalSchurSourceIntegralClosurePrime K hm hn) := by
    rw [← criticalSheetIntermediateCentre_comap K hm hn hplace]
    exact (Ideal.map_comap_of_surjective
      ((criticalSheetIntegralClosureEquiv K hm hn σ :
        CriticalSchurSourceIntegralClosure K hm hn →+*
          integralClosure (CriticalSchurNormalBaseRing K hm hn) ↥(AlgHom.fieldRange σ)))
      (criticalSheetIntegralClosureEquiv K hm hn σ).surjective _).symm
  have h1 := Ideal.ramificationIdx'_eq_ramificationIdx
    (IsLocalRing.maximalIdeal (CriticalSchurNormalBaseRing K hm hn))
    (ValuationInertia.intermediateCentre (AlgHom.fieldRange σ)
      (criticalNormalClosureSchurValuationSubring K hm hn)
      (criticalSchurNormalBase_algebraMap_mem K hm hn)) hp
  rw [← h1, hmapeq, ramificationIdx'_algEquiv]
  exact criticalSchur_source_ramificationIdx_eq_two K

end

end GaloisForLFunctions.HTGeometry

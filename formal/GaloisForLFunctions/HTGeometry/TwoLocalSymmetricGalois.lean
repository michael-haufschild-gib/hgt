import GaloisForLFunctions.HTGeometry.DirectionComparison
import GaloisForLFunctions.HTGeometry.AdjoinRootFamilyTransport
import GaloisForLFunctions.HTGeometry.GalBaseDescent

/-!
# The transverse family has the full symmetric Galois group

Every hypercube edge swap is realized on the canonical labelled root family: the swaps of one
direction are realized on that direction's radical field, and the deformation of the remaining
couplings carries them to the canonical labelling, which is the same for every direction.  The edge
swaps generate the full symmetric group on the hypercube, so the Galois group of the universal
characteristic polynomial is symmetric.

## Main results

* `card_gal_universalCharpoly` — **the Galois group of the universal transverse characteristic
  polynomial over the rational function field is the full symmetric group on the hypercube.**
-/

open Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type} [Field A] {m : ℕ}

/-- **The universal transverse characteristic polynomial has symmetric Galois group.** -/
theorem card_gal_universalCharpoly (h2 : (2 : A) ≠ 0)
    {d : (Fin (m + 1) → Bool) → A} (hd : Function.Injective d)
    (hδinj : ∀ i, Function.Injective (detuning d i))
    (hδne : ∀ i z z', detuning d i z ≠ -detuning d i z') :
    Nat.card (((universalCharpoly A (m + 1) d).map
      (algebraMap (MvPolynomial (Fin (m + 1)) A)
        (FractionRing (MvPolynomial (Fin (m + 1)) A)))).Gal) = (2 ^ (m + 1)).factorial := by
  classical
  haveI : IsDomain (MvPowerSeries (Fin (m + 1)) A) := isDomain_mvPowerSeries A _
  have hcoeinj : Function.Injective
      (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin (m + 1)) (R := A)) :=
    MvPolynomial.coe_injective (σ := Fin (m + 1)) (R := A)
  letI : Algebra (FractionRing (MvPolynomial (Fin (m + 1)) A))
      (FractionRing (MvPowerSeries (Fin (m + 1)) A)) := (fracLift hcoeinj).toAlgebra
  obtain ⟨Θ, hΘ, hconst⟩ := exists_canonicalRootFamily d hd
  set θ : (Fin (m + 1) → Bool) → FractionRing (MvPowerSeries (Fin (m + 1)) A) :=
    fun x => algebraMap (MvPowerSeries (Fin (m + 1)) A)
      (FractionRing (MvPowerSeries (Fin (m + 1)) A)) (Θ x) with hθdef
  have hΘinj : Function.Injective Θ := by
    intro x y hxy
    have := congrArg (MvPowerSeries.constantCoeff (σ := Fin (m + 1)) (R := A)) hxy
    rw [hconst, hconst] at this
    exact hd this
  have hθinj : Function.Injective θ :=
    Function.Injective.comp
      (IsFractionRing.injective (MvPowerSeries (Fin (m + 1)) A)
        (FractionRing (MvPowerSeries (Fin (m + 1)) A))) hΘinj
  set E : IntermediateField (FractionRing (MvPolynomial (Fin (m + 1)) A))
      (FractionRing (MvPowerSeries (Fin (m + 1)) A)) :=
    IntermediateField.adjoin _ (Set.range θ) with hE
  set θE : (Fin (m + 1) → Bool) → ↥E :=
    fun x => ⟨θ x, IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩⟩ with hθE
  have hθEinj : Function.Injective θE := fun x y hxy => hθinj (congrArg Subtype.val hxy)
  set f : Polynomial (FractionRing (MvPolynomial (Fin (m + 1)) A)) :=
    (universalCharpoly A (m + 1) d).map
      (algebraMap (MvPolynomial (Fin (m + 1)) A)
        (FractionRing (MvPolynomial (Fin (m + 1)) A))) with hf
  have hbase : ∀ p : MvPolynomial (Fin (m + 1)) A,
      algebraMap (FractionRing (MvPolynomial (Fin (m + 1)) A))
          (FractionRing (MvPowerSeries (Fin (m + 1)) A))
          (algebraMap (MvPolynomial (Fin (m + 1)) A)
            (FractionRing (MvPolynomial (Fin (m + 1)) A)) p)
        = algebraMap (MvPowerSeries (Fin (m + 1)) A)
            (FractionRing (MvPowerSeries (Fin (m + 1)) A))
            (MvPolynomial.coeToMvPowerSeries.ringHom p) := fun p => fracLift_algebraMap hcoeinj p
  have hsplitΩ : f.map (algebraMap (FractionRing (MvPolynomial (Fin (m + 1)) A))
      (FractionRing (MvPowerSeries (Fin (m + 1)) A))) = ∏ x, (X - C (θ x)) := by
    rw [hf, Polynomial.map_map,
      show ((algebraMap (FractionRing (MvPolynomial (Fin (m + 1)) A))
            (FractionRing (MvPowerSeries (Fin (m + 1)) A))).comp
          (algebraMap (MvPolynomial (Fin (m + 1)) A)
            (FractionRing (MvPolynomial (Fin (m + 1)) A))))
        = (algebraMap (MvPowerSeries (Fin (m + 1)) A)
            (FractionRing (MvPowerSeries (Fin (m + 1)) A))).comp
          (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin (m + 1)) (R := A)) from
        RingHom.ext hbase, ← Polynomial.map_map,
      show (universalCharpoly A (m + 1) d).map
          (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin (m + 1)) (R := A))
        = universalCharpolySeries d from rfl, hΘ, Polynomial.map_prod]
    exact Finset.prod_congr rfl fun x _ => by
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have hsplit : f.map (algebraMap (FractionRing (MvPolynomial (Fin (m + 1)) A)) ↥E)
      = ∏ x, (X - C (θE x)) := by
    refine Polynomial.map_injective (E.val : ↥E →+* FractionRing (MvPowerSeries (Fin (m + 1)) A))
      (fun a b hab => Subtype.ext hab) ?_
    rw [Polynomial.map_map,
      show ((E.val : ↥E →+* FractionRing (MvPowerSeries (Fin (m + 1)) A)).comp
          (algebraMap (FractionRing (MvPolynomial (Fin (m + 1)) A)) ↥E))
        = algebraMap (FractionRing (MvPolynomial (Fin (m + 1)) A))
            (FractionRing (MvPowerSeries (Fin (m + 1)) A)) from
        RingHom.ext fun k => E.val.commutes k, hsplitΩ, Polynomial.map_prod]
    exact (Finset.prod_congr rfl fun x _ => by
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      rfl).symm
  haveI : Fact ((f.map (algebraMap (FractionRing (MvPolynomial (Fin (m + 1)) A)) ↥E)).Splits) := by
    refine ⟨?_⟩
    rw [hsplit]
    exact Polynomial.Splits.prod fun x _ => Polynomial.Splits.X_sub_C _
  refine card_gal_eq_factorial_of_cubeSwaps f hθEinj hsplit ?_
  intro x i
  have hδ : ∀ z, detuning d i z ≠ 0 := fun z hz => hδne i z z (by rw [hz, neg_zero])
  haveI : IsDomain (MvPowerSeries {j : Fin (m + 1) // j ≠ i} ↥(directionField h2 hδ)) :=
    isDomain_mvPowerSeries _ _
  haveI : IsDomain (MvPowerSeries {j : Fin (m + 1) // j ≠ i} (LaurentSeries A)) :=
    isDomain_mvPowerSeries _ _
  obtain ⟨Θ', hΘ', hconst'⟩ := exists_deformationRootFamily h2 hδ hd
  obtain ⟨σL, hσL⟩ := exists_algEquiv_swap_dirRootField h2 hδ (hδinj i) (hδne i) x
  have hcompinj : Function.Injective
      ((dirCompare A i).comp
        (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin (m + 1)) (R := A))) := by
    intro p q hpq
    exact hcoeinj (dirCompare_injective (A := A) (i := i) hpq)
  letI : Algebra (FractionRing (MvPolynomial (Fin (m + 1)) A))
      (FractionRing (MvPowerSeries {j : Fin (m + 1) // j ≠ i} ↥(directionField h2 hδ))) :=
    (fracLift (dirDeform_injective h2 hδ)).toAlgebra
  letI : Algebra (FractionRing (MvPolynomial (Fin (m + 1)) A))
      (FractionRing (MvPowerSeries {j : Fin (m + 1) // j ≠ i} (LaurentSeries A))) :=
    (fracLift hcompinj).toAlgebra
  have halgR : ∀ p : MvPolynomial (Fin (m + 1)) A,
      algebraMap (FractionRing (MvPolynomial (Fin (m + 1)) A))
          (FractionRing (MvPowerSeries {j : Fin (m + 1) // j ≠ i} (LaurentSeries A)))
          (algebraMap (MvPolynomial (Fin (m + 1)) A) _ p)
        = algebraMap (MvPowerSeries {j : Fin (m + 1) // j ≠ i} (LaurentSeries A)) _
            ((dirCompare A i).comp
              (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin (m + 1)) (R := A)) p) :=
    fun p => fracLift_algebraMap hcompinj p
  have halgS : ∀ p : MvPolynomial (Fin (m + 1)) A,
      algebraMap (FractionRing (MvPolynomial (Fin (m + 1)) A))
          (FractionRing (MvPowerSeries {j : Fin (m + 1) // j ≠ i} ↥(directionField h2 hδ)))
          (algebraMap (MvPolynomial (Fin (m + 1)) A) _ p)
        = algebraMap (MvPowerSeries {j : Fin (m + 1) // j ≠ i} ↥(directionField h2 hδ)) _
            (dirDeform h2 hδ p) :=
    fun p => fracLift_algebraMap (dirDeform_injective h2 hδ) p
  have hβcomm : ∀ k, fracLift (dirCompare_injective (A := A) (i := i))
      (algebraMap (FractionRing (MvPolynomial (Fin (m + 1)) A))
        (FractionRing (MvPowerSeries (Fin (m + 1)) A)) k)
      = algebraMap (FractionRing (MvPolynomial (Fin (m + 1)) A))
          (FractionRing (MvPowerSeries {j : Fin (m + 1) // j ≠ i} (LaurentSeries A))) k := by
    have hcomp := fractionRing_ringHom_ext
      ((fracLift (dirCompare_injective (A := A) (i := i))).comp
        (algebraMap (FractionRing (MvPolynomial (Fin (m + 1)) A))
          (FractionRing (MvPowerSeries (Fin (m + 1)) A))))
      (algebraMap (FractionRing (MvPolynomial (Fin (m + 1)) A))
        (FractionRing (MvPowerSeries {j : Fin (m + 1) // j ≠ i} (LaurentSeries A))))
      (fun p => by
        rw [RingHom.comp_apply, hbase p,
          fracLift_algebraMap (dirCompare_injective (A := A) (i := i))
            (MvPolynomial.coeToMvPowerSeries.ringHom p), halgR p]
        rfl)
    exact fun k => RingHom.congr_fun hcomp k
  have hγcomm : ∀ k, fracLift (dirInclude_injective h2 hδ)
      (algebraMap (FractionRing (MvPolynomial (Fin (m + 1)) A))
        (FractionRing (MvPowerSeries {j : Fin (m + 1) // j ≠ i} ↥(directionField h2 hδ))) k)
      = algebraMap (FractionRing (MvPolynomial (Fin (m + 1)) A))
          (FractionRing (MvPowerSeries {j : Fin (m + 1) // j ≠ i} (LaurentSeries A))) k := by
    have hcomp := fractionRing_ringHom_ext
      ((fracLift (dirInclude_injective h2 hδ)).comp
        (algebraMap (FractionRing (MvPolynomial (Fin (m + 1)) A))
          (FractionRing (MvPowerSeries {j : Fin (m + 1) // j ≠ i} ↥(directionField h2 hδ)))))
      (algebraMap (FractionRing (MvPolynomial (Fin (m + 1)) A))
        (FractionRing (MvPowerSeries {j : Fin (m + 1) // j ≠ i} (LaurentSeries A))))
      (fun p => by
        rw [RingHom.comp_apply, halgS p,
          fracLift_algebraMap (dirInclude_injective h2 hδ) (dirDeform h2 hδ p), halgR p]
        congr 1
        exact RingHom.congr_fun (dirInclude_comp_dirDeform h2 hδ) p)
    exact fun k => RingHom.congr_fun hcomp k
  have hσcomm : ∀ k, fracRingEquiv (mvPsRingEquiv (σ := {j : Fin (m + 1) // j ≠ i}) σL.toRingEquiv)
      (algebraMap (FractionRing (MvPolynomial (Fin (m + 1)) A))
        (FractionRing (MvPowerSeries {j : Fin (m + 1) // j ≠ i} ↥(directionField h2 hδ))) k)
      = algebraMap (FractionRing (MvPolynomial (Fin (m + 1)) A))
          (FractionRing (MvPowerSeries {j : Fin (m + 1) // j ≠ i} ↥(directionField h2 hδ))) k := by
    have hcomp := fractionRing_ringHom_ext
      (((fracRingEquiv (mvPsRingEquiv (σ := {j : Fin (m + 1) // j ≠ i}) σL.toRingEquiv)) :
          FractionRing (MvPowerSeries {j : Fin (m + 1) // j ≠ i} ↥(directionField h2 hδ)) →+*
          FractionRing (MvPowerSeries {j : Fin (m + 1) // j ≠ i} ↥(directionField h2 hδ))).comp
        (algebraMap (FractionRing (MvPolynomial (Fin (m + 1)) A))
          (FractionRing (MvPowerSeries {j : Fin (m + 1) // j ≠ i} ↥(directionField h2 hδ)))))
      (algebraMap (FractionRing (MvPolynomial (Fin (m + 1)) A))
        (FractionRing (MvPowerSeries {j : Fin (m + 1) // j ≠ i} ↥(directionField h2 hδ))))
      (fun p => by
        rw [RingHom.comp_apply, halgS p]
        show fracRingEquiv (mvPsRingEquiv (σ := {j : Fin (m + 1) // j ≠ i}) σL.toRingEquiv)
          (algebraMap (MvPowerSeries {j : Fin (m + 1) // j ≠ i} ↥(directionField h2 hδ)) _
            (dirDeform h2 hδ p)) = _
        rw [fracRingEquiv_algebraMap, mvPsRingEquiv_apply]
        congr 1
        exact RingHom.congr_fun (map_comp_dirDeform h2 hδ σL) p)
    exact fun k => RingHom.congr_fun hcomp k
  set β : FractionRing (MvPowerSeries (Fin (m + 1)) A) →ₐ[FractionRing
      (MvPolynomial (Fin (m + 1)) A)]
      FractionRing (MvPowerSeries {j : Fin (m + 1) // j ≠ i} (LaurentSeries A)) :=
    { fracLift (dirCompare_injective (A := A) (i := i)) with commutes' := hβcomm } with hβ
  set γ : FractionRing (MvPowerSeries {j : Fin (m + 1) // j ≠ i} ↥(directionField h2 hδ)) →ₐ[
      FractionRing (MvPolynomial (Fin (m + 1)) A)]
      FractionRing (MvPowerSeries {j : Fin (m + 1) // j ≠ i} (LaurentSeries A)) :=
    { fracLift (dirInclude_injective h2 hδ) with commutes' := hγcomm } with hγ
  set σ' : FractionRing (MvPowerSeries {j : Fin (m + 1) // j ≠ i} ↥(directionField h2 hδ)) ≃ₐ[
      FractionRing (MvPolynomial (Fin (m + 1)) A)]
      FractionRing (MvPowerSeries {j : Fin (m + 1) // j ≠ i} ↥(directionField h2 hδ)) :=
    { fracRingEquiv (mvPsRingEquiv (σ := {j : Fin (m + 1) // j ≠ i}) σL.toRingEquiv) with commutes' := hσcomm } with hσ'def
  set θ' : (Fin (m + 1) → Bool) →
      FractionRing (MvPowerSeries {j : Fin (m + 1) // j ≠ i} ↥(directionField h2 hδ)) :=
    fun y => algebraMap (MvPowerSeries {j : Fin (m + 1) // j ≠ i} ↥(directionField h2 hδ)) _
      (Θ' y) with hθ'def
  have hmatch : ∀ y, β (θ y) = γ (θ' y) := by
    intro y
    show fracLift (dirCompare_injective (A := A) (i := i)) (θ y)
      = fracLift (dirInclude_injective h2 hδ) (θ' y)
    rw [hθdef, hθ'def, fracLift_algebraMap, fracLift_algebraMap,
      dirCompare_canonicalRoot h2 hδ hd hΘ hconst hΘ' hconst' y]
  have hperm : ∀ y, σ' (θ' y) = θ' (Equiv.swap x (boolToggle x i) y) := by
    intro y
    show fracRingEquiv (mvPsRingEquiv (σ := {j : Fin (m + 1) // j ≠ i}) σL.toRingEquiv) (θ' y) = θ' _
    rw [hθ'def, fracRingEquiv_algebraMap, mvPsRingEquiv_apply]
    congr 1
    exact map_mvRootFamily_of_perm hΘ' hconst' (dirRootField_injective h2 hδ hd)
      σL.toRingEquiv
      (by rw [Polynomial.map_map, map_comp_dirDeform h2 hδ σL])
      (Equiv.swap x (boolToggle x i)) hσL y
  obtain ⟨σ, hσ⟩ := exists_algEquiv_adjoin_of_matching β γ θ θ' hmatch σ' hperm
  exact ⟨σ, fun y => hσ y⟩

end

end GaloisForLFunctions.HTGeometry

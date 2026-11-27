import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedTypeReduction
import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.PrimeToInertiaRoots
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TeichmullerLabelDatum

/-! A split inertia polynomial with Teichmüller roots reduces coefficientwise
to the product over their prime-to-residue-characteristic parts. -/

noncomputable section

open IsLocalRing Polynomial
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.CyclotomicNorms
open WindowedLandauTheory.MainNotions.N

namespace WindowedLandauTheory.NormalizedTypes

/-- Reducing a polynomial split by Teichmüller lifts keeps all root
multiplicities. The primary part at the residue characteristic disappears. -/
theorem map_eq_prod_reduceLift {R K : Type} [CommRing R] [Field K]
    {g ℓ : ℕ} [Fact g.Prime] [Fact ℓ.Prime]
    (B : ValuationSubring K) (κ : ResidueField B ≃+* Fbar ℓ) (t : Fbar g →* K)
    (j : R →+* B) (P : R[X]) (S : Multiset (Fbar g)) (hS : ∀ x ∈ S, x ≠ 0)
    (hP : P.map (B.subtype.comp j) = (S.map fun x => X - C (t x)).prod) :
    P.map ((κ.toRingHom.comp (residue B)).comp j) =
      (S.map fun x => X - C (GlobalTheory.TeichPlace.reduceLift B κ t (primeToPart ℓ x))).prod := by
  let z (x : Fbar g) : B := ⟨t x, GlobalTheory.TeichPlace.lift_mem B t x⟩
  have he : P.map j = (S.map fun x => X - C (z x)).prod := by
    apply Polynomial.map_injective B.subtype Subtype.val_injective
    rw [Polynomial.map_map, hP, Polynomial.map_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro x _
    simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  rw [← Polynomial.map_map, he, Polynomial.map_multiset_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro x hx
  simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  congr 2
  change κ (residue B (z x)) = redThrough B κ (t (primeToPart ℓ x))
  rw [redThrough_primeToPart B κ t x (fbar_isOfFinOrder (hS x hx)).orderOf_pos, redThrough,
    dif_pos (GlobalTheory.TeichPlace.lift_mem B t x)]

variable {D : D7} {jE : D.host.E →+* AlgebraicClosure ℚ}

/-- At a row's coefficient place the reduced Teichmüller roots are read by
the normalized residue maps. -/
theorem map_residue_eq_prod_primeToPart (T : NormalizedTypesCompatibility D jE)
    (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (P : (D.nd.O i)[X])
    (S : Multiset (Fb (D.host.g k) (D.host.g_prime k))) (hS : ∀ x ∈ S, x ≠ 0)
    (hP : P.map (iotaO D.nd D.naut i) = (S.map fun x => X - C (D.ntypes.teichC k x)).prod) :
    P.map ((D.naut.kFbar i).comp (residue (D.nd.O i))) =
      (S.map fun x => X - C (fbCast (D.nd.w_l i)
        (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
          (D.ntypes.iota k v (D.nd.w i)
            (primeToPart (D.what₂.places.resChar (D.nd.w i)) x)))).prod := by
  let ℓ := D.what₂.places.resChar (D.nd.w i)
  letI : Fact ℓ.Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
  letI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨B, κ, hcompat, hι⟩ := T.iota_loc i
  let c := fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
  let j := (iotaO D.nd D.naut i).codRestrict B.toSubring fun y => (hcompat y).choose
  let r := κ.toRingHom.comp (residue B)
  have hcomm : c.toRingHom.comp (r.comp j) = (D.naut.kFbar i).comp (residue (D.nd.O i)) := by
    ext y
    exact (hcompat y).choose_spec
  have he := map_eq_prod_reduceLift B κ (D.ntypes.teichC k) j P S hS hP
  rw [← hcomm, ← Polynomial.map_map, he, Polynomial.map_multiset_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro x _
  simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  congr 2
  rw [hι]
  rfl

end WindowedLandauTheory.NormalizedTypes

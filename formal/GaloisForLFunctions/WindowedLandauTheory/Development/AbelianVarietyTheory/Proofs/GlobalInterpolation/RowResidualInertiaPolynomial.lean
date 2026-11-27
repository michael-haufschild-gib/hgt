import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ResidualInertiaPolynomial
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsobaricRank

/-! The local inertia characteristic-polynomial identities descend to the
residual representation at the row's coefficient place. -/

noncomputable section

open IsLocalRing Polynomial Module
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.ConjugateSelfDual
open WindowedLandauTheory.CyclotomicNorms WindowedLandauTheory.MainNotions.N

namespace WindowedLandauTheory.NormalizedTypes

variable {D : D7} {jE : D.host.E →+* AlgebraicClosure ℚ}
variable {i : D.nd.Loc} {σ : D.what₂.FT} {P : List (Part D.naut.CG)}
variable {ρ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* GL (Fin D.R.r) (D.nd.O i)}

/-- The global row's tame inertia roots are the reductions of the
Teichmüller lifts of its isobaric label. -/
theorem charpoly_rbar_tg_of_local_charpoly (T : NormalizedTypesCompatibility D jE)
    (hP : HasParamW D.nd D.naut i σ P) (hρ : IsRepOfSig D.nd D.naut i P ρ)
    (hg : D.nd.goodRow σ) (k : Fin 2) (v : D.nd.PlG k)
    (hI : ((ρ (D.ntypes.tg k v) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly.map
          (iotaO D.nd D.naut i) =
      D.naut.inePol (isoLoc D.nd D.naut P (D.naut.plGw k v)) (D.ntypes.tg k v)) :
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ((D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) : GL _ _) :
      Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly =
      ((rootsBar (D.nd.lab k σ v)).map fun x => X - C
        (D.ntypes.iota k v (D.nd.w i) (primeToPart (D.what₂.places.resChar (D.nd.w i)) x))).prod := by
  letI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  let L := isoLoc D.nd D.naut P (D.naut.plGw k v)
  let S := rootsBar (D.nd.lab k σ v)
  let M := (ρ (D.ntypes.tg k v) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly
  have hl := items₂_isoLoc_eq_lab_of_hasParamW D i σ P hP k v
  have hdim : D.naut.lpDim L = D.R.r := (lpDim_isoLoc D.nd D.naut P _).trans hP.2.1
  have hdegree : (D.naut.items₂ k (D.naut.plGw k v) L).natDegree = D.naut.lpDim L := by
    change (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut P (D.naut.plGw k v))).natDegree =
      D.naut.lpDim L
    rw [hl, hdim]
    exact (D.nd.lab_monic k σ v).2
  have hp : M.map (iotaO D.nd D.naut i) = (S.map fun x => X - C (D.ntypes.teichC k x)).prod := by
    rw [show M.map (iotaO D.nd D.naut i) = D.naut.inePol L (D.ntypes.tg k v) from hI,
      D.ntypes.inertiaCharpoly_type k v L hdegree]
    change (((rootsBar (D.naut.items₂ k (D.naut.plGw k v)
      (isoLoc D.nd D.naut P (D.naut.plGw k v)))).map fun x => X - C (D.ntypes.teichC k x)).prod) = _
    rw [hl]
  have hnz (x : Fbar (D.host.g k)) (hx : x ∈ S) : x ≠ 0 := by
    obtain ⟨hm, hsq, -⟩ := (hg k).1
    exact CycleTypeFiniteOrder.ne_zero_of_mem
      (⟨(hm v).1, (hm v).2.1, (hm v).2.2, hsq v⟩ :
        CycleTypeFiniteOrder.GoodPoly D.R.r (D.nd.lab k σ v)) hx
  let e := fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
  apply Polynomial.map_injective e.toRingHom e.injective
  have hcp := (D.rbar_tie i σ P ρ hP hρ).2 (D.ntypes.tg k v)
  rw [hcp, map_residue_eq_prod_primeToPart T i k v M S hnz hp,
    Polynomial.map_multiset_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro x _
  simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rfl

/-- Wild inertia that has characteristic polynomial `(X - 1)^r` in the
local characteristic-zero model has the same polynomial after reduction. -/
theorem charpoly_rbar_eq_unipotent_of_local_charpoly
    (hP : HasParamW D.nd D.naut i σ P) (hρ : IsRepOfSig D.nd D.naut i P ρ)
    (s : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om))
    (hI : (ρ s : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly.map
      (iotaO D.nd D.naut i) = (X - 1) ^ D.R.r) :
    (D.ntypes.rbar σ (D.nd.w i) s).val.charpoly =
      (X - 1) ^ D.R.r := by
  have hj : Function.Injective (iotaO D.nd D.naut i) :=
    (D.naut.iotaQC i).injective.comp ((D.naut.iotaQ i).injective.comp
      (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))))
  have hI' : (ρ s : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly = (X - 1) ^ D.R.r := by
    apply Polynomial.map_injective _ hj
    rw [hI, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one]
  let e := fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
  apply Polynomial.map_injective e.toRingHom e.injective
  rw [(D.rbar_tie i σ P ρ hP hρ).2 s, hI']
  simp only [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one]

end WindowedLandauTheory.NormalizedTypes

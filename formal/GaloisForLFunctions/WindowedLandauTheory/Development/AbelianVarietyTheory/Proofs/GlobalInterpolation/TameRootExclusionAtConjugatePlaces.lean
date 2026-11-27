import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjugateInertiaComparison
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DesignatedTameRootExclusion
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TameGeneratorRootExclusion
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WildInertiaSubgroup

/-! Conjugate self-duality transports the character-root exclusion from
the designated places to their conjugates. The argument uses generation
in the finite tame image of the representation and character. -/

noncomputable section

open NumberField IsDedekindDomain IsLocalRing Polynomial
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.ConjugateSelfDual
open WindowedLandauTheory.MainNotions.N WindowedLandauTheory.CyclotomicNorms
open ReciprocityTheory.Gal GlobalTheory.ConjugateInertia GlobalTheory.TameKummer

namespace WindowedLandauTheory.NormalizedTypes

variable (D : D7) (i : D.nd.Loc)
local notation "Γ" => (D.nd.Om ≃ₐ[D.host.E] D.nd.Om)
local notation "ℓ" => D.nd.l i

/-- Conjugating the inverse of a tame generator transfers the original
residual characteristic polynomial and character value to the opposite place. -/
private theorem conjugate_inverse_values (hF : SplitFrobeniusDense D)
    {π : D.naut.CG D.R.r} (hπ : D.naut.csd π)
    (r : Γ →* GL (Fin D.R.r) (D.nd.O i)) (hr : IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] r)
    (w : PlE D.host) (hw : w ∉ placesOver D.host.E ℓ)
    {s : Γ} (hs : s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) (g : Γ) :
    let ρ := mapRep ((D.naut.kFbar i).comp (residue (D.nd.O i))) r
    let t := g * cConj D s⁻¹ * g⁻¹
    (ρ t).val.charpoly = (ρ s).val.charpoly ∧ chiBar D i t = chiBar D i s := by
  let red := (D.naut.kFbar i).comp (residue (D.nd.O i))
  let ρ := mapRep red r
  let χ := chiBar D i
  let u := cConj D s⁻¹
  have hi := conj_inertia D hF i π r hπ hr w _ hw (D.nd.plOm.2 w) s⁻¹
    ((Ine (F := D.host.E) (D.nd.plOm.1 w)).inv_mem hs)
  change (ρ (g * u * g⁻¹)).val.charpoly = (ρ s).val.charpoly ∧ χ (g * u * g⁻¹) = χ s
  constructor
  · have he : (ρ u).val.charpoly = (ρ s).val.charpoly := by
      rw [show (ρ u).val.charpoly = (r u).val.charpoly.map red from charpoly_mapRep red r u,
        show (ρ s).val.charpoly = (r s).val.charpoly.map red from charpoly_mapRep red r s]
      simpa only [u, inv_inv] using congrArg (Polynomial.map red) hi.1
    rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
    exact (Matrix.charpoly_units_conj (ρ g) (ρ u).val).trans he
  · rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    change (Units.map red.toMonoidHom) (D.nd.chi i 1 (cConj D s⁻¹)) =
      (Units.map red.toMonoidHom) (D.nd.chi i 1 s)
    rw [hi.2, map_inv (D.nd.chi i 1), inv_inv]

/-- An exclusion at one designated tame element suffices for all tame
generators at the conjugate place. -/
theorem not_isRoot_at_conjugate_place (hF : SplitFrobeniusDense D)
    {π : D.naut.CG D.R.r} (hπ : D.naut.csd π)
    (r : Γ →* GL (Fin D.R.r) (D.nd.O i)) (hr : IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] r)
    (k : Fin 2) (v : D.nd.PlG k) (w : PlE D.host)
    (hconj : IsConjPl D.host (D.naut.plGw k v) w) (hw : w ∉ placesOver D.host.E ℓ)
    {s : Γ} (hs : TameGenAt (D.nd.plOm.1 w) s)
    (hW : ∀ u, (∀ y : D.nd.Om, y ≠ 0 →
      (D.nd.plOm.1 (D.naut.plGw k v)).valuation (u y / y - 1) < 1) →
      (mapRep ((D.naut.kFbar i).comp (residue (D.nd.O i))) r) u = 1 ∧ chiBar D i u = 1)
    (hex : ¬ ((mapRep ((D.naut.kFbar i).comp (residue (D.nd.O i))) r) (D.ntypes.tg k v)).val.charpoly.IsRoot
      (chiBar D i (D.ntypes.tg k v) : Fbar ℓ)) :
    ¬ ((mapRep ((D.naut.kFbar i).comp (residue (D.nd.O i))) r) s).val.charpoly.IsRoot
      (chiBar D i s : Fbar ℓ) := by
  let B := D.nd.plOm.1 (D.naut.plGw k v)
  obtain ⟨g, hg⟩ := exists_tameGenAt_conj D (isConjPl_symm D hconj) (tameGenAt_inv hs)
  have hrOpen := isOpen_ker_of_ideal_adic r hr.1 (D.nd.O_adic i) (D.naut.kFbar i)
  have h := not_isRoot_of_tameGen B _ (chiBar D i) hrOpen (isOpen_ker_chiBar D i) hW
    (D.ntypes.tg_mem k v) hg hex
  obtain ⟨hpoly, hχ⟩ := conjugate_inverse_values D i hF hπ r hr w hw hs.1 g
  rwa [hpoly, hχ] at h

/-- Local characteristic-polynomial matching and trivial wild character
supply the tame conditions for a good cuspidal signature. -/
theorem residual_tame_conditions_of_local_matching {jE : D.host.E →+* AlgebraicClosure ℚ}
    (T : NormalizedTypesCompatibility D jE) (hF : SplitFrobeniusDense D)
    {π : D.naut.CG D.R.r} (hπ : D.naut.csd π)
    (r : Γ →* GL (Fin D.R.r) (D.nd.O i)) (hr : IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] r)
    (hg : goodSig D.nd D.naut [⟨D.R.r, π, 1⟩])
    (hfull : ∀ (k : Fin 2) (v : D.nd.PlG k),
      let L := isoLoc D.nd D.naut [⟨D.R.r, π, 1⟩] (D.naut.plGw k v)
      (D.naut.items₂ k _ L).natDegree = D.naut.lpDim L)
    (hI : ∀ (k : Fin 2), ℓ ≠ D.host.g k → ∀ (v : D.nd.PlG k),
      let w := D.naut.plGw k v
      ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), (r s).val.charpoly.map (iotaO D.nd D.naut i) =
        D.naut.inePol (isoLoc D.nd D.naut [⟨D.R.r, π, 1⟩] w) s)
    (hW : ∀ (k : Fin 2), ℓ ≠ D.host.g k → ∀ (v : D.nd.PlG k),
      let w := D.naut.plGw k v
      ∀ s ∈ wildInertia (E := D.host.E) (D.nd.plOm.1 w),
        D.naut.inePol (isoLoc D.nd D.naut [⟨D.R.r, π, 1⟩] w) s = (X - 1) ^ D.R.r ∧
        D.nd.chi i 1 s = 1)
    (haway : ∀ (k : Fin 2), ℓ ≠ D.host.g k → ∀ w ∈ placesOver D.host.E (D.host.g k),
      w ∉ placesOver D.host.E ℓ) :
    (∀ (k : Fin 2), ℓ ≠ D.host.g k → ∀ v, ResidualTameLabels D i [⟨D.R.r, π, 1⟩] r k v) ∧
      ResidualTameRootExclusion D i r := by
  refine ⟨?_, ?_⟩
  · intro k hk v
    exact tame_fixed_of_local_charpoly D i _ T r hr hg k hk v (hfull k v) (hI k hk v)
      (fun s _ h => (hW k hk v s h).1)
  · intro k hk w hw hs
    obtain ⟨v, rfl | hc⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
    · rw [D.ntypes.heckeLoc_gamma_places]
      exact not_isRoot_at_designated_place D i T _ hg r k hk v (hfull k v)
        (hI k hk v _ (D.ntypes.tg_mem k v))
    · have hgen : TameGenAt (D.nd.plOm.1 w) (D.nd.gam0 i w) :=
        ⟨D.nd.locNd_chebotarevPlace_mem i w, hs⟩
      refine not_isRoot_at_conjugate_place D i hF hπ r hr k v w hc (haway k hk w hw) hgen
        (fun s hs' => ?_) (not_isRoot_at_designated_place D i T _ hg r k hk v (hfull k v)
          (hI k hk v _ (D.ntypes.tg_mem k v)))
      have hwi : s ∈ wildInertia (E := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)) := hs'
      have hi := wildInertia_le_inertia _ hwi
      obtain ⟨hp, hχ⟩ := hW k hk v s hwi
      refine ⟨residual_eq_one_of_wild_charpoly D i r hr.1 k hk v hs' ((hI k hk v s hi).trans hp), ?_⟩
      change Units.map _ (D.nd.chi i 1 s) = 1
      rw [hχ, map_one]

end WindowedLandauTheory.NormalizedTypes

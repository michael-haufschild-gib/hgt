import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Index

/-! Restriction from a compositum over a base change of smaller degree
surjects onto an extension of prime degree. The index of the image
divides both degrees. -/

noncomputable section

open Module

namespace GlobalTheory.Reciprocity

variable (K A B L : Type*) [Field K] [Field A] [Field B] [Field L]
  [Algebra K A] [Algebra K B] [Algebra K L] [Algebra A L] [Algebra B L]
  [IsScalarTower K A L] [IsScalarTower K B L]
  [IsGalois K A] [IsGalois K B] [IsGalois K L]
  [FiniteDimensional K A] [FiniteDimensional K B]

theorem surjective_restrictNormalHom_comp_restrictScalarsHom_of_prime_degree
    {p : ℕ} (hp : p.Prime) (hA : finrank K A = p) (hB : finrank K B < p) :
    Function.Surjective ((AlgEquiv.restrictNormalHom A : Gal(L/K) →* Gal(A/K)).comp
      (AlgEquiv.restrictScalarsHom K : Gal(L/B) →* Gal(L/K))) := by
  let j : Gal(L/B) →* Gal(L/K) := AlgEquiv.restrictScalarsHom K
  let f : Gal(L/K) →* Gal(A/K) := AlgEquiv.restrictNormalHom A
  let g : Gal(L/K) →* Gal(B/K) := AlgEquiv.restrictNormalHom B
  have hf : Function.Surjective f :=
    AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := A) (E := L)
  have hg : Function.Surjective g :=
    AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := B) (E := L)
  have hk : j.range = g.ker := by
    ext σ
    constructor
    · rintro ⟨τ, rfl⟩
      apply MonoidHom.mem_ker.mpr
      apply AlgEquiv.ext
      intro x
      apply (algebraMap B L).injective
      exact ((j τ).restrictNormal_commutes B x).trans (τ.commutes x)
    · intro hσ
      have hfix (x : B) : σ (algebraMap B L x) = algebraMap B L x := by
        calc
          σ (algebraMap B L x) = algebraMap B L (g σ x) := (σ.restrictNormal_commutes B x).symm
          _ = algebraMap B L x := congrArg (fun τ : Gal(B/K) => algebraMap B L (τ x))
            (show g σ = 1 from hσ)
      exact ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) hfix, rfl⟩
  have hi : g.ker.index = finrank K B :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hg).toEquiv).trans
      (IsGalois.card_aut_eq_finrank K B)
  have hd := (g.ker.index_map_dvd hf).trans (dvd_of_eq hi)
  have hd' := (g.ker.map f).index_dvd_card.trans
    (dvd_of_eq ((IsGalois.card_aut_eq_finrank K A).trans hA))
  have h1 : (g.ker.map f).index = 1 := ((Nat.dvd_prime hp).mp hd').resolve_right fun h => by
    rw [h] at hd
    exact hB.not_ge (Nat.le_of_dvd Module.finrank_pos hd)
  apply MonoidHom.range_eq_top.mp
  change (f.comp j).range = ⊤
  rw [MonoidHom.range_comp, hk, Subgroup.index_eq_one.mp h1]

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.surjective_restrictNormalHom_comp_restrictScalarsHom_of_prime_degree

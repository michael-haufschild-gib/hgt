import GaloisForLFunctions.HTGeometry.ApartmentUnnormalizedCycle
import GaloisForLFunctions.HTGeometry.ApartmentInterval

/-!
# The boundary of the star half of an apartment cycle is the cycle of the link

The chambers of an apartment whose ordering ends with a chosen frame vector are exactly those that
contain the coatom opposite it.  Their signed sum has, by the cancellation of all the other faces,
the boundary carried by the face that deletes that coatom — and that face is the chamber of the
restricted ordering, a chamber of the apartment of the remaining frame vectors inside the interval
below the coatom.

So the boundary of the star half of an apartment cycle is, up to the sign of the top place, the
apartment cycle one frame vector smaller, pushed into the interval.  The reindexing is by the
restriction of an ordering that fixes the last place, which preserves the sign because it is a
permutation of a subtype.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u

variable {ι : Type u}

/-! ## Permutations that fix the last place -/

section Perm

variable {n : ℕ}

/-- The places other than the last one. -/
def notLastEquiv (m : ℕ) : Fin m ≃ {x : Fin (m + 1) // x ≠ Fin.last m} where
  toFun j := ⟨j.castSucc, Fin.ne_of_lt (Fin.castSucc_lt_last j)⟩
  invFun x := x.1.castPred x.2
  left_inv _ := Fin.castPred_castSucc _
  right_inv _ := Subtype.ext (Fin.castSucc_castPred _ _)

theorem notLastEquiv_symm_apply (m : ℕ) (x : {x : Fin (m + 1) // x ≠ Fin.last m}) :
    (notLastEquiv m).symm x = (x : Fin (m + 1)).castPred x.2 := rfl

/-- A permutation fixing the last place preserves the other places. -/
theorem subtypePerm_cond {σ : Equiv.Perm (Fin (n + 3))}
    (hσ : σ (Fin.last (n + 2)) = Fin.last (n + 2)) :
    ∀ x : Fin (n + 3), (σ x ≠ Fin.last (n + 2)) ↔ (x ≠ Fin.last (n + 2)) := by
  intro x
  constructor
  · intro h hx
    exact h (hx ▸ hσ)
  · intro h hcon
    exact h (σ.injective (hcon.trans hσ.symm))

/-- **An ordering that ends with a chosen vector restricts to an ordering of the rest**, as a
permutation of the remaining places. -/
def restrictPerm {σ : Equiv.Perm (Fin (n + 3))} (hσ : σ (Fin.last (n + 2)) = Fin.last (n + 2)) :
    Equiv.Perm (Fin (n + 2)) :=
  (notLastEquiv (n + 2)).symm.permCongr (σ.subtypePerm (subtypePerm_cond hσ))

theorem restrictPerm_castSucc {σ : Equiv.Perm (Fin (n + 3))}
    (hσ : σ (Fin.last (n + 2)) = Fin.last (n + 2)) (j : Fin (n + 2)) :
    (restrictPerm hσ j).castSucc = σ j.castSucc := by
  rw [restrictPerm, Equiv.permCongr_apply, Equiv.symm_symm, notLastEquiv_symm_apply,
    Fin.castSucc_castPred]
  rfl

/-- **The restriction keeps the sign**: it is the same permutation, read on a subtype. -/
theorem sign_restrictPerm {σ : Equiv.Perm (Fin (n + 3))}
    (hσ : σ (Fin.last (n + 2)) = Fin.last (n + 2)) :
    Equiv.Perm.sign (restrictPerm hσ) = Equiv.Perm.sign σ := by
  have h := Equiv.Perm.ofSubtype_subtypePerm (p := fun x : Fin (n + 3) => x ≠ Fin.last (n + 2))
    (f := σ) (subtypePerm_cond hσ) (fun x hx hcon => hx (by rw [hcon, hσ]))
  rw [restrictPerm, Equiv.Perm.sign_permCongr, ← Equiv.Perm.sign_ofSubtype, h]

/-- An ordering of the other places, extended by the last one. -/
def extendPerm (τ : Equiv.Perm (Fin (n + 2))) : Equiv.Perm (Fin (n + 3)) :=
  Equiv.Perm.ofSubtype ((notLastEquiv (n + 2)).permCongr τ)

theorem extendPerm_last (τ : Equiv.Perm (Fin (n + 2))) :
    extendPerm τ (Fin.last (n + 2)) = Fin.last (n + 2) :=
  Equiv.Perm.ofSubtype_apply_of_not_mem ((notLastEquiv (n + 2)).permCongr τ) (fun h => h rfl)

theorem extendPerm_castSucc (τ : Equiv.Perm (Fin (n + 2))) (j : Fin (n + 2)) :
    extendPerm τ j.castSucc = (τ j).castSucc := by
  rw [extendPerm, Equiv.Perm.ofSubtype_apply_of_mem ((notLastEquiv (n + 2)).permCongr τ)
    (show j.castSucc ≠ Fin.last (n + 2) from Fin.ne_of_lt (Fin.castSucc_lt_last j)),
    Equiv.permCongr_apply]
  show ((notLastEquiv (n + 2)) (τ ((notLastEquiv (n + 2)).symm
    ⟨j.castSucc, Fin.ne_of_lt (Fin.castSucc_lt_last j)⟩)) : Fin (n + 3)) = (τ j).castSucc
  rw [notLastEquiv_symm_apply]
  simp only [Fin.castPred_castSucc]
  rfl

theorem restrictPerm_extendPerm (τ : Equiv.Perm (Fin (n + 2))) :
    restrictPerm (extendPerm_last τ) = τ := by
  refine Equiv.ext fun j => Fin.castSucc_injective _ ?_
  rw [restrictPerm_castSucc, extendPerm_castSucc]

theorem extendPerm_restrictPerm {σ : Equiv.Perm (Fin (n + 3))}
    (hσ : σ (Fin.last (n + 2)) = Fin.last (n + 2)) : extendPerm (restrictPerm hσ) = σ := by
  refine Equiv.ext fun x => ?_
  induction x using Fin.lastCases with
  | last => rw [extendPerm_last, hσ]
  | cast j => rw [extendPerm_castSucc, restrictPerm_castSucc]

end Perm

/-! ## The link of a coatom of an apartment -/

section Link

/-- The apartment of a subset of a frame, as a subposet of the whole apartment. -/
def properBelowIncl (S : Set ι) : properPart (Set ↥S) →o properPart (Set ι) where
  toFun T := ((properBelowSetOrderIso S).symm T : properPart (Set ι))
  monotone' _ _ h := (properBelowSetOrderIso S).symm.monotone h

/-- **The face of a chamber that deletes the top vertex is a chamber of the link.** -/
theorem delta_last_apartmentChainSimplex {n : ℕ} {a : ι} {e : Fin (n + 3) ≃ ι}
    (he : e (Fin.last (n + 2)) = a) :
    (nerve (properPart (Set ι))).δ (Fin.last (n + 1)) (apartmentChainSimplex e)
      = (orderHomNerveMap (properBelowIncl (Set.univ \ {a}))).app (op ⦋n⦌)
          (apartmentChainSimplex (restrictOrdering he)) := by
  refine nerve_simplex_ext fun j => ?_
  rw [delta_apartmentChainSimplex_obj]
  show chainOfOrdering e ((Fin.last (n + 1)).succAbove j)
    = properBelowIncl (Set.univ \ {a}) (chainOfOrdering (restrictOrdering he) j)
  rw [Fin.succAbove_last]
  exact (coe_properBelowSetOrderIso_symm_chainOfOrdering he j).symm

end Link

/-! ## The boundary of the star half -/

section Boundary

variable {C : Type u} [Category.{v} C] [Preadditive C] [Limits.HasCoproducts.{u} C]

/-- **The boundary of the star half of an apartment cycle is the apartment cycle of the link.**
All the faces but the one deleting the top vertex cancel in pairs, and the surviving faces are the
chambers of the apartment of the frame with the chosen vector removed. -/
theorem apartmentChainIn_star_comp_d_eq {n : ℕ} {a : ι} {e₀ : Fin (n + 3) ≃ ι}
    (he₀ : e₀ (Fin.last (n + 2)) = a) {X : SSet.{u}}
    (g : nerve (properPart (Set ι)) ⟶ X) (R : C) :
    apartmentChainIn e₀ g R (starOrderings n) ≫ (X.chainComplex R).d (n + 1) n
      = ((-1) ^ (n + 1) : ℤ) •
        apartmentChainIn (restrictOrdering he₀)
          (orderHomNerveMap (properBelowIncl (Set.univ \ {a})) ≫ g) R Finset.univ := by
  classical
  rw [apartmentChainIn_star_comp_d, apartmentChainIn, Finset.smul_sum]
  refine Finset.sum_bij' (fun σ hσ => restrictPerm (mem_starOrderings.1 hσ))
    (fun τ _ => extendPerm τ) (fun σ _ => Finset.mem_univ _)
    (fun τ _ => mem_starOrderings.2 (extendPerm_last τ))
    (fun σ hσ => extendPerm_restrictPerm _) (fun τ _ => restrictPerm_extendPerm τ)
    (fun σ hσ => ?_)
  have hσ' : (σ.trans e₀) (Fin.last (n + 2)) = a := by
    show e₀ (σ (Fin.last (n + 2))) = a
    rw [mem_starOrderings.1 hσ, he₀]
  have hord : restrictOrdering hσ'
      = (restrictPerm (mem_starOrderings.1 hσ)).trans (restrictOrdering he₀) := by
    refine Equiv.ext fun j => Subtype.ext ?_
    show (σ.trans e₀) j.castSucc = e₀ (restrictPerm (mem_starOrderings.1 hσ) j).castSucc
    rw [restrictPerm_castSucc]
    rfl
  rw [delta_last_apartmentChainSimplex hσ', hord, smul_smul,
    ← sign_restrictPerm (mem_starOrderings.1 hσ), mul_comm]
  rfl

end Boundary

end GaloisForLFunctions.HTGeometry

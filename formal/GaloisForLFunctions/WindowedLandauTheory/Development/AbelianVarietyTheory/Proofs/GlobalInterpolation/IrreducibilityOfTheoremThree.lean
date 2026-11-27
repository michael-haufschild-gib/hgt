import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedTypeReduction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibilityFromTrace

/-! The row representation inherits residual irreducibility and exclusion of the
auxiliary inertia root from the finite type data. -/

noncomputable section
open Polynomial
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.MainNotions.N
open WindowedLandauTheory.CyclotomicNorms WindowedLandauTheory.ConjugateSelfDual
open WindowedLandauTheory.MainNotions.ArithmeticCylinders
open GlobalTheory.BrauerNesbittIrr

namespace WindowedLandauTheory.MainNotions.SumRepresentations.At

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

/-- Irreducibility of the row residual representation and exclusion of the
rank-one character on the tame inertia generators. -/
def IrreducibilityParameter (N : NData R H what₂) (A : NAut N) : Prop :=
  ∀ i σ, what₂.isot (N.j i) σ ≠ ⊥ → N.goodRow σ → ∀ Sig, HasParamW N A i σ Sig →
    ∀ ρ, IsRepOfSig N A i Sig ρ →
      IrredOn (mapRep ((A.kFbar i).comp (IsLocalRing.residue (N.O i))) ρ) ⊤ ∧
      ∀ k, N.l i ≠ H.g k → ∀ v : N.PlG k, TameGen N (N.plOm.1 (A.plGw k v)) (N.gam0 i (A.plGw k v)) →
        ¬ (((mapRep ((A.kFbar i).comp (IsLocalRing.residue (N.O i))) ρ (N.gam0 i (A.plGw k v)) :
            GL _ _) : Matrix (Fin R.r) (Fin R.r) _).charpoly).IsRoot
          (A.kFbar i (IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i (A.plGw k v)))))

end WindowedLandauTheory.MainNotions.SumRepresentations.At

namespace WindowedLandauTheory.MainNotions.N

theorem charpoly_mapRep {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {a : ℕ}
    (f : A →+* B) (ρ : Γ →* GL (Fin a) A) (g : Γ) :
    ((mapRep f ρ g : GL _ _) : Matrix (Fin a) (Fin a) B).charpoly =
      (((ρ g : GL _ _) : Matrix (Fin a) (Fin a) A).charpoly).map f :=
  Matrix.charpoly_map _ f

theorem irredOn_fbCast {Γ : Type} [Group Γ] {p q : ℕ} (h : p = q) (hp : p.Prime) (hq : q.Prime)
    {a : ℕ} (ρ : Γ →* GL (Fin a) (Fb p hp)) (hρ : @IrredOn a p ⟨hp⟩ Γ _ ρ ⊤) :
    @IrredOn a q ⟨hq⟩ Γ _ (mapRep (fbCast h hp hq).toRingHom ρ) ⊤ := by
  subst h
  have e : mapRep (fbCast rfl hp hq).toRingHom ρ = ρ := by
    ext g i j
    rfl
  rw [e]
  exact hρ

end WindowedLandauTheory.MainNotions.N

namespace WindowedLandauTheory.NormalizedTypes

open WindowedLandauTheory.MainNotions.SumRepresentations.At

theorem irreducibility_of_theorem_three (D : D7) {jE : D.host.E →+* AlgebraicClosure ℚ}
    (T : NormalizedTypesCompatibility D jE) (h33 : PointsLemma D) :
    IrreducibilityParameter D.nd D.naut := by
  have hc := globalDatumRegularity_of_typesCompatibility T
  intro i σ _ hgood Sig hSig ρ hρ
  obtain ⟨-, hw⟩ := h33 D.ntypes.BB_disj σ hgood (fun k v => (D.ntypes.tg_gen k v).2)
  obtain ⟨hirr, -, hroot⟩ := hw (D.nd.w i)
  obtain ⟨-, hcp⟩ := D.rbar_tie i σ Sig ρ hSig hρ
  refine ⟨?_, ?_⟩
  · refine irredOn_top_of_charpoly_eq _ _ (fun g => ?_)
      (irredOn_fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out _ hirr)
    rw [charpoly_mapRep, charpoly_mapRep]
    exact (hcp g).symm
  · intro k hk v _ hr
    rw [D.ntypes.heckeLoc_gamma_places i k v] at hr
    have hk' : D.what₂.places.resChar (D.nd.w i) ≠ D.host.g k := by rwa [D.nd.w_l i]
    rw [charpoly_mapRep, ← hcp] at hr
    have hχ : chi1 D.nd i (D.ntypes.tg k v) =
        ((D.nd.chi i 1 (D.ntypes.tg k v) : (D.nd.O i)ˣ) : D.nd.O i) := rfl
    rcases D.ntypes.chiT_tg i k v hk with h | h
    · rw [hχ, hc i k v _ _ hk h] at hr
      exact hroot k hk' v _ _ (Or.inl rfl) (hr.of_map (RingEquiv.injective _))
    · rw [hχ, hc i k v _ _ hk h] at hr
      exact hroot k hk' v _ _ (Or.inr rfl) (hr.of_map (RingEquiv.injective _))

end WindowedLandauTheory.NormalizedTypes

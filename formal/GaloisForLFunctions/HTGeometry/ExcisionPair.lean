import GaloisForLFunctions.HTGeometry.Excision
import GaloisForLFunctions.HTGeometry.PairSequence

/-!
# Excision for pairs of subspaces

The relative complex of a pair `S ⊆ T` of subspaces is the chains supported in `T` modulo those
supported in `S`.  For the excision pair the second isomorphism theorem identifies

  `C(Zᶜ)/C(A ∩ Zᶜ)`  with  `C^{A,Zᶜ}/C(A)`,

because the chains small for `{A, Zᶜ}` are the sum of the two pieces and the two pieces meet in the
chains supported in `A ∩ Zᶜ`.  Combined with the excision quasi-isomorphism this says that the
relative homology of `(X, A)` is the relative homology of `(Zᶜ, A ∩ Zᶜ)`.
-/

open CategoryTheory Limits

namespace GaloisForLFunctions.HTGeometry

universe v

variable (R : Type) [CommRing R] {X : Type v} [TopologicalSpace X]

/-- The chains supported in `S`, viewed inside the chains supported in `T`. -/
noncomputable def pairSub {S T : Set X} (h : S ⊆ T) :
    ModuleSubcomplex R (subcomplexOfSubset R T).complex :=
  ModuleSubcomplex.restrictTo (subcomplexOfSubset R T) (subcomplexOfSubset R S)
    (fun k => subChains_mono R h k)

/-- The relative chain complex of a pair of subspaces. -/
noncomputable def pairComplex {S T : Set X} (h : S ⊆ T) : ChainComplex (ModuleCat R) ℕ :=
  (pairSub R h).quotComplex

variable (A Z : Set X)

theorem subChains_compl_le_smallPair (k : ℕ) :
    subChains R (Zᶜ) k ≤ (subcomplexOfFamily R ({A, Zᶜ} : Set (Set X))).carrier k := by
  intro c hc
  rw [subcomplexOfFamily_pair_carrier]
  exact Submodule.mem_sup_right hc

/-- The comparison of the two relative complexes. -/
noncomputable def excPairHom :
    ModuleSubcomplex.Hom (pairSub R (Set.inter_subset_right : A ∩ Zᶜ ⊆ Zᶜ)) (excSub R A Z) where
  map := ModuleSubcomplex.leHom (fun k => subChains_compl_le_smallPair R A Z k)
  mem := by
    intro k x hx
    exact subChains_mono R Set.inter_subset_left k hx

theorem injective_excPairQuot (k : ℕ) :
    Function.Injective ⇑(((excPairHom R A Z).quotMap).f k) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective
    ((pairSub R (Set.inter_subset_right : A ∩ Zᶜ ⊆ Zᶜ)).carrier k) y
  have hy' : (Submodule.Quotient.mk
      ((ModuleSubcomplex.leHom (P := subcomplexOfSubset R (Zᶜ))
        (Q := subcomplexOfFamily R ({A, Zᶜ} : Set (Set X)))
        (fun k => subChains_compl_le_smallPair R A Z k)).f k c) :
      _ ⧸ (excSub R A Z).carrier k) = 0 := hy
  have h1 := (Submodule.Quotient.mk_eq_zero ((excSub R A Z).carrier k)).mp hy'
  have hval : (Subtype.val (p := fun d : C(topSimplex k, X) →₀ R => d ∈ subChains R (Zᶜ) k) c)
      ∈ subChains R A k := h1
  have hval2 : (Subtype.val (p := fun d : C(topSimplex k, X) →₀ R => d ∈ subChains R (Zᶜ) k) c)
      ∈ subChains R (Zᶜ) k :=
    Subtype.property (p := fun d : C(topSimplex k, X) →₀ R => d ∈ subChains R (Zᶜ) k) c
  refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
  show (Subtype.val (p := fun d : C(topSimplex k, X) →₀ R => d ∈ subChains R (Zᶜ) k) c)
      ∈ subChains R (A ∩ Zᶜ) k
  rw [subChains_inter]
  exact ⟨hval, hval2⟩

theorem surjective_excPairQuot (k : ℕ) :
    Function.Surjective ⇑(((excPairHom R A Z).quotMap).f k) := by
  intro w
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective ((excSub R A Z).carrier k) w
  have hu : (Subtype.val (p := fun d : C(topSimplex k, X) →₀ R =>
        d ∈ smallSubmodule R ({A, Zᶜ} : Set (Set X)) k) u)
      ∈ subChains R A k ⊔ subChains R (Zᶜ) k :=
    (smallChain_pair_iff R A (Zᶜ) _).mp
      (Subtype.property (p := fun d : C(topSimplex k, X) →₀ R =>
        d ∈ smallSubmodule R ({A, Zᶜ} : Set (Set X)) k) u)
  obtain ⟨a, ha, z, hz, hazu⟩ := Submodule.mem_sup.mp hu
  refine ⟨Submodule.Quotient.mk
    (Subtype.mk (p := fun d : C(topSimplex k, X) →₀ R => d ∈ subChains R (Zᶜ) k) z hz), ?_⟩
  have key : (Submodule.Quotient.mk
      ((ModuleSubcomplex.leHom (P := subcomplexOfSubset R (Zᶜ))
        (Q := subcomplexOfFamily R ({A, Zᶜ} : Set (Set X)))
        (fun k => subChains_compl_le_smallPair R A Z k)).f k
        (Subtype.mk (p := fun d : C(topSimplex k, X) →₀ R => d ∈ subChains R (Zᶜ) k) z hz)) :
      _ ⧸ (excSub R A Z).carrier k) = Submodule.Quotient.mk u := by
    refine (Submodule.Quotient.eq _).mpr ?_
    show (z - Subtype.val (p := fun d : C(topSimplex k, X) →₀ R =>
      d ∈ smallSubmodule R ({A, Zᶜ} : Set (Set X)) k) u) ∈ subChains R A k
    rw [← hazu, show z - (a + z) = -a from by abel]
    exact Submodule.neg_mem _ ha
  exact key

instance isIso_excPairQuot_f (k : ℕ) : IsIso (((excPairHom R A Z).quotMap).f k) := by
  haveI : Mono (((excPairHom R A Z).quotMap).f k) :=
    (ModuleCat.mono_iff_injective _).mpr (injective_excPairQuot R A Z k)
  haveI : Epi (((excPairHom R A Z).quotMap).f k) :=
    (ModuleCat.epi_iff_surjective _).mpr (surjective_excPairQuot R A Z k)
  exact isIso_of_mono_of_epi _

/-- **The second isomorphism theorem for the excision pair.** -/
instance isIso_excPairQuot : IsIso ((excPairHom R A Z).quotMap) :=
  HomologicalComplex.Hom.isIso_of_components _

end GaloisForLFunctions.HTGeometry

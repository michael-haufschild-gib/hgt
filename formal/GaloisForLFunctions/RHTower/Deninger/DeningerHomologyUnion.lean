import GaloisForLFunctions.RHTower.Deninger.DeningerAmalgamCyclic

/-!
# Homology of an increasing union of subgroups

A chain has finite support, so it involves only finitely many group elements and therefore lives in
one member of an increasing chain of subgroups whose union is the whole group.  Vanishing of
homology in a fixed degree therefore passes from the members of the chain to the group.

* `deningerSubChains` : the pushforward of chains along a subgroup inclusion.
* `deningerIsZero_of_iUnion` : vanishing passes to an increasing union.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits

universe u

variable (k G : Type u) [CommRing k] [Group G]

/-- The pushforward of inhomogeneous chains along the inclusion of a subgroup. -/
noncomputable def deningerSubChains (S : Subgroup G) :
    groupHomology.inhomogeneousChains (Rep.trivial k S k) ⟶
      groupHomology.inhomogeneousChains (Rep.trivial k G k) :=
  groupHomology.chainsMap S.subtype (𝟙 _)

/-- The inclusion of tuples in a subgroup into tuples in the group. -/
def deningerTupleIncl (S : Subgroup G) (n : ℕ) : (Fin n → S) → (Fin n → G) :=
  fun w i => (w i : G)

theorem deningerTupleIncl_injective (S : Subgroup G) (n : ℕ) :
    Function.Injective (deningerTupleIncl G S n) := fun _ _ hab =>
  funext fun i => Subtype.ext (congrFun hab i)

theorem deningerSubChains_f (S : Subgroup G) (n : ℕ) :
    (deningerSubChains k G S).f n =
      ModuleCat.ofHom (Finsupp.lmapDomain k k (deningerTupleIncl G S n)) := by
  refine ModuleCat.hom_ext (Finsupp.lhom_ext' fun x => LinearMap.ext_ring ?_)
  show (deningerSubChains k G S).f n (Finsupp.single x (1 : k)) =
    Finsupp.lmapDomain k k (deningerTupleIncl G S n) (Finsupp.single x (1 : k))
  rw [deningerSubChains, groupHomology.chainsMap_f_single]
  simp [Finsupp.lmapDomain, Finsupp.mapDomain_single]
  rfl

theorem deningerSubChains_injective (S : Subgroup G) (n : ℕ) :
    Function.Injective ((deningerSubChains k G S).f n) := by
  rw [deningerSubChains_f]
  exact Finsupp.mapDomain_injective (deningerTupleIncl_injective G S n)

/-- **Vanishing of homology passes to an increasing union of subgroups.**  A chain has finite
support, so it lives in one member of the chain. -/
theorem deningerIsZero_of_iUnion (S : ℕ → Subgroup G) (hmono : Monotone S)
    (hunion : ∀ g : G, ∃ m, g ∈ S m) (n : ℕ)
    (h : ∀ m, IsZero (groupHomology (Rep.trivial k (S m) k) (n + 1))) :
    IsZero (groupHomology (Rep.trivial k G k) (n + 1)) := by
  classical
  choose fidx hfidx using hunion
  rw [show groupHomology (Rep.trivial k G k) (n + 1) =
      (groupHomology.inhomogeneousChains (Rep.trivial k G k)).homology (n + 1) from rfl,
    ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hxd : (groupHomology.inhomogeneousChains (Rep.trivial k G k)).d (n + 1) n x = 0 := hx
  set m := x.support.sup (fun v => Finset.univ.sup (fun i => fidx (v i))) with hm
  have hmem : ∀ v ∈ x.support, ∀ i : Fin (n + 1), v i ∈ S m := by
    intro v hv i
    refine hmono ?_ (hfidx (v i))
    exact le_trans (Finset.le_sup (f := fun i : Fin (n + 1) => fidx (v i)) (Finset.mem_univ i))
      (Finset.le_sup (f := fun v : Fin (n + 1) → G => Finset.univ.sup fun i => fidx (v i)) hv)
  have hrange : (↑x.support : Set (Fin (n + 1) → G)) ⊆
      Set.range (deningerTupleIncl G (S m) (n + 1)) := fun v hv =>
    ⟨fun i => ⟨v i, hmem v (by simpa using hv) i⟩, rfl⟩
  set x' := Finsupp.comapDomain (deningerTupleIncl G (S m) (n + 1)) x
    ((deningerTupleIncl_injective G (S m) (n + 1)).injOn) with hx'def
  have hmapx : (deningerSubChains k G (S m)).f (n + 1) x' = x := by
    rw [deningerSubChains_f]
    exact Finsupp.mapDomain_comapDomain _ (deningerTupleIncl_injective G (S m) (n + 1)) x hrange
  have hcomm : ∀ i j : ℕ, ∀ z,
      (deningerSubChains k G (S m)).f j
          ((groupHomology.inhomogeneousChains (Rep.trivial k (S m) k)).d i j z) =
        (groupHomology.inhomogeneousChains (Rep.trivial k G k)).d i j
          ((deningerSubChains k G (S m)).f i z) := by
    intro i j z
    have hc := (deningerSubChains k G (S m)).comm i j
    have hz := ConcreteCategory.congr_hom hc z
    simpa using hz.symm
  have hdx' : (groupHomology.inhomogeneousChains (Rep.trivial k (S m) k)).d (n + 1) n x' = 0 := by
    refine deningerSubChains_injective k G (S m) n ?_
    rw [hcomm, hmapx, hxd, map_zero]
  have hexact := h m
  rw [show groupHomology (Rep.trivial k (S m) k) (n + 1) =
      (groupHomology.inhomogeneousChains (Rep.trivial k (S m) k)).homology (n + 1) from rfl,
    ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at hexact
  obtain ⟨y', hy'⟩ := hexact x' hdx'
  have hy'd : (groupHomology.inhomogeneousChains (Rep.trivial k (S m) k)).d (n + 2) (n + 1) y'
      = x' := hy'
  refine ⟨(deningerSubChains k G (S m)).f (n + 2) y', ?_⟩
  show (groupHomology.inhomogeneousChains (Rep.trivial k G k)).d (n + 2) (n + 1)
    ((deningerSubChains k G (S m)).f (n + 2) y') = x
  rw [← hcomm, hy'd, hmapx]

end RHTower

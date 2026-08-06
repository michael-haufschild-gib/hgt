import GaloisForLFunctions.HTGeometry.SiteFactorGraphWitness
import GaloisForLFunctions.HTGeometry.ArbitraryGraphLocalHamiltonianGenericityLaw

/-!
# Hypergraph-local Hamiltonians and the two-section reduction

A finite *interaction hypergraph* on a site set `V` is a finite family `𝔥` of
site packets.  Its admissible Hamiltonians are the real span of Hermitian
operators supported on a single site or supported inside one hyperedge.  The
support convention is exactly `IsSiteSupported X H`: an admissible term acts as
the identity outside its hyperedge, and lower-body operators inside a hyperedge
are allowed.

The *two-section graph* `twoSection 𝔥` joins two distinct sites whenever some
hyperedge contains both.  Its edges are therefore admissible packets of the
hypergraph, which gives the inclusion

```
siteFactorLocalSubmodule A (twoSection 𝔥) ≤ hypergraphLocalSubmodule A 𝔥
```

of equation `(2)` of the hypergraph local projective spectral factorization
card.  Since a nonzero spectral obstruction restricted to a subspace is still
nonzero on the ambient space, the connected-graph spanning-tree witness of
`SiteFactorGraphWitness` transports verbatim: a connected hypergraph carries a
maximally projective hyperedge-local Hamiltonian, and maximal projective
rational spectral rank is dense, residual and of full Lebesgue measure in the
canonical coordinates of the whole hyperedge-local space.

Nothing here restricts hyperedge sizes, vertex degrees, interaction order or
geometry.
-/

open Set SimpleGraph MeasureTheory Topology Filter
open scoped Matrix BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### The two-section graph of a hypergraph -/

/-- Two-section graph of a finite interaction hypergraph: distinct sites are
adjacent exactly when some hyperedge contains both. -/
def twoSection {V : Type*} (𝔥 : Finset (Finset V)) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => ∃ X ∈ 𝔥, u ∈ X ∧ v ∈ X

theorem twoSection_adj_iff {V : Type*} {𝔥 : Finset (Finset V)} {u v : V} :
    (twoSection 𝔥).Adj u v ↔ u ≠ v ∧ ∃ X ∈ 𝔥, u ∈ X ∧ v ∈ X := by
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨hne, ?_⟩
    rcases h with ⟨X, hX, hu, hv⟩ | ⟨X, hX, hv, hu⟩
    · exact ⟨X, hX, hu, hv⟩
    · exact ⟨X, hX, hu, hv⟩
  · rintro ⟨hne, hX⟩
    exact ⟨hne, Or.inl hX⟩

theorem twoSection_adj_of_mem_hyperedge {V : Type*} {𝔥 : Finset (Finset V)}
    {X : Finset V} (hX : X ∈ 𝔥) {u v : V} (hu : u ∈ X) (hv : v ∈ X)
    (huv : u ≠ v) : (twoSection 𝔥).Adj u v :=
  twoSection_adj_iff.2 ⟨huv, X, hX, hu, hv⟩

/-- Enlarging the hyperedge family enlarges the two-section graph. -/
theorem twoSection_mono {V : Type*} {𝔥 𝔨 : Finset (Finset V)} (h : 𝔥 ⊆ 𝔨) :
    twoSection 𝔥 ≤ twoSection 𝔨 := by
  intro u v huv
  obtain ⟨hne, X, hX, hu, hv⟩ := twoSection_adj_iff.1 huv
  exact twoSection_adj_iff.2 ⟨hne, X, h hX, hu, hv⟩

/-- A hyperedge is contained in a single connected component of the
two-section graph: any two of its sites are reachable from one another. -/
theorem twoSection_reachable_of_mem_hyperedge {V : Type*}
    {𝔥 : Finset (Finset V)} {X : Finset V} (hX : X ∈ 𝔥) {u v : V}
    (hu : u ∈ X) (hv : v ∈ X) : (twoSection 𝔥).Reachable u v := by
  by_cases huv : u = v
  · subst huv
    exact SimpleGraph.Reachable.refl u
  · exact (twoSection_adj_of_mem_hyperedge hX hu hv huv).reachable

/-! ### Hyperedge-local Hamiltonians -/

variable {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → Type*) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]

/-- Hermitian one-site and hyperedge-local generators of an interaction
hypergraph on a site-factorized carrier.  A hyperedge term is *any* Hermitian
operator acting as the identity outside that hyperedge. -/
def hypergraphLocalGenerator (𝔥 : Finset (Finset V)) :
    Set (Matrix (∀ v, A v) (∀ v, A v) ℂ) :=
  {H : Matrix (∀ v, A v) (∀ v, A v) ℂ | H.IsHermitian ∧
    ((∃ v : V, IsSiteSupported {v} H) ∨ ∃ X ∈ 𝔥, IsSiteSupported X H)}

/-- Exact real vector space of Hermitian onsite-plus-hyperedge Hamiltonians of
a finite interaction hypergraph. -/
def hypergraphLocalSubmodule (𝔥 : Finset (Finset V)) :
    Submodule ℝ (Matrix (∀ v, A v) (∀ v, A v) ℂ) :=
  Submodule.span ℝ (hypergraphLocalGenerator A 𝔥)

omit [Fintype V] [DecidableEq V] [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] in
theorem hypergraphLocalSubmodule_le_selfAdjoint (𝔥 : Finset (Finset V)) :
    hypergraphLocalSubmodule A 𝔥 ≤
      selfAdjoint.submodule ℝ (Matrix (∀ v, A v) (∀ v, A v) ℂ) := by
  refine Submodule.span_le.2 ?_
  rintro H ⟨hH, -⟩
  exact hH

omit [Fintype V] [DecidableEq V] [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] in
theorem mem_hypergraphLocalSubmodule_of_oneSite (𝔥 : Finset (Finset V))
    {H : Matrix (∀ v, A v) (∀ v, A v) ℂ} (hH : H.IsHermitian) (v : V)
    (hsupp : IsSiteSupported {v} H) : H ∈ hypergraphLocalSubmodule A 𝔥 :=
  Submodule.subset_span ⟨hH, Or.inl ⟨v, hsupp⟩⟩

omit [Fintype V] [DecidableEq V] [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] in
theorem mem_hypergraphLocalSubmodule_of_hyperedge {𝔥 : Finset (Finset V)}
    {H : Matrix (∀ v, A v) (∀ v, A v) ℂ} (hH : H.IsHermitian)
    {X : Finset V} (hX : X ∈ 𝔥) (hsupp : IsSiteSupported X H) :
    H ∈ hypergraphLocalSubmodule A 𝔥 :=
  Submodule.subset_span ⟨hH, Or.inr ⟨X, hX, hsupp⟩⟩

omit [Fintype V] [DecidableEq V] [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] in
/-- Adding hyperedges enlarges the hyperedge-local Hamiltonian space. -/
theorem hypergraphLocalSubmodule_mono {𝔥 𝔨 : Finset (Finset V)} (h : 𝔥 ⊆ 𝔨) :
    hypergraphLocalSubmodule A 𝔥 ≤ hypergraphLocalSubmodule A 𝔨 := by
  refine Submodule.span_le.2 ?_
  rintro H ⟨hH, hcase⟩
  refine Submodule.subset_span ⟨hH, ?_⟩
  rcases hcase with ⟨v, hv⟩ | ⟨X, hX, hsupp⟩
  · exact Or.inl ⟨v, hv⟩
  · exact Or.inr ⟨X, h hX, hsupp⟩

omit [Fintype V] [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] in
/-- **Equation `(2)`: the two-section spanning inclusion.**  Every ordinary
one-site or two-site interaction term of the two-section graph is a legitimate
hyperedge-local term, because a two-section edge lies inside some hyperedge and
site support is monotone in the packet. -/
theorem siteFactorLocalSubmodule_twoSection_le_hypergraphLocalSubmodule
    (𝔥 : Finset (Finset V)) :
    siteFactorLocalSubmodule A (twoSection 𝔥) ≤ hypergraphLocalSubmodule A 𝔥 := by
  refine Submodule.span_le.2 ?_
  rintro H ⟨hH, hcase⟩
  rcases hcase with ⟨v, hv⟩ | ⟨u, v, huv, hsupp⟩
  · exact Submodule.subset_span ⟨hH, Or.inl ⟨v, hv⟩⟩
  · obtain ⟨-, X, hX, hu, hvX⟩ := twoSection_adj_iff.1 huv
    refine Submodule.subset_span ⟨hH, Or.inr ⟨X, hX, hsupp.mono ?_⟩⟩
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hu
    · exact hvX

/-! ### The connected witness -/

/-- **Connected hypergraphs realize maximal projective rank.**  Every finite
interaction hypergraph whose two-section graph is connected, with local factors
of dimension at least two, admits a Hermitian onsite-plus-hyperedge Hamiltonian
whose spectrum has maximal projective rational rank.

The witness is produced on a spanning tree of the two-section graph and then
read inside the larger hyperedge-local space through equation `(2)`. -/
theorem exists_maximallyProjective_mem_hypergraphLocalSubmodule
    {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → Type) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    (hA : ∀ v, 2 ≤ Fintype.card (A v))
    (𝔥 : Finset (Finset V)) (hconn : (twoSection 𝔥).Connected) :
    ∃ H : Matrix (∀ v, A v) (∀ v, A v) ℂ, ∃ hH : H.IsHermitian,
      H ∈ hypergraphLocalSubmodule A 𝔥 ∧
        MaximallyProjectiveEnergy hH.eigenvalues := by
  classical
  letI : DecidableRel (twoSection 𝔥).Adj := Classical.decRel _
  obtain ⟨H, hH, hmem, hmax⟩ :=
    exists_maximallyProjective_mem_siteFactorLocalSubmodule
      (twoSection 𝔥) hconn A hA
  exact ⟨H, hH,
    siteFactorLocalSubmodule_twoSection_le_hypergraphLocalSubmodule A 𝔥 hmem,
    hmax⟩

/-! ### Maximal projectivity forces a simple spectrum -/

/-- **Maximal projective rank forces distinct levels.**  A repeated level is a
balanced integer relation with two nonzero coefficients. -/
theorem injective_of_maximallyProjectiveEnergy
    {I : Type*} [Fintype I] [DecidableEq I] {energy : I → ℝ}
    (hmax : MaximallyProjectiveEnergy energy) : Function.Injective energy := by
  intro a b hab
  by_contra hne
  have hzero := hmax (fun i => (if i = a then 1 else 0) - if i = b then 1 else 0)
    (by
      show (∑ i, ((if i = a then (1 : ℤ) else 0) - if i = b then 1 else 0)) = 0
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ a fun _ => (1 : ℤ),
        Finset.sum_ite_eq' Finset.univ b fun _ => (1 : ℤ)]
      simp)
    (by
      have hexpand : ∀ i : I,
          (((if i = a then (1 : ℤ) else 0) - if i = b then 1 else 0 : ℤ) : ℝ) *
              energy i =
            (if i = a then energy i else 0) - if i = b then energy i else 0 := by
        intro i
        by_cases hia : i = a <;> by_cases hib : i = b <;>
          simp [hia, hib, hne, Ne.symm hne]
      rw [Finset.sum_congr rfl fun i _ => hexpand i, Finset.sum_sub_distrib,
        Finset.sum_ite_eq' Finset.univ a energy,
        Finset.sum_ite_eq' Finset.univ b energy]
      simp [hab])
  have ha := congrFun hzero a
  rw [if_pos rfl, if_neg hne] at ha
  simp at ha

/-! ### Canonical coordinates of the hyperedge-local space -/

/-- Canonical Hermitian basis generators of the hyperedge-local space. -/
def hypergraphLocalGeneratorFin (𝔥 : Finset (Finset V)) :
    Fin (Module.finrank ℝ (hypergraphLocalSubmodule A 𝔥)) →
      Matrix (∀ v, A v) (∀ v, A v) ℂ :=
  realMatrixSubmoduleGenerator (hypergraphLocalSubmodule A 𝔥)

omit [∀ v, DecidableEq (A v)] in
theorem hypergraphLocalGeneratorFin_isHermitian (𝔥 : Finset (Finset V))
    (i : Fin (Module.finrank ℝ (hypergraphLocalSubmodule A 𝔥))) :
    (hypergraphLocalGeneratorFin A 𝔥 i).IsHermitian :=
  realMatrixSubmoduleGenerator_isHermitian _
    (hypergraphLocalSubmodule_le_selfAdjoint A 𝔥) i

/-- The Hamiltonian at a canonical coordinate vector. -/
def hypergraphLocalMatrix (𝔥 : Finset (Finset V))
    (p : Fin (Module.finrank ℝ (hypergraphLocalSubmodule A 𝔥)) → ℝ) :
    Matrix (∀ v, A v) (∀ v, A v) ℂ :=
  realAffineMatrix 0 (hypergraphLocalGeneratorFin A 𝔥) p

omit [∀ v, DecidableEq (A v)] in
theorem hypergraphLocalMatrix_isHermitian (𝔥 : Finset (Finset V))
    (p : Fin (Module.finrank ℝ (hypergraphLocalSubmodule A 𝔥)) → ℝ) :
    (hypergraphLocalMatrix A 𝔥 p).IsHermitian :=
  realAffineMatrix_isHermitian 0 (hypergraphLocalGeneratorFin A 𝔥)
    Matrix.isHermitian_zero (hypergraphLocalGeneratorFin_isHermitian A 𝔥) p

omit [∀ v, DecidableEq (A v)] in
/-- The canonical coordinates exhaust the hyperedge-local space. -/
theorem hypergraphLocalMatrix_mem (𝔥 : Finset (Finset V))
    (p : Fin (Module.finrank ℝ (hypergraphLocalSubmodule A 𝔥)) → ℝ) :
    hypergraphLocalMatrix A 𝔥 p ∈ hypergraphLocalSubmodule A 𝔥 :=
  realAffineMatrix_mem_submodule _ p

omit [∀ v, DecidableEq (A v)] in
theorem exists_hypergraphLocalCoordinates (𝔥 : Finset (Finset V))
    {H : Matrix (∀ v, A v) (∀ v, A v) ℂ}
    (hH : H ∈ hypergraphLocalSubmodule A 𝔥) :
    ∃ p, hypergraphLocalMatrix A 𝔥 p = H :=
  exists_realAffineMatrix_eq_of_mem_submodule _ H hH

/-- Coordinates at which the hyperedge-local Hamiltonian has maximal
projective rational spectral rank. -/
def hypergraphLocalMaximalSet (𝔥 : Finset (Finset V)) :
    Set (Fin (Module.finrank ℝ (hypergraphLocalSubmodule A 𝔥)) → ℝ) :=
  realHermitianSubmoduleMaximalSet (hypergraphLocalSubmodule A 𝔥)
    (hypergraphLocalSubmodule_le_selfAdjoint A 𝔥)

theorem maximallyProjective_of_mem_hypergraphLocalMaximalSet
    (𝔥 : Finset (Finset V))
    (p : Fin (Module.finrank ℝ (hypergraphLocalSubmodule A 𝔥)) → ℝ)
    (hp : p ∈ hypergraphLocalMaximalSet A 𝔥) :
    MaximallyProjectiveEnergy
      (hypergraphLocalMatrix_isHermitian A 𝔥 p).eigenvalues := by
  have hmapHerm :
      ((realAffineMatrixPolynomial (0 : Matrix (∀ v, A v) (∀ v, A v) ℂ)
        (hypergraphLocalGeneratorFin A 𝔥)).map
          (MvPolynomial.eval₂Hom (RingHom.id ℂ)
            (fun t => (p t : ℂ)))).IsHermitian := by
    rw [eval_realAffineMatrixPolynomial]
    exact hypergraphLocalMatrix_isHermitian A 𝔥 p
  have hp' : MaximallyProjectiveEnergy hmapHerm.eigenvalues := hp
  have heig : hmapHerm.eigenvalues =
      (hypergraphLocalMatrix_isHermitian A 𝔥 p).eigenvalues := by
    apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).2
    rw [eval_realAffineMatrixPolynomial]
    rfl
  rwa [heig] at hp'

/-- **Connected hypergraph-local genericity.**  In the entire real vector space
generated by arbitrary Hermitian one-site terms and arbitrary Hermitian terms
supported inside the hyperedges, maximal projective rational spectral rank is
dense, residual and of full Lebesgue measure, for every finite hypergraph with
connected two-section graph. -/
theorem hypergraphLocalMaximalSet_dense_residual_fullMeasure
    {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → Type) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    (hA : ∀ v, 2 ≤ Fintype.card (A v))
    (𝔥 : Finset (Finset V)) (hconn : (twoSection 𝔥).Connected) :
    Dense (hypergraphLocalMaximalSet A 𝔥) ∧
      hypergraphLocalMaximalSet A 𝔥 ∈
        residual (Fin (Module.finrank ℝ (hypergraphLocalSubmodule A 𝔥)) → ℝ) ∧
      volume (hypergraphLocalMaximalSet A 𝔥)ᶜ = 0 := by
  obtain ⟨H, hH, hmem, hmax⟩ :=
    exists_maximallyProjective_mem_hypergraphLocalSubmodule A hA 𝔥 hconn
  exact realHermitianSubmoduleMaximalSet_dense_residual_fullMeasure
    (hypergraphLocalSubmodule A 𝔥)
    (hypergraphLocalSubmodule_le_selfAdjoint A 𝔥) H hmem hH hmax

/-- **Connected hypergraph projective spectral rank.**  At every coordinate of
the generic set the anchored projective rational spectral rank of the
hyperedge-local Hamiltonian is exactly `D - 1`, where `D` is the total tensor
dimension.  It does not depend on hyperedge sizes, interaction order, vertex
degrees or geometry. -/
theorem anchoredTemporalRank_hypergraphLocalMatrix_eq
    (𝔥 : Finset (Finset V))
    (p : Fin (Module.finrank ℝ (hypergraphLocalSubmodule A 𝔥)) → ℝ)
    (hp : p ∈ hypergraphLocalMaximalSet A 𝔥) (r : ∀ v, A v) :
    anchoredTemporalRank (hypergraphLocalMatrix_isHermitian A 𝔥 p).eigenvalues r
      = (∏ v, Fintype.card (A v)) - 1 := by
  rw [anchoredTemporalRank_eq_card_sub_one_of_maximallyProjective
    (hypergraphLocalMatrix_isHermitian A 𝔥 p).eigenvalues
    (maximallyProjective_of_mem_hypergraphLocalMaximalSet A 𝔥 p hp) r,
    Fintype.card_pi]

/-- **Connected hypergraph spectral simplicity.**  At every coordinate of the
generic set the hyperedge-local Hamiltonian has a simple spectrum. -/
theorem injective_eigenvalues_hypergraphLocalMatrix
    (𝔥 : Finset (Finset V))
    (p : Fin (Module.finrank ℝ (hypergraphLocalSubmodule A 𝔥)) → ℝ)
    (hp : p ∈ hypergraphLocalMaximalSet A 𝔥) :
    Function.Injective (hypergraphLocalMatrix_isHermitian A 𝔥 p).eigenvalues :=
  injective_of_maximallyProjectiveEnergy
    (maximallyProjective_of_mem_hypergraphLocalMaximalSet A 𝔥 p hp)

end

end GaloisForLFunctions.HTGeometry

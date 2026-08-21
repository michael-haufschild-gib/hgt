import GaloisForLFunctions.HTGeometry.RelativeSingularHomology
import GaloisForLFunctions.HTGeometry.SubdivisionHomotopy

/-!
# Chains small for a cover compute singular homology

The quotient of the singular chains by the chains small for a family `𝒱` is acyclic as soon as some
open cover refines `𝒱`: given a chain whose boundary is already small, enough subdivisions make the
chain itself small, and the subdivision homotopy exhibits the difference as a boundary plus a small
chain.  Hence the inclusion of the small chains induces an isomorphism on homology in every degree.

Allowing the family `𝒱` to be coarser than the open cover is what makes the statement usable for
excision, where the two pieces are not open but their interiors cover.
-/

open CategoryTheory Limits

namespace GaloisForLFunctions.HTGeometry

universe v

variable (R : Type) [CommRing R] {X : Type v} [TopologicalSpace X]

theorem smallSimplex_zero (𝒱 𝒰 : Set (Set X)) (hcover : (Set.univ : Set X) ⊆ ⋃₀ 𝒰)
    (href : ∀ U ∈ 𝒰, ∃ V ∈ 𝒱, U ⊆ V) (σ : C(topSimplex 0, X)) : SmallSimplex 𝒱 σ := by
  haveI : Unique (topSimplex 0) := inferInstanceAs (Unique (stdSimplex ℝ (Fin 1)))
  obtain ⟨U, hU, hmem⟩ := hcover (Set.mem_univ (σ default))
  obtain ⟨V, hV, hUV⟩ := href U hU
  refine ⟨V, hV, ?_⟩
  rintro _ ⟨x, rfl⟩
  rw [Subsingleton.elim x default]
  exact hUV hmem

theorem smallSubmodule_zero_eq_top (𝒱 𝒰 : Set (Set X)) (hcover : (Set.univ : Set X) ⊆ ⋃₀ 𝒰)
    (href : ∀ U ∈ 𝒰, ∃ V ∈ 𝒱, U ⊆ V) : smallSubmodule R 𝒱 0 = ⊤ :=
  eq_top_iff.mpr fun _ _ σ _ => smallSimplex_zero 𝒱 𝒰 hcover href σ

theorem quotComplex_exactAt_zero (𝒱 𝒰 : Set (Set X)) (hcover : (Set.univ : Set X) ⊆ ⋃₀ 𝒰)
    (href : ∀ U ∈ 𝒰, ∃ V ∈ 𝒱, U ⊆ V) :
    (subcomplexOfFamily R 𝒱).quotComplex.ExactAt 0 := by
  refine HomologicalComplex.ExactAt.of_isZero ?_
  haveI hsub : Subsingleton
      (((singChainComplex R X).X 0) ⧸ (subcomplexOfFamily R 𝒱).carrier 0) := by
    constructor
    intro x y
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [Submodule.Quotient.eq, show (subcomplexOfFamily R 𝒱).carrier 0 = ⊤ from
      smallSubmodule_zero_eq_top R 𝒱 𝒰 hcover href]
    trivial
  exact ModuleCat.isZero_of_subsingleton
    (ModuleCat.of R (((singChainComplex R X).X 0) ⧸ (subcomplexOfFamily R 𝒱).carrier 0))

theorem exists_quot_mk_finsupp (𝒱 : Set (Set X)) (k : ℕ)
    (x : ((singChainComplex R X).X k) ⧸ (subcomplexOfFamily R 𝒱).carrier k) :
    ∃ c : C(topSimplex k, X) →₀ R, Submodule.Quotient.mk c = x := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨c, rfl⟩

theorem quotComplex_exactAt_succ (𝒱 𝒰 : Set (Set X)) (hopen : ∀ U ∈ 𝒰, IsOpen U)
    (hcover : (Set.univ : Set X) ⊆ ⋃₀ 𝒰) (href : ∀ U ∈ 𝒰, ∃ V ∈ 𝒱, U ⊆ V) (k : ℕ) :
    (subcomplexOfFamily R 𝒱).quotComplex.ExactAt (k + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (k + 2) (k + 1) k
      (ComplexShape.prev_eq' _ rfl) (ChainComplex.next_nat_succ k),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  obtain ⟨c, rfl⟩ := exists_quot_mk_finsupp R 𝒱 (k + 1) x
  have hg : ∀ d : C(topSimplex (k + 1), X) →₀ R,
      ((HomologicalComplex.sc' (subcomplexOfFamily R 𝒱).quotComplex (k + 2) (k + 1) k).g)
          (Submodule.Quotient.mk d :
            ((singChainComplex R X).X (k + 1)) ⧸ (subcomplexOfFamily R 𝒱).carrier (k + 1))
        = (Submodule.Quotient.mk (singBd R X k d) :
            ((singChainComplex R X).X k) ⧸ (subcomplexOfFamily R 𝒱).carrier k) := by
    intro d
    show ((subcomplexOfFamily R 𝒱).quotComplex.d (k + 1) k) _ = _
    rw [ModuleSubcomplex.quotComplex_d]
    rfl
  have hg2 : ∀ d : C(topSimplex (k + 2), X) →₀ R,
      ((HomologicalComplex.sc' (subcomplexOfFamily R 𝒱).quotComplex (k + 2) (k + 1) k).f)
          (Submodule.Quotient.mk d :
            ((singChainComplex R X).X (k + 2)) ⧸ (subcomplexOfFamily R 𝒱).carrier (k + 2))
        = (Submodule.Quotient.mk (singBd R X (k + 1) d) :
            ((singChainComplex R X).X (k + 1)) ⧸ (subcomplexOfFamily R 𝒱).carrier (k + 1)) := by
    intro d
    show ((subcomplexOfFamily R 𝒱).quotComplex.d (k + 2) (k + 1)) _ = _
    rw [ModuleSubcomplex.quotComplex_d]
    rfl
  have hbd : SmallChain R 𝒱 (singBd R X k c) := by
    have h0 : (Submodule.Quotient.mk (singBd R X k c) :
        ((singChainComplex R X).X k) ⧸ (subcomplexOfFamily R 𝒱).carrier k) = 0 := by
      rw [← hg c]
      exact hx
    exact (Submodule.Quotient.mk_eq_zero _).mp h0
  obtain ⟨N, hN0⟩ := exists_singSdPow_small R 𝒰 hopen hcover c
  have hN : SmallChain R 𝒱 (singSdPow R (k + 1) N c) := smallChain_refine R href hN0
  refine ⟨Submodule.Quotient.mk (-(singD R (k + 1) N c)), ?_⟩
  refine (hg2 _).trans ?_
  have hid := singBd_singD R N c
  have hsplit : singBd R X (k + 1) (-(singD R (k + 1) N c)) - c
      = singD R k N (singBd R X k c) - singSdPow R (k + 1) N c := by
    rw [map_neg]
    have hb : singBd R X (k + 1) (singD R (k + 1) N c)
        = singSdPow R (k + 1) N c - c - singD R k N (singBd R X k c) := by
      rw [← hid]
      abel
    rw [hb]
    abel
  have final : SmallChain R 𝒱 (singBd R X (k + 1) (-(singD R (k + 1) N c)) - c) := by
    rw [hsplit]
    exact smallChain_sub R (smallChain_singD R N hbd) hN
  have hgoal : (Submodule.Quotient.mk (singBd R X (k + 1) (-(singD R (k + 1) N c))) :
      ((singChainComplex R X).X (k + 1)) ⧸ (subcomplexOfFamily R 𝒱).carrier (k + 1))
      = Submodule.Quotient.mk c :=
    (Submodule.Quotient.eq _).mpr final
  exact hgoal

/-- **The chains small for a family refined by an open cover compute singular homology.** -/
theorem isIso_homologyMap_smallIncl (𝒱 𝒰 : Set (Set X)) (hopen : ∀ U ∈ 𝒰, IsOpen U)
    (hcover : (Set.univ : Set X) ⊆ ⋃₀ 𝒰) (href : ∀ U ∈ 𝒰, ∃ V ∈ 𝒱, U ⊆ V) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (subcomplexOfFamily R 𝒱).incl n) := by
  have hac : ∀ m : ℕ, (subcomplexOfFamily R 𝒱).quotComplex.ExactAt m := by
    intro m
    cases m with
    | zero => exact quotComplex_exactAt_zero R 𝒱 𝒰 hcover href
    | succ k => exact quotComplex_exactAt_succ R 𝒱 𝒰 hopen hcover href k
  have hzero : ∀ m : ℕ, IsZero ((subcomplexOfFamily R 𝒱).quotComplex.homology m) :=
    fun m => (hac m).isZero_homology
  have hepi : Epi (HomologicalComplex.homologyMap (subcomplexOfFamily R 𝒱).incl n) := by
    refine ShortComplex.Exact.epi_f (ModuleSubcomplex.homology_exact₂ _ n) ?_
    exact (hzero n).eq_zero_of_tgt _
  have hmono : Mono (HomologicalComplex.homologyMap (subcomplexOfFamily R 𝒱).incl n) := by
    refine ShortComplex.Exact.mono_g
      (ModuleSubcomplex.homology_exact₁ (subcomplexOfFamily R 𝒱) (n + 1) n rfl) ?_
    exact (hzero (n + 1)).eq_zero_of_src _
  exact isIso_of_mono_of_epi _

end GaloisForLFunctions.HTGeometry

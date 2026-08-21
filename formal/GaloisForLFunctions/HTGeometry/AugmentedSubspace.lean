import GaloisForLFunctions.HTGeometry.AugmentedShift
import GaloisForLFunctions.HTGeometry.SingularFunctoriality

/-!
# Reduced homology of a subspace in low degrees

The augmentation is preserved by pushforward, so a chain supported in a subspace has the same total
coefficient computed in the subspace or in the ambient space.  Hence the augmented subcomplex of a
nonempty subspace has no homology in degree zero, and none in degree one when the subspace is
path-connected.
-/

open CategoryTheory Limits

namespace GaloisForLFunctions.HTGeometry

universe v

variable (R : Type) [CommRing R] {X Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

theorem singAug_singMapHom (f : C(Y, X)) (c : C(topSimplex 0, Y) →₀ R) :
    singAug R (singMapHom R f 0 c) = singAug R c := by
  have hmap : (singAug R (X := X)).comp (singMapHom R f 0) = singAug R (X := Y) := by
    refine Finsupp.lhom_ext' fun σ => LinearMap.ext_ring ?_
    show singAug R (singMapHom R f 0 (Finsupp.single σ (1 : R))) = singAug R (Finsupp.single σ 1)
    rw [singMapHom_single, singAug_single, singAug_single]
  exact LinearMap.congr_fun hmap c

theorem singAug_subChainIncl (S : Set X) (c : C(topSimplex 0, ↥S) →₀ R) :
    singAug R (subChainIncl R S 0 c) = singAug R c :=
  singAug_singMapHom R ⟨Subtype.val, continuous_subtype_val⟩ c

variable (X)

theorem isZero_augHomology_zero [Nonempty X] : IsZero ((augChain R X).homology 0) := by
  have hsurj : Function.Surjective ⇑((augChain R X).d 1 0).hom := by
    intro y
    obtain ⟨c, hc⟩ := singAug_surjective R (X := X) ((ULift.moduleEquiv (R := R) (M := R)) y)
    refine ⟨c, ?_⟩
    rw [augChain_d]
    show (ULift.moduleEquiv (R := R) (M := R)).symm (singAug R c) = y
    rw [hc]
    exact (ULift.moduleEquiv (R := R) (M := R)).symm_apply_apply y
  haveI hsub : Subsingleton
      ((augChain R X).X 0 ⧸ LinearMap.range ((augChain R X).d 1 0).hom) := by
    constructor
    intro a b
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Submodule.Quotient.eq]
    have hrange : LinearMap.range ((augChain R X).d 1 0).hom = ⊤ :=
      LinearMap.range_eq_top.mpr hsurj
    rw [hrange]
    exact Submodule.mem_top
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _) (homologyZeroIso R (augChain R X))

variable {X}

theorem single_const_mem_subChains {S : Set X} {x : X} (hx : x ∈ S) (r : R) :
    Finsupp.single (constSimplex x 0) r ∈ subChains R S 0 := by
  rw [mem_subChains]
  intro σ hσ
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hσ)]
  rintro _ ⟨y, rfl⟩
  exact hx

theorem isZero_augSub_homology_zero (S : Set X) (hS : S.Nonempty) :
    IsZero ((augSub R X S).complex.homology 0) := by
  obtain ⟨x, hx⟩ := hS
  have hsurj : Function.Surjective ⇑((augSub R X S).complex.d 1 0).hom := by
    intro y
    obtain ⟨y, rfl⟩ : ∃ y' : ((augSub R X S).carrier 0), y' = y := ⟨y, rfl⟩
    refine ⟨⟨Finsupp.single (constSimplex x 0)
      ((ULift.moduleEquiv (R := R) (M := R)) (y : (augChain R X).X 0)),
      single_const_mem_subChains R hx _⟩, ?_⟩
    rw [ModuleSubcomplex.complex_d]
    refine Subtype.ext ?_
    show ((augChain R X).d 1 0).hom
      (Finsupp.single (constSimplex x 0)
        ((ULift.moduleEquiv (R := R) (M := R)) (y : (augChain R X).X 0)))
      = (y : (augChain R X).X 0)
    rw [augChain_d]
    show (ULift.moduleEquiv (R := R) (M := R)).symm
      (singAug R (Finsupp.single (constSimplex x 0)
        ((ULift.moduleEquiv (R := R) (M := R)) (y : (augChain R X).X 0)))) = _
    rw [singAug_single]
    exact (ULift.moduleEquiv (R := R) (M := R)).symm_apply_apply _
  haveI hsub : Subsingleton
      ((augSub R X S).complex.X 0 ⧸ LinearMap.range ((augSub R X S).complex.d 1 0).hom) := by
    constructor
    intro a b
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Submodule.Quotient.eq, LinearMap.range_eq_top.mpr hsurj]
    exact Submodule.mem_top
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _)
    (homologyZeroIso R (augSub R X S).complex)

theorem isZero_augSub_homology_one (S : Set X) [PathConnectedSpace ↥S] :
    IsZero ((augSub R X S).complex.homology 1) := by
  refine HomologicalComplex.ExactAt.isZero_homology ?_
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (ComplexShape.prev_eq' _ rfl)
      (ChainComplex.next_nat_succ 0), ShortComplex.moduleCat_exact_iff]
  intro u hu
  obtain ⟨u, rfl⟩ : ∃ u' : (subChains R S 0), u' = u := ⟨u, rfl⟩
  have hu0 : singAug R (u : C(topSimplex 0, X) →₀ R) = 0 := by
    have h1 : ((augSub R X S).complex.d 1 0) u = 0 := hu
    rw [ModuleSubcomplex.complex_d] at h1
    have h2 := congrArg
      (fun z : ((augSub R X S).carrier 0) => (z : (augChain R X).X 0)) h1
    simp only at h2
    have h4 : ((augChain R X).d 1 0).hom
        (Subtype.val (p := fun z : C(topSimplex 0, X) →₀ R => z ∈ subChains R S 0) u) = 0 := h2
    rw [augChain_d] at h4
    refine (ULift.moduleEquiv (R := R) (M := R)).symm.injective ?_
    rw [map_zero]
    exact h4
  obtain ⟨c', hc'⟩ : ∃ c' : C(topSimplex 0, ↥S) →₀ R,
      subChainIncl R S 0 c' = (u : C(topSimplex 0, X) →₀ R) :=
    (range_subChainIncl R S 0).ge u.2
  have hc'0 : singAug R c' = 0 := by
    rw [← singAug_subChainIncl R S c', hc', hu0]
  obtain ⟨d', hd'⟩ := exists_singBd_eq_of_singAug_eq_zero R c' hc'0
  refine ⟨⟨subChainIncl R S 1 d', (range_subChainIncl R S 1).le ⟨d', rfl⟩⟩, ?_⟩
  refine Subtype.ext ?_
  show ((augChain R X).d 2 1).hom (subChainIncl R S 1 d')
    = Subtype.val (p := fun z : C(topSimplex 0, X) →₀ R => z ∈ subChains R S 0) u
  rw [augChain_d]
  show singBd R X 0 (subChainIncl R S 1 d') = _
  rw [← subChainIncl_singBd, hd', hc']

/-- **On a path-connected subspace a supported `0`-chain of total coefficient zero bounds within
that subspace.** -/
theorem exists_singBd_supported (S : Set X) [PathConnectedSpace ↥S]
    {c : C(topSimplex 0, X) →₀ R} (hc : c ∈ subChains R S 0) (hc0 : singAug R c = 0) :
    ∃ d, d ∈ subChains R S 1 ∧ singBd R X 0 d = c := by
  obtain ⟨c', hc'⟩ : ∃ c' : C(topSimplex 0, ↥S) →₀ R, subChainIncl R S 0 c' = c :=
    (range_subChainIncl R S 0).ge hc
  have hc'0 : singAug R c' = 0 := by
    rw [← singAug_subChainIncl R S c', hc', hc0]
  obtain ⟨d', hd'⟩ := exists_singBd_eq_of_singAug_eq_zero R c' hc'0
  exact ⟨subChainIncl R S 1 d', (range_subChainIncl R S 1).le ⟨d', rfl⟩,
    by rw [← subChainIncl_singBd, hd', hc']⟩

end GaloisForLFunctions.HTGeometry

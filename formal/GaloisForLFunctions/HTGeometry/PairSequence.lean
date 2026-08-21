import GaloisForLFunctions.HTGeometry.PointHomology

/-!
# The chains of a subspace as a subcomplex, and the sequence of a pair

Composing with the inclusion identifies the singular chain complex of a subspace with the
subcomplex of chains supported in it, so the long exact sequence of the subcomplex is the long exact
sequence of the pair.  When the ambient space is contractible the two outer terms vanish and the
connecting map is an isomorphism.
-/

open CategoryTheory Limits

namespace GaloisForLFunctions.HTGeometry

universe v

variable (R : Type) [CommRing R] {X : Type v} [TopologicalSpace X]

/-- The chains of a subspace are the chains supported in it. -/
noncomputable def subspaceChainEquiv (S : Set X) (k : ℕ) :
    (C(topSimplex k, ↥S) →₀ R) ≃ₗ[R] (subChains R S k) :=
  (LinearEquiv.ofInjective (subChainIncl R S k) (subChainIncl_injective R S k)).trans
    (LinearEquiv.ofEq _ _ (range_subChainIncl R S k))

theorem subspaceChainEquiv_coe (S : Set X) (k : ℕ) (c : C(topSimplex k, ↥S) →₀ R) :
    ((subspaceChainEquiv R S k c : subChains R S k) : C(topSimplex k, X) →₀ R)
      = subChainIncl R S k c := rfl

/-- The chain map identifying the chains of a subspace with the chains supported in it. -/
noncomputable def subspaceChainMap (S : Set X) :
    singChainComplex R (↥S) ⟶ (subcomplexOfSubset R S).complex where
  f k := ModuleCat.ofHom (subspaceChainEquiv R S k).toLinearMap
  comm' := by
    rintro i j (hij : j + 1 = i)
    subst hij
    rw [ModuleSubcomplex.complex_d]
    refine ModuleCat.hom_ext (LinearMap.ext fun c => Subtype.ext ?_)
    exact (subChainIncl_singBd R S c).symm

instance isIso_subspaceChainMap_f (S : Set X) (k : ℕ) :
    IsIso ((subspaceChainMap R S).f k) := by
  refine ⟨ModuleCat.ofHom (subspaceChainEquiv R S k).symm.toLinearMap, ?_, ?_⟩
  · exact ModuleCat.hom_ext (LinearMap.ext fun c => (subspaceChainEquiv R S k).symm_apply_apply c)
  · exact ModuleCat.hom_ext (LinearMap.ext fun c => (subspaceChainEquiv R S k).apply_symm_apply c)

instance isIso_subspaceChainMap (S : Set X) : IsIso (subspaceChainMap R S) :=
  HomologicalComplex.Hom.isIso_of_components _

/-- **The homology of a subspace is the homology of the chains supported in it.** -/
noncomputable def subspaceComplexIso (S : Set X) :
    singChainComplex R (↥S) ≅ (subcomplexOfSubset R S).complex :=
  asIso (subspaceChainMap R S)

/-! ### The connecting map of a pair in a contractible space -/

/-- **In a contractible space the connecting map of a pair is an isomorphism in degrees ≥ 2.** -/
theorem isIso_connecting_of_homotopy_const {x : X}
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.const X x))
    (S : Set X) (k : ℕ) :
    IsIso ((subcomplexOfSubset R S).connecting (k + 2) (k + 1) rfl) := by
  have hz1 : IsZero ((singChainComplex R X).homology (k + 2)) :=
    isZero_homology_of_homotopy_const R H (k + 1)
  have hz2 : IsZero ((singChainComplex R X).homology (k + 1)) :=
    isZero_homology_of_homotopy_const R H k
  have hmono : Mono ((subcomplexOfSubset R S).connecting (k + 2) (k + 1) rfl) := by
    refine ShortComplex.Exact.mono_g
      (ModuleSubcomplex.homology_exact₃ (subcomplexOfSubset R S) (k + 2) (k + 1) rfl) ?_
    exact hz1.eq_zero_of_src _
  have hepi : Epi ((subcomplexOfSubset R S).connecting (k + 2) (k + 1) rfl) := by
    refine ShortComplex.Exact.epi_f
      (ModuleSubcomplex.homology_exact₁ (subcomplexOfSubset R S) (k + 2) (k + 1) rfl) ?_
    exact hz2.eq_zero_of_tgt _
  exact isIso_of_mono_of_epi _

end GaloisForLFunctions.HTGeometry

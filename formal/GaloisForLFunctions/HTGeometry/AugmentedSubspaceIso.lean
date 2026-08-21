import GaloisForLFunctions.HTGeometry.AugmentedSubspace

/-!
# The augmented chains supported in a subspace are the augmented chains of that subspace

Composing with the inclusion identifies the two, degree by degree: the coefficient ring with itself
in degree zero, and the chains supported in the subspace with the chains of the subspace above.  The
squares commute because the augmentation and the boundary are both preserved by pushforward.
-/

open CategoryTheory Limits

namespace GaloisForLFunctions.HTGeometry

universe v

variable (R : Type) [CommRing R] {X : Type v} [TopologicalSpace X] (S : Set X)

theorem subChainIncl_symm (k : ℕ) (c : (subChains R S k)) :
    subChainIncl R S k ((subspaceChainEquiv R S k).symm c) = (c : C(topSimplex k, X) →₀ R) := by
  have h := subspaceChainEquiv_coe R S k ((subspaceChainEquiv R S k).symm c)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- The comparison map, degree by degree. -/
noncomputable def augSubComplexF : ∀ k,
    (augSub R X S).complex.X k ⟶ (augChain R ↥S).X k
  | 0 => ModuleCat.ofHom (Submodule.topEquiv).toLinearMap
  | (n + 1) => ModuleCat.ofHom (subspaceChainEquiv R S n).symm.toLinearMap

/-- The comparison chain map. -/
noncomputable def augSubComplexMap : (augSub R X S).complex ⟶ augChain R ↥S where
  f := augSubComplexF R S
  comm' := by
    rintro i j (hij : j + 1 = i)
    subst hij
    cases j with
    | zero =>
      have hd1 : ∀ y : C(topSimplex 0, ↥S) →₀ R,
          ((augChain R ↥S).d 1 0) y
            = (ULift.moduleEquiv (R := R) (M := R)).symm (singAug R y) := by
        intro y
        rw [augChain_d]
        rfl
      have hd2 : ∀ y : C(topSimplex 0, X) →₀ R,
          ((augChain R X).d 1 0) y
            = (ULift.moduleEquiv (R := R) (M := R)).symm (singAug R y) := by
        intro y
        rw [augChain_d]
        rfl
      refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
      have key := singAug_subChainIncl R S ((subspaceChainEquiv R S 0).symm c)
      rw [subChainIncl_symm] at key
      show ((augChain R ↥S).d 1 0) ((subspaceChainEquiv R S 0).symm c)
        = Submodule.topEquiv (((augSub R X S).complex.d 1 0) c)
      rw [hd1, ModuleSubcomplex.complex_d]
      show _ = ((augChain R X).d 1 0).hom
        (Subtype.val (p := fun z : C(topSimplex 0, X) →₀ R => z ∈ subChains R S 0) c)
      rw [hd2, ← key]
    | succ n =>
      have hd1 : ∀ y : C(topSimplex (n + 1), ↥S) →₀ R,
          ((augChain R ↥S).d (n + 2) (n + 1)) y = singBd R (↥S) n y := by
        intro y
        rw [augChain_d]
        rfl
      have hd2 : ∀ y : C(topSimplex (n + 1), X) →₀ R,
          ((augChain R X).d (n + 2) (n + 1)) y = singBd R X n y := by
        intro y
        rw [augChain_d]
        rfl
      refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
      have key := subChainIncl_singBd R S ((subspaceChainEquiv R S (n + 1)).symm c)
      rw [subChainIncl_symm] at key
      refine (subChainIncl_injective R S n) ?_
      show subChainIncl R S n
          (((augChain R ↥S).d (n + 2) (n + 1)) ((subspaceChainEquiv R S (n + 1)).symm c))
        = subChainIncl R S n ((subspaceChainEquiv R S n).symm
            (((augSub R X S).complex.d (n + 2) (n + 1)) c))
      rw [hd1, key, subChainIncl_symm, ModuleSubcomplex.complex_d]
      show _ = ((augChain R X).d (n + 2) (n + 1)).hom
        (Subtype.val (p := fun z : C(topSimplex (n + 1), X) →₀ R => z ∈ subChains R S (n + 1)) c)
      rw [hd2]

instance isIso_augSubComplexF (k : ℕ) : IsIso (augSubComplexF R S k) := by
  cases k with
  | zero =>
    exact ⟨ModuleCat.ofHom (Submodule.topEquiv (R := R)
        (M := ((augChain R X).X 0))).symm.toLinearMap,
      ModuleCat.hom_ext (LinearMap.ext fun x =>
        (Submodule.topEquiv (R := R) (M := ((augChain R X).X 0))).symm_apply_apply x),
      ModuleCat.hom_ext (LinearMap.ext fun x =>
        (Submodule.topEquiv (R := R) (M := ((augChain R X).X 0))).apply_symm_apply x)⟩
  | succ n =>
    exact ⟨ModuleCat.ofHom (subspaceChainEquiv R S n).toLinearMap,
      ModuleCat.hom_ext (LinearMap.ext fun x => (subspaceChainEquiv R S n).apply_symm_apply x),
      ModuleCat.hom_ext (LinearMap.ext fun x => (subspaceChainEquiv R S n).symm_apply_apply x)⟩

instance isIso_augSubComplexMap_f (k : ℕ) : IsIso ((augSubComplexMap R S).f k) :=
  isIso_augSubComplexF R S k

instance isIso_augSubComplexMap : IsIso (augSubComplexMap R S) :=
  HomologicalComplex.Hom.isIso_of_components _

/-- **The augmented chains supported in a subspace compute the reduced homology of that
subspace.** -/
noncomputable def augSubComplexIso : (augSub R X S).complex ≅ augChain R ↥S :=
  asIso (augSubComplexMap R S)

noncomputable def augSubHomologyIso (n : ℕ) :
    (augSub R X S).complex.homology n ≅ (augChain R ↥S).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso
    (augSubComplexIso R S)

end GaloisForLFunctions.HTGeometry

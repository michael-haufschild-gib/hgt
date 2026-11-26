import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedHomology

/-! A linear equivalence respecting the differential and projections gives
equivalences on all homogeneous cohomology groups. -/

noncomputable section

open CategoryTheory

namespace GlobalTheory.CechDR.FiniteGradedComplex

variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {G : FiniteGradedComplex K V} {H : FiniteGradedComplex K W} (e : V ≃ₗ[K] W)
  (hπ : ∀ n x, e (G.π n x) = H.π n (e x))

private def termCongr (n : ℕ) : G.term n ≃ₗ[K] H.term n where
  toFun x := ⟨e x.1, ⟨e x.1, (hπ n x.1).symm.trans (congrArg e (G.π_apply_term n x))⟩⟩
  invFun y := ⟨e.symm y.1, ⟨e.symm y.1, e.injective
    ((hπ n (e.symm y.1)).trans ((congrArg (H.π n) (e.apply_symm_apply y.1)).trans
      ((H.π_apply_term n y).trans (e.apply_symm_apply y.1).symm)))⟩⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  map_add' x y := Subtype.ext (e.map_add x.1 y.1)
  map_smul' r x := Subtype.ext (e.map_smul r x.1)

/-- A graded cochain isomorphism induces an isomorphism in each degree. -/
theorem nonempty_homology_equiv_of_graded (hd : ∀ x, e (G.d x) = H.d (e x)) (n : ℕ) :
    Nonempty ((G.degreeShort n).homology ≃ₗ[K] (H.degreeShort n).homology) := by
  have comm (j : ℕ) :
      (termCongr e hπ j).toModuleIso.hom ≫ ModuleCat.ofHom (H.termMap j) =
        ModuleCat.ofHom (G.termMap j) ≫ (termCongr e hπ (j + 1)).toModuleIso.hom := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change H.d (e x.1) = e (G.d x.1)
    exact (hd x.1).symm
  let φ : G.degreeShort n ≅ H.degreeShort n := ShortComplex.isoMk
    (termCongr e hπ n).toModuleIso (termCongr e hπ (n + 1)).toModuleIso
    (termCongr e hπ (n + 2)).toModuleIso (comm n) (comm (n + 1))
  exact ⟨(ShortComplex.homologyMapIso φ).toLinearEquiv⟩

end GlobalTheory.CechDR.FiniteGradedComplex

import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedPresentations

/-! A finite graded module has a finite free cover by homogeneous generators. -/

open DirectSum MvPolynomial

namespace GlobalTheory

theorem exists_graded_surjection {ι R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
    (D : ℤ → Submodule R M) [Decomposition D] [PolyGradedSMul ι D]
    [Module.Finite (MvPolynomial ι R) M] :
    ∃ (a : ℕ) (d : Fin a → ℤ) (f : (Fin a → MvPolynomial ι R) →ₗ[MvPolynomial ι R] M),
      IsGradedMap (grFree ι R d) D f ∧ Function.Surjective f := by
  classical
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := MvPolynomial ι R) (M := M)
  let U := G.sigma fun g => (decompose D g).support
  let e := U.equivFin.symm
  let g (j : Fin U.card) := gradedProj D (e j).1.2 (e j).1.1
  refine ⟨U.card, fun j => (e j).1.2, Fintype.linearCombination _ g,
    isGradedMap_linearCombination D (fun j => gradedProj_mem D _ _), ?_⟩
  rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, eq_top_iff, ← hG,
    Submodule.span_le]
  intro x hx
  rw [← sum_support_gradedProj D x]
  refine Submodule.sum_mem _ fun j hj => Submodule.subset_span ?_
  let z : U := ⟨⟨x, j⟩, Finset.mem_sigma.2 ⟨hx, hj⟩⟩
  exact ⟨e.symm z, by simp [g, z]⟩

end GlobalTheory

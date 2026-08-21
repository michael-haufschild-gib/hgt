import GaloisForLFunctions.HTGeometry.SimplicialMayerVietoris

/-!
# Relative chains of a subcomplex and the long exact sequence of a pair

The chain map induced by the inclusion of a subcomplex is a degreewise split monomorphism, because
in each degree it is the inclusion of a subcoproduct.  Hence the sequence

  `0 → C(A) → C(X) → C(X)/C(A) → 0`

of chain complexes is short exact, and the homology long exact sequence of a short exact sequence
applies: relative simplicial homology sits in a long exact sequence with the homology of the
subcomplex and of the ambient simplicial set.

Applied to the singular simplicial set of a topological space and the subcomplex of simplices
landing in a subspace, this is the long exact sequence of a pair in singular homology.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u w

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable (X : SSet.{w}) (R : C) (A : X.Subcomplex)

/-- The inclusion of a subcoproduct into the full coproduct is a split monomorphism. -/
theorem inclFull_comp_restrFull {T : Type w} (S : Set T) :
    inclFull R S ≫ restrFull R S = 𝟙 (subCoproduct R S) := by
  refine Sigma.hom_ext _ _ (fun x => ?_)
  rw [← Category.assoc, ι_inclFull R S x, ι_restrFull_of_mem R (x : T) x.2]
  simp

theorem mono_inclFull {T : Type w} (S : Set T) : Mono (inclFull R S) := by
  haveI : IsSplitMono (inclFull R S) := ⟨⟨restrFull R S, inclFull_comp_restrFull R S⟩⟩
  infer_instance

/-- The chain map induced by the inclusion of a subcomplex is a monomorphism. -/
instance mono_chainComplexMap_ι : Mono (SSet.chainComplexMap A.ι R) := by
  refine HomologicalComplex.mono_of_mono_f _ fun n => ?_
  rw [chainComplexMap_ι_f]
  exact mono_inclFull R _

/-- The relative chain complex `C(X)/C(A)` of a subcomplex. -/
noncomputable def relChainComplex : ChainComplex C ℕ :=
  cokernel (SSet.chainComplexMap A.ι R)

/-- The short complex `C(A) → C(X) → C(X)/C(A)`. -/
noncomputable def relChainShortComplex : ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk (SSet.chainComplexMap A.ι R) (cokernel.π _) (cokernel.condition _)

/-- **The relative chain sequence of a subcomplex is short exact.** -/
theorem relChainShortExact : (relChainShortComplex X R A).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel (relChainShortComplex X R A)
    (cokernelIsCokernel (SSet.chainComplexMap A.ι R))
  mono_f := mono_chainComplexMap_ι X R A
  epi_g := coequalizer.π_epi

/-- The connecting map of the pair. -/
noncomputable def relConnecting (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    (relChainComplex X R A).homology i ⟶ ((A : SSet.{w}).chainComplex R).homology j :=
  (relChainShortExact X R A).δ i j hij

theorem rel_homology_exact₁ (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    (ShortComplex.mk _ _ (ShortComplex.ShortExact.δ_comp
      (relChainShortExact X R A) i j hij)).Exact :=
  ShortComplex.ShortExact.homology_exact₁ (relChainShortExact X R A) i j hij

theorem rel_homology_exact₂ (i : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (relChainShortComplex X R A).f i)
      (HomologicalComplex.homologyMap (relChainShortComplex X R A).g i)
      (by rw [← HomologicalComplex.homologyMap_comp, (relChainShortComplex X R A).zero,
        HomologicalComplex.homologyMap_zero])).Exact :=
  ShortComplex.ShortExact.homology_exact₂ (relChainShortExact X R A) i

theorem rel_homology_exact₃ (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    (ShortComplex.mk _ _ (ShortComplex.ShortExact.comp_δ
      (relChainShortExact X R A) i j hij)).Exact :=
  ShortComplex.ShortExact.homology_exact₃ (relChainShortExact X R A) i j hij

end

end GaloisForLFunctions.HTGeometry

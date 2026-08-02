import GaloisForLFunctions.HTGeometry.NerveHomotopy
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate

/-!
# In the top degree homology is a subobject of the chains

A chain complex that vanishes one degree up has no boundaries in that degree, so its homology there
is its object of cycles, hence a subobject of the chains.  That identification is natural, so a chain
map which is a monomorphism in that degree is a monomorphism on homology there.

For a simplicial set of dimension at most `n` the normalized chains vanish above `n`, and their
degree-`n` part is the coproduct of copies of the coefficients over the nondegenerate `n`-simplices.
So a map of simplicial sets which is injective on nondegenerate `n`-simplices — and keeps them
nondegenerate — is a monomorphism on homology in degree `n`.  That is what makes a fundamental class
of a subcomplex of top dimension a nonzero class of the ambient complex.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u w

section Complexes

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- With nothing one degree up, the projection from the cycles to the homology is invertible. -/
theorem isIso_homologyπ_of_isZero (K : ChainComplex C ℕ) (n : ℕ) (h : Limits.IsZero (K.X (n + 1))) :
    IsIso (K.homologyπ n) :=
  K.isIso_homologyπ (n + 1) n (by simp) (h.eq_zero_of_src _)

/-- **In the top degree the homology is a subobject of the chains.** -/
noncomputable def topHomologyι (K : ChainComplex C ℕ) (n : ℕ)
    (h : Limits.IsZero (K.X (n + 1))) : K.homology n ⟶ K.X n :=
  haveI := isIso_homologyπ_of_isZero K n h
  inv (K.homologyπ n) ≫ K.iCycles n

theorem mono_topHomologyι (K : ChainComplex C ℕ) (n : ℕ) (h : Limits.IsZero (K.X (n + 1))) :
    Mono (topHomologyι K n h) := by
  haveI := isIso_homologyπ_of_isZero K n h
  rw [topHomologyι]
  exact mono_comp _ _

theorem topHomologyι_naturality {K L : ChainComplex C ℕ} (φ : K ⟶ L) (n : ℕ)
    (hK : Limits.IsZero (K.X (n + 1))) (hL : Limits.IsZero (L.X (n + 1))) :
    HomologicalComplex.homologyMap φ n ≫ topHomologyι L n hL
      = topHomologyι K n hK ≫ φ.f n := by
  haveI := isIso_homologyπ_of_isZero K n hK
  haveI := isIso_homologyπ_of_isZero L n hL
  rw [← cancel_epi (K.homologyπ n), topHomologyι, topHomologyι, ← Category.assoc,
    HomologicalComplex.homologyπ_naturality, Category.assoc, IsIso.hom_inv_id_assoc,
    HomologicalComplex.cyclesMap_i, Category.assoc, IsIso.hom_inv_id_assoc]

/-- **A chain map which is injective in the top degree is injective on homology there.** -/
theorem mono_homologyMap_of_mono_f {K L : ChainComplex C ℕ} (φ : K ⟶ L) (n : ℕ)
    (hK : Limits.IsZero (K.X (n + 1))) (hL : Limits.IsZero (L.X (n + 1)))
    (hmono : Mono (φ.f n)) : Mono (HomologicalComplex.homologyMap φ n) := by
  haveI := mono_topHomologyι K n hK
  have hcomp : Mono (HomologicalComplex.homologyMap φ n ≫ topHomologyι L n hL) := by
    rw [topHomologyι_naturality φ n hK hL]
    exact mono_comp _ _
  exact mono_of_mono _ (topHomologyι L n hL)

end Complexes

section Simplicial

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable {X Y : SSet.{w}} (f : X ⟶ Y) (R : C) (n : ℕ)

open scoped Classical in
/-- The retraction of the normalized chains attached to a map that is injective on nondegenerate
simplices. -/
noncomputable def nondegRetraction :
    (Y.normalizedChainComplex R).X n ⟶ (X.normalizedChainComplex R).X n :=
  (Y.isColimitCofanNormalizedChainComplex R n).desc
    (Cofan.mk _ fun y : Y.nonDegenerate n =>
      if h : ∃ x : X.nonDegenerate n, f.app _ (x : X _⦋n⦌) = (y : Y _⦋n⦌)
        then X.ιNormalizedChainComplex (h.choose : X _⦋n⦌) else 0)

/-- **A map injective on nondegenerate simplices is injective on normalized chains.** -/
theorem mono_normalizedChainComplexMap_f
    (hnd : ∀ x : X _⦋n⦌, x ∈ X.nonDegenerate n → f.app _ x ∈ Y.nonDegenerate n)
    (hinj : ∀ x x' : X _⦋n⦌, f.app _ x = f.app _ x' → x = x') :
    Mono ((SSet.normalizedChainComplexMap f R).f n) := by
  classical
  have hretr : (SSet.normalizedChainComplexMap f R).f n ≫ nondegRetraction f R n = 𝟙 _ := by
    ext x hx
    rw [← Category.assoc, SSet.ι_normalizedChainComplexMap_f, Category.comp_id]
    have hy : ∃ x' : X.nonDegenerate n, f.app _ (x' : X _⦋n⦌) = f.app _ x := ⟨⟨x, hx⟩, rfl⟩
    have hfac := (Y.isColimitCofanNormalizedChainComplex R n).fac
      (Cofan.mk _ fun y : Y.nonDegenerate n =>
        if h : ∃ x : X.nonDegenerate n, f.app _ (x : X _⦋n⦌) = (y : Y _⦋n⦌)
          then X.ιNormalizedChainComplex (h.choose : X _⦋n⦌) else 0)
      ⟨⟨f.app _ x, hnd x hx⟩⟩
    rw [nondegRetraction]
    refine hfac.trans ?_
    show (if h : ∃ x' : X.nonDegenerate n, f.app _ (x' : X _⦋n⦌) = f.app _ x
      then X.ιNormalizedChainComplex (h.choose : X _⦋n⦌) else 0) = _
    rw [dif_pos hy]
    exact congrArg X.ιNormalizedChainComplex (hinj _ _ hy.choose_spec)
  exact ⟨fun {_} g h heq => by
    have := congrArg (fun t => t ≫ nondegRetraction f R n) heq
    simpa only [Category.assoc, hretr, Category.comp_id] using this⟩

end Simplicial

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable {X Y : SSet.{w}} (f : X ⟶ Y) (R : C) (n : ℕ)

/-- **A map of simplicial sets of dimension at most `n` which is injective on nondegenerate
`n`-simplices is injective on homology in degree `n`.** -/
theorem mono_homologyMap_of_injective_nonDegenerate [X.HasDimensionLT (n + 1)]
    [Y.HasDimensionLT (n + 1)]
    (hnd : ∀ x : X _⦋n⦌, x ∈ X.nonDegenerate n → f.app _ x ∈ Y.nonDegenerate n)
    (hinj : ∀ x x' : X _⦋n⦌, f.app _ x = f.app _ x' → x = x') :
    Mono (SSet.homologyMap f R n) := by
  haveI hmono := mono_normalizedChainComplexMap_f f R n hnd hinj
  haveI hnorm : Mono (HomologicalComplex.homologyMap (SSet.normalizedChainComplexMap f R) n) :=
    mono_homologyMap_of_mono_f _ n
      (X.isZero_normalizedChainComplex_X_of_hasDimensionLT R (n + 1) (n + 1))
      (Y.isZero_normalizedChainComplex_X_of_hasDimensionLT R (n + 1) (n + 1)) hmono
  have hsq := congrArg (fun ψ => HomologicalComplex.homologyMap ψ n)
    (SSet.toNormalizedChainComplex_normalizedChainComplexMap f R)
  simp only [HomologicalComplex.homologyMap_comp] at hsq
  haveI : IsIso (HomologicalComplex.homologyMap (X.toNormalizedChainComplex R) n) := by
    infer_instance
  haveI : IsIso (HomologicalComplex.homologyMap (Y.toNormalizedChainComplex R) n) := by
    infer_instance
  have hfac : HomologicalComplex.homologyMap (SSet.chainComplexMap f R) n
      = HomologicalComplex.homologyMap (X.toNormalizedChainComplex R) n
        ≫ HomologicalComplex.homologyMap (SSet.normalizedChainComplexMap f R) n
        ≫ inv (HomologicalComplex.homologyMap (Y.toNormalizedChainComplex R) n) := by
    rw [← Category.assoc, hsq, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  show Mono (HomologicalComplex.homologyMap (SSet.chainComplexMap f R) n)
  rw [hfac]
  exact mono_comp _ _

/-- **In the top degree the homology is the cycles of the normalized chains.**  For a simplicial set
of dimension at most `n` there are no boundaries in degree `n`, so a homology class there is exactly
a normalized cycle. -/
noncomputable def topHomologyIsoCycles [X.HasDimensionLT (n + 1)] :
    X.homology R n ≅ (X.normalizedChainComplex R).cycles n := by
  haveI : IsIso (HomologicalComplex.homologyMap (X.toNormalizedChainComplex R) n) := inferInstance
  haveI := isIso_homologyπ_of_isZero (X.normalizedChainComplex R) n
    (X.isZero_normalizedChainComplex_X_of_hasDimensionLT R (n + 1) (n + 1))
  exact asIso (HomologicalComplex.homologyMap (X.toNormalizedChainComplex R) n)
    ≪≫ (asIso ((X.normalizedChainComplex R).homologyπ n)).symm

end

end GaloisForLFunctions.HTGeometry

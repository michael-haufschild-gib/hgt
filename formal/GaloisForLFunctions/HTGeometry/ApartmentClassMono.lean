import GaloisForLFunctions.HTGeometry.TopDegreeMono
import GaloisForLFunctions.HTGeometry.ApartmentClass
import GaloisForLFunctions.HTGeometry.ProjectiveFlagDimension

/-!
# The apartment class is a monomorphism

The apartment of a frame and the building have the same top dimension, and the inclusion of the
apartment is injective on chains and keeps strict chains strict.  In the top degree homology is a
subobject of the normalized chains, so the inclusion is injective on top homology: the fundamental
class of the Coxeter sphere of a frame is a genuine, nonzero class of the Steinberg module.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite Module

universe v u

/-! ## Chain bounds and dimension -/

section Chains

variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- A simplex of a nerve is determined by its vertices. -/
theorem nerve_simplex_ext {n : ℕ} {x x' : (nerve P) _⦋n⦌} (h : ∀ i, x.obj i = x'.obj i) : x = x' :=
  CategoryTheory.Functor.ext h fun _ _ _ => Subsingleton.elim _ _

/-- **A nerve of dimension below `m` has strict chains of at most `m` members.** -/
theorem chain_bound_of_hasDimensionLT (m : ℕ)
    [h : SSet.HasDimensionLT (nerveFunctor.obj (Cat.of P)) m] {n : ℕ} (f : Fin (n + 1) → P)
    (hf : StrictMono f) : n + 1 ≤ m := by
  by_contra hcon
  have hdeg : (nerve P).degenerate n = ⊤ := h.degenerate_eq_top n (by omega)
  have hnd : (Monotone.functor hf.monotone : (nerve P) _⦋n⦌) ∈ (nerve P).nonDegenerate n :=
    (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).2 hf
  have hmem : (Monotone.functor hf.monotone : (nerve P) _⦋n⦌) ∈ (nerve P).degenerate n := by
    rw [hdeg]
    trivial
  exact ((SSet.mem_nonDegenerate_iff_notMem_degenerate _ _).1 hnd) hmem

/-- **An order-reflecting map inherits the dimension bound of its target.** -/
theorem hasDimensionLT_nerve_of_reflecting (m : ℕ) (g : P →o Q) (hg : ∀ a b : P, g a ≤ g b → a ≤ b)
    [SSet.HasDimensionLT (nerveFunctor.obj (Cat.of Q)) m] :
    SSet.HasDimensionLT (nerveFunctor.obj (Cat.of P)) m := by
  refine hasDimensionLT_nerve_of_chain_bound m fun n f hf => ?_
  refine chain_bound_of_hasDimensionLT m (fun i => g (f i)) fun i j hij => ?_
  refine lt_of_le_of_ne (g.monotone (le_of_lt (hf hij))) fun hcon => ?_
  exact absurd (hf hij) (not_lt_of_ge (hg _ _ (le_of_eq hcon.symm)))

end Chains

section Dimension

variable (K V : Type u) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **The building of a vector space has dimension below `N - 1`.** -/
theorem properPartSubmoduleHasDimensionLT :
    SSet.HasDimensionLT (nerveFunctor.obj (Cat.of (properPart (Submodule K V))))
      (finrank K V - 1) := by
  classical
  refine hasDimensionLT_nerve_of_chain_bound _ fun n f hf => ?_
  have hinj : Function.Injective (fun i : Fin (n + 1) => ((f i : properPart (Submodule K V)) :
      Submodule K V)) := fun i j h => hf.injective (Subtype.ext h)
  set T : Finset (Submodule K V) :=
    Finset.image (fun i : Fin (n + 1) => ((f i : properPart (Submodule K V)) : Submodule K V))
      Finset.univ with hT
  have hcard : T.card = n + 1 := by
    rw [hT, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hmem : ∀ W ∈ T, ∃ i : Fin (n + 1),
      ((f i : properPart (Submodule K V)) : Submodule K V) = W := by
    intro W hW
    rw [hT, Finset.mem_image] at hW
    obtain ⟨i, -, hi⟩ := hW
    exact ⟨i, hi⟩
  have hchain : ∀ W ∈ T, ∀ W' ∈ T, W ≤ W' ∨ W' ≤ W := by
    intro W hW W' hW'
    obtain ⟨i, rfl⟩ := hmem W hW
    obtain ⟨j, rfl⟩ := hmem W' hW'
    rcases le_total i j with h | h
    · exact Or.inl (hf.monotone h)
    · exact Or.inr (hf.monotone h)
  have hbot : ∀ W ∈ T, W ≠ ⊥ := by
    intro W hW
    obtain ⟨i, rfl⟩ := hmem W hW
    exact ne_of_gt (f i).2.1
  have htop : ∀ W ∈ T, W ≠ ⊤ := by
    intro W hW
    obtain ⟨i, rfl⟩ := hmem W hW
    exact ne_of_lt (f i).2.2
  have := card_le_finrank_sub_one T hchain hbot htop
  omega

end Dimension

section Mono

variable {K V ι : Type u} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

omit [Fintype ι] in
/-- The vertices of a frame's apartment are distinguished by the subspaces they span. -/
theorem apartmentVertices_injective (b : Basis ι K V) :
    Function.Injective (apartmentVertices b) := fun s t h =>
  le_antisymm ((apartmentVertices_le_iff b s t).1 (le_of_eq h))
    ((apartmentVertices_le_iff b t s).1 (le_of_eq h.symm))

omit [Fintype ι] in
/-- The inclusion of an apartment acts on the vertices of a chain by spanning. -/
theorem apartmentNerveMap_obj (b : Basis ι K V) (n : ℕ)
    (x : (nerve (properPart (Set ι))) _⦋n⦌) (i : Fin (n + 1)) :
    (((apartmentNerveMap b).app (op ⦋n⦌) x : (nerve (properPart (Submodule K V))) _⦋n⦌)).obj i
      = apartmentVertices b (x.obj i) := rfl

omit [Fintype ι] in
/-- **The apartment has the dimension of the building.** -/
theorem apartmentHasDimensionLT [FiniteDimensional K V] (b : Basis ι K V) :
    SSet.HasDimensionLT (nerveFunctor.obj (Cat.of (properPart (Set ι)))) (finrank K V - 1) := by
  haveI := properPartSubmoduleHasDimensionLT K V
  exact hasDimensionLT_nerve_of_reflecting _ (apartmentVertices b)
    fun s t h => (apartmentVertices_le_iff b s t).1 h

/-- **The inclusion of an apartment is injective on top homology.** -/
theorem mono_homologyMap_apartmentNerveMap [FiniteDimensional K V] (b : Basis ι K V) (R : C)
    (h3 : 3 ≤ Nat.card ι) :
    Mono (SSet.homologyMap (apartmentNerveMap b) R (Nat.card ι - 2)) := by
  have hdeg : Nat.card ι - 2 + 1 = finrank K V - 1 := by
    rw [card_eq_finrank b] at h3 ⊢
    omega
  haveI hdimA : SSet.HasDimensionLT (nerveFunctor.obj (Cat.of (properPart (Set ι))))
      (Nat.card ι - 2 + 1) := by
    rw [hdeg]
    exact apartmentHasDimensionLT b
  haveI hdimB : SSet.HasDimensionLT (nerveFunctor.obj (Cat.of (properPart (Submodule K V))))
      (Nat.card ι - 2 + 1) := by
    rw [hdeg]
    exact properPartSubmoduleHasDimensionLT K V
  refine mono_homologyMap_of_injective_nonDegenerate (apartmentNerveMap b) R (Nat.card ι - 2)
    (fun x hx => ?_) (fun x x' hxx' => ?_)
  · have hxy : (x : (nerve (properPart (Set ι))) _⦋Nat.card ι - 2⦌)
        ∈ (nerve (properPart (Set ι))).nonDegenerate (Nat.card ι - 2) := hx
    have hx' := (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).1 hxy
    have hgoal : ((apartmentNerveMap b).app (op ⦋Nat.card ι - 2⦌) x :
        (nerve (properPart (Submodule K V))) _⦋Nat.card ι - 2⦌)
        ∈ (nerve (properPart (Submodule K V))).nonDegenerate (Nat.card ι - 2) := by
      refine (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).2 fun i j hij => ?_
      rw [apartmentNerveMap_obj b _ _ i, apartmentNerveMap_obj b _ _ j]
      refine lt_of_le_of_ne ((apartmentVertices b).monotone (le_of_lt (hx' hij))) fun hcon => ?_
      exact absurd (hx' hij) (not_lt_of_ge (le_of_eq (apartmentVertices_injective b hcon).symm))
    exact hgoal
  · refine nerve_simplex_ext fun i => apartmentVertices_injective b ?_
    rw [← apartmentNerveMap_obj b _ _ i, ← apartmentNerveMap_obj b _ _ i]
    exact congrArg (fun s : (nerve (properPart (Submodule K V))) _⦋Nat.card ι - 2⦌ => s.obj i) hxx'

/-- **The apartment class is a monomorphism.** -/
theorem mono_apartmentClass [FiniteDimensional K V] (b : Basis ι K V) (R : C)
    (h3 : 3 ≤ Nat.card ι) : Mono (apartmentClass b R h3) := by
  haveI := mono_homologyMap_apartmentNerveMap b R h3
  rw [apartmentClass, apartmentClass']
  exact mono_comp _ _

/-- **The apartment class of a frame is not zero.**  The fundamental class of the Coxeter sphere of
an observer frame is a nonzero class of the Steinberg module. -/
theorem apartmentClass_ne_zero [FiniteDimensional K V] (b : Basis ι K V) (R : C)
    (h3 : 3 ≤ Nat.card ι) (hR : ¬ Limits.IsZero R) : apartmentClass b R h3 ≠ 0 := by
  intro hcon
  haveI := mono_apartmentClass b R h3
  refine hR ?_
  rw [Limits.IsZero.iff_id_eq_zero]
  refine (cancel_mono (apartmentClass b R h3)).1 ?_
  rw [Category.id_comp, hcon, Limits.zero_comp]

end Mono

end GaloisForLFunctions.HTGeometry

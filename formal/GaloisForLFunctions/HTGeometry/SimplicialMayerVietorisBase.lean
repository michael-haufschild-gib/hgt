import GaloisForLFunctions.HTGeometry.SimplicialMayerVietorisConnected
import GaloisForLFunctions.HTGeometry.SubcomplexDistrib

/-!
# Folding a cover whose pieces meet only inside a base

A cover by a fixed base together with a family of further pieces is foldable when the pieces meet
each other only inside the base: the intersection of a piece with the partial union built so far is
then the intersection of that piece with the base alone, independently of how much has been built.
Each Mayer--Vietoris step therefore sees the same intersection term, and the whole induction needs
only one hypothesis per piece.

Two statements are folded, in the two forms the induction needs: vanishing in a positive degree,
where the intersection term enters through the injectivity of its homology one degree down; and
connectedness in degree zero, where the intersection term enters only through the existence of a
vertex.

This is the shape of the Solomon--Tits cover of a building: the subspaces that do not span with a
fixed point form the base, the stars of the hyperplanes avoiding that point are the pieces, and two
such stars meet only in subspaces of both hyperplanes, which already lie in the base.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u w

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable (X : SSet.{w}) (R : C) {ι : Type*} (A₀ : X.Subcomplex) (A : ι → X.Subcomplex)

/-- **The intersection of a piece with a partial union is its intersection with the base**, as soon
as the pieces meet each other inside the base. -/
theorem base_sup_inf_eq (hsink : ∀ b a, A b ⊓ A a ≤ A₀ ⊓ A a) (s : Finset ι) (a : ι) :
    (A₀ ⊔ s.sup A) ⊓ A a = A₀ ⊓ A a := by
  refine le_antisymm ?_ (inf_le_inf_right _ le_sup_left)
  rw [Subcomplex.sup_inf_right]
  exact sup_le le_rfl (finsetSup_inf_le A (A a) (A₀ ⊓ A a) (fun b => hsink b a) s)

/-- Injectivity of the homology of an inclusion depends only on the subcomplex included. -/
theorem mono_homologyMap_homOfLE_congr {P Q T : X.Subcomplex} (hPQ : P = Q) (hP : P ≤ T)
    (hQ : Q ≤ T) (j : ℕ)
    (h : Mono (SSet.homologyMap (SSet.Subcomplex.homOfLE hQ) R j)) :
    Mono (SSet.homologyMap (SSet.Subcomplex.homOfLE hP) R j) := by
  subst hPQ
  exact h

/-- Rearranging a partial union so that the new piece comes last. -/
theorem base_sup_insert (s : Finset ι) (a : ι) [DecidableEq ι] :
    A₀ ⊔ (insert a s).sup A = (A₀ ⊔ s.sup A) ⊔ A a := by
  rw [Finset.sup_insert, ← sup_assoc, sup_comm (A₀) (A a), sup_assoc, sup_comm (A a) (A₀ ⊔ s.sup A)]

/-- **Vanishing for a cover with a base.**  The base and every piece are acyclic in degree `i`, and
the homology of the intersection of the base with each piece injects into that of the piece one
degree down; then every partial union is acyclic in degree `i`. -/
theorem isZero_homology_base_finsetSup (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j)
    (hsink : ∀ b a, A b ⊓ A a ≤ A₀ ⊓ A a)
    (h0 : Limits.IsZero (((A₀ : SSet.{w}).chainComplex R).homology i))
    (hA : ∀ a, Limits.IsZero (((A a : SSet.{w}).chainComplex R).homology i))
    (hmono : ∀ a, Mono (SSet.homologyMap
      (SSet.Subcomplex.homOfLE (inf_le_right : A₀ ⊓ A a ≤ A a)) R j))
    (s : Finset ι) :
    Limits.IsZero ((((A₀ ⊔ s.sup A : X.Subcomplex) : SSet.{w}).chainComplex R).homology i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sup_empty, sup_bot_eq]
      exact h0
  | insert a s _ ih =>
      rw [base_sup_insert X A₀ A s a]
      refine isZero_homology_of_mayerVietoris_sup_mono X R (A₀ ⊔ s.sup A) (A a) i j hij ih (hA a)
        (mono_homologyMap_mvChainFst_of_right X R (A₀ ⊔ s.sup A) (A a) j ?_)
      exact mono_homologyMap_homOfLE_congr X R (base_sup_inf_eq X A₀ A hsink s a) _ _ j (hmono a)

/-- **Connectedness for a cover with a base.**  The base and every piece are homologically constant
in degree zero, and each piece meets the base in a vertex; then every partial union is
homologically constant in degree zero. -/
theorem exists_homologyMap_const_eq_id_base_finsetSup
    (hsink : ∀ b a, A b ⊓ A a ≤ A₀ ⊓ A a)
    (p : ∀ a, ((A₀ ⊓ A a : X.Subcomplex) : SSet.{w}) _⦋0⦌)
    (h0 : ∃ v : ((A₀ : X.Subcomplex) : SSet.{w}) _⦋0⦌,
      SSet.homologyMap (SSet.const (X := ((A₀ : X.Subcomplex) : SSet.{w}))
        (Y := ((A₀ : X.Subcomplex) : SSet.{w})) v) R 0 = 𝟙 _)
    (hA : ∀ a, ∃ v : ((A a : X.Subcomplex) : SSet.{w}) _⦋0⦌,
      SSet.homologyMap (SSet.const (X := ((A a : X.Subcomplex) : SSet.{w}))
        (Y := ((A a : X.Subcomplex) : SSet.{w})) v) R 0 = 𝟙 _)
    (s : Finset ι) :
    ∃ v : ((A₀ ⊔ s.sup A : X.Subcomplex) : SSet.{w}) _⦋0⦌,
      SSet.homologyMap (SSet.const (X := ((A₀ ⊔ s.sup A : X.Subcomplex) : SSet.{w}))
        (Y := ((A₀ ⊔ s.sup A : X.Subcomplex) : SSet.{w})) v) R 0 = 𝟙 _ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sup_empty, sup_bot_eq]
      exact h0
  | insert a s _ ih =>
      rw [base_sup_insert X A₀ A s a]
      obtain ⟨v, hv⟩ := ih
      obtain ⟨w, hw⟩ := hA a
      refine ⟨supVertex ((base_sup_inf_eq X A₀ A hsink s a) ▸ p a), ?_⟩
      exact homologyMap_const_eq_id_of_sup X R (A₀ ⊔ s.sup A) (A a) _
        (homologyMap_const_eq_id_of_vertex R 0 hv _)
        (homologyMap_const_eq_id_of_vertex R 0 hw _)

end

end GaloisForLFunctions.HTGeometry

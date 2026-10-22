import GaloisForLFunctions.RHTower.Deninger.DeningerPushoutFirstLetter

/-!
# Acyclicity of the tree of cosets

The boundary map of the tree of cosets of a pushout of groups is injective.  The proof grades the
edges by the distance from the base coset to their far endpoint, and shows that an edge of maximal
grade in the support of a cycle is the only edge of the support meeting one of its vertices, so its
coefficient is forced to vanish.

* `deningerEdgeRank` : the grading.
* `deningerTreeBoundary_injective` : the boundary map is injective.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

variable {ι : Type u} {G : ι → Type u} {H : Type u} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

section Rank

variable [DecidableEq ι] [∀ i, DecidableEq (G i)]

/-- The rank of an edge: the distance from the base coset to the endpoint of the edge that is
further away.  The edge `(i, x)` points away from the base coset exactly when the normal form
attached to `x` does not already begin in the factor `i`. -/
noncomputable def deningerEdgeRank (d : NormalWord.Transversal φ) (e : DeningerTreeEdge φ) : ℕ :=
  2 * deningerCosetLen d e.coset + (if deningerFirstIdx d e.coset = some e.idx then 0 else 1)

end Rank

section Coefficients

open scoped Classical

variable (k : Type u) [CommRing k]

/-- The coefficient of a vertex in a chain. -/
noncomputable def deningerVertexCoeff (v : DeningerTreeVertex φ) :
    MonoidAlgebra k (DeningerTreeVertex φ) →ₗ[k] k :=
  Finsupp.lapply (R := k) v ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

theorem deningerVertexCoeff_single (v w : DeningerTreeVertex φ) (c : k) :
    deningerVertexCoeff k v (MonoidAlgebra.single w c) = if w = v then c else 0 := by
  show Finsupp.lapply (R := k) v
    ((MonoidAlgebra.coeffLinearEquiv k) (MonoidAlgebra.single w c)) = _
  rw [show (MonoidAlgebra.coeffLinearEquiv k) (MonoidAlgebra.single w c) =
    Finsupp.single w c from rfl]
  exact Finsupp.single_apply

/-- The incidence coefficient of a vertex and an edge. -/
noncomputable def deningerBoundaryChar (v : DeningerTreeVertex φ) (e : DeningerTreeEdge φ) : k :=
  (if DeningerTreeVertex.ofSummand e.idx (deningerEdgeHead e.idx e.coset) = v then (1 : k)
    else 0) -
  (if DeningerTreeVertex.ofBase e.coset = v then (1 : k) else 0)

theorem deningerVertexCoeff_boundary (v : DeningerTreeVertex φ)
    (f : MonoidAlgebra k (DeningerTreeEdge φ)) :
    deningerVertexCoeff k v (deningerTreeBoundary k f) =
      (MonoidAlgebra.coeffLinearEquiv k f).sum
        (fun e c => c • deningerBoundaryChar k v e) := by
  have key : deningerVertexCoeff k v ∘ₗ deningerTreeBoundary k =
      Finsupp.lift k k (DeningerTreeEdge φ) (deningerBoundaryChar k v) ∘ₗ
        (MonoidAlgebra.coeffLinearEquiv k).toLinearMap := by
    refine MonoidAlgebra.lhom_ext' fun e => LinearMap.ext_ring ?_
    show deningerVertexCoeff k v (deningerTreeBoundary k (MonoidAlgebra.single e (1 : k))) =
      Finsupp.lift k k (DeningerTreeEdge φ) (deningerBoundaryChar k v)
        ((MonoidAlgebra.coeffLinearEquiv k) (MonoidAlgebra.single e (1 : k)))
    rw [deningerTreeBoundary_single, one_smul, map_sub, deningerVertexCoeff_single,
      deningerVertexCoeff_single,
      show (MonoidAlgebra.coeffLinearEquiv k) (MonoidAlgebra.single e (1 : k)) =
        Finsupp.single e (1 : k) from rfl,
      Finsupp.lift_apply, Finsupp.sum_single_index (by simp)]
    simp [deningerBoundaryChar]
  calc deningerVertexCoeff k v (deningerTreeBoundary k f)
      = Finsupp.lift k k (DeningerTreeEdge φ) (deningerBoundaryChar k v)
          ((MonoidAlgebra.coeffLinearEquiv k) f) := DFunLike.congr_fun key f
    _ = _ := Finsupp.lift_apply _ _ _ _ _

end Coefficients

section Acyclic

open scoped Classical

variable (k : Type u) [CommRing k]

/-- **The tree of cosets is acyclic.**  An edge of maximal rank in the support of a cycle is the
only edge of the support meeting one of its two vertices, so its coefficient vanishes. -/
theorem deningerTreeBoundary_injective (hφ : ∀ i, Function.Injective (φ i)) :
    Function.Injective (deningerTreeBoundary (φ := φ) k) := by
  classical
  obtain ⟨d⟩ := NormalWord.transversal_nonempty φ hφ
  have key : ∀ f : MonoidAlgebra k (DeningerTreeEdge φ),
      deningerTreeBoundary k f = 0 → f = 0 := by
    intro f hf
    by_contra hne
    set F := (MonoidAlgebra.coeffLinearEquiv k) f with hFdef
    have hFne : F ≠ 0 := fun h => hne ((MonoidAlgebra.coeffLinearEquiv k).map_eq_zero_iff.1 h)
    obtain ⟨e₀, he₀, hmax⟩ := F.support.exists_max_image (deningerEdgeRank d)
      (Finsupp.support_nonempty_iff.2 hFne)
    obtain ⟨i₀, x₀⟩ := e₀
    have hFe₀ : F ⟨i₀, x₀⟩ ≠ 0 := Finsupp.mem_support_iff.1 he₀
    by_cases hcase : deningerFirstIdx d x₀ = some i₀
    · have hchar : ∀ e : DeningerTreeEdge φ,
          deningerBoundaryChar k (DeningerTreeVertex.ofBase x₀) e =
            -(if e.coset = x₀ then (1 : k) else 0) := by
        intro e
        simp [deningerBoundaryChar]
      have hzero : ∀ e : DeningerTreeEdge φ, F e ≠ 0 → e ≠ ⟨i₀, x₀⟩ →
          F e • deningerBoundaryChar k (DeningerTreeVertex.ofBase x₀) e = 0 := by
        intro e hFe hee
        have hcoset : e.coset ≠ x₀ := by
          intro hc
          have hidx : e.idx ≠ i₀ := fun hi => hee (DeningerTreeEdge.ext hi hc)
          have hr : deningerEdgeRank d e = 2 * deningerCosetLen d x₀ + 1 := by
            rw [deningerEdgeRank, hc, if_neg (by rw [hcase]; simpa using Ne.symm hidx)]
          have h₀ : deningerEdgeRank d (⟨i₀, x₀⟩ : DeningerTreeEdge φ) =
              2 * deningerCosetLen d x₀ := by
            rw [deningerEdgeRank]
            simp [hcase]
          have := hmax e (Finsupp.mem_support_iff.2 hFe)
          omega
        rw [hchar, if_neg hcoset]
        simp
      have hsum := deningerVertexCoeff_boundary k (DeningerTreeVertex.ofBase x₀) f
      rw [hf, map_zero, ← hFdef, Finsupp.sum_eq_single ⟨i₀, x₀⟩ hzero (by simp)] at hsum
      rw [hchar, if_pos rfl] at hsum
      simp at hsum
      exact hFe₀ hsum
    · have hchar : ∀ e : DeningerTreeEdge φ,
          deningerBoundaryChar k
              (DeningerTreeVertex.ofSummand i₀ (deningerEdgeHead i₀ x₀)) e =
            (if DeningerTreeVertex.ofSummand e.idx (deningerEdgeHead e.idx e.coset) =
              DeningerTreeVertex.ofSummand i₀ (deningerEdgeHead i₀ x₀)
              then (1 : k) else 0) := by
        intro e
        simp [deningerBoundaryChar]
      have hzero : ∀ e : DeningerTreeEdge φ, F e ≠ 0 → e ≠ ⟨i₀, x₀⟩ →
          F e • deningerBoundaryChar k
            (DeningerTreeVertex.ofSummand i₀ (deningerEdgeHead i₀ x₀)) e = 0 := by
        intro e hFe hee
        obtain ⟨i, x⟩ := e
        rw [hchar, if_neg ?_, smul_zero]
        intro hveq
        simp only [DeningerTreeVertex.ofSummand.injEq] at hveq
        obtain ⟨hidx, hheq⟩ := hveq
        subst i
        have hhead : deningerEdgeHead i₀ x = deningerEdgeHead i₀ x₀ := eq_of_heq hheq
        obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective x₀
        obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective x
        have hcoset : x ≠ x₀ := fun hc => hee (DeningerTreeEdge.ext rfl hc)
        have hmem : g₀⁻¹ * g ∈ (PushoutI.of (φ := φ) i₀).range := by
          have hq : (QuotientGroup.mk g₀ : PushoutI φ ⧸ (PushoutI.of (φ := φ) i₀).range) =
              QuotientGroup.mk g := by
            rw [← hg₀, ← hg] at hhead
            simpa using hhead.symm
          exact QuotientGroup.eq.1 hq
        obtain ⟨y, hy⟩ := hmem
        have hgg : g = g₀ * PushoutI.of i₀ y := by rw [hy]; group
        have hne' : (QuotientGroup.mk (g₀ * PushoutI.of i₀ y) :
            PushoutI φ ⧸ (PushoutI.base φ).range) ≠ QuotientGroup.mk g₀ := by
          rw [← hgg, hg, hg₀]
          exact hcoset
        have hfirst : deningerFirstIdx d (QuotientGroup.mk g₀ :
            PushoutI φ ⧸ (PushoutI.base φ).range) ≠ some i₀ := by
          rw [hg₀]
          exact hcase
        have hlen : deningerCosetLen d x = deningerCosetLen d x₀ + 1 := by
          rw [← hg, ← hg₀, hgg]
          exact deningerCosetLen_mul_of_eq i₀ g₀ y hfirst hne'
        have h₀ : deningerEdgeRank d (⟨i₀, x₀⟩ : DeningerTreeEdge φ) =
            2 * deningerCosetLen d x₀ + 1 := by
          rw [deningerEdgeRank]
          simp [hcase]
        have hle := hmax ⟨i₀, x⟩ (Finsupp.mem_support_iff.2 hFe)
        have hge : 2 * deningerCosetLen d x ≤
            deningerEdgeRank d (⟨i₀, x⟩ : DeningerTreeEdge φ) := by
          rw [deningerEdgeRank]
          simp only []
          omega
        omega
      have hsum := deningerVertexCoeff_boundary k
        (DeningerTreeVertex.ofSummand i₀ (deningerEdgeHead i₀ x₀)) f
      rw [hf, map_zero, ← hFdef, Finsupp.sum_eq_single ⟨i₀, x₀⟩ hzero (by simp)] at hsum
      rw [hchar, if_pos rfl] at hsum
      simp at hsum
      exact hFe₀ hsum.symm
  intro f₁ f₂ h
  exact sub_eq_zero.1 (key (f₁ - f₂) (by rw [map_sub, h, sub_self]))

end Acyclic

end RHTower

import GaloisForLFunctions.HTGeometry.UnboundedFredholm
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Closed inverses of compact hyperplane injections

Let `K` be a closed subspace of a complex Hilbert space `H`, and let
`B : K → H` be a bounded injective map with dense range.  Its graph inverse, followed by the
inclusion `K → H`, is a closed densely defined operator `A` with

`ker A = 0`, `range A = K`.

When `K` is a hyperplane this makes `A` Fredholm of index `-1`.  The results below keep the
operator as an actual `LinearPMap`; no graph relation or Fredholm datum is postulated.
-/

open Module Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A compact resolvent at `z`, stated as an actual compact bounded two-sided inverse of `T-z`.
This definition applies equally to self-adjoint squares and block Dirac operators. -/
def LinearPMap.HasCompactResolventAt (T : H →ₗ.[ℂ] H) (z : ℂ) : Prop :=
  ∃ R : H →L[ℂ] H, IsCompactOperator R ∧
    (∀ x : H, R x ∈ T.domain) ∧
    (∀ x : H, T ⟨R x, by assumption⟩ - z • R x = x) ∧
    (∀ x : T.domain, R (T x - z • (x : H)) = (x : H))

/-- The bounded injection whose graph is inverted. -/
def hyperplaneInjectionPMap (K : Submodule ℂ H) (B : K →L[ℂ] H) : K →ₗ.[ℂ] H :=
  B.toLinearMap.toPMap ⊤

/-- Closed graph inverse of `B`, with values included back into the ambient Hilbert space. -/
def closedHyperplaneInverse (K : Submodule ℂ H) (B : K →L[ℂ] H) : H →ₗ.[ℂ] H :=
  K.subtype.compPMap (hyperplaneInjectionPMap K B).inverse

theorem hyperplaneInjectionPMap_toFun_ker_eq_bot
    (K : Submodule ℂ H) (B : K →L[ℂ] H) (hB : Function.Injective B) :
    LinearMap.ker (hyperplaneInjectionPMap K B).toFun = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  apply Subtype.ext
  exact hB hx

theorem closedHyperplaneInverse_domain
    (K : Submodule ℂ H) (B : K →L[ℂ] H) :
    (closedHyperplaneInverse K B).domain = B.range := by
  rw [closedHyperplaneInverse, LinearMap.compPMap, LinearPMap.inverse_domain]
  rfl

theorem closedHyperplaneInverse_apply_B
    (K : Submodule ℂ H) (B : K →L[ℂ] H) (hB : Function.Injective B) (x : K) :
    B x ∈ (closedHyperplaneInverse K B).domain ∧
      closedHyperplaneInverse K B ⟨B x, by simpa [closedHyperplaneInverse_domain]⟩ = (x : H) := by
  have hmem : B x ∈ (closedHyperplaneInverse K B).domain := by
    rw [closedHyperplaneInverse_domain]
    exact ⟨x, rfl⟩
  refine ⟨hmem, ?_⟩
  change K.subtype
      ((hyperplaneInjectionPMap K B).inverse
        ⟨B x, by simpa [closedHyperplaneInverse_domain] using hmem⟩) = (x : H)
  have hker := hyperplaneInjectionPMap_toFun_ker_eq_bot K B hB
  have hinv := LinearPMap.inverse_apply_eq hker
    (x := ⟨x, by simp [hyperplaneInjectionPMap]⟩)
    (y := ⟨B x, by
      rw [LinearPMap.inverse_domain]
      exact ⟨⟨x, by simp [hyperplaneInjectionPMap]⟩, rfl⟩⟩)
    (by rfl)
  exact congrArg Subtype.val hinv

theorem closedHyperplaneInverse_isClosed
    (K : Submodule ℂ H) (hK : IsClosed (K : Set H))
    (B : K →L[ℂ] H) (hB : Function.Injective B) :
    (closedHyperplaneInverse K B).IsClosed := by
  have hBP : (hyperplaneInjectionPMap K B).IsClosed := by
    rw [LinearPMap.IsClosed]
    exact B.isClosed_graph
  have hinv : ((hyperplaneInjectionPMap K B).inverse).IsClosed :=
    (LinearPMap.inverse_closed_iff
      (hyperplaneInjectionPMap_toFun_ker_eq_bot K B hB)).2 hBP
  rw [LinearPMap.IsClosed] at hinv ⊢
  have hgraph : (closedHyperplaneInverse K B).graph =
      ((hyperplaneInjectionPMap K B).inverse).graph.map
        ((LinearMap.id : H →ₗ[ℂ] H).prodMap K.subtype) := by
    ext p
    simp only [closedHyperplaneInverse, LinearPMap.mem_graph_iff,
      LinearMap.compPMap_apply, Submodule.mem_map, LinearMap.prodMap_apply,
      LinearMap.id_coe, id, Prod.exists, Prod.mk.injEq]
    constructor
    · rintro ⟨x, hx, hout⟩
      refine ⟨(p.1, x), ?_, rfl, ?_⟩
      · rw [LinearPMap.mem_graph_iff]
        exact ⟨⟨p.1, x.2⟩, rfl, rfl⟩
      · exact ⟨rfl, hout⟩
    · rintro ⟨⟨a, x⟩, hx, ha, hout⟩
      subst ha
      rw [LinearPMap.mem_graph_iff] at hx
      rcases hx with ⟨y, hy, hxy⟩
      refine ⟨⟨p.1, y.2⟩, rfl, ?_⟩
      rw [← hout.2, ← hxy]
      rfl
  rw [hgraph]
  let e : H × K ≃L[ℂ] (H × (K : Type _)) := ContinuousLinearEquiv.refl ℂ _
  have hclosedRange : IsClosed (Set.range (fun p : H × K => ((p.1 : H), (p.2 : H)))) := by
    have hrange : Set.range (fun p : H × K => ((p.1 : H), (p.2 : H))) =
        {p : H × H | p.2 ∈ K} := by
      ext p
      constructor
      · rintro ⟨q, rfl⟩
        exact q.2.property
      · intro hp
        exact ⟨(p.1, ⟨p.2, hp⟩), rfl⟩
    rw [hrange]
    exact hK.preimage continuous_snd
  exact hinv.image_of_continuousOn_injective
    (Continuous.continuousOn
      ((ContinuousLinearMap.fst ℂ H K).prod
        (K.subtypeL.comp (ContinuousLinearMap.snd ℂ H K))).continuous)
    (by
      intro p _ q _ hpq
      apply Prod.ext
      · exact congrArg Prod.fst hpq
      · apply Subtype.ext
        exact congrArg Prod.snd hpq)
    hclosedRange

theorem closedHyperplaneInverse_dense_domain
    (K : Submodule ℂ H) (B : K →L[ℂ] H) (hDense : Dense (B.range : Set H)) :
    Dense ((closedHyperplaneInverse K B).domain : Set H) := by
  simpa only [closedHyperplaneInverse_domain] using hDense

theorem closedHyperplaneInverse_kernel_eq_bot
    (K : Submodule ℂ H) (B : K →L[ℂ] H) (hB : Function.Injective B) :
    (closedHyperplaneInverse K B).kernel = ⊥ := by
  rw [LinearPMap.kernel_eq_bot_iff]
  intro x hx
  have hxrange : (x : H) ∈ B.range := by
    simpa only [closedHyperplaneInverse_domain] using x.property
  rcases hxrange with ⟨y, hy⟩
  have hxy : closedHyperplaneInverse K B x = (y : H) := by
    have h := (closedHyperplaneInverse_apply_B K B hB y).2
    convert h using 1
    exact Subtype.ext hy.symm
  rw [hxy] at hx
  exact hx

theorem closedHyperplaneInverse_range
    (K : Submodule ℂ H) (B : K →L[ℂ] H) (hB : Function.Injective B) :
    (closedHyperplaneInverse K B).rangeSubmodule = K := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    change K.subtype _ ∈ K
    exact Subtype.property _
  · intro y hy
    let yK : K := ⟨y, hy⟩
    let x : (closedHyperplaneInverse K B).domain :=
      ⟨B yK, (closedHyperplaneInverse_apply_B K B hB yK).1⟩
    exact ⟨x, (closedHyperplaneInverse_apply_B K B hB yK).2⟩

theorem closedHyperplaneInverse_isFredholm
    (K : Submodule ℂ H) (hK : IsClosed (K : Set H))
    (B : K →L[ℂ] H) (hB : Function.Injective B)
    (φ : H →L[ℂ] ℂ) (hφ : Function.Surjective φ) (hKφ : K = LinearMap.ker φ) :
    (closedHyperplaneInverse K B).IsFredholm := by
  apply LinearPMap.isFredholm_of_injective_of_range_eq_ker φ.continuous
    (closedHyperplaneInverse_kernel_eq_bot K B hB) hφ
  rw [closedHyperplaneInverse_range K B hB, hKφ]

theorem closedHyperplaneInverse_index_eq_neg_one
    (K : Submodule ℂ H) (B : K →L[ℂ] H) (hB : Function.Injective B)
    (φ : H →L[ℂ] ℂ) (hφ : Function.Surjective φ) (hKφ : K = LinearMap.ker φ) :
    (closedHyperplaneInverse K B).index = -1 := by
  apply LinearPMap.index_eq_neg_one_of_injective_of_range_eq_ker
    (closedHyperplaneInverse_kernel_eq_bot K B hB) hφ
  rw [closedHyperplaneInverse_range K B hB, hKφ]

end

end GaloisForLFunctions.HTGeometry

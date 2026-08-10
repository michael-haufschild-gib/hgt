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
    (∃ hRdom : ∀ x : H, R x ∈ T.domain,
      ∀ x : H, T ⟨R x, hRdom x⟩ - z • R x = x) ∧
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
  apply hB
  change B (x : K) = B 0
  rw [map_zero]
  exact hx

theorem closedHyperplaneInverse_domain
    (K : Submodule ℂ H) (B : K →L[ℂ] H) :
    (closedHyperplaneInverse K B).domain = B.range := by
  change ((hyperplaneInjectionPMap K B).inverse).domain = B.range
  rw [LinearPMap.inverse_domain]
  ext y
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨(x : K), hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨x, by simp [hyperplaneInjectionPMap]⟩, hx⟩

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
        ⟨B x, by
          rw [LinearPMap.inverse_domain]
          exact ⟨⟨x, by simp [hyperplaneInjectionPMap]⟩, rfl⟩⟩) = (x : H)
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
    have hgraph : (hyperplaneInjectionPMap K B).graph =
        {p : K × H | B p.1 = p.2} := by
      ext p
      simp [LinearPMap.mem_graph_iff, hyperplaneInjectionPMap]
    rw [hgraph]
    exact isClosed_eq (B.continuous.comp continuous_fst) continuous_snd
  have hinv : ((hyperplaneInjectionPMap K B).inverse).IsClosed :=
    (LinearPMap.inverse_closed_iff
      (hyperplaneInjectionPMap_toFun_ker_eq_bot K B hB)).2 hBP
  have hgraph : (closedHyperplaneInverse K B).graph =
      LinearMap.range (B.toLinearMap.prod K.subtype) := by
    ext p
    constructor
    · intro hp
      rw [LinearPMap.mem_graph_iff] at hp
      rcases hp with ⟨x, hx, hout⟩
      have hxrange : (x : H) ∈ B.range := by
        rw [← closedHyperplaneInverse_domain K B]
        exact x.property
      rcases hxrange with ⟨y, hy⟩
      have happ := (closedHyperplaneInverse_apply_B K B hB y).2
      have hxeq : x = ⟨B y, (closedHyperplaneInverse_apply_B K B hB y).1⟩ := by
        exact Subtype.ext hy.symm
      refine ⟨y, ?_⟩
      apply Prod.ext
      · exact hy.trans hx
      · have hout' : closedHyperplaneInverse K B
            ⟨B y, (closedHyperplaneInverse_apply_B K B hB y).1⟩ = p.2 := by
          rw [← hxeq]
          exact hout
        exact happ.symm.trans hout'
    · intro hp
      rcases hp with ⟨y, hyp⟩
      have hp1 : B y = p.1 := congrArg Prod.fst hyp
      have hp2 : (y : H) = p.2 := congrArg Prod.snd hyp
      rw [LinearPMap.mem_graph_iff]
      let x : (closedHyperplaneInverse K B).domain :=
        ⟨B y, (closedHyperplaneInverse_apply_B K B hB y).1⟩
      refine ⟨x, hp1, ?_⟩
      exact (closedHyperplaneInverse_apply_B K B hB y).2.trans hp2
  rw [LinearPMap.IsClosed, hgraph]
  let F : K →L[ℂ] H × H := B.prod K.subtypeL
  haveI : CompleteSpace K := hK.completeSpace_coe
  have hanti : AntilipschitzWith 1 F := by
    apply F.antilipschitz_of_bound
    intro x
    simpa [F] using norm_snd_le (B x, (x : H))
  exact hanti.isClosed_range F.uniformContinuous

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
    have heq : x = ⟨B y, (closedHyperplaneInverse_apply_B K B hB y).1⟩ :=
      Subtype.ext hy.symm
    simpa [heq] using h
  rw [hxy] at hx
  calc
    (x : H) = B y := hy.symm
    _ = B 0 := by rw [show y = 0 from Subtype.ext hx]
    _ = 0 := map_zero B

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
    (φ : H →L[ℂ] ℂ) (hφ : Function.Surjective φ)
    (hKφ : K = LinearMap.ker φ.toLinearMap) :
    (closedHyperplaneInverse K B).IsFredholm := by
  apply LinearPMap.isFredholm_of_injective_of_range_eq_ker φ.continuous
    (closedHyperplaneInverse_kernel_eq_bot K B hB) hφ
  rw [closedHyperplaneInverse_range K B hB, hKφ]

theorem closedHyperplaneInverse_index_eq_neg_one
    (K : Submodule ℂ H) (B : K →L[ℂ] H) (hB : Function.Injective B)
    (φ : H →L[ℂ] ℂ) (hφ : Function.Surjective φ)
    (hKφ : K = LinearMap.ker φ.toLinearMap) :
    (closedHyperplaneInverse K B).index = -1 := by
  apply LinearPMap.index_eq_neg_one_of_injective_of_range_eq_ker
    (closedHyperplaneInverse_kernel_eq_bot K B hB) hφ
  rw [closedHyperplaneInverse_range K B hB, hKφ]

end

end GaloisForLFunctions.HTGeometry

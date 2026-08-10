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

/-- Kernel of the Hilbert-space adjoint is exactly the orthogonal complement of the range. -/
theorem closedHyperplaneInverse_adjoint_kernel
    (K : Submodule ℂ H) (B : K →L[ℂ] H) (hB : Function.Injective B)
    (hDense : Dense (B.range : Set H)) :
    (closedHyperplaneInverse K B).adjoint.kernel = Kᗮ := by
  let A := closedHyperplaneInverse K B
  have hAdense : Dense (A.domain : Set H) :=
    closedHyperplaneInverse_dense_domain K B hDense
  have hArange : A.rangeSubmodule = K :=
    closedHyperplaneInverse_range K B hB
  ext y
  rw [LinearPMap.mem_kernel_iff]
  constructor
  · rintro ⟨hyDom, hy0⟩
    rw [Submodule.mem_orthogonal']
    intro k hk
    have hkRange : k ∈ A.rangeSubmodule := by rw [hArange]; exact hk
    rcases hkRange with ⟨x, hx⟩
    have hformal := LinearPMap.adjoint_isFormalAdjoint hAdense
      (⟨y, hyDom⟩ : A.adjoint.domain) x
    rw [hy0, inner_zero_left] at hformal
    calc
      inner ℂ y k = inner ℂ y (A x) := congrArg (inner ℂ y) hx.symm
      _ = 0 := hformal.symm
  · intro hyOrth
    rw [Submodule.mem_orthogonal'] at hyOrth
    have hyDom : y ∈ A.adjoint.domain := by
      apply LinearPMap.mem_adjoint_domain_of_exists
      refine ⟨0, ?_⟩
      intro x
      rw [inner_zero_left]
      symm
      apply hyOrth
      rw [← hArange]
      exact ⟨x, rfl⟩
    refine ⟨hyDom, ?_⟩
    apply LinearPMap.adjoint_apply_eq hAdense
    intro x
    rw [inner_zero_left]
    symm
    apply hyOrth
    rw [← hArange]
    exact ⟨x, rfl⟩

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

/-! ## Inverses of bounded operators with dense range -/

/-- The graph inverse of a bounded operator on the whole Hilbert space. -/
def closedDenseInverse (C : H →L[ℂ] H) : H →ₗ.[ℂ] H :=
  closedHyperplaneInverse ⊤ (C.comp (⊤ : Submodule ℂ H).subtypeL)

theorem closedDenseInverse_domain (C : H →L[ℂ] H) :
    (closedDenseInverse C).domain = C.range := by
  rw [closedDenseInverse, closedHyperplaneInverse_domain]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(x : H), rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, Submodule.mem_top⟩, rfl⟩

theorem closedDenseInverse_apply_C (C : H →L[ℂ] H) (hC : Function.Injective C) (x : H) :
    C x ∈ (closedDenseInverse C).domain ∧
      closedDenseInverse C ⟨C x, by rw [closedDenseInverse_domain]; exact ⟨x, rfl⟩⟩ = x := by
  let xTop : (⊤ : Submodule ℂ H) := ⟨x, Submodule.mem_top⟩
  have hCtop : Function.Injective (C.comp (⊤ : Submodule ℂ H).subtypeL) := by
    intro u v huv
    exact Subtype.ext (hC huv)
  have h := closedHyperplaneInverse_apply_B (⊤ : Submodule ℂ H)
    (C.comp (⊤ : Submodule ℂ H).subtypeL) hCtop xTop
  constructor
  · rw [closedDenseInverse_domain]
    exact ⟨x, rfl⟩
  · have heq :
        (⟨C x, by rw [closedDenseInverse_domain]; exact ⟨x, rfl⟩⟩ :
          (closedDenseInverse C).domain) =
        ⟨(C.comp (⊤ : Submodule ℂ H).subtypeL) xTop, h.1⟩ := Subtype.ext rfl
    rw [heq]
    exact h.2

theorem closedDenseInverse_isClosed (C : H →L[ℂ] H) (hC : Function.Injective C) :
    (closedDenseInverse C).IsClosed := by
  apply closedHyperplaneInverse_isClosed (⊤ : Submodule ℂ H) isClosed_univ
  intro u v huv
  exact Subtype.ext (hC huv)

theorem closedDenseInverse_dense_domain (C : H →L[ℂ] H) (hDense : Dense (C.range : Set H)) :
    Dense ((closedDenseInverse C).domain : Set H) := by
  rw [closedDenseInverse_domain]
  exact hDense

/-- The inverse of an injective, dense-range bounded self-adjoint operator is self-adjoint. -/
theorem closedDenseInverse_isSelfAdjoint (C : H →L[ℂ] H)
    (hCinj : Function.Injective C) (hCdense : Dense (C.range : Set H))
    (hCself : IsSelfAdjoint C) : IsSelfAdjoint (closedDenseInverse C) := by
  let A := closedDenseInverse C
  have hAdense : Dense (A.domain : Set H) := closedDenseInverse_dense_domain C hCdense
  have hCeq : C.adjoint = C := hCself
  have hCsymm : ∀ x y, inner ℂ (C x) y = inner ℂ x (C y) := by
    intro x y
    rw [← C.adjoint_inner_right, hCeq]
  have hAform : A.IsFormalAdjoint A := by
    intro x y
    have hxRange : (x : H) ∈ C.range := by
      simpa only [A, closedDenseInverse_domain] using x.property
    have hyRange : (y : H) ∈ C.range := by
      simpa only [A, closedDenseInverse_domain] using y.property
    rcases hxRange with ⟨a, ha⟩
    rcases hyRange with ⟨b, hb⟩
    have hAx : A x = a := by
      have h := (closedDenseInverse_apply_C C hCinj a).2
      have heq : x = ⟨C a, (closedDenseInverse_apply_C C hCinj a).1⟩ := Subtype.ext ha.symm
      simpa only [A, heq] using h
    have hAy : A y = b := by
      have h := (closedDenseInverse_apply_C C hCinj b).2
      have heq : y = ⟨C b, (closedDenseInverse_apply_C C hCinj b).1⟩ := Subtype.ext hb.symm
      simpa only [A, heq] using h
    calc
      inner ℂ (A x) (y : H) = inner ℂ a (y : H) := by rw [hAx]
      _ = inner ℂ a (C b) := congrArg (fun z : H => inner ℂ a z) hb.symm
      _ = inner ℂ (C a) b := (hCsymm a b).symm
      _ = inner ℂ (x : H) b := congrArg (fun z : H => inner ℂ z b) ha
      _ = inner ℂ (x : H) (A y) := by rw [hAy]
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨?_, ?_⟩
    · intro y hy
      let yAdj : A.adjoint.domain := ⟨y, hy⟩
      let w : H := A.adjoint yAdj
      have hCw : C w = y := by
        apply ext_inner_right ℂ
        intro a
        have hCa : C a ∈ A.domain := by
          simpa only [A] using (closedDenseInverse_apply_C C hCinj a).1
        let x : A.domain := ⟨C a, hCa⟩
        have hAx : A x = a := by
          simpa only [A, x] using (closedDenseInverse_apply_C C hCinj a).2
        calc
          inner ℂ (C w) a = inner ℂ w (C a) := hCsymm w a
          _ = inner ℂ y (A x) := LinearPMap.adjoint_isFormalAdjoint hAdense yAdj x
          _ = inner ℂ y a := by rw [hAx]
      have : y ∈ A.domain := by
        rw [show A.domain = C.range by simpa only [A] using closedDenseInverse_domain C]
        exact ⟨w, hCw⟩
      simpa only [A] using this
    · intro y z hyz
      let yAdj : A.adjoint.domain := y
      let w : H := A.adjoint yAdj
      have hCw : C w = (y : H) := by
        apply ext_inner_right ℂ
        intro a
        have hCa : C a ∈ A.domain := by
          simpa only [A] using (closedDenseInverse_apply_C C hCinj a).1
        let x : A.domain := ⟨C a, hCa⟩
        have hAx : A x = a := by
          simpa only [A, x] using (closedDenseInverse_apply_C C hCinj a).2
        calc
          inner ℂ (C w) a = inner ℂ w (C a) := hCsymm w a
          _ = inner ℂ (y : H) (A x) :=
            LinearPMap.adjoint_isFormalAdjoint hAdense yAdj x
          _ = inner ℂ (y : H) a := by rw [hAx]
      have hAz : A z = w := by
        have h := (closedDenseInverse_apply_C C hCinj w).2
        have heq : z = ⟨C w, by simpa only [A] using
            (closedDenseInverse_apply_C C hCinj w).1⟩ :=
          Subtype.ext (hyz.symm.trans hCw.symm)
        simpa only [A, heq] using h
      exact hAz.symm
  · exact hAform.le_adjoint hAdense

end

end GaloisForLFunctions.HTGeometry

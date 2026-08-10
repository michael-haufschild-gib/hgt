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

open Module Topology Filter

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

/-! ### Bounded transforms of a closed graph inverse -/

/-- The closed graph inverse of `B`, followed by an arbitrary bounded output map `J` on the
graph coordinate.  For `J k = k + α B k`, this is literally the translate `A + α` of the
inverse operator `A`. -/
def closedGraphTransform (K : Submodule ℂ H) (B J : K →L[ℂ] H) : H →ₗ.[ℂ] H :=
  J.toLinearMap.compPMap (hyperplaneInjectionPMap K B).inverse

theorem closedGraphTransform_domain
    (K : Submodule ℂ H) (B J : K →L[ℂ] H) :
    (closedGraphTransform K B J).domain = B.range := by
  change ((hyperplaneInjectionPMap K B).inverse).domain = B.range
  rw [LinearPMap.inverse_domain]
  ext y
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨(x : K), hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨x, by simp [hyperplaneInjectionPMap]⟩, hx⟩

theorem closedGraphTransform_apply_B
    (K : Submodule ℂ H) (B J : K →L[ℂ] H) (hB : Function.Injective B) (x : K) :
    B x ∈ (closedGraphTransform K B J).domain ∧
      closedGraphTransform K B J
        ⟨B x, by simpa [closedGraphTransform_domain]⟩ = J x := by
  have hmem : B x ∈ (closedGraphTransform K B J).domain := by
    rw [closedGraphTransform_domain]
    exact ⟨x, rfl⟩
  refine ⟨hmem, ?_⟩
  change J
      ((hyperplaneInjectionPMap K B).inverse
        ⟨B x, by
          rw [LinearPMap.inverse_domain]
          exact ⟨⟨x, by simp [hyperplaneInjectionPMap]⟩, rfl⟩⟩) = J x
  exact congrArg J (LinearPMap.inverse_apply_eq
    (hyperplaneInjectionPMap_toFun_ker_eq_bot K B hB)
    (x := ⟨x, by simp [hyperplaneInjectionPMap]⟩)
    (y := ⟨B x, by
      rw [LinearPMap.inverse_domain]
      exact ⟨⟨x, by simp [hyperplaneInjectionPMap]⟩, rfl⟩⟩)
    rfl)

theorem closedGraphTransform_graph
    (K : Submodule ℂ H) (B J : K →L[ℂ] H) (hB : Function.Injective B) :
    (closedGraphTransform K B J).graph = LinearMap.range (B.toLinearMap.prod J) := by
  ext p
  constructor
  · intro hp
    rw [LinearPMap.mem_graph_iff] at hp
    rcases hp with ⟨x, hx, hout⟩
    have hxrange : (x : H) ∈ B.range := by
      simpa only [closedGraphTransform_domain] using x.property
    rcases hxrange with ⟨y, hy⟩
    have happ := (closedGraphTransform_apply_B K B J hB y).2
    have hxeq : x = ⟨B y, (closedGraphTransform_apply_B K B J hB y).1⟩ :=
      Subtype.ext hy.symm
    refine ⟨y, ?_⟩
    apply Prod.ext
    · exact hy.trans hx
    · have hout' : closedGraphTransform K B J
          ⟨B y, (closedGraphTransform_apply_B K B J hB y).1⟩ = p.2 := by
        rw [← hxeq]
        exact hout
      exact happ.symm.trans hout'
  · rintro ⟨y, hyp⟩
    have hp1 : B y = p.1 := congrArg Prod.fst hyp
    have hp2 : J y = p.2 := congrArg Prod.snd hyp
    rw [LinearPMap.mem_graph_iff]
    let x : (closedGraphTransform K B J).domain :=
      ⟨B y, (closedGraphTransform_apply_B K B J hB y).1⟩
    refine ⟨x, hp1, ?_⟩
    exact (closedGraphTransform_apply_B K B J hB y).2.trans hp2

theorem closedGraphTransform_isClosed
    (K : Submodule ℂ H) [CompleteSpace K]
    (B J : K →L[ℂ] H) (hB : Function.Injective B)
    {c : NNReal} (hBJ : AntilipschitzWith c (B.prod J)) :
    (closedGraphTransform K B J).IsClosed := by
  rw [LinearPMap.IsClosed, closedGraphTransform_graph K B J hB]
  exact hBJ.isClosed_range (B.prod J).uniformContinuous

theorem closedGraphTransform_range
    (K : Submodule ℂ H) (B J : K →L[ℂ] H) (hB : Function.Injective B) :
    (closedGraphTransform K B J).rangeSubmodule = J.range := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    have hxrange : (x : H) ∈ B.range := by
      simpa only [closedGraphTransform_domain] using x.property
    rcases hxrange with ⟨k, hk⟩
    have hxeq : x = ⟨B k, (closedGraphTransform_apply_B K B J hB k).1⟩ :=
      Subtype.ext hk.symm
    refine ⟨k, ?_⟩
    exact ((congrArg (closedGraphTransform K B J) hxeq).trans
      (closedGraphTransform_apply_B K B J hB k).2).symm
  · rintro y ⟨k, rfl⟩
    exact ⟨⟨B k, (closedGraphTransform_apply_B K B J hB k).1⟩,
      (closedGraphTransform_apply_B K B J hB k).2⟩

theorem closedGraphTransform_kernel_eq_bot
    (K : Submodule ℂ H) (B J : K →L[ℂ] H)
    (hB : Function.Injective B) (hJ : Function.Injective J) :
    (closedGraphTransform K B J).kernel = ⊥ := by
  rw [LinearPMap.kernel_eq_bot_iff]
  intro x hx
  have hxrange : (x : H) ∈ B.range := by
    simpa only [closedGraphTransform_domain] using x.property
  rcases hxrange with ⟨k, hk⟩
  have hxeq : x = ⟨B k, (closedGraphTransform_apply_B K B J hB k).1⟩ :=
    Subtype.ext hk.symm
  have hJk : J k = 0 := by
    simpa [hxeq, (closedGraphTransform_apply_B K B J hB k).2] using hx
  have hk0 : k = 0 := hJ (by simpa using hJk)
  calc
    (x : H) = B k := hk.symm
    _ = B 0 := by rw [hk0]
    _ = 0 := map_zero B

/-- An injective compact perturbation of a closed-subspace inclusion is bounded below.  This is
the rectangular form of the first half of Atkinson's theorem needed by translated graph
inverses. -/
theorem antilipschitz_subtype_add_smul_of_compact_of_injective
    (K : Submodule ℂ H) (hK : IsClosed (K : Set H))
    (B : K →L[ℂ] H) (hB : IsCompactOperator B) (α : ℂ)
    (hJ : Function.Injective (K.subtypeL + α • B)) :
    ∃ c : NNReal, AntilipschitzWith c (K.subtypeL + α • B) := by
  letI : CompleteSpace K := hK.completeSpace_coe
  let J : K →L[ℂ] H := K.subtypeL + α • B
  rw [antilipschitzWith_iff_exists_mul_le_norm]
  by_contra! hlower
  have hshell : ∃ c > 0, ∀ ε > 0, ∃ x : K,
      ‖x‖ ≤ 1 ∧ c ≤ ‖x‖ ∧ ‖J x‖ < ε := by
    obtain ⟨C, hC⟩ := NormedField.exists_one_lt_norm ℂ
    refine ⟨‖C‖⁻¹, by positivity, fun ε hε => ?_⟩
    obtain ⟨x, hx⟩ := hlower ε hε
    have hx0 : x ≠ 0 := by
      rintro rfl
      simpa using hx
    obtain ⟨η, hη, h₁, h₂, h₃⟩ :=
      rescale_to_shell hC (ε := 1) (by simp) hx0
    refine ⟨η • x, h₁.le, by simpa using h₂, ?_⟩
    grw [map_smul, norm_smul, hx, mul_left_comm, ← norm_smul]
    linear_combination ε * h₁
  obtain ⟨c, hc0, hc⟩ := hshell
  obtain ⟨φ, hφanti, hφpos, hφ⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
  have hexists (n : ℕ) : ∃ x : K,
      ‖x‖ ≤ 1 ∧ c ≤ ‖x‖ ∧ ‖J x‖ < φ n := hc (φ n) (hφpos n)
  choose x hxUpper hxLower hxBound using hexists
  have hJlim : Tendsto (fun n => J (x n)) atTop (𝓝 0) :=
    squeeze_zero_norm (by grind) hφ
  obtain ⟨C, hCcompact, hCsub⟩ := hB.image_closedBall_subset_compact 1
  obtain ⟨y, hyC, ψ, hψ, hψy⟩ := hCcompact.tendsto_subseq
    (x := fun n => B (x n)) (fun n => hCsub ⟨x n, by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hxUpper n, rfl⟩)
  have hJsub : Tendsto (fun n => J (x (ψ n))) atTop (𝓝 0) :=
    hJlim.comp hψ.tendsto_atTop
  have hcoeLim : Tendsto (fun n => ((x (ψ n) : K) : H)) atTop (𝓝 (-α • y)) := by
    have hdiff := hJsub.sub (hψy.const_smul α)
    convert hdiff using 1
    · funext n
      simp [J]
    · simp
  have hlimitMem : -α • y ∈ K :=
    hK.mem_of_tendsto hcoeLim (Eventually.of_forall fun n => (x (ψ n)).property)
  let z : K := ⟨-α • y, hlimitMem⟩
  have hzlim : Tendsto (fun n => x (ψ n)) atTop (𝓝 z) := by
    rw [tendsto_subtype_rng]
    exact hcoeLim
  have hnormLim : Tendsto (fun n => ‖x (ψ n)‖) atTop (𝓝 ‖z‖) :=
    continuous_norm.continuousAt.tendsto.comp hzlim
  have hcz : c ≤ ‖z‖ :=
    ge_of_tendsto hnormLim (Eventually.of_forall fun n => hxLower (ψ n))
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hcz
    exact (not_lt_of_ge hcz) hc0
  have hJzLim : Tendsto (fun n => J (x (ψ n))) atTop (𝓝 (J z)) :=
    J.continuous.continuousAt.tendsto.comp hzlim
  have hJz : J z = 0 := tendsto_nhds_unique hJzLim hJsub
  apply hz0
  apply hJ
  simpa [J] using hJz

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

/-- Exact graph action of the Hilbert-space adjoint on the bounded-adjoint range. -/
theorem closedHyperplaneInverse_adjoint_apply_adjoint
    (K : Submodule ℂ H) [CompleteSpace K] (B : K →L[ℂ] H)
    (hB : Function.Injective B) (hDense : Dense (B.range : Set H)) (y : H) :
    ∃ hmem : (B.adjoint y : H) ∈ (closedHyperplaneInverse K B).adjoint.domain,
      (closedHyperplaneInverse K B).adjoint ⟨(B.adjoint y : H), hmem⟩ = y := by
  let A := closedHyperplaneInverse K B
  have hAdense : Dense (A.domain : Set H) :=
    closedHyperplaneInverse_dense_domain K B hDense
  have hpair : ∀ x : A.domain,
      inner ℂ y (x : H) = inner ℂ (B.adjoint y : H) (A x) := by
    intro x
    have hxRange : (x : H) ∈ B.range := by
      rw [← closedHyperplaneInverse_domain K B]
      exact x.property
    rcases hxRange with ⟨k, hk⟩
    have hAx : A x = (k : H) := by
      have h := (closedHyperplaneInverse_apply_B K B hB k).2
      have heq : x = ⟨B k, (closedHyperplaneInverse_apply_B K B hB k).1⟩ :=
        Subtype.ext hk.symm
      exact (congrArg A heq).trans h
    calc
      inner ℂ y (x : H) = inner ℂ y (B k) := congrArg (inner ℂ y) hk.symm
      _ = inner ℂ (B.adjoint y) k := (B.adjoint_inner_left k y).symm
      _ = inner ℂ (B.adjoint y : H) (k : H) := K.coe_inner _ _
      _ = inner ℂ (B.adjoint y : H) (A x) :=
        congrArg (inner ℂ (B.adjoint y : H)) hAx.symm
  have hmem : (B.adjoint y : H) ∈ A.adjoint.domain := by
    apply LinearPMap.mem_adjoint_domain_of_exists
    exact ⟨y, hpair⟩
  refine ⟨hmem, ?_⟩
  apply LinearPMap.adjoint_apply_eq hAdense
  exact hpair

/-- On the range hyperplane, the adjoint domain is exactly the range of `B†`. -/
theorem closedHyperplaneInverse_mem_adjoint_domain_iff
    (K : Submodule ℂ H) [CompleteSpace K] (B : K →L[ℂ] H)
    (hB : Function.Injective B) (hDense : Dense (B.range : Set H)) (k : K) :
    (k : H) ∈ (closedHyperplaneInverse K B).adjoint.domain ↔ k ∈ B.adjoint.range := by
  let A := closedHyperplaneInverse K B
  have hAdense : Dense (A.domain : Set H) :=
    closedHyperplaneInverse_dense_domain K B hDense
  constructor
  · intro hkdom
    let kAdj : A.adjoint.domain := ⟨(k : H), hkdom⟩
    let y : H := A.adjoint kAdj
    refine ⟨y, ?_⟩
    apply ext_inner_right ℂ
    intro j
    have hBjDom : B j ∈ A.domain :=
      (closedHyperplaneInverse_apply_B K B hB j).1
    let x : A.domain := ⟨B j, hBjDom⟩
    have hAx : A x = (j : H) := by
      simpa only [A, x] using (closedHyperplaneInverse_apply_B K B hB j).2
    have hformal := LinearPMap.adjoint_isFormalAdjoint hAdense kAdj x
    calc
      inner ℂ (B.adjoint y) j = inner ℂ y (B j) := B.adjoint_inner_left j y
      _ = inner ℂ (k : H) (A x) := hformal
      _ = inner ℂ (k : H) (j : H) := by rw [hAx]
      _ = inner ℂ k j := (K.coe_inner k j).symm
  · rintro ⟨y, hy⟩
    obtain ⟨hmem, _⟩ :=
      closedHyperplaneInverse_adjoint_apply_adjoint K B hB hDense y
    have hyH : (B.adjoint y : H) = (k : H) := congrArg Subtype.val hy
    exact hyH ▸ hmem

theorem closedHyperplaneInverse_adjoint_apply_of_eq_adjoint
    (K : Submodule ℂ H) [CompleteSpace K] (B : K →L[ℂ] H)
    (hB : Function.Injective B) (hDense : Dense (B.range : Set H))
    (k : K) (y : H) (hky : B.adjoint y = k)
    (hkdom : (k : H) ∈ (closedHyperplaneInverse K B).adjoint.domain) :
    (closedHyperplaneInverse K B).adjoint ⟨(k : H), hkdom⟩ = y := by
  obtain ⟨hmem, happly⟩ :=
    closedHyperplaneInverse_adjoint_apply_adjoint K B hB hDense y
  have hkyH : (k : H) = (B.adjoint y : H) :=
    congrArg (fun z : K => (z : H)) hky.symm
  have heq :
      (⟨(k : H), hkdom⟩ : (closedHyperplaneInverse K B).adjoint.domain) =
        ⟨(B.adjoint y : H), hmem⟩ := Subtype.ext hkyH
  exact (congrArg (closedHyperplaneInverse K B).adjoint heq).trans happly

/-! ## Natural adjoint squares -/

/-- Natural domain of `T†T`: vectors in `T.domain` whose image lies in `T†.domain`. -/
def LinearPMap.adjointSquareDomain (T : H →ₗ.[ℂ] H) : Submodule ℂ H :=
  (T.adjoint.domain.comap T.toFun).map T.domain.subtype

theorem LinearPMap.mem_adjointSquareDomain_iff (T : H →ₗ.[ℂ] H) (x : H) :
    x ∈ LinearPMap.adjointSquareDomain T ↔
      ∃ hx : x ∈ T.domain, T ⟨x, hx⟩ ∈ T.adjoint.domain := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.property, hz⟩
  · rintro ⟨hx, hTx⟩
    exact ⟨⟨x, hx⟩, hTx, rfl⟩

theorem LinearPMap.adjointSquareDomain_le (T : H →ₗ.[ℂ] H) :
    LinearPMap.adjointSquareDomain T ≤ T.domain := by
  intro x hx
  exact (LinearPMap.mem_adjointSquareDomain_iff T x).mp hx |>.choose

def LinearPMap.adjointSquareToAdjointDomain (T : H →ₗ.[ℂ] H) :
    LinearPMap.adjointSquareDomain T →ₗ[ℂ] T.adjoint.domain :=
  (T.toFun.comp (Submodule.inclusion (LinearPMap.adjointSquareDomain_le T))).codRestrict
    T.adjoint.domain (fun x => by
      have hx := (LinearPMap.mem_adjointSquareDomain_iff T (x : H)).mp x.property
      have heq : (Submodule.inclusion (LinearPMap.adjointSquareDomain_le T) x : T.domain) =
          ⟨(x : H), hx.choose⟩ := Subtype.ext rfl
      change T (Submodule.inclusion (LinearPMap.adjointSquareDomain_le T) x) ∈
        T.adjoint.domain
      rw [heq]
      exact hx.choose_spec)

/-- Actual partially defined operator `T†T`, with its natural composition domain. -/
def LinearPMap.adjointSquare (T : H →ₗ.[ℂ] H) : H →ₗ.[ℂ] H where
  domain := LinearPMap.adjointSquareDomain T
  toFun := T.adjoint.toFun.comp (LinearPMap.adjointSquareToAdjointDomain T)

theorem LinearPMap.adjointSquare_domain (T : H →ₗ.[ℂ] H) :
    (LinearPMap.adjointSquare T).domain = LinearPMap.adjointSquareDomain T := rfl

theorem LinearPMap.adjointSquare_apply (T : H →ₗ.[ℂ] H)
    (x : (LinearPMap.adjointSquare T).domain) (hx : (x : H) ∈ T.domain)
    (hTx : T ⟨(x : H), hx⟩ ∈ T.adjoint.domain) :
    LinearPMap.adjointSquare T x = T.adjoint ⟨T ⟨(x : H), hx⟩, hTx⟩ := by
  change T.adjoint
      (LinearPMap.adjointSquareToAdjointDomain T ⟨(x : H), x.property⟩) = _
  apply congrArg T.adjoint
  apply Subtype.ext
  change T (Submodule.inclusion (LinearPMap.adjointSquareDomain_le T)
      ⟨(x : H), x.property⟩) = T ⟨(x : H), hx⟩
  apply congrArg T
  rfl

theorem continuousLinearMap_adjoint_injective_of_dense_range
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (B : K →L[ℂ] H) (hDense : Dense (B.range : Set H)) :
    Function.Injective B.adjoint := by
  intro x y hxy
  apply hDense.eq_of_inner_left ℂ
  intro _ hk
  rcases hk with ⟨k, rfl⟩
  calc
    inner ℂ x (B k) = inner ℂ (B.adjoint x) k := (B.adjoint_inner_left k x).symm
    _ = inner ℂ (B.adjoint y) k := congrArg (fun z => inner ℂ z k) hxy
    _ = inner ℂ y (B k) := B.adjoint_inner_left k y

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

/-- For an injective compact inverse coordinate `B`, the natural operator `A†A` is exactly the
closed inverse of the bounded Gram operator `BB†`. -/
theorem closedHyperplaneInverse_adjointSquare_eq_closedDenseInverse
    (K : Submodule ℂ H) [CompleteSpace K] (B : K →L[ℂ] H)
    (hB : Function.Injective B) (hDense : Dense (B.range : Set H)) :
    LinearPMap.adjointSquare (closedHyperplaneInverse K B) =
      closedDenseInverse (B.comp B.adjoint) := by
  let A := closedHyperplaneInverse K B
  let C := B.comp B.adjoint
  have hBadj : Function.Injective B.adjoint :=
    continuousLinearMap_adjoint_injective_of_dense_range B hDense
  have hCinj : Function.Injective C := by
    simpa only [C, ContinuousLinearMap.coe_comp] using
      (B.self_comp_adjoint_injective_iff.mpr hBadj)
  have hdomain :
      (LinearPMap.adjointSquare A).domain = (closedDenseInverse C).domain := by
    ext x
    rw [LinearPMap.adjointSquare_domain,
      LinearPMap.mem_adjointSquareDomain_iff, closedDenseInverse_domain]
    constructor
    · rintro ⟨hxA, hAxdom⟩
      have hxRange : x ∈ B.range := by
        rw [← closedHyperplaneInverse_domain K B]
        exact hxA
      rcases hxRange with ⟨k, hk⟩
      have hAeq : A ⟨x, hxA⟩ = (k : H) := by
        have happly := (closedHyperplaneInverse_apply_B K B hB k).2
        have heq : (⟨x, hxA⟩ : A.domain) =
            ⟨B k, (closedHyperplaneInverse_apply_B K B hB k).1⟩ :=
          Subtype.ext hk.symm
        exact (congrArg A heq).trans happly
      have hkdom : (k : H) ∈ A.adjoint.domain := by
        rw [← hAeq]
        exact hAxdom
      have hkRange : k ∈ B.adjoint.range :=
        (closedHyperplaneInverse_mem_adjoint_domain_iff K B hB hDense k).mp hkdom
      rcases hkRange with ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change B (B.adjoint y) = x
      exact (congrArg B hy).trans hk
    · rintro ⟨y, hy⟩
      have hy' : B (B.adjoint y) = x := by
        change B (B.adjoint y) = x at hy
        exact hy
      have hxA : x ∈ A.domain := by
        change x ∈ (closedHyperplaneInverse K B).domain
        rw [closedHyperplaneInverse_domain]
        exact ⟨B.adjoint y, hy'⟩
      have hAeq : A ⟨x, hxA⟩ = (B.adjoint y : H) := by
        have happly := (closedHyperplaneInverse_apply_B K B hB (B.adjoint y)).2
        have heq : (⟨x, hxA⟩ : A.domain) =
            ⟨B (B.adjoint y),
              (closedHyperplaneInverse_apply_B K B hB (B.adjoint y)).1⟩ :=
          Subtype.ext hy'.symm
        exact (congrArg A heq).trans happly
      obtain ⟨hmem, _⟩ :=
        closedHyperplaneInverse_adjoint_apply_adjoint K B hB hDense y
      refine ⟨hxA, ?_⟩
      rw [hAeq]
      exact hmem
  apply LinearPMap.ext hdomain
  intro x hxSquare hxInverse
  have hxRange : x ∈ C.range := by
    rw [← closedDenseInverse_domain C]
    exact hxInverse
  rcases hxRange with ⟨y, hy⟩
  have hy' : B (B.adjoint y) = x := by
    change B (B.adjoint y) = x at hy
    exact hy
  have hxA : x ∈ A.domain := by
    change x ∈ (closedHyperplaneInverse K B).domain
    rw [closedHyperplaneInverse_domain]
    exact ⟨B.adjoint y, hy'⟩
  have hAeq : A ⟨x, hxA⟩ = (B.adjoint y : H) := by
    have happly := (closedHyperplaneInverse_apply_B K B hB (B.adjoint y)).2
    have heq : (⟨x, hxA⟩ : A.domain) =
        ⟨B (B.adjoint y),
          (closedHyperplaneInverse_apply_B K B hB (B.adjoint y)).1⟩ :=
      Subtype.ext hy'.symm
    exact (congrArg A heq).trans happly
  obtain ⟨hmem, hadjApply⟩ :=
    closedHyperplaneInverse_adjoint_apply_adjoint K B hB hDense y
  have hAxdom : A ⟨x, hxA⟩ ∈ A.adjoint.domain := by
    rw [hAeq]
    exact hmem
  have hSquareApply :=
    LinearPMap.adjointSquare_apply A ⟨x, hxSquare⟩ hxA hAxdom
  have hAdjSubtype :
      (⟨A ⟨x, hxA⟩, hAxdom⟩ : A.adjoint.domain) =
        ⟨(B.adjoint y : H), hmem⟩ := Subtype.ext hAeq
  have hSquareY : LinearPMap.adjointSquare A ⟨x, hxSquare⟩ = y :=
    hSquareApply.trans ((congrArg A.adjoint hAdjSubtype).trans hadjApply)
  have hInverseApply := (closedDenseInverse_apply_C C hCinj y).2
  have hInverseSubtype :
      (⟨x, hxInverse⟩ : (closedDenseInverse C).domain) =
        ⟨C y, (closedDenseInverse_apply_C C hCinj y).1⟩ := Subtype.ext hy.symm
  have hInverseY : closedDenseInverse C ⟨x, hxInverse⟩ = y :=
    (congrArg (closedDenseInverse C) hInverseSubtype).trans hInverseApply
  exact hSquareY.trans hInverseY.symm

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

theorem closedDenseInverse_isClosed (C : H →L[ℂ] H) (hC : Function.Injective C) :
    (closedDenseInverse C).IsClosed := by
  apply closedHyperplaneInverse_isClosed (⊤ : Submodule ℂ H) isClosed_univ
  intro u v huv
  exact Subtype.ext (hC huv)

theorem closedDenseInverse_dense_domain (C : H →L[ℂ] H) (hDense : Dense (C.range : Set H)) :
    Dense ((closedDenseInverse C).domain : Set H) := by
  rw [closedDenseInverse_domain]
  exact hDense

theorem closedDenseInverse_kernel_eq_bot (C : H →L[ℂ] H) (hC : Function.Injective C) :
    (closedDenseInverse C).kernel = ⊥ := by
  rw [closedDenseInverse]
  apply closedHyperplaneInverse_kernel_eq_bot
  intro u v huv
  exact Subtype.ext (hC huv)

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

/-- Zero is a compact resolvent point of the inverse of an injective compact operator. -/
theorem closedDenseInverse_hasCompactResolventAt_zero (C : H →L[ℂ] H)
    (hCinj : Function.Injective C) (hCcompact : IsCompactOperator C) :
    LinearPMap.HasCompactResolventAt (closedDenseInverse C) 0 := by
  refine ⟨C, hCcompact, ?_, ?_⟩
  · refine ⟨fun x => (closedDenseInverse_apply_C C hCinj x).1, ?_⟩
    intro x
    rw [zero_smul, sub_zero]
    exact (closedDenseInverse_apply_C C hCinj x).2
  · intro x
    rw [zero_smul, sub_zero]
    have hxRange : (x : H) ∈ C.range := by
      rw [← closedDenseInverse_domain C]
      exact x.property
    rcases hxRange with ⟨y, hy⟩
    have hApply := (closedDenseInverse_apply_C C hCinj y).2
    have heq : x = ⟨C y, (closedDenseInverse_apply_C C hCinj y).1⟩ :=
      Subtype.ext hy.symm
    have hxApply : closedDenseInverse C x = y :=
      (congrArg (closedDenseInverse C) heq).trans hApply
    calc
      C (closedDenseInverse C x) = C y := congrArg C hxApply
      _ = (x : H) := hy

/-- A graph core determines the maximal Hilbert-space adjoint: testing its weak pairing only on
the core is equivalent to membership in the full adjoint domain. -/
theorem LinearPMap.mem_adjoint_domain_iff_of_graph_core
    (T C : H →ₗ.[ℂ] H) (hDense : Dense (T.domain : Set H))
    (hCT : C ≤ T) (hgraph : closure (C.graph : Set (H × H)) = T.graph)
    (y : H) :
    y ∈ T.adjoint.domain ↔
      ∃ w : H, ∀ x : C.domain, inner ℂ w (x : H) = inner ℂ y (C x) := by
  constructor
  · intro hy
    let yAdj : T.adjoint.domain := ⟨y, hy⟩
    refine ⟨T.adjoint yAdj, ?_⟩
    intro x
    let xT : T.domain := ⟨(x : H), hCT.1 x.property⟩
    have happly : C x = T xT := hCT.2 rfl
    calc
      inner ℂ (T.adjoint yAdj) (x : H) = inner ℂ y (T xT) :=
        LinearPMap.adjoint_isFormalAdjoint hDense yAdj xT
      _ = inner ℂ y (C x) := congrArg (inner ℂ y) happly.symm
  · rintro ⟨w, hw⟩
    apply LinearPMap.mem_adjoint_domain_of_exists
    refine ⟨w, ?_⟩
    intro x
    let S : Set (H × H) := {p | inner ℂ w p.1 = inner ℂ y p.2}
    have hSclosed : IsClosed S := by
      change IsClosed {p : H × H | inner ℂ w p.1 = inner ℂ y p.2}
      apply isClosed_eq
      · fun_prop
      · fun_prop
    have hcore : (C.graph : Set (H × H)) ⊆ S := by
      intro p hp
      change p ∈ C.graph at hp
      rw [LinearPMap.mem_graph_iff] at hp
      rcases hp with ⟨z, hz1, hz2⟩
      change inner ℂ w p.1 = inner ℂ y p.2
      rw [← hz1, ← hz2]
      exact hw z
    have hpGraph : ((x : H), T x) ∈ T.graph := by
      rw [LinearPMap.mem_graph_iff]
      exact ⟨x, rfl, rfl⟩
    have hpClosure : ((x : H), T x) ∈ closure (C.graph : Set (H × H)) := by
      rw [hgraph]
      exact hpGraph
    exact closure_minimal hcore hSclosed hpClosure

end

end GaloisForLFunctions.HTGeometry

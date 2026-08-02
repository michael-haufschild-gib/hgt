import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Order
import Mathlib.Analysis.Normed.Module.Basic

/-!
# The inductive-limit test topology and the Kummer scale

A test space built as an increasing union of finite stages carries the inductive-limit topology:
the finest one for which every stage inclusion is continuous.  Two exhaustions that refine each
other induce the same topology, so the test topology does not depend on the chosen exhaustion, and
a map out of the limit is continuous exactly when it is continuous on every stage.

The Kummer test space is the closed span of the Kummer functions inside the test space.  A
continuous functional vanishing on the Kummer functions vanishes on the whole closed span, and a
continuous operator preserving the span preserves the closed span — this is why the integral kills
the Kummer scale and why the Galois, norm-projection and power operations act on it.

Finally, along a dense continuous injection the restriction of continuous functionals is
injective, which is what turns a dense scale of spaces into a scale of dual spaces.

* `deningerIndLimitTopology`, `deningerIndLimit_continuous_iff` : the test topology and stagewise
  continuity.
* `deningerIndLimit_eq_of_refines` : independence of the chosen exhaustion.
* `deningerKummerClosure`, `_le_ker`, `_map_le` : the closed Kummer span, the vanishing of a
  functional on it, and its stability under operations.
* `deningerDual_comp_injective` : dense continuous injections give injections of duals.
-/

namespace RHTower

open TopologicalSpace

section InductiveLimit

variable {α : Type*}

/-- **The inductive-limit topology** of a family of stage maps: the finest topology on the limit
for which every stage map is continuous. -/
@[reducible]
def deningerIndLimitTopology {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    (f : ∀ i, X i → α) : TopologicalSpace α :=
  ⨆ i, TopologicalSpace.coinduced (f i) inferInstance

/-- Every stage map is continuous for the inductive-limit topology. -/
theorem deningerIndLimit_continuous_stage {ι : Type*} {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] (f : ∀ i, X i → α) (i : ι) :
    @Continuous _ _ inferInstance (deningerIndLimitTopology f) (f i) := by
  rw [continuous_iff_coinduced_le, deningerIndLimitTopology]
  exact le_iSup (fun i => TopologicalSpace.coinduced (f i) inferInstance) i

/-- **Continuity out of an inductive limit is stagewise.**  This is why a functional continuous on
every finite stage is continuous on the whole test space. -/
theorem deningerIndLimit_continuous_iff {ι : Type*} {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] (f : ∀ i, X i → α)
    {β : Type*} [TopologicalSpace β] (h : α → β) :
    @Continuous _ _ (deningerIndLimitTopology f) inferInstance h
      ↔ ∀ i, Continuous (h ∘ f i) := by
  rw [deningerIndLimitTopology, continuous_iSup_dom]
  exact forall_congr' fun _ => continuous_coinduced_dom

/-- **A refinement of exhaustions coarsens the inductive-limit topology.**  If every stage of one
exhaustion factors continuously through a stage of another, the first inductive-limit topology is
at most the second. -/
theorem deningerIndLimit_le_of_refines {ι κ : Type*} {X : ι → Type*} {Y : κ → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ j, TopologicalSpace (Y j)]
    (f : ∀ i, X i → α) (g : ∀ j, Y j → α)
    (h : ∀ i, ∃ j, ∃ φ : X i → Y j, Continuous φ ∧ g j ∘ φ = f i) :
    deningerIndLimitTopology f ≤ deningerIndLimitTopology g := by
  refine iSup_le fun i => ?_
  obtain ⟨j, φ, hφ, hcomp⟩ := h i
  calc TopologicalSpace.coinduced (f i) inferInstance
      = TopologicalSpace.coinduced (g j ∘ φ) inferInstance := by rw [hcomp]
    _ = TopologicalSpace.coinduced (g j) (TopologicalSpace.coinduced φ inferInstance) :=
        coinduced_compose.symm
    _ ≤ TopologicalSpace.coinduced (g j) inferInstance :=
        coinduced_mono (continuous_iff_coinduced_le.mp hφ)
    _ ≤ deningerIndLimitTopology g :=
        le_iSup (fun j => TopologicalSpace.coinduced (g j) inferInstance) j

/-- **The test topology does not depend on the chosen exhaustion.**  Two mutually refining
exhaustions induce the same inductive-limit topology. -/
theorem deningerIndLimit_eq_of_refines {ι κ : Type*} {X : ι → Type*} {Y : κ → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ j, TopologicalSpace (Y j)]
    (f : ∀ i, X i → α) (g : ∀ j, Y j → α)
    (h₁ : ∀ i, ∃ j, ∃ φ : X i → Y j, Continuous φ ∧ g j ∘ φ = f i)
    (h₂ : ∀ j, ∃ i, ∃ ψ : Y j → X i, Continuous ψ ∧ f i ∘ ψ = g j) :
    deningerIndLimitTopology f = deningerIndLimitTopology g :=
  le_antisymm (deningerIndLimit_le_of_refines f g h₁) (deningerIndLimit_le_of_refines g f h₂)

end InductiveLimit

section KummerClosure

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousConstSMul ℝ E]

/-- **The Kummer test space**: the closure of the span of the Kummer functions. -/
def deningerKummerClosure (S : Set E) : Submodule ℝ E :=
  (Submodule.span ℝ S).topologicalClosure

theorem deningerKummerClosure_isClosed (S : Set E) :
    IsClosed (deningerKummerClosure S : Set E) :=
  Submodule.isClosed_topologicalClosure _

theorem deningerKummerClosure_coe (S : Set E) :
    (deningerKummerClosure S : Set E)
      = closure ((Submodule.span ℝ S : Submodule ℝ E) : Set E) :=
  Submodule.topologicalClosure_coe _

theorem deningerSubset_kummerClosure (S : Set E) : S ⊆ (deningerKummerClosure S : Set E) :=
  fun _ hx => Submodule.le_topologicalClosure _ (Submodule.subset_span hx)

/-- **A continuous functional vanishing on the Kummer functions vanishes on the whole Kummer test
space.**  The kernel is a closed subspace containing the span, hence containing its closure. -/
theorem deningerKummerClosure_le_ker (I : E →L[ℝ] ℝ) {S : Set E} (h : ∀ x ∈ S, I x = 0) :
    deningerKummerClosure S ≤ LinearMap.ker (I : E →ₗ[ℝ] ℝ) := by
  refine Submodule.topologicalClosure_minimal _ ?_ I.isClosed_ker
  rw [Submodule.span_le]
  intro x hx
  exact h x hx

theorem deningerKummerClosure_apply_eq_zero (I : E →L[ℝ] ℝ) {S : Set E}
    (h : ∀ x ∈ S, I x = 0) {x : E} (hx : x ∈ deningerKummerClosure S) : I x = 0 :=
  deningerKummerClosure_le_ker I h hx

/-- **The Kummer test space is stable under every continuous operation preserving the span.**
Galois maps, normalized field-norm projections and Tate-twisted power maps all preserve the span,
so they preserve its closure. -/
theorem deningerKummerClosure_map_le (T : E →L[ℝ] E) {S : Set E}
    (h : ∀ x ∈ (Submodule.span ℝ S : Submodule ℝ E), T x ∈ Submodule.span ℝ S) :
    ∀ x ∈ deningerKummerClosure S, T x ∈ deningerKummerClosure S := by
  intro x hx
  rw [← SetLike.mem_coe, deningerKummerClosure_coe] at hx ⊢
  have himg : T x ∈ closure (T '' ((Submodule.span ℝ S : Submodule ℝ E) : Set E)) :=
    image_closure_subset_closure_image T.continuous ⟨x, hx, rfl⟩
  refine closure_mono ?_ himg
  rintro _ ⟨z, hz, rfl⟩
  exact h z hz

/-- A span-preserving continuous operation preserves the vanishing of the integral. -/
theorem deningerKummerClosure_map_ker (I : E →L[ℝ] ℝ) (T : E →L[ℝ] E) {S : Set E}
    (hS : ∀ x ∈ S, I x = 0)
    (hT : ∀ x ∈ (Submodule.span ℝ S : Submodule ℝ E), T x ∈ Submodule.span ℝ S)
    {x : E} (hx : x ∈ deningerKummerClosure S) : I (T x) = 0 :=
  deningerKummerClosure_apply_eq_zero I hS (deningerKummerClosure_map_le T hT x hx)

end KummerClosure

section DenseRangeScale

variable {E F G : Type*} [TopologicalSpace G]

/-- **Density propagates along the scale.**  If a composite has dense image then so does the second
map, which is why every arrow of the scale has dense image once the Kummer span is dense in the
last space. -/
theorem deningerDenseRange_of_comp {f : E → F} {g : F → G} (h : DenseRange (g ∘ f)) :
    DenseRange g := by
  refine Dense.mono ?_ h
  rintro _ ⟨x, rfl⟩
  exact ⟨f x, rfl⟩

end DenseRangeScale

section DenseScale

variable {E F : Type*}
variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- **A dense continuous injection gives an injection of dual spaces.**  Two continuous functionals
agreeing on a dense subspace are equal, so restriction along the scale is injective and the dual
scale is a scale of injections. -/
theorem deningerDual_comp_injective (i : E →L[ℝ] F) (hd : DenseRange i) :
    Function.Injective (fun φ : F →L[ℝ] ℝ => φ.comp i) := by
  intro φ ψ h
  have hfun : (φ : F → ℝ) ∘ (i : E → F) = (ψ : F → ℝ) ∘ (i : E → F) :=
    congrArg (fun T : E →L[ℝ] ℝ => (T : E → ℝ)) h
  have := hd.equalizer φ.continuous ψ.continuous hfun
  exact ContinuousLinearMap.coe_injective (DFunLike.coe_injective this)

end DenseScale

end RHTower


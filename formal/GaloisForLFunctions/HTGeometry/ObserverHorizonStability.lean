import GaloisForLFunctions.HTGeometry.HilbertClosedRange
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Sequences
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Observer-horizon stability under bounded and compact repair

The **multivalued horizon** of a partially defined operator `T` is the vertical part of the closure
of its graph,

`Hor T = {y | (0, y) ∈ closure (graph T)}`,

and `T` is closable exactly when `Hor T = {0}`.

* `multivaluedHorizon_boundedShift` : adding a bounded operator shears the closed graph by a
  bounded invertible transformation which fixes the vertical axis, so the entire horizon survives
  unchanged and closability is preserved in both directions;
* `isSequentiallyClosableForm_add_iff` : a bounded nonnegative form correction preserves sequential
  closability of a nonnegative form in both directions;
* `tendsto_norm_add_compact_of_weaklyNull` : a compact perturbation cannot remove a weakly-null
  singular sequence, so no uniform lower bound and no injective closed-range repair survive.
-/

open Filter
open scoped Topology InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

section BoundedRepair

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- The **multivalued horizon** of a partially defined operator. -/
def multivaluedHorizon (T : X →ₗ.[𝕜] Y) : Set Y :=
  {y | ((0 : X), y) ∈ closure ((T.graph : Submodule 𝕜 (X × Y)) : Set (X × Y))}

/-- A bounded additive repair of a partially defined operator, on the same domain. -/
def boundedShift (T : X →ₗ.[𝕜] Y) (B : X →L[𝕜] Y) : X →ₗ.[𝕜] Y where
  domain := T.domain
  toFun := T.toFun + (B : X →ₗ[𝕜] Y).comp T.domain.subtype

@[simp] theorem boundedShift_domain (T : X →ₗ.[𝕜] Y) (B : X →L[𝕜] Y) :
    (boundedShift T B).domain = T.domain := rfl

@[simp] theorem boundedShift_apply (T : X →ₗ.[𝕜] Y) (B : X →L[𝕜] Y)
    (u : (boundedShift T B).domain) :
    boundedShift T B u = T u + B (u : X) := rfl

/-- The bounded shear `(x, y) ↦ (x, y + B x)` of the ambient product. -/
noncomputable def graphShearMap (B : X →L[𝕜] Y) : (X × Y) →L[𝕜] (X × Y) :=
  (ContinuousLinearMap.fst 𝕜 X Y).prod
    (ContinuousLinearMap.snd 𝕜 X Y + B ∘L ContinuousLinearMap.fst 𝕜 X Y)

@[simp] theorem graphShearMap_apply (B : X →L[𝕜] Y) (z : X × Y) :
    graphShearMap B z = (z.1, z.2 + B z.1) := rfl

/-- The shear is a bounded invertible transformation of the ambient product. -/
noncomputable def graphShear (B : X →L[𝕜] Y) : (X × Y) ≃L[𝕜] (X × Y) :=
  ContinuousLinearEquiv.equivOfInverse (graphShearMap B) (graphShearMap (-B))
    (fun z => by simp) (fun z => by simp)

@[simp] theorem graphShear_apply (B : X →L[𝕜] Y) (z : X × Y) :
    graphShear B z = (z.1, z.2 + B z.1) := rfl

/-- The shear carries the graph of `T` onto the graph of `T + B`. -/
theorem graphShear_image_graph (T : X →ₗ.[𝕜] Y) (B : X →L[𝕜] Y) :
    graphShear B '' ((T.graph : Submodule 𝕜 (X × Y)) : Set (X × Y))
      = (((boundedShift T B).graph : Submodule 𝕜 (X × Y)) : Set (X × Y)) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨u, hu1, hu2⟩ := (LinearPMap.mem_graph_iff T).mp hw
    refine (LinearPMap.mem_graph_iff _).mpr ⟨u, ?_, ?_⟩
    · rw [graphShear_apply, ← hu1]
    · rw [graphShear_apply]
      have hval : (boundedShift T B) u = T u + B (u : X) := rfl
      rw [hval, hu2, hu1]
  · intro hz
    obtain ⟨u, hu1, hu2⟩ := (LinearPMap.mem_graph_iff (boundedShift T B)).mp hz
    refine ⟨((u : X), T u), (LinearPMap.mem_graph_iff T).mpr ⟨u, rfl, rfl⟩, ?_⟩
    rw [graphShear_apply]
    refine Prod.ext hu1 ?_
    have hval : (boundedShift T B) u = T u + B (u : X) := rfl
    rw [← hu2, hval]

/-- **Bounded-repair invariance of the closed graph.** -/
theorem closure_graph_boundedShift (T : X →ₗ.[𝕜] Y) (B : X →L[𝕜] Y) :
    closure (((boundedShift T B).graph : Submodule 𝕜 (X × Y)) : Set (X × Y))
      = graphShear B '' closure ((T.graph : Submodule 𝕜 (X × Y)) : Set (X × Y)) := by
  rw [← graphShear_image_graph T B]
  exact ((graphShear B).toHomeomorph.image_closure _).symm

/-- **Exact defect conservation.**  Every horizon vector survives a bounded additive repair
unchanged. -/
theorem multivaluedHorizon_boundedShift (T : X →ₗ.[𝕜] Y) (B : X →L[𝕜] Y) :
    multivaluedHorizon (boundedShift T B) = multivaluedHorizon T := by
  ext y
  simp only [multivaluedHorizon, Set.mem_setOf_eq, closure_graph_boundedShift]
  constructor
  · rintro ⟨w, hw, hwz⟩
    have hx := congrArg Prod.fst hwz
    have hy2 := congrArg Prod.snd hwz
    simp only [graphShear_apply] at hx hy2
    have hw' : w = ((0 : X), y) := by
      refine Prod.ext hx ?_
      rw [hx] at hy2
      simpa using hy2
    rwa [hw'] at hw
  · intro hy
    exact ⟨((0 : X), y), hy, by simp⟩

/-- **Closability is a bounded-repair invariant.** -/
theorem multivaluedHorizon_boundedShift_eq_singleton_iff (T : X →ₗ.[𝕜] Y) (B : X →L[𝕜] Y) :
    multivaluedHorizon (boundedShift T B) = {0} ↔ multivaluedHorizon T = {0} := by
  rw [multivaluedHorizon_boundedShift]

end BoundedRepair

/-! ## Bounded nonnegative form corrections -/

section Forms

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Sequential closability of a nonnegative quadratic form through the ambient norm. -/
def IsSequentiallyClosableForm (D : Submodule 𝕜 X) (Q : X → ℝ) : Prop :=
  ∀ x : ℕ → X, (∀ n, x n ∈ D) → Tendsto x atTop (𝓝 0) →
    (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, Q (x n - x m) < ε) →
    Tendsto (fun n => Q (x n)) atTop (𝓝 0)

/-- A null sequence is uniformly Cauchy in the squared ambient norm. -/
theorem uniform_normSq_small_of_tendsto_zero {x : ℕ → X} (hx : Tendsto x atTop (𝓝 0))
    {C : ℝ} (hC : 0 ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ m ≥ N, ∀ n ≥ N, C * ‖x n - x m‖ ^ 2 < ε := by
  have hδ : (0 : ℝ) < Real.sqrt (ε / (C + 1)) / 2 := by positivity
  have hnorm : Tendsto (fun n => ‖x n‖) atTop (𝓝 0) := by
    simpa using (tendsto_zero_iff_norm_tendsto_zero.mp hx)
  obtain ⟨N, hN⟩ := (hnorm.eventually (gt_mem_nhds hδ)).exists_forall_of_atTop
  refine ⟨N, fun m hm n hn => ?_⟩
  have hmn : ‖x n - x m‖ < Real.sqrt (ε / (C + 1)) := by
    calc ‖x n - x m‖ ≤ ‖x n‖ + ‖x m‖ := norm_sub_le _ _
      _ < Real.sqrt (ε / (C + 1)) / 2 + Real.sqrt (ε / (C + 1)) / 2 :=
        add_lt_add (hN n hn) (hN m hm)
      _ = Real.sqrt (ε / (C + 1)) := by ring
  have hsq : ‖x n - x m‖ ^ 2 < ε / (C + 1) := by
    have h0 : (0 : ℝ) ≤ ‖x n - x m‖ := norm_nonneg _
    have hpos : (0 : ℝ) < ε / (C + 1) := by positivity
    calc ‖x n - x m‖ ^ 2 < Real.sqrt (ε / (C + 1)) ^ 2 := by nlinarith [Real.sqrt_nonneg (ε / (C+1))]
      _ = ε / (C + 1) := Real.sq_sqrt hpos.le
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  calc C * ‖x n - x m‖ ^ 2 ≤ (C + 1) * ‖x n - x m‖ ^ 2 := by nlinarith [sq_nonneg ‖x n - x m‖]
    _ < (C + 1) * (ε / (C + 1)) := mul_lt_mul_of_pos_left hsq hC1
    _ = ε := by field_simp

/-- **Bounded nonnegative form corrections preserve sequential closability.** -/
theorem isSequentiallyClosableForm_add_iff (D : Submodule 𝕜 X) (Q B : X → ℝ)
    (hQ : ∀ x, 0 ≤ Q x) (hB : ∀ x, 0 ≤ B x) {C : ℝ} (hC : 0 ≤ C)
    (hBb : ∀ x, B x ≤ C * ‖x‖ ^ 2) :
    IsSequentiallyClosableForm D (fun x => Q x + B x) ↔ IsSequentiallyClosableForm D Q := by
  have hBnull : ∀ x : ℕ → X, Tendsto x atTop (𝓝 0) → Tendsto (fun n => B (x n)) atTop (𝓝 0) := by
    intro x hx
    have hnorm : Tendsto (fun n => C * ‖x n‖ ^ 2) atTop (𝓝 (C * 0 ^ 2)) := by
      have h := (tendsto_zero_iff_norm_tendsto_zero.mp hx)
      exact ((h.pow 2).const_mul C)
    rw [show C * (0 : ℝ) ^ 2 = 0 by ring] at hnorm
    exact squeeze_zero (fun n => hB (x n)) (fun n => hBb (x n)) hnorm
  constructor
  · intro hQB x hxD hx0 hcauchy
    have hcauchy' : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, (Q (x n - x m) + B (x n - x m)) < ε := by
      intro ε hε
      obtain ⟨N₁, hN₁⟩ := hcauchy (ε / 2) (by linarith)
      obtain ⟨N₂, hN₂⟩ := uniform_normSq_small_of_tendsto_zero hx0 hC (show (0:ℝ) < ε / 2 by linarith)
      refine ⟨max N₁ N₂, fun m hm n hn => ?_⟩
      have h1 := hN₁ m (le_trans (le_max_left _ _) hm) n (le_trans (le_max_left _ _) hn)
      have h2 := hN₂ m (le_trans (le_max_right _ _) hm) n (le_trans (le_max_right _ _) hn)
      have h3 : B (x n - x m) ≤ C * ‖x n - x m‖ ^ 2 := hBb _
      linarith
    have hsum := hQB x hxD hx0 hcauchy'
    exact squeeze_zero (fun n => hQ (x n)) (fun n => by linarith [hB (x n)]) hsum
  · intro hQcl x hxD hx0 hcauchy
    have hcauchyQ : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, Q (x n - x m) < ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := hcauchy ε hε
      refine ⟨N, fun m hm n hn => ?_⟩
      have h1 := hN m hm n hn
      have h2 := hB (x n - x m)
      linarith
    have hQn := hQcl x hxD hx0 hcauchyQ
    have hBn := hBnull x hx0
    have hsum : Tendsto (fun n => Q (x n) + B (x n)) atTop (𝓝 (0 + 0)) := hQn.add hBn
    simpa using hsum

/-- The Hermitian-form version: a bounded nonnegative form correction preserves sequential
closability of a nonnegative form. -/
theorem isSequentiallyClosableForm_add_bounded_iff (D : Submodule 𝕜 X)
    (q b : X → X → 𝕜)
    (hq : ∀ x, 0 ≤ RCLike.re (q x x)) (hb : ∀ x, 0 ≤ RCLike.re (b x x))
    {C : ℝ} (hC : 0 ≤ C) (hbC : ∀ x, RCLike.re (b x x) ≤ C * ‖x‖ ^ 2) :
    IsSequentiallyClosableForm D (fun x => RCLike.re (q x x) + RCLike.re (b x x))
      ↔ IsSequentiallyClosableForm D (fun x => RCLike.re (q x x)) :=
  isSequentiallyClosableForm_add_iff D _ _ hq hb hC hbC

end Forms

/-! ## Compact repair cannot remove a weakly escaping singular sequence -/

section Compact

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [CompleteSpace Y]

/-- A compact operator sends a bounded weakly-null sequence to a norm-null sequence. -/
theorem tendsto_norm_compact_of_weaklyNull (K : X →L[𝕜] Y) (hK : IsCompactOperator K)
    (x : ℕ → X) (hb : ∀ n, ‖x n‖ ≤ 1)
    (hweak : ∀ z : X, Tendsto (fun n => ⟪z, x n⟫_𝕜) atTop (𝓝 0)) :
    Tendsto (fun n => K (x n)) atTop (𝓝 0) := by
  have hKweak : ∀ w : Y, Tendsto (fun n => ⟪w, K (x n)⟫_𝕜) atTop (𝓝 0) := by
    intro w
    have hadj : ∀ n, ⟪w, K (x n)⟫_𝕜 = ⟪ContinuousLinearMap.adjoint K w, x n⟫_𝕜 := by
      intro n
      exact (ContinuousLinearMap.adjoint_inner_left K (x n) w).symm
    simpa only [hadj] using hweak (ContinuousLinearMap.adjoint K w)
  have hcompact : IsCompact (closure (K '' Metric.closedBall 0 1)) :=
    hK.isCompact_closure_image_closedBall 1
  have hmem : ∀ n, K (x n) ∈ closure (K '' Metric.closedBall (0 : X) 1) := by
    intro n
    apply subset_closure
    exact ⟨x n, by simpa [Metric.mem_closedBall, dist_eq_norm] using hb n, rfl⟩
  refine tendsto_of_subseq_tendsto ?_
  intro ns hns
  obtain ⟨z, _, φ, hφ, hconv⟩ :=
    hcompact.tendsto_subseq (x := fun i => K (x (ns i))) (fun i => hmem (ns i))
  have hconv' : Tendsto (fun i => K (x (ns (φ i)))) atTop (𝓝 z) := by
    simpa [Function.comp_def] using hconv
  have hz : z = 0 := by
    have hinner : Tendsto (fun i => ⟪z, K (x (ns (φ i)))⟫_𝕜) atTop (𝓝 ⟪z, z⟫_𝕜) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => z) atTop (𝓝 z)).inner hconv'
    have hzero : Tendsto (fun i => ⟪z, K (x (ns (φ i)))⟫_𝕜) atTop (𝓝 0) :=
      (hKweak z).comp (hns.comp hφ.tendsto_atTop)
    have hzz : ⟪z, z⟫_𝕜 = 0 := tendsto_nhds_unique hinner hzero
    exact (inner_self_eq_zero (𝕜 := 𝕜)).mp hzz
  exact ⟨φ, by rw [← hz]; exact hconv'⟩

/-- **Compact stability of a precision horizon.**  A compact perturbation preserves a weakly-null
singular sequence. -/
theorem tendsto_norm_add_compact_of_weaklyNull (T : X →ₗ.[𝕜] Y) (K : X →L[𝕜] Y)
    (hK : IsCompactOperator K) (u : ℕ → T.domain)
    (hnorm : ∀ n, ‖((u n : X))‖ = 1)
    (hweak : ∀ z : X, Tendsto (fun n => ⟪z, (u n : X)⟫_𝕜) atTop (𝓝 0))
    (hT : Tendsto (fun n => T (u n)) atTop (𝓝 0)) :
    Tendsto (fun n => T (u n) + K ((u n : X))) atTop (𝓝 0) := by
  have hcpt := tendsto_norm_compact_of_weaklyNull K hK (fun n => (u n : X))
    (fun n => le_of_eq (hnorm n)) hweak
  have := hT.add hcpt
  simpa using this

/-- No uniform lower bound survives a compact perturbation along a weakly escaping unit
sequence. -/
theorem not_exists_lower_bound_of_weaklyNull (T : X →ₗ.[𝕜] Y) (K : X →L[𝕜] Y)
    (hK : IsCompactOperator K) (u : ℕ → T.domain)
    (hnorm : ∀ n, ‖((u n : X))‖ = 1)
    (hweak : ∀ z : X, Tendsto (fun n => ⟪z, (u n : X)⟫_𝕜) atTop (𝓝 0))
    (hT : Tendsto (fun n => T (u n)) atTop (𝓝 0)) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ v : T.domain, c * ‖((v : X))‖ ≤ ‖T v + K ((v : X))‖ := by
  rintro ⟨c, hc, hbound⟩
  have hlim := tendsto_norm_add_compact_of_weaklyNull T K hK u hnorm hweak hT
  have hnormlim : Tendsto (fun n => ‖T (u n) + K ((u n : X))‖) atTop (𝓝 0) := by
    simpa using hlim.norm
  have hge : ∀ n, c ≤ ‖T (u n) + K ((u n : X))‖ := by
    intro n
    have := hbound (u n)
    rwa [hnorm n, mul_one] at this
  have hle : c ≤ 0 := ge_of_tendsto' hnormlim hge
  linarith

/-- **No compact repair of a bounded observer.**  If a bounded operator carries a weakly-null unit
sequence to zero, then no compact perturbation of it is both injective and of closed range. -/
theorem not_injective_and_isClosed_range_of_weaklyNull (S : X →L[𝕜] Y) (K : X →L[𝕜] Y)
    (hK : IsCompactOperator K) (u : ℕ → X)
    (hnorm : ∀ n, ‖u n‖ = 1)
    (hweak : ∀ z : X, Tendsto (fun n => ⟪z, u n⟫_𝕜) atTop (𝓝 0))
    (hS : Tendsto (fun n => S (u n)) atTop (𝓝 0)) :
    ¬ (Function.Injective (S + K) ∧ IsClosed (Set.range (S + K))) := by
  rintro ⟨hinj, hclosed⟩
  obtain ⟨c, hc, hbound⟩ :=
    (ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range (S + K)).mpr hclosed
  have hker : LinearMap.ker ((S + K : X →L[𝕜] Y) : X →ₗ[𝕜] Y) = ⊥ :=
    LinearMap.ker_eq_bot'.mpr fun v hv => hinj (by simpa using hv)
  have hall : ∀ v : X, c * ‖v‖ ≤ ‖(S + K) v‖ := by
    intro v
    refine hbound v ?_
    rw [hker]
    simp
  have hcpt := tendsto_norm_compact_of_weaklyNull K hK u (fun n => le_of_eq (hnorm n)) hweak
  have hlim : Tendsto (fun n => (S + K) (u n)) atTop (𝓝 0) := by
    have := hS.add hcpt
    simpa using this
  have hnormlim : Tendsto (fun n => ‖(S + K) (u n)‖) atTop (𝓝 0) := by
    simpa using hlim.norm
  have hge : ∀ n, c ≤ ‖(S + K) (u n)‖ := by
    intro n
    have := hall (u n)
    rwa [hnorm n, mul_one] at this
  have hle : c ≤ 0 := ge_of_tendsto' hnormlim hge
  linarith

end Compact

end GaloisForLFunctions.HTGeometry

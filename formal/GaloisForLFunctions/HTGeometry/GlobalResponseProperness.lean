import GaloisForLFunctions.HTGeometry.HilbertClosedRange
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Global response properness

For a bounded response operator `R : 𝓔 → 𝓨` between Hilbert spaces, with invisible kernel
`N = ker R` and positive response `Q = R* R`, the following are equivalent `(SR.26)`:

1. `ran R` is closed;
2. `‖R K‖² ≥ α dist(K, N)²` for some `α > 0`;
3. the reduced positive response `Q|_{N^⊥} : N^⊥ → N^⊥` has a bounded inverse;
4. no unit sequence in `N^⊥` has response tending to zero.

All four are the transverse lower bound `c ‖x‖ ≤ ‖R x‖` on `N^⊥`: the distance to `N` is the norm
of the `N^⊥`-component, `⟨Q x, x⟩ = ‖R x‖²` makes `Q|_{N^⊥}` coercive, and a failing bound
produces a normalized null sequence.  When they hold, asymptotically vanishing response forces
the intervention to `N`.  A compact `R` with infinite-dimensional `N^⊥` satisfies none of them:
compactness and Bessel's inequality send every orthonormal sequence, along a subsequence, to
response zero.

Unitaries `U`, `V` with `V R = R U` preserve `N`, the distance to `N`, the response norms, the
positive response, null sequences and closedness of the range; such an action can neither create
properness nor select an intervention.
-/

open Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The invisible kernel `N = ker R`. -/
abbrev invisibleKernel (R : E →L[𝕜] F) : Submodule 𝕜 E := LinearMap.ker (R : E →ₗ[𝕜] F)

omit [CompleteSpace F] in
/-- The distance to the invisible kernel is the norm of the transverse component. -/
theorem infDist_invisibleKernel (R : E →L[𝕜] F) (K : E) :
    Metric.infDist K (invisibleKernel R : Set E) =
      ‖K - (invisibleKernel R).starProjection K‖ := by
  apply le_antisymm
  · have h := Metric.infDist_le_dist_of_mem (x := K)
      ((invisibleKernel R).starProjection_apply_mem K)
    rwa [dist_eq_norm] at h
  · rw [Metric.le_infDist ⟨0, (invisibleKernel R).zero_mem⟩]
    intro y hy
    rw [Submodule.starProjection_minimal, dist_eq_norm]
    exact ciInf_le ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩
      (⟨y, hy⟩ : invisibleKernel R)

omit [CompleteSpace F] in
theorem infDist_invisibleKernel_of_mem {R : E →L[𝕜] F} {x : E}
    (hx : x ∈ (invisibleKernel R)ᗮ) : Metric.infDist x (invisibleKernel R : Set E) = ‖x‖ := by
  rw [infDist_invisibleKernel, ((invisibleKernel R).starProjection_apply_eq_zero_iff).mpr hx,
    sub_zero]

omit [CompleteSpace F] in
theorem transverse_mem (R : E →L[𝕜] F) (K : E) :
    K - (invisibleKernel R).starProjection K ∈ (invisibleKernel R)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal K

omit [CompleteSpace F] in
theorem apply_transverse (R : E →L[𝕜] F) (K : E) :
    R (K - (invisibleKernel R).starProjection K) = R K := by
  have h : R ((invisibleKernel R).starProjection K) = 0 :=
    (invisibleKernel R).starProjection_apply_mem K
  rw [map_sub, h, sub_zero]

/-- The reduced positive response `Q|_{N^⊥} : N^⊥ → N^⊥`, `Q = R* R`. -/
def reducedPositiveResponse (R : E →L[𝕜] F) :
    (invisibleKernel R)ᗮ →L[𝕜] (invisibleKernel R)ᗮ :=
  ((ContinuousLinearMap.adjoint R ∘L R) ∘L (invisibleKernel R)ᗮ.subtypeL).codRestrict
    (invisibleKernel R)ᗮ fun x =>
      ContinuousLinearMap.range_adjoint_le_ker_orthogonal R ⟨R x, rfl⟩

theorem coe_reducedPositiveResponse_apply (R : E →L[𝕜] F) (x : (invisibleKernel R)ᗮ) :
    (reducedPositiveResponse R x : E) = ContinuousLinearMap.adjoint R (R x) := rfl

theorem inner_reducedPositiveResponse (R : E →L[𝕜] F) (x : (invisibleKernel R)ᗮ) :
    ⟪reducedPositiveResponse R x, x⟫_𝕜 = ⟪R x, R x⟫_𝕜 := by
  rw [Submodule.coe_inner, coe_reducedPositiveResponse_apply,
    ContinuousLinearMap.adjoint_inner_left]

/-! ### Theorem 5.1 -/

section Classification

variable (R : E →L[𝕜] F)

omit [CompleteSpace F] in
theorem lowerBound_of_transverse {c : ℝ} (hc : 0 < c)
    (h : ∀ x ∈ (invisibleKernel R)ᗮ, c * ‖x‖ ≤ ‖R x‖) (K : E) :
    c ^ 2 * Metric.infDist K (invisibleKernel R : Set E) ^ 2 ≤ ‖R K‖ ^ 2 := by
  rw [infDist_invisibleKernel, ← apply_transverse R K, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (h _ (transverse_mem R K)) 2

omit [CompleteSpace F] in
theorem transverse_of_lowerBound {α : ℝ} (hα : 0 < α)
    (h : ∀ K : E, α * Metric.infDist K (invisibleKernel R : Set E) ^ 2 ≤ ‖R K‖ ^ 2) :
    ∀ x ∈ (invisibleKernel R)ᗮ, Real.sqrt α * ‖x‖ ≤ ‖R x‖ := by
  intro x hx
  have h1 := h x
  rw [infDist_invisibleKernel_of_mem hx] at h1
  have h2 : Real.sqrt (α * ‖x‖ ^ 2) ≤ Real.sqrt (‖R x‖ ^ 2) := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_mul hα.le, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h2

theorem isUnit_reducedPositiveResponse_of_transverse {c : ℝ} (hc : 0 < c)
    (h : ∀ x ∈ (invisibleKernel R)ᗮ, c * ‖x‖ ≤ ‖R x‖) :
    IsUnit (reducedPositiveResponse R) := by
  have hcoer : ∀ x : (invisibleKernel R)ᗮ,
      c ^ 2 * ‖x‖ ^ 2 ≤ RCLike.re ⟪reducedPositiveResponse R x, x⟫_𝕜 := by
    intro x
    rw [inner_reducedPositiveResponse, inner_self_eq_norm_sq, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (h x x.2) 2
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  refine ⟨fun x y hxy => ?_, ContinuousLinearMap.surjective_of_reCoercive (by positivity) hcoer⟩
  have hb := ContinuousLinearMap.norm_le_of_reCoercive hcoer (x - y)
  rw [map_sub, hxy, sub_self, norm_zero] at hb
  have : ‖x - y‖ = 0 := le_antisymm (by
    by_contra hpos
    push Not at hpos
    have : 0 < c ^ 2 * ‖x - y‖ := by positivity
    linarith) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

theorem transverse_of_isUnit (hu : IsUnit (reducedPositiveResponse R)) :
    ∃ c > 0, ∀ x ∈ (invisibleKernel R)ᗮ, c * ‖x‖ ≤ ‖R x‖ := by
  obtain ⟨u, hu⟩ := hu
  set M := ‖(↑u⁻¹ : (invisibleKernel R)ᗮ →L[𝕜] (invisibleKernel R)ᗮ)‖
  set A := ‖ContinuousLinearMap.adjoint R‖
  refine ⟨1 / (M * A + 1), by positivity, fun x hx => ?_⟩
  set y : (invisibleKernel R)ᗮ := ⟨x, hx⟩
  have h1 : y = (↑u⁻¹ : (invisibleKernel R)ᗮ →L[𝕜] _) (reducedPositiveResponse R y) := by
    rw [← hu]
    exact (congrArg (fun T => T y) (Units.inv_mul u)).symm
  have h2 : ‖y‖ ≤ M * ‖reducedPositiveResponse R y‖ := by
    conv_lhs => rw [h1]
    exact ContinuousLinearMap.le_opNorm _ _
  have h3 : ‖reducedPositiveResponse R y‖ ≤ A * ‖R x‖ := by
    rw [← Submodule.norm_coe, coe_reducedPositiveResponse_apply]
    exact ContinuousLinearMap.le_opNorm _ _
  have hy : ‖y‖ = ‖x‖ := rfl
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  have hM : 0 ≤ M := norm_nonneg _
  calc ‖x‖ ≤ M * (A * ‖R x‖) := by
        rw [← hy]
        exact h2.trans (mul_le_mul_of_nonneg_left h3 hM)
    _ ≤ ‖R x‖ * (M * A + 1) := by nlinarith [norm_nonneg (R x)]

omit [CompleteSpace E] [CompleteSpace F] in
theorem not_nullSequence_of_transverse {c : ℝ} (hc : 0 < c)
    (h : ∀ x ∈ (invisibleKernel R)ᗮ, c * ‖x‖ ≤ ‖R x‖) :
    ¬ ∃ u : ℕ → E, (∀ n, u n ∈ (invisibleKernel R)ᗮ) ∧ (∀ n, ‖u n‖ = 1) ∧
      Tendsto (fun n => R (u n)) atTop (𝓝 0) := by
  rintro ⟨u, hu, hnorm, hlim⟩
  have hlim' := (tendsto_zero_iff_norm_tendsto_zero.mp hlim).eventually (gt_mem_nhds hc)
  obtain ⟨n, hn⟩ := hlim'.exists
  have := h (u n) (hu n)
  rw [hnorm n, mul_one] at this
  linarith

omit [CompleteSpace E] [CompleteSpace F] in
theorem transverse_of_not_nullSequence
    (h : ¬ ∃ u : ℕ → E, (∀ n, u n ∈ (invisibleKernel R)ᗮ) ∧ (∀ n, ‖u n‖ = 1) ∧
      Tendsto (fun n => R (u n)) atTop (𝓝 0)) :
    ∃ c > 0, ∀ x ∈ (invisibleKernel R)ᗮ, c * ‖x‖ ≤ ‖R x‖ := by
  by_contra hno
  push Not at hno
  apply h
  have hx : ∀ n : ℕ, ∃ x ∈ (invisibleKernel R)ᗮ, ‖R x‖ < 1 / ((n : ℝ) + 1) * ‖x‖ :=
    fun n => hno _ (by positivity)
  choose x hxmem hxlt using hx
  have hxne : ∀ n, x n ≠ 0 := fun n h0 => by
    have := hxlt n
    rw [h0] at this
    simp at this
  refine ⟨fun n => ((‖x n‖⁻¹ : ℝ) : 𝕜) • x n, fun n => Submodule.smul_mem _ _ (hxmem n),
    fun n => ?_, ?_⟩
  · rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hxne n))]
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [map_smul, norm_smul, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    have hpos : 0 < ‖x n‖ := norm_pos_iff.mpr (hxne n)
    rw [inv_mul_le_iff₀ hpos]
    linarith [hxlt n]

/-- **Theorem 5.1: global response/properness classification.** -/
theorem globalProperness_tfae :
    List.TFAE [IsClosed (Set.range R),
      ∃ α > 0, ∀ K : E, α * Metric.infDist K (invisibleKernel R : Set E) ^ 2 ≤ ‖R K‖ ^ 2,
      IsUnit (reducedPositiveResponse R),
      ¬ ∃ u : ℕ → E, (∀ n, u n ∈ (invisibleKernel R)ᗮ) ∧ (∀ n, ‖u n‖ = 1) ∧
        Tendsto (fun n => R (u n)) atTop (𝓝 0)] := by
  have hT : IsClosed (Set.range R) ↔ ∃ c > 0, ∀ x ∈ (invisibleKernel R)ᗮ, c * ‖x‖ ≤ ‖R x‖ := by
    rw [← ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range]
    rfl
  tfae_have 1 → 2 := fun h => by
    obtain ⟨c, hc, hb⟩ := hT.mp h
    exact ⟨c ^ 2, by positivity, lowerBound_of_transverse R hc hb⟩
  tfae_have 2 → 1 := fun ⟨α, hα, hb⟩ =>
    hT.mpr ⟨Real.sqrt α, Real.sqrt_pos.mpr hα, transverse_of_lowerBound R hα hb⟩
  tfae_have 1 → 3 := fun h => by
    obtain ⟨c, hc, hb⟩ := hT.mp h
    exact isUnit_reducedPositiveResponse_of_transverse R hc hb
  tfae_have 3 → 1 := fun h => hT.mpr (transverse_of_isUnit R h)
  tfae_have 1 → 4 := fun h => by
    obtain ⟨c, hc, hb⟩ := hT.mp h
    exact not_nullSequence_of_transverse R hc hb
  tfae_have 4 → 1 := fun h => hT.mpr (transverse_of_not_nullSequence R h)
  tfae_finish

/-- Under closed range, asymptotically vanishing response forces the interventions to the
invisible kernel. -/
theorem tendsto_infDist_of_isClosed_range (hR : IsClosed (Set.range R)) {K : ℕ → E}
    (hK : Tendsto (fun n => R (K n)) atTop (𝓝 0)) :
    Tendsto (fun n => Metric.infDist (K n) (invisibleKernel R : Set E)) atTop (𝓝 0) := by
  have h2 := ((globalProperness_tfae R).out 0 1).mp hR
  obtain ⟨α, hα, hb⟩ := h2
  have hlim : Tendsto (fun n => ‖R (K n)‖ / Real.sqrt α) atTop (𝓝 0) := by
    simpa using (tendsto_zero_iff_norm_tendsto_zero.mp hK).div_const (Real.sqrt α)
  refine squeeze_zero (fun n => Metric.infDist_nonneg) (fun n => ?_) hlim
  have hs := transverse_of_lowerBound R hα hb
  rw [infDist_invisibleKernel, le_div_iff₀ (Real.sqrt_pos.mpr hα), mul_comm,
    ← apply_transverse R (K n)]
  exact hs _ (transverse_mem R (K n))

end Classification

/-! ### Compact responses -/

/-- A compact operator sends an orthonormal sequence, along a subsequence, to zero. -/
theorem exists_subseq_tendsto_zero_of_orthonormal {R : E →L[𝕜] F} (hR : IsCompactOperator R)
    {e : ℕ → E} (he : Orthonormal 𝕜 e) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun n => R (e (φ n))) atTop (𝓝 0) := by
  have hcpt := hR.isCompact_closure_image_closedBall (f := (R : E →ₗ[𝕜] F)) 1
  have hmem : ∀ n, R (e n) ∈ closure ((R : E →ₗ[𝕜] F) '' Metric.closedBall 0 1) := fun n =>
    subset_closure ⟨e n, by simp [he.1 n], rfl⟩
  obtain ⟨y, -, φ, hφ, hlim⟩ := hcpt.tendsto_subseq hmem
  refine ⟨φ, hφ, ?_⟩
  have hweak : ∀ z : F, Tendsto (fun n => ⟪z, R (e n)⟫_𝕜) atTop (𝓝 0) := fun z => by
    have hs := (he.inner_products_summable (ContinuousLinearMap.adjoint R z)).tendsto_atTop_zero
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hs' : Tendsto (fun n => ‖⟪e n, ContinuousLinearMap.adjoint R z⟫_𝕜‖) atTop (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hs
      simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using h
    refine hs'.congr fun n => ?_
    rw [norm_inner_symm, ContinuousLinearMap.adjoint_inner_left]
  have hy : y = 0 := by
    have h1 : Tendsto (fun n => ⟪y, R (e (φ n))⟫_𝕜) atTop (𝓝 ⟪y, y⟫_𝕜) :=
      ((continuous_const.inner continuous_id).tendsto y).comp hlim
    have h2 := (hweak y).comp hφ.tendsto_atTop
    exact inner_self_eq_zero.mp (tendsto_nhds_unique h1 h2)
  rw [← hy]
  exact hlim

/-- An infinite-dimensional Hilbert space contains an orthonormal sequence. -/
theorem exists_orthonormal_seq_of_infinite_dimensional {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] [CompleteSpace V] (hV : ¬ FiniteDimensional 𝕜 V) :
    ∃ e : ℕ → V, Orthonormal 𝕜 e := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 V
  have hw : Infinite w := by
    rw [← not_finite_iff_infinite]
    intro hfin
    haveI : Finite w := hfin
    haveI : FiniteDimensional 𝕜 (Submodule.span 𝕜 (Set.range b)) :=
      FiniteDimensional.span_of_finite 𝕜 (Set.finite_range b)
    have htop : Submodule.span 𝕜 (Set.range b) = ⊤ := by
      have hd := b.dense_span
      rwa [(Submodule.closed_of_finiteDimensional _).submodule_topologicalClosure_eq] at hd
    exact hV (Module.Finite.equiv (htop ▸ Submodule.topEquiv))
  let ι : ℕ ↪ w := Infinite.natEmbedding w
  exact ⟨b ∘ ι, b.orthonormal.comp ι ι.injective⟩

/-- **Compact responses are never proper** on an infinite-dimensional transverse space: there
is a unit null sequence in `N^⊥`, so none of the conditions of Theorem 5.1 holds. -/
theorem exists_nullSequence_of_isCompactOperator {R : E →L[𝕜] F} (hR : IsCompactOperator R)
    (hN : ¬ FiniteDimensional 𝕜 (invisibleKernel R)ᗮ) :
    ∃ u : ℕ → E, (∀ n, u n ∈ (invisibleKernel R)ᗮ) ∧ (∀ n, ‖u n‖ = 1) ∧
      Tendsto (fun n => R (u n)) atTop (𝓝 0) := by
  obtain ⟨e, he⟩ := exists_orthonormal_seq_of_infinite_dimensional hN
  have he' : Orthonormal 𝕜 (fun n => (e n : E)) :=
    he.comp_linearIsometry (invisibleKernel R)ᗮ.subtypeₗᵢ
  obtain ⟨φ, -, hlim⟩ := exists_subseq_tendsto_zero_of_orthonormal hR he'
  exact ⟨fun n => (e (φ n) : E), fun n => (e (φ n)).2, fun n => he'.1 (φ n), hlim⟩

theorem not_isClosed_range_of_isCompactOperator {R : E →L[𝕜] F} (hR : IsCompactOperator R)
    (hN : ¬ FiniteDimensional 𝕜 (invisibleKernel R)ᗮ) : ¬ IsClosed (Set.range R) := by
  intro h
  have h4 := ((globalProperness_tfae R).out 0 3).mp h
  exact h4 (exists_nullSequence_of_isCompactOperator hR hN)

/-! ### Corollary 5.2: intertwining unitaries -/

section Intertwining

variable {R : E →L[𝕜] F} (U : E ≃ₗᵢ[𝕜] E) (V : F ≃ₗᵢ[𝕜] F) (hUV : ∀ K, V (R K) = R (U K))
include hUV

omit [CompleteSpace E] [CompleteSpace F] in
theorem norm_apply_intertwined (K : E) : ‖R (U K)‖ = ‖R K‖ := by
  rw [← hUV, LinearIsometryEquiv.norm_map]

omit [CompleteSpace E] [CompleteSpace F] in
theorem mem_invisibleKernel_iff_intertwined (K : E) :
    U K ∈ invisibleKernel R ↔ K ∈ invisibleKernel R := by
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ← hUV,
    LinearIsometryEquiv.map_eq_zero_iff]

omit [CompleteSpace E] [CompleteSpace F] in
theorem infDist_intertwined (K : E) :
    Metric.infDist (U K) (invisibleKernel R : Set E) =
      Metric.infDist K (invisibleKernel R : Set E) := by
  have himage : (U : E → E) '' (invisibleKernel R : Set E) = invisibleKernel R := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mem_invisibleKernel_iff_intertwined U V hUV x).mpr hx
    · intro hy
      refine ⟨U.symm y, ?_, U.apply_symm_apply y⟩
      rw [SetLike.mem_coe, ← mem_invisibleKernel_iff_intertwined U V hUV, U.apply_symm_apply]
      exact hy
  calc Metric.infDist (U K) (invisibleKernel R : Set E)
      = Metric.infDist (U K) ((U : E → E) '' (invisibleKernel R : Set E)) := by rw [himage]
    _ = Metric.infDist K (invisibleKernel R : Set E) := Metric.infDist_image U.isometry

/-- The positive response commutes with the intervention unitary. -/
theorem positiveResponse_intertwined (K : E) :
    ContinuousLinearMap.adjoint R (R (U K)) = U (ContinuousLinearMap.adjoint R (R K)) := by
  refine ext_inner_right 𝕜 fun z => ?_
  obtain ⟨z', rfl⟩ := U.surjective z
  rw [ContinuousLinearMap.adjoint_inner_left, LinearIsometryEquiv.inner_map_map,
    ContinuousLinearMap.adjoint_inner_left, ← hUV, ← hUV, LinearIsometryEquiv.inner_map_map]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Null sequences are transported. -/
theorem tendsto_intertwined_iff {K : ℕ → E} :
    Tendsto (fun n => R (U (K n))) atTop (𝓝 0) ↔ Tendsto (fun n => R (K n)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero (f := fun n => R (U (K n))),
    tendsto_zero_iff_norm_tendsto_zero (f := fun n => R (K n))]
  simp only [norm_apply_intertwined U V hUV]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The `(SR.26)` constants are transported. -/
theorem lowerBound_intertwined_iff (α : ℝ) :
    (∀ K, α * Metric.infDist (U K) (invisibleKernel R : Set E) ^ 2 ≤ ‖R (U K)‖ ^ 2) ↔
      ∀ K, α * Metric.infDist K (invisibleKernel R : Set E) ^ 2 ≤ ‖R K‖ ^ 2 := by
  simp only [infDist_intertwined U V hUV, norm_apply_intertwined U V hUV]

omit [CompleteSpace E] [CompleteSpace F] hUV in
/-- **Corollary 5.2**: the intertwined response `R ∘ U` is proper exactly when `R` is. -/
theorem isClosed_range_intertwined_iff :
    IsClosed (Set.range fun K => R (U K)) ↔ IsClosed (Set.range R) := by
  have h : (Set.range fun K => R (U K)) = Set.range R := by
    ext y
    constructor
    · rintro ⟨K, rfl⟩
      exact ⟨U K, rfl⟩
    · rintro ⟨K, rfl⟩
      exact ⟨U.symm K, by simp⟩
  rw [h]

end Intertwining

end GaloisForLFunctions.HTGeometry

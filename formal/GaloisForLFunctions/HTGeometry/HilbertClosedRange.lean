import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Transverse lower bounds and the Hilbert closed-range theorem

For a bounded operator `T` between Hilbert spaces the three properties

* a uniform lower bound `c‖x‖ ≤ ‖T x‖` on the orthogonal complement of `ker T`,
* closedness of `ran T`,
* closedness of `ran T*`,

are equivalent, and under them `ran T* = (ker T)ᗮ` exactly.

The proof is self-contained.  A bounded operator whose quadratic form is uniformly positive is
bounded below, so its range is closed, and a vector orthogonal to its range is orthogonal to its
own image, hence zero; therefore such an operator is surjective.  Applying this to the
corestriction of `T* ∘ T` to `(ker T)ᗮ` identifies `ran T*` with `(ker T)ᗮ`.  The reverse
implication follows from `T** = T`.
-/

open scoped InnerProductSpace

namespace ContinuousLinearMap

section Coercive

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [CompleteSpace V]

omit [CompleteSpace V] in
/-- A bounded operator with uniformly positive quadratic form is bounded below. -/
theorem norm_le_of_reCoercive {S : V →L[𝕜] V} {c : ℝ}
    (hS : ∀ w : V, c * ‖w‖ ^ 2 ≤ RCLike.re (⟪S w, w⟫_𝕜)) (w : V) :
    c * ‖w‖ ≤ ‖S w‖ := by
  rcases eq_or_lt_of_le (norm_nonneg w) with hw | hw
  · have hSw : c * ‖w‖ = 0 := by rw [← hw]; ring
    rw [hSw]
    exact norm_nonneg _
  · have h1 : RCLike.re (⟪S w, w⟫_𝕜) ≤ ‖S w‖ * ‖w‖ :=
      le_trans (RCLike.re_le_norm _) (norm_inner_le_norm _ _)
    have h3 : c * ‖w‖ * ‖w‖ ≤ ‖S w‖ * ‖w‖ := by
      calc c * ‖w‖ * ‖w‖ = c * ‖w‖ ^ 2 := by ring
        _ ≤ RCLike.re (⟪S w, w⟫_𝕜) := hS w
        _ ≤ ‖S w‖ * ‖w‖ := h1
    exact le_of_mul_le_mul_right h3 hw

/-- **Coercive surjectivity.**  A bounded operator with uniformly positive quadratic form is
surjective. -/
theorem surjective_of_reCoercive {S : V →L[𝕜] V} {c : ℝ} (hc : 0 < c)
    (hS : ∀ w : V, c * ‖w‖ ^ 2 ≤ RCLike.re (⟪S w, w⟫_𝕜)) :
    Function.Surjective S := by
  have hanti : AntilipschitzWith (Real.toNNReal c⁻¹) S := by
    refine AddMonoidHomClass.antilipschitz_of_bound S ?_
    intro w
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr hc.le), inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
    exact norm_le_of_reCoercive hS w
  have hclosed : IsClosed (Set.range S) := hanti.isClosed_range S.uniformContinuous
  have hrange : IsClosed ((LinearMap.range (S : V →ₗ[𝕜] V) : Submodule 𝕜 V) : Set V) := by
    rwa [LinearMap.coe_range]
  haveI : CompleteSpace (LinearMap.range (S : V →ₗ[𝕜] V)) := hrange.completeSpace_coe
  have hperp : (LinearMap.range (S : V →ₗ[𝕜] V))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    have hzz : ⟪S z, z⟫_𝕜 = 0 :=
      (Submodule.mem_orthogonal _ z).mp hz (S z) ⟨z, rfl⟩
    have hzc := hS z
    rw [hzz, map_zero] at hzc
    have hz2 : ‖z‖ ^ 2 ≤ 0 := by nlinarith
    have hz0 : ‖z‖ ≤ 0 := by nlinarith [norm_nonneg z]
    exact norm_eq_zero.mp (le_antisymm hz0 (norm_nonneg z))
  have htop : LinearMap.range (S : V →ₗ[𝕜] V) = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.mp hperp
  intro y
  have hy : y ∈ LinearMap.range (S : V →ₗ[𝕜] V) := by rw [htop]; trivial
  exact hy

end Coercive

section ClosedRange

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The **transverse lower bound**: a uniform positive lower bound for `T` on the orthogonal
complement of its kernel. -/
def HasTransverseLowerBound (T : E →L[𝕜] F) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x ∈ (LinearMap.ker (T : E →ₗ[𝕜] F))ᗮ, c * ‖x‖ ≤ ‖T x‖

instance kerHasOrthogonalProjection (T : E →L[𝕜] F) :
    (LinearMap.ker (T : E →ₗ[𝕜] F)).HasOrthogonalProjection := by
  haveI : CompleteSpace (LinearMap.ker (T : E →ₗ[𝕜] F)) :=
    (T.isClosed_ker).completeSpace_coe
  infer_instance

instance kerOrthogonalCompleteSpace (T : E →L[𝕜] F) :
    CompleteSpace ((LinearMap.ker (T : E →ₗ[𝕜] F))ᗮ : Submodule 𝕜 E) :=
  (Submodule.isClosed_orthogonal _).completeSpace_coe

/-- The restriction of `T` to the orthogonal complement of its kernel. -/
noncomputable def transverseRestriction (T : E →L[𝕜] F) :
    ((LinearMap.ker (T : E →ₗ[𝕜] F))ᗮ : Submodule 𝕜 E) →L[𝕜] F :=
  T ∘L (LinearMap.ker (T : E →ₗ[𝕜] F))ᗮ.subtypeL

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem transverseRestriction_apply (T : E →L[𝕜] F)
    (v : ((LinearMap.ker (T : E →ₗ[𝕜] F))ᗮ : Submodule 𝕜 E)) :
    transverseRestriction T v = T (v : E) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
theorem transverseRestriction_injective (T : E →L[𝕜] F) :
    Function.Injective (transverseRestriction T) := by
  intro v w hvw
  have hvw' : T (v : E) = T (w : E) := hvw
  have hker : (v : E) - (w : E) ∈ LinearMap.ker (T : E →ₗ[𝕜] F) := by
    have h : (T : E →ₗ[𝕜] F) ((v : E) - (w : E)) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hvw'
    exact h
  have hperp : (v : E) - (w : E) ∈ (LinearMap.ker (T : E →ₗ[𝕜] F))ᗮ :=
    Submodule.sub_mem _ v.2 w.2
  have hzero : ⟪(v : E) - (w : E), (v : E) - (w : E)⟫_𝕜 = 0 :=
    (Submodule.mem_orthogonal _ _).mp hperp _ hker
  exact Subtype.ext (sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := 𝕜)).mp hzero))

omit [CompleteSpace F] in
theorem range_transverseRestriction (T : E →L[𝕜] F) :
    Set.range (transverseRestriction T) = Set.range T := by
  apply Set.Subset.antisymm
  · rintro _ ⟨v, rfl⟩
    exact ⟨(v : E), rfl⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨⟨(LinearMap.ker (T : E →ₗ[𝕜] F))ᗮ.starProjection x,
      (LinearMap.ker (T : E →ₗ[𝕜] F))ᗮ.starProjection_apply_mem x⟩, ?_⟩
    have hsplit : (LinearMap.ker (T : E →ₗ[𝕜] F)).starProjection x
        + (LinearMap.ker (T : E →ₗ[𝕜] F))ᗮ.starProjection x = x :=
      (LinearMap.ker (T : E →ₗ[𝕜] F)).starProjection_add_starProjection_orthogonal x
    have hkerx : T ((LinearMap.ker (T : E →ₗ[𝕜] F)).starProjection x) = 0 :=
      (LinearMap.ker (T : E →ₗ[𝕜] F)).starProjection_apply_mem x
    show T ((LinearMap.ker (T : E →ₗ[𝕜] F))ᗮ.starProjection x) = T x
    conv_rhs => rw [← hsplit]
    rw [map_add, hkerx, zero_add]

/-- **Transverse lower bound is closed range.** -/
theorem hasTransverseLowerBound_iff_isClosed_range (T : E →L[𝕜] F) :
    HasTransverseLowerBound T ↔ IsClosed (Set.range T) := by
  set K := LinearMap.ker (T : E →ₗ[𝕜] F) with hK
  constructor
  · rintro ⟨c, hc, hbound⟩
    have hanti : AntilipschitzWith (Real.toNNReal c⁻¹) (transverseRestriction T) := by
      refine AddMonoidHomClass.antilipschitz_of_bound _ ?_
      intro v
      rw [Real.coe_toNNReal _ (inv_nonneg.mpr hc.le), inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
      exact hbound (v : E) v.2
    have hcl := hanti.isClosed_range (transverseRestriction T).uniformContinuous
    rwa [range_transverseRestriction] at hcl
  · intro hclosed
    have hclosed' : IsClosed (Set.range (transverseRestriction T)) := by
      rwa [range_transverseRestriction]
    obtain ⟨M, hM⟩ :=
      ((transverseRestriction T).isClosed_range_iff_antilipschitz_of_injective
        (transverseRestriction_injective T)).mp hclosed'
    have hpos : (0 : ℝ) < max (M : ℝ) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    refine ⟨(max (M : ℝ) 1)⁻¹, by positivity, ?_⟩
    intro x hx
    have hv : ‖x‖ ≤ (M : ℝ) * ‖T x‖ := by
      have hd := hM.le_mul_dist (⟨x, hx⟩ : (Kᗮ : Submodule 𝕜 E)) 0
      simpa [dist_eq_norm] using hd
    have hx' : ‖x‖ ≤ max (M : ℝ) 1 * ‖T x‖ :=
      le_trans hv (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    rw [inv_mul_eq_div, div_le_iff₀ hpos, mul_comm]
    exact hx'

theorem range_adjoint_le_ker_orthogonal (T : E →L[𝕜] F) :
    LinearMap.range ((ContinuousLinearMap.adjoint T : F →L[𝕜] E) : F →ₗ[𝕜] E)
      ≤ (LinearMap.ker (T : E →ₗ[𝕜] F))ᗮ := by
  rw [T.orthogonal_ker]
  exact Submodule.le_topologicalClosure _

/-- **Closed range identifies the adjoint range.**  If `ran T` is closed then `ran T* = (ker T)ᗮ`.
-/
theorem range_adjoint_eq_ker_orthogonal_of_isClosed_range (T : E →L[𝕜] F)
    (hclosed : IsClosed (Set.range T)) :
    LinearMap.range ((ContinuousLinearMap.adjoint T : F →L[𝕜] E) : F →ₗ[𝕜] E)
      = (LinearMap.ker (T : E →ₗ[𝕜] F))ᗮ := by
  set K := LinearMap.ker (T : E →ₗ[𝕜] F) with hK
  refine le_antisymm (range_adjoint_le_ker_orthogonal T) ?_
  obtain ⟨c, hc, hbound⟩ := (hasTransverseLowerBound_iff_isClosed_range T).mpr hclosed
  have hmem : ∀ v : (Kᗮ : Submodule 𝕜 E),
      (ContinuousLinearMap.adjoint T) (T (v : E)) ∈ Kᗮ :=
    fun v => range_adjoint_le_ker_orthogonal T ⟨T (v : E), rfl⟩
  set S : (Kᗮ : Submodule 𝕜 E) →L[𝕜] (Kᗮ : Submodule 𝕜 E) :=
    (((ContinuousLinearMap.adjoint T) ∘L T) ∘L Kᗮ.subtypeL).codRestrict Kᗮ hmem with hS
  have hSapply : ∀ v : (Kᗮ : Submodule 𝕜 E),
      ((S v : (Kᗮ : Submodule 𝕜 E)) : E) = (ContinuousLinearMap.adjoint T) (T (v : E)) :=
    fun v => rfl
  have hform : ∀ v : (Kᗮ : Submodule 𝕜 E),
      c ^ 2 * ‖v‖ ^ 2 ≤ RCLike.re (⟪S v, v⟫_𝕜) := by
    intro v
    have hinner : ⟪S v, v⟫_𝕜 = ⟪T (v : E), T (v : E)⟫_𝕜 := by
      have h1 : ⟪S v, v⟫_𝕜 = ⟪((S v : (Kᗮ : Submodule 𝕜 E)) : E), (v : E)⟫_𝕜 := rfl
      rw [h1, hSapply v]
      exact ContinuousLinearMap.adjoint_inner_left T (v : E) (T (v : E))
    rw [hinner, inner_self_eq_norm_sq]
    have hb : c * ‖v‖ ≤ ‖T (v : E)‖ := hbound (v : E) v.2
    have hsq : (c * ‖v‖) ^ 2 ≤ ‖T (v : E)‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hb 2
    calc c ^ 2 * ‖v‖ ^ 2 = (c * ‖v‖) ^ 2 := by ring
      _ ≤ ‖T (v : E)‖ ^ 2 := hsq
  have hsurj := surjective_of_reCoercive (by positivity : (0 : ℝ) < c ^ 2) hform
  intro x hx
  obtain ⟨w, hw⟩ := hsurj ⟨x, hx⟩
  refine ⟨T (w : E), ?_⟩
  have := congrArg (fun z : (Kᗮ : Submodule 𝕜 E) => (z : E)) hw
  simpa [hSapply w] using this

/-- **Hilbert closed-range theorem.**  The range of a bounded Hilbert-space operator is closed
exactly when the range of its adjoint is. -/
theorem isClosed_range_adjoint_iff (T : E →L[𝕜] F) :
    IsClosed (Set.range (ContinuousLinearMap.adjoint T)) ↔ IsClosed (Set.range T) := by
  constructor
  · intro h
    have hT : IsClosed (Set.range (ContinuousLinearMap.adjoint
        (ContinuousLinearMap.adjoint T))) := by
      have hrange := range_adjoint_eq_ker_orthogonal_of_isClosed_range
        (ContinuousLinearMap.adjoint T) h
      have hset : Set.range (ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint T))
          = (((LinearMap.ker ((ContinuousLinearMap.adjoint T : F →L[𝕜] E) : F →ₗ[𝕜] E))ᗮ
            : Submodule 𝕜 F) : Set F) := by
        rw [← hrange]
        exact (LinearMap.coe_range _).symm
      rw [hset]
      exact Submodule.isClosed_orthogonal _
    rwa [ContinuousLinearMap.adjoint_adjoint] at hT
  · intro h
    have hrange := range_adjoint_eq_ker_orthogonal_of_isClosed_range T h
    have hset : Set.range (ContinuousLinearMap.adjoint T)
        = (((LinearMap.ker (T : E →ₗ[𝕜] F))ᗮ : Submodule 𝕜 E) : Set E) := by
      rw [← hrange]
      exact (LinearMap.coe_range _).symm
    rw [hset]
    exact Submodule.isClosed_orthogonal _

end ClosedRange

end ContinuousLinearMap

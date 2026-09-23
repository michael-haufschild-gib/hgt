import GaloisForLFunctions.HTGeometry.SymmetricReplicaRankLaw
import GaloisForLFunctions.HTGeometry.QuenchedReplicaReturnExcisionLaw

/-!
# Projected replica return-excision law

A complete target-capture event survives one-copy orthogonal projection with
amplitude threshold reduced only by the source projection defect.  Return
excision is performed on the source before integration, so recurrence mass is
charged once and all nonreturn fibre sheets retain their multiplicity.

Two exact measure laws result.  The shifted-threshold form has denominator
`(sqrt a - eta)^(2r)`.  The additive form retains the original threshold and
pays the complete target union's projection error once as
`2 r eta * measure(returnSetᶜ)`.  Neither law enumerates target labels.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

theorem norm_inner_projected_projected_ge_sqrt_sub
    {α : Type*} [Fintype α]
    (S : Submodule ℂ (EuclideanSpace ℂ α))
    (ψ z : α → ℂ) {a η : ℝ}
    (hz : ‖WithLp.toLp 2 z‖ ≤ 1)
    (hdef : ‖WithLp.toLp 2 ψ -
      S.starProjection (WithLp.toLp 2 ψ)‖ ≤ η)
    (hcap : a ≤ finitePureStateFidelity ψ z) :
    Real.sqrt a - η ≤
      ‖inner ℂ (S.starProjection (WithLp.toLp 2 ψ))
        (S.starProjection (WithLp.toLp 2 z))‖ := by
  let u : EuclideanSpace ℂ α := WithLp.toLp 2 ψ
  let v : EuclideanSpace ℂ α := WithLp.toLp 2 z
  let p : EuclideanSpace ℂ α := S.starProjection u
  have hsqrt : Real.sqrt a ≤ ‖inner ℂ u v‖ := by
    rw [Real.sqrt_le_left (norm_nonneg _)]
    simpa [u, v, finitePureStateFidelity,
      inner_toLp_eq_finiteComplexInner] using hcap
  have herror : ‖inner ℂ (u - p) v‖ ≤ η := by
    calc
      ‖inner ℂ (u - p) v‖ ≤ ‖u - p‖ * ‖v‖ := norm_inner_le_norm _ _
      _ ≤ η * 1 := mul_le_mul hdef hz (norm_nonneg v) (by linarith [norm_nonneg (u - p)])
      _ = η := mul_one _
  have hsplit : inner ℂ u v = inner ℂ (u - p) v + inner ℂ p v := by
    rw [← inner_add_left]
    congr 2
    abel
  have htri : ‖inner ℂ u v‖ ≤ η + ‖inner ℂ p v‖ := by
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add herror le_rfl)
  have hlow : Real.sqrt a - η ≤ ‖inner ℂ p v‖ := by linarith
  have hpfix : S.starProjection p = p :=
    S.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem u)
  have hinner : inner ℂ p (S.starProjection v) = inner ℂ p v := by
    rw [← S.inner_starProjection_left_eq_right, hpfix]
  simpa [u, v, p, hinner] using hlow

theorem completeTargetCapture_subset_projectedCapture
    {X C α : Type*} [Fintype α]
    (S : Submodule ℂ (EuclideanSpace ℂ α))
    (target : C → α → ℂ) (state : X → α → ℂ)
    (htarget : ∀ c, ‖WithLp.toLp 2 (target c)‖ ≤ 1)
    {a η : ℝ} (hdelta : 0 ≤ Real.sqrt a - η)
    (hdef : ∀ x, ‖WithLp.toLp 2 (state x) -
      S.starProjection (WithLp.toLp 2 (state x))‖ ≤ η) :
    {x | ∃ c, a ≤ finitePureStateFidelity (state x) (target c)} ⊆
      {x | ∃ c, (Real.sqrt a - η) ^ (2 : ℕ) ≤
        finitePureStateFidelity
          (fun i => S.starProjection (WithLp.toLp 2 (state x)) i)
          (projectedReplicaTarget S target c)} := by
  intro x hx
  rcases hx with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  have hlower := norm_inner_projected_projected_ge_sqrt_sub
    S (state x) (target c) (htarget c) (hdef x) hc
  have hsquare := pow_le_pow_left₀ hdelta hlower 2
  have hstate :
      WithLp.toLp 2
          (fun i => S.starProjection (WithLp.toLp 2 (state x)) i) =
        S.starProjection (WithLp.toLp 2 (state x)) := by
    ext i
    rfl
  have htarget' :
      WithLp.toLp 2 (projectedReplicaTarget S target c) =
        S.starProjection (WithLp.toLp 2 (target c)) := by
    ext i
    rfl
  simpa [finitePureStateFidelity, ← inner_toLp_eq_finiteComplexInner,
    hstate, htarget'] using hsquare

theorem measureReal_capture_le_return_add_projectedMoment
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) [IsFiniteMeasure μ]
    {r : ℕ} (hr : 0 < r)
    (S : Submodule ℂ (EuclideanSpace ℂ α))
    (target : C → α → ℂ) (state : X → α → ℂ)
    (htarget : ∀ c, ‖WithLp.toLp 2 (target c)‖ ≤ 1)
    {a η : ℝ} (hη : η < Real.sqrt a)
    (hdef : ∀ x, ‖WithLp.toLp 2 (state x) -
      S.starProjection (WithLp.toLp 2 (state x))‖ ≤ η)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (hint : Integrable
      (fun x => replicaTargetProjectionMass r
        (projectedReplicaTarget S target)
        (fun i => S.starProjection (WithLp.toLp 2 (state x)) i))
      (μ.restrict returnSetᶜ)) :
    μ.real {x | ∃ c, a ≤ finitePureStateFidelity (state x) (target c)} ≤
      μ.real returnSet +
        (∫ x, replicaTargetProjectionMass r
          (projectedReplicaTarget S target)
          (fun i => S.starProjection (WithLp.toLp 2 (state x)) i)
            ∂(μ.restrict returnSetᶜ)) /
          (Real.sqrt a - η) ^ (2 * r) := by
  let δ := Real.sqrt a - η
  let projectedState : X → α → ℂ := fun x i =>
    S.starProjection (WithLp.toLp 2 (state x)) i
  let projectedTarget : C → α → ℂ := projectedReplicaTarget S target
  let E : Set X :=
    {x | ∃ c, a ≤ finitePureStateFidelity (state x) (target c)}
  let EP : Set X :=
    {x | ∃ c, δ ^ (2 : ℕ) ≤
      finitePureStateFidelity (projectedState x) (projectedTarget c)}
  have hδ : 0 < δ := sub_pos.mpr hη
  have hsubset : E ⊆ EP := by
    simpa [E, EP, δ, projectedState, projectedTarget] using
      completeTargetCapture_subset_projectedCapture S target state htarget
        hδ.le hdef
  have hprojectedTarget : ∀ c,
      ‖finitePureTensorPowerEuclidean r (projectedTarget c)‖ ≤ 1 := by
    intro c
    apply norm_finitePureTensorPowerEuclidean_le_one
    have hcoord :
        WithLp.toLp 2 (projectedTarget c) =
          S.starProjection (WithLp.toLp 2 (target c)) := by
      ext i
      rfl
    rw [hcoord]
    exact (S.norm_starProjection_apply_le _).trans (htarget c)
  have hprojected :
      (μ.restrict returnSetᶜ).real EP ≤
        (∫ x, replicaTargetProjectionMass r projectedTarget (projectedState x)
          ∂(μ.restrict returnSetᶜ)) / δ ^ (2 * r) := by
    have hbound := measure_completePureStateTargetCapture_le_replicaProjectionMoment
      (μ.restrict returnSetᶜ) hr projectedTarget projectedState
        hprojectedTarget (δ ^ (2 : ℕ)) (sq_pos_of_pos hδ) (by
          simpa [projectedTarget, projectedState] using hint)
    simpa [EP, pow_mul] using hbound
  have hresidual :
      (μ.restrict returnSetᶜ).real E ≤
        (∫ x, replicaTargetProjectionMass r projectedTarget (projectedState x)
          ∂(μ.restrict returnSetᶜ)) / δ ^ (2 * r) :=
    (measureReal_mono hsubset).trans hprojected
  have hcut := measureReal_capture_le_return_add_restrict_compl
    μ target state a returnSet hreturn
  calc
    μ.real {x | ∃ c, a ≤ finitePureStateFidelity (state x) (target c)} =
        μ.real E := rfl
    _ ≤ μ.real returnSet + (μ.restrict returnSetᶜ).real E := by
      simpa [E] using hcut
    _ ≤ μ.real returnSet +
        (∫ x, replicaTargetProjectionMass r projectedTarget (projectedState x)
          ∂(μ.restrict returnSetᶜ)) / δ ^ (2 * r) :=
      add_le_add le_rfl hresidual
    _ = _ := rfl

theorem measureReal_capture_le_return_add_projectedMoment_error
    {X C α : Type*} [MeasurableSpace X] [Fintype α] [DecidableEq α]
    (μ : Measure X) [IsFiniteMeasure μ]
    {r : ℕ} (hr : 0 < r)
    (S : Submodule ℂ (EuclideanSpace ℂ α))
    (target : C → α → ℂ) (state : X → α → ℂ)
    (htarget : ∀ c,
      ‖finitePureTensorPowerEuclidean r (target c)‖ ≤ 1)
    (hstate : ∀ x, ‖WithLp.toLp 2 (state x)‖ ≤ 1)
    {a η : ℝ} (ha : 0 < a)
    (hdef : ∀ x, ‖WithLp.toLp 2 (state x) -
      S.starProjection (WithLp.toLp 2 (state x))‖ ≤ η)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (hintOriginal : Integrable
      (fun x => replicaTargetProjectionMass r target (state x))
      (μ.restrict returnSetᶜ))
    (hintProjected : Integrable
      (fun x => replicaTargetProjectionMass r
        (projectedReplicaTarget S target)
        (fun i => S.starProjection (WithLp.toLp 2 (state x)) i))
      (μ.restrict returnSetᶜ)) :
    μ.real {x | ∃ c, a ≤ finitePureStateFidelity (state x) (target c)} ≤
      μ.real returnSet +
        ((∫ x, replicaTargetProjectionMass r
          (projectedReplicaTarget S target)
          (fun i => S.starProjection (WithLp.toLp 2 (state x)) i)
            ∂(μ.restrict returnSetᶜ)) +
          2 * (r : ℝ) * η * μ.real returnSetᶜ) / a ^ r := by
  let ν := μ.restrict returnSetᶜ
  let q : X → ℝ := fun x => replicaTargetProjectionMass r target (state x)
  let qP : X → ℝ := fun x => replicaTargetProjectionMass r
    (projectedReplicaTarget S target)
    (fun i => S.starProjection (WithLp.toLp 2 (state x)) i)
  let E : Set X :=
    {x | ∃ c, a ≤ finitePureStateFidelity (state x) (target c)}
  have hpoint : ∀ x, q x ≤ qP x + 2 * (r : ℝ) * η := by
    intro x
    exact replicaTargetProjectionMass_le_projected_add_error
      hr S target (state x) (hstate x) (hdef x)
  have hintP : Integrable qP ν := by
    simpa [qP, ν] using hintProjected
  have hsumInt : Integrable (fun x => qP x + 2 * (r : ℝ) * η) ν :=
    hintP.add (integrable_const _)
  have hintQ : Integrable q ν := by simpa [q, ν] using hintOriginal
  have hintegral :
      (∫ x, q x ∂ν) ≤
        (∫ x, qP x ∂ν) + 2 * (r : ℝ) * η * μ.real returnSetᶜ := by
    calc
      (∫ x, q x ∂ν) ≤ ∫ x, qP x + 2 * (r : ℝ) * η ∂ν :=
        integral_mono hintQ hsumInt hpoint
      _ = (∫ x, qP x ∂ν) + 2 * (r : ℝ) * η * μ.real returnSetᶜ := by
        rw [integral_add hintP (integrable_const _), integral_const, smul_eq_mul]
        change (∫ x, qP x ∂ν) + ν.real Set.univ * (2 * (r : ℝ) * η) = _
        rw [show ν.real Set.univ = μ.real returnSetᶜ by
          simp [ν, Measure.real]]
        ring
  have hmoment := measure_completePureStateTargetCapture_le_replicaProjectionMoment
    ν hr target state htarget a ha (by simpa [q, ν] using hintOriginal)
  have hresidual :
      ν.real E ≤
        ((∫ x, qP x ∂ν) + 2 * (r : ℝ) * η * μ.real returnSetᶜ) /
          a ^ r := by
    calc
      ν.real E ≤ (∫ x, q x ∂ν) / a ^ r := by
        simpa [E, q, ν] using hmoment
      _ ≤ ((∫ x, qP x ∂ν) + 2 * (r : ℝ) * η * μ.real returnSetᶜ) /
          a ^ r := div_le_div_of_nonneg_right hintegral (pow_nonneg ha.le r)
  have hcut := measureReal_capture_le_return_add_restrict_compl
    μ target state a returnSet hreturn
  calc
    μ.real {x | ∃ c, a ≤ finitePureStateFidelity (state x) (target c)} =
        μ.real E := rfl
    _ ≤ μ.real returnSet + ν.real E := by simpa [E, ν] using hcut
    _ ≤ μ.real returnSet +
        ((∫ x, qP x ∂ν) + 2 * (r : ℝ) * η * μ.real returnSetᶜ) /
          a ^ r := add_le_add le_rfl hresidual
    _ = _ := rfl

end

end GaloisForLFunctions.HTGeometry

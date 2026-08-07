import GaloisForLFunctions.HTGeometry.ReplicaHilbertCoareaIncidenceLaw

/-!
# Return-shell replica coarea incidence law

Exact return removal sends a longitudinal target to zero, but approximate
return removal supplies more information: its residual has norm strictly below
one.  This file retains that norm through replica lifting instead of discarding
it in the usual projection estimate.

Targets are grouped into finitely many residual-norm shells.  Each shell is
represented only by the span of its occupied replica image, so duplicate
labels do not count.  Its one-copy squared-radius is then raised to replica
order.  The resulting single reporter bounds the complete target union before
integration.  Source points are never quotiented, so every fibre sheet remains
inside the quenched integral.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The squared norm of a replica lift is the replica power of the one-copy
squared norm. -/
theorem norm_sq_finitePureTensorPowerEuclidean_eq_pow
    {α : Type*} [Fintype α] (r : ℕ) (ψ : α → ℂ) :
    ‖finitePureTensorPowerEuclidean r ψ‖ ^ 2 =
      (‖WithLp.toLp 2 ψ‖ ^ 2) ^ r := by
  have hreplica := inner_finitePureTensorPowerEuclidean r ψ ψ
  rw [inner_self_eq_norm_sq_to_K] at hreplica
  have hone := inner_toLp_eq_finiteComplexInner ψ ψ
  rw [inner_self_eq_norm_sq_to_K] at hone
  rw [← hone] at hreplica
  exact_mod_cast hreplica

/-- A one-copy squared-radius cap becomes its `r`th power after replica
lifting. -/
theorem norm_sq_finitePureTensorPowerEuclidean_le_radius_pow
    {α : Type*} [Fintype α] (r : ℕ) (ψ : α → ℂ) {radius : ℝ}
    (hψ : ‖WithLp.toLp 2 ψ‖ ^ 2 ≤ radius) :
    ‖finitePureTensorPowerEuclidean r ψ‖ ^ 2 ≤ radius ^ r := by
  rw [norm_sq_finitePureTensorPowerEuclidean_eq_pow]
  exact pow_le_pow_left₀ (sq_nonneg _) hψ r

/-- Sharp target-span domination retaining the target norm.  The earlier
unit-ball law is obtained by bounding the final factor by one. -/
theorem finitePureStateFidelity_pow_le_replicaTargetProjectionMass_mul_norm_sq
    {C α : Type*} [Fintype α]
    (r : ℕ) (target : C → α → ℂ)
    (ψ : α → ℂ) (c : C) :
    finitePureStateFidelity ψ (target c) ^ r ≤
      replicaTargetProjectionMass r target ψ *
        ‖finitePureTensorPowerEuclidean r (target c)‖ ^ 2 := by
  let S := replicaTargetSpan r target
  let u := finitePureTensorPowerEuclidean r ψ
  let v := finitePureTensorPowerEuclidean r (target c)
  have hv : v ∈ S :=
    Submodule.subset_span (Set.mem_range_self c)
  let vS : S := ⟨v, hv⟩
  have hproj :
      inner ℂ (S.orthogonalProjectionOnto u) vS = inner ℂ u v :=
    S.inner_orthogonalProjectionOnto_eq_of_mem_right vS u
  have hcs := norm_inner_le_norm (𝕜 := ℂ)
    (S.orthogonalProjectionOnto u) vS
  have hinner :
      ‖inner ℂ u v‖ ≤ ‖S.orthogonalProjectionOnto u‖ * ‖vS‖ := by
    rw [← hproj]
    exact hcs
  have hfid :
      finitePureStateFidelity ψ (target c) ^ r =
        ‖inner ℂ u v‖ ^ 2 := by
    rw [← finitePureStateFidelity_tensorPower r ψ (target c)]
    rw [finitePureStateFidelity, show inner ℂ u v =
      finiteComplexInner (finitePureTensorPower r ψ)
        (finitePureTensorPower r (target c)) by
          exact inner_toLp_eq_finiteComplexInner _ _]
  rw [hfid, replicaTargetProjectionMass]
  calc
    ‖inner ℂ u v‖ ^ 2 ≤
        (‖S.orthogonalProjectionOnto u‖ * ‖vS‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hinner 2
    _ = ‖S.orthogonalProjectionOnto u‖ ^ 2 * ‖v‖ ^ 2 := by
      simp [vS, mul_pow]

/-- One complete reporter for finitely many residual-radius shells.  Within a
shell only the occupied replica span matters; its coefficient is the replica
power of that shell's one-copy squared-radius. -/
noncomputable def replicaReturnShellProjectionMass
    {B α : Type*} [Fintype B] [Fintype α]
    (r : ℕ) (C : B → Type*)
    (target : ∀ b, C b → α → ℂ)
    (radius : B → ℝ) (ψ : α → ℂ) : ℝ :=
  ∑ b, radius b ^ r * replicaTargetProjectionMass r (target b) ψ

theorem replicaReturnShellProjectionMass_nonneg
    {B α : Type*} [Fintype B] [Fintype α]
    (r : ℕ) (C : B → Type*)
    (target : ∀ b, C b → α → ℂ)
    {radius : B → ℝ} (hradius : ∀ b, 0 ≤ radius b)
    (ψ : α → ℂ) :
    0 ≤ replicaReturnShellProjectionMass r C target radius ψ := by
  unfold replicaReturnShellProjectionMass
  exact Finset.sum_nonneg fun b _ =>
    mul_nonneg (pow_nonneg (hradius b) r) (sq_nonneg _)

private theorem le_sum_univ_of_nonneg
    {B : Type*} [Fintype B] (f : B → ℝ)
    (hf : ∀ b, 0 ≤ f b) (b : B) :
    f b ≤ ∑ j, f j := by
  exact Finset.single_le_sum (fun j _ => hf j) (Finset.mem_univ b)

/-- Duplicating every target label inside every shell changes neither the
weighted reporter nor its occupied image. -/
theorem replicaReturnShellProjectionMass_duplicated
    {B α : Type*} [Fintype B] [Fintype α]
    (r : ℕ) (C : B → Type*)
    (target : ∀ b, C b → α → ℂ)
    (radius : B → ℝ) (ψ : α → ℂ) :
    replicaReturnShellProjectionMass r (fun b => C b ⊕ C b)
        (fun b => duplicatedReplicaTarget (target b)) radius ψ =
      replicaReturnShellProjectionMass r C target radius ψ := by
  unfold replicaReturnShellProjectionMass
  apply Finset.sum_congr rfl
  intro b hb
  rw [replicaTargetProjectionMass_duplicated]

/-- Adjoining an exact-return zero to every shell changes neither the
weighted reporter nor its occupied image. -/
theorem replicaReturnShellProjectionMass_withZero
    {B α : Type*} [Fintype B] [Fintype α]
    {r : ℕ} (hr : 0 < r) (C : B → Type*)
    (target : ∀ b, C b → α → ℂ)
    (radius : B → ℝ) (ψ : α → ℂ) :
    replicaReturnShellProjectionMass r (fun b => Option (C b))
        (fun b => replicaTargetWithZero (target b)) radius ψ =
      replicaReturnShellProjectionMass r C target radius ψ := by
  unfold replicaReturnShellProjectionMass
  apply Finset.sum_congr rfl
  intro b hb
  rw [replicaTargetProjectionMass_withZero hr]

/-- **Return-shell pointwise incidence law.**  Capture by any target in any
shell forces one weighted complete-image reporter to cross the matched
replica threshold. -/
theorem completePureStateReturnShellCapture_subset_projectionMass
    {X B α : Type*} [Fintype B] [Fintype α]
    {r : ℕ} (_hr : 0 < r)
    (C : B → Type*) (target : ∀ b, C b → α → ℂ)
    (state : X → α → ℂ)
    (radius : B → ℝ) (hradius : ∀ b, 0 ≤ radius b)
    (htarget : ∀ b c,
      ‖WithLp.toLp 2 (target b c)‖ ^ 2 ≤ radius b)
    (threshold : ℝ) (hthreshold : 0 ≤ threshold) :
    {x | ∃ b, ∃ c,
      threshold ≤ finitePureStateFidelity (state x) (target b c)} ⊆
      {x | threshold ^ r ≤
        replicaReturnShellProjectionMass r C target radius (state x)} := by
  intro x hx
  rcases hx with ⟨b, c, hc⟩
  have hnorm :
      ‖finitePureTensorPowerEuclidean r (target b c)‖ ^ 2 ≤
        radius b ^ r :=
    norm_sq_finitePureTensorPowerEuclidean_le_radius_pow
      r (target b c) (htarget b c)
  have hqnonneg :
      0 ≤ replicaTargetProjectionMass r (target b) (state x) :=
    sq_nonneg _
  calc
    threshold ^ r ≤
        finitePureStateFidelity (state x) (target b c) ^ r :=
      pow_le_pow_left₀ hthreshold hc r
    _ ≤ replicaTargetProjectionMass r (target b) (state x) *
          ‖finitePureTensorPowerEuclidean r (target b c)‖ ^ 2 :=
      finitePureStateFidelity_pow_le_replicaTargetProjectionMass_mul_norm_sq
        r (target b) (state x) c
    _ ≤ radius b ^ r *
          replicaTargetProjectionMass r (target b) (state x) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hnorm hqnonneg
    _ ≤ replicaReturnShellProjectionMass r C target radius (state x) := by
      unfold replicaReturnShellProjectionMass
      let f : B → ℝ := fun j => radius j ^ r *
        replicaTargetProjectionMass r (target j) (state x)
      change f b ≤ ∑ j, f j
      apply le_sum_univ_of_nonneg f
      intro j
      exact mul_nonneg (pow_nonneg (hradius j) r) (sq_nonneg _)

/-- **Quenched return-shell coarea bound.**  The complete approximate-target
event is bounded by one shell-weighted replica moment.  Integration remains on
the source, retaining every fibre sheet; each target shell enters only through
its occupied replica span and its post-return radius. -/
theorem measure_completePureStateReturnShellCapture_le_projectionMoment
    {X B α : Type*} [MeasurableSpace X] [Fintype B] [Fintype α]
    (μ : Measure X) [IsFiniteMeasure μ]
    {r : ℕ} (hr : 0 < r)
    (C : B → Type*) (target : ∀ b, C b → α → ℂ)
    (state : X → α → ℂ)
    (radius : B → ℝ) (hradius : ∀ b, 0 ≤ radius b)
    (htarget : ∀ b c,
      ‖WithLp.toLp 2 (target b c)‖ ^ 2 ≤ radius b)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (hint : Integrable
      (fun x => replicaReturnShellProjectionMass
        r C target radius (state x)) μ) :
    μ.real {x | ∃ b, ∃ c,
      threshold ≤ finitePureStateFidelity (state x) (target b c)} ≤
      (∫ x, replicaReturnShellProjectionMass
        r C target radius (state x) ∂μ) / threshold ^ r := by
  let q : X → ℝ := fun x => replicaReturnShellProjectionMass
    r C target radius (state x)
  let E : Set X := {x | ∃ b, ∃ c,
    threshold ≤ finitePureStateFidelity (state x) (target b c)}
  let Q : Set X := {x | threshold ^ r ≤ q x}
  have hEQ : E ⊆ Q :=
    completePureStateReturnShellCapture_subset_projectionMass
      hr C target state radius hradius htarget threshold hthreshold.le
  have hmeas : μ.real E ≤ μ.real Q := measureReal_mono hEQ
  have hqnonneg : 0 ≤ᵐ[μ] q :=
    Filter.Eventually.of_forall fun x =>
      replicaReturnShellProjectionMass_nonneg
        r C target hradius (state x)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    hqnonneg hint (threshold ^ r)
  have hprod : μ.real E * threshold ^ r ≤ ∫ x, q x ∂μ := by
    calc
      μ.real E * threshold ^ r ≤ μ.real Q * threshold ^ r := by
        gcongr
      _ = threshold ^ r * μ.real Q := mul_comm _ _
      _ ≤ ∫ x, q x ∂μ := hmarkov
  apply (le_div_iff₀' (pow_pos hthreshold r)).2
  simpa [E, q, mul_comm] using hprod

end

end GaloisForLFunctions.HTGeometry

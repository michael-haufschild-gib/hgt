import GaloisForLFunctions.HTGeometry.ClockFlatFrameCovariance

/-!
# The characteristic form of the clock equation in two dimensions

In the null frame `ξ = x⁰ + x¹`, `η = x⁰ - x¹` of two-dimensional Minkowski space both frame
covectors are null, so the frame-covariance formula leaves only the mixed second derivatives:

`□(u ∘ F)(x) = -2 · ((∂₁∂₀u) + (∂₀∂₁u))(F x)`.

Consequently the clock equation `□U + VU = 0` is, in null coordinates, the characteristic equation

`(∂₁∂₀u + ∂₀∂₁u)(F x) = ½ V(x) · u(F x)`,

which is the Goursat problem solved by Riemann's method. This file records the reduction: a solution
of the characteristic equation nonvanishing at a null point yields a clock probe nonvanishing at the
corresponding event, and hence determines the potential there.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

open scoped ContDiff

/-! ## The null frame -/

/-- Signature of two-dimensional Minkowski space. -/
noncomputable def nullEps : Fin (1 + 1) → ℝ := fun i => if (i : ℕ) = 0 then -1 else 1

theorem nullEps_ne_zero : ∀ i, nullEps i ≠ 0 := by
  intro i
  rw [nullEps]
  by_cases h : (i : ℕ) = 0 <;> simp [h]

theorem nullEps_zero : nullEps 0 = -1 := by simp [nullEps]

theorem nullEps_one : nullEps 1 = 1 := by simp [nullEps]

/-- The two null covectors `dξ = dx⁰ + dx¹` and `dη = dx⁰ - dx¹`. -/
noncomputable def nullCovectors : Fin (1 + 1) → (Fin (1 + 1) → ℝ) := fun k =>
  if k = 0 then (fun i => if i = 0 then 1 else if i = 1 then 1 else 0)
  else fun i => if i = 0 then 1 else if i = 1 then -1 else 0

theorem fin_zero_ne_one : (0 : Fin (1 + 1)) ≠ 1 := by simp

theorem nullCovectors_zero :
    nullCovectors 0 = fun i => if i = 0 then (1 : ℝ) else if i = 1 then 1 else 0 :=
  if_pos rfl

theorem nullCovectors_one :
    nullCovectors 1 = fun i => if i = 0 then (1 : ℝ) else if i = 1 then -1 else 0 :=
  if_neg (Ne.symm fin_zero_ne_one)

theorem covectorPairing_null_zero_zero :
    covectorPairing nullEps (nullCovectors 0) (nullCovectors 0) = 0 := by
  rw [nullCovectors_zero, covectorPairing_twoIndex _ fin_zero_ne_one, nullEps_zero, nullEps_one]
  norm_num

theorem covectorPairing_null_one_one :
    covectorPairing nullEps (nullCovectors 1) (nullCovectors 1) = 0 := by
  rw [nullCovectors_one, covectorPairing_twoIndex _ fin_zero_ne_one, nullEps_zero, nullEps_one]
  norm_num

theorem covectorPairing_null_zero_one :
    covectorPairing nullEps (nullCovectors 0) (nullCovectors 1) = -2 := by
  rw [nullCovectors_zero, nullCovectors_one, covectorPairing_twoIndex _ fin_zero_ne_one,
    nullEps_zero, nullEps_one]
  norm_num

theorem covectorPairing_null_one_zero :
    covectorPairing nullEps (nullCovectors 1) (nullCovectors 0) = -2 := by
  rw [nullCovectors_zero, nullCovectors_one, covectorPairing_twoIndex _ fin_zero_ne_one,
    nullEps_zero, nullEps_one]
  norm_num

/-- The null coordinates of an event. -/
noncomputable def nullFrame : (Fin (1 + 1) → ℝ) → (Fin (1 + 1) → ℝ) := frameMap nullCovectors

theorem nullFrame_zero (x : Fin (1 + 1) → ℝ) : nullFrame x 0 = x 0 + x 1 := by
  rw [nullFrame, frameMap, covectorPhase, nullCovectors_zero, Fin.sum_univ_two]
  norm_num [fin_zero_ne_one, Ne.symm fin_zero_ne_one]

theorem nullFrame_one (x : Fin (1 + 1) → ℝ) : nullFrame x 1 = x 0 - x 1 := by
  rw [nullFrame, frameMap, covectorPhase, nullCovectors_one, Fin.sum_univ_two]
  norm_num [fin_zero_ne_one, Ne.symm fin_zero_ne_one]
  ring

/-- **Every null point is the null coordinate of an event.** -/
theorem exists_event_of_nullPoint (p : Fin (1 + 1) → ℝ) :
    ∃ x : Fin (1 + 1) → ℝ, nullFrame x 0 = p 0 ∧ nullFrame x 1 = p 1 := by
  refine ⟨fun i => if i = 0 then (p 0 + p 1) / 2 else (p 0 - p 1) / 2, ?_, ?_⟩
  · rw [nullFrame_zero]
    norm_num [fin_zero_ne_one, Ne.symm fin_zero_ne_one]
    ring
  · rw [nullFrame_one]
    norm_num [fin_zero_ne_one, Ne.symm fin_zero_ne_one]
    ring

/-! ## The characteristic form -/

/-- **The two-dimensional clock operator in null coordinates.** Both frame covectors are null, so
only the mixed second derivatives survive. -/
theorem dalembert_nullFrame {u : (Fin (1 + 1) → ℝ) → ℝ} {x : Fin (1 + 1) → ℝ}
    {W : Set (Fin (1 + 1) → ℝ)} (hW : IsOpen W) (hFx : nullFrame x ∈ W)
    (hu : ∀ z ∈ W, DifferentiableAt ℝ u z)
    (hu2 : ∀ k, ∀ z ∈ W, DifferentiableAt ℝ (coordPartial k u) z) :
    (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart.dalembert
        (fun y => u (nullFrame y)) x
      = -2 * (coordPartial 1 (coordPartial 0 u) (nullFrame x)
          + coordPartial 0 (coordPartial 1 u) (nullFrame x)) := by
  rw [nullFrame] at hFx ⊢
  rw [dalembert_comp_frame nullEps nullEps_ne_zero nullCovectors hW hFx hu hu2,
    Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two,
    covectorPairing_null_zero_zero, covectorPairing_null_zero_one,
    covectorPairing_null_one_zero, covectorPairing_null_one_one]
  ring

/-- **A characteristic solution is a clock probe.** -/
theorem solvesPotentialWaveAt_of_characteristic {V : (Fin (1 + 1) → ℝ) → ℝ}
    {u : (Fin (1 + 1) → ℝ) → ℝ} {x : Fin (1 + 1) → ℝ}
    {W : Set (Fin (1 + 1) → ℝ)} (hW : IsOpen W) (hFx : nullFrame x ∈ W)
    (hu : ∀ z ∈ W, DifferentiableAt ℝ u z)
    (hu2 : ∀ k, ∀ z ∈ W, DifferentiableAt ℝ (coordPartial k u) z)
    (hchar : coordPartial 1 (coordPartial 0 u) (nullFrame x)
        + coordPartial 0 (coordPartial 1 u) (nullFrame x)
      = V x * u (nullFrame x) / 2) :
    SolvesPotentialWaveAt
      (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart.dalembert V
      (fun y => u (nullFrame y)) x := by
  show (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart.dalembert
      (fun y => u (nullFrame y)) x + V x * u (nullFrame x) = 0
  rw [dalembert_nullFrame hW hFx hu hu2, hchar]
  ring

/-- **The two-dimensional inverse step reduces to the Goursat problem.** A family of characteristic
solutions without a common zero determines the potential. -/
theorem potential_eq_of_characteristic_family {V other : (Fin (1 + 1) → ℝ) → ℝ}
    (hfamily : ∀ x : Fin (1 + 1) → ℝ, ∃ (u : (Fin (1 + 1) → ℝ) → ℝ)
      (W : Set (Fin (1 + 1) → ℝ)), IsOpen W ∧ nullFrame x ∈ W ∧
      (∀ z ∈ W, DifferentiableAt ℝ u z) ∧
      (∀ k, ∀ z ∈ W, DifferentiableAt ℝ (coordPartial k u) z) ∧
      (coordPartial 1 (coordPartial 0 u) (nullFrame x)
          + coordPartial 0 (coordPartial 1 u) (nullFrame x)
        = V x * u (nullFrame x) / 2) ∧
      u (nullFrame x) ≠ 0)
    (hother : ∀ (x : Fin (1 + 1) → ℝ) (u : (Fin (1 + 1) → ℝ) → ℝ),
      SolvesPotentialWaveAt
        (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart.dalembert V u x →
      SolvesPotentialWaveAt
        (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart.dalembert other u x) :
    other = V := by
  funext x
  obtain ⟨u, W, hW, hFx, hu, hu2, hchar, hne⟩ := hfamily x
  have hprobe := solvesPotentialWaveAt_of_characteristic hW hFx hu hu2 hchar
  exact potential_eq_of_solvesPotentialWaveAt (hother x _ hprobe) hprobe hne

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.ClockNullFrameReduction

/-!
# The characteristic reduction is an equivalence

The null frame of two-dimensional Minkowski space is invertible, with inverse
`x⁰ = (ξ+η)/2`, `x¹ = (ξ-η)/2`. Transporting a clock probe through the inverse turns it into a
solution of the characteristic equation, so the reduction of the previous file is not merely
sufficient but exact: clock probes at an event and characteristic solutions at the corresponding
null point are the same data.

That pins the remaining open input of the two-dimensional inverse step precisely: it is the Goursat
problem and nothing weaker.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

open scoped ContDiff

theorem fin_two_ext {f g : Fin (1 + 1) → ℝ} (h0 : f 0 = g 0) (h1 : f 1 = g 1) : f = g := by
  funext k
  fin_cases k
  · exact h0
  · exact h1

/-- The covectors of the inverse null frame. -/
noncomputable def invNullCovectors : Fin (1 + 1) → (Fin (1 + 1) → ℝ) := fun k =>
  if k = 0 then (fun i => if i = 0 then 1 / 2 else if i = 1 then 1 / 2 else 0)
  else fun i => if i = 0 then 1 / 2 else if i = 1 then -(1 / 2) else 0

theorem invNullCovectors_zero :
    invNullCovectors 0 = fun i => if i = 0 then (1 / 2 : ℝ) else if i = 1 then 1 / 2 else 0 :=
  if_pos rfl

theorem invNullCovectors_one :
    invNullCovectors 1
      = fun i => if i = 0 then (1 / 2 : ℝ) else if i = 1 then -(1 / 2) else 0 :=
  if_neg (Ne.symm fin_zero_ne_one)

/-- The event with prescribed null coordinates. -/
noncomputable def invNullFrame : (Fin (1 + 1) → ℝ) → (Fin (1 + 1) → ℝ) :=
  frameMap invNullCovectors

theorem invNullFrame_zero (p : Fin (1 + 1) → ℝ) :
    invNullFrame p 0 = (p 0 + p 1) / 2 := by
  rw [invNullFrame, frameMap, covectorPhase, invNullCovectors_zero, Fin.sum_univ_two]
  norm_num [fin_zero_ne_one, Ne.symm fin_zero_ne_one]
  ring

theorem invNullFrame_one (p : Fin (1 + 1) → ℝ) :
    invNullFrame p 1 = (p 0 - p 1) / 2 := by
  rw [invNullFrame, frameMap, covectorPhase, invNullCovectors_one, Fin.sum_univ_two]
  norm_num [fin_zero_ne_one, Ne.symm fin_zero_ne_one]
  ring

/-- **The null frame is invertible.** -/
theorem nullFrame_invNullFrame (p : Fin (1 + 1) → ℝ) : nullFrame (invNullFrame p) = p := by
  refine fin_two_ext ?_ ?_
  · rw [nullFrame_zero, invNullFrame_zero, invNullFrame_one]
    ring
  · rw [nullFrame_one, invNullFrame_zero, invNullFrame_one]
    ring

theorem invNullFrame_nullFrame (x : Fin (1 + 1) → ℝ) : invNullFrame (nullFrame x) = x := by
  refine fin_two_ext ?_ ?_
  · rw [invNullFrame_zero, nullFrame_zero, nullFrame_one]
    ring
  · rw [invNullFrame_one, nullFrame_zero, nullFrame_one]
    ring

theorem comp_invNullFrame_nullFrame (U : (Fin (1 + 1) → ℝ) → ℝ) :
    (fun y => U (invNullFrame (nullFrame y))) = U := by
  funext y
  rw [invNullFrame_nullFrame]

/-- **A clock probe is a characteristic solution.** The converse of the reduction, so the two
descriptions carry the same data. -/
theorem characteristic_of_solvesPotentialWaveAt {V U : (Fin (1 + 1) → ℝ) → ℝ}
    {x : Fin (1 + 1) → ℝ} {W : Set (Fin (1 + 1) → ℝ)} (hW : IsOpen W)
    (hFx : nullFrame x ∈ W)
    (hu : ∀ z ∈ W, DifferentiableAt ℝ (fun y => U (invNullFrame y)) z)
    (hu2 : ∀ k, ∀ z ∈ W,
      DifferentiableAt ℝ (coordPartial k (fun y => U (invNullFrame y))) z)
    (hsolve : SolvesPotentialWaveAt
      (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart.dalembert V U x) :
    coordPartial 1 (coordPartial 0 (fun y => U (invNullFrame y))) (nullFrame x)
        + coordPartial 0 (coordPartial 1 (fun y => U (invNullFrame y))) (nullFrame x)
      = V x * U x / 2 := by
  have hred := dalembert_nullFrame (u := fun y => U (invNullFrame y)) hW hFx hu hu2
  rw [comp_invNullFrame_nullFrame U] at hred
  have hs : (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart.dalembert U x
      + V x * U x = 0 := hsolve
  rw [hred] at hs
  linarith [hs]

/-- **The two-dimensional inverse step is exactly the Goursat problem.** Clock probes at an event
and characteristic solutions at the corresponding null point determine one another. -/
theorem solvesPotentialWaveAt_iff_characteristic {V U : (Fin (1 + 1) → ℝ) → ℝ}
    {x : Fin (1 + 1) → ℝ} {W : Set (Fin (1 + 1) → ℝ)} (hW : IsOpen W)
    (hFx : nullFrame x ∈ W)
    (hu : ∀ z ∈ W, DifferentiableAt ℝ (fun y => U (invNullFrame y)) z)
    (hu2 : ∀ k, ∀ z ∈ W,
      DifferentiableAt ℝ (coordPartial k (fun y => U (invNullFrame y))) z) :
    SolvesPotentialWaveAt
        (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart.dalembert V U x
      ↔ coordPartial 1 (coordPartial 0 (fun y => U (invNullFrame y))) (nullFrame x)
          + coordPartial 0 (coordPartial 1 (fun y => U (invNullFrame y))) (nullFrame x)
        = V x * U x / 2 := by
  constructor
  · intro h
    exact characteristic_of_solvesPotentialWaveAt hW hFx hu hu2 h
  · intro h
    have hprobe := solvesPotentialWaveAt_of_characteristic (V := V)
      (u := fun y => U (invNullFrame y)) hW hFx hu hu2
      (by rw [invNullFrame_nullFrame]; exact h)
    rw [comp_invNullFrame_nullFrame U] at hprobe
    exact hprobe

end GaloisForLFunctions.HTGeometry

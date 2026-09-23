import GaloisForLFunctions.HTGeometry.ExactCompletedC5SeamSlopeChamberNoGo

/-!
# Exact completed C5 slope: refined projective cone no-go

The refined projective chamber adds the corpus's parabolic clock walls and scale floor to the
source-positive chart.  These data still do not orient corrected C5 slope.  A ray with
`R = 10`, `z = s`, and `v = 131s/320` lies strictly between both refined clock walls, satisfies
exact source-positive reconstruction and the scale floor, and tends to the already-negative
`X = 100` seam.  Polynomial continuity therefore supplies a strict negative-slope witness inside
the open refined chamber.

RH chain killed: refined projective clock/scale inequalities alone cannot give corrected-slope
positivity, hence cannot by themselves force growth of exact completed C5 orientation, direct
fixed-action orientation at every centre, rank-four/Ptolemy assembly, CLG/TTF or Weil positivity,
and RH.  Positive survivor: any static C5 argument must couple the refined scale floor with the
independent physical gap cap; alternatively it must use actual orbit history.  This theorem does
not test that joint capped-refined chamber.
-/

open Complex Real

namespace HTGeometry

noncomputable section

/-- Projective refined-parabolic chamber, expressed in source-positive coordinates. -/
def StrictSourcePositiveRefinedParabolicClockCone
    (σ : ModularThetaSourcePositiveState → ℂ) : Prop :=
  ∃ R z v : ℝ,
    0 < R ∧ 0 < z ∧ z < 3 / 10 ∧
    (13 / 32 + z ^ (2 : ℕ) / 32 : ℝ) * z < v ∧
    v < (33 / 80 + z ^ (2 : ℕ) / 16 : ℝ) * z ∧
    (191 / 10 + (37 / 5 : ℝ) * z ^ (2 : ℕ)) < R ^ (2 : ℕ) ∧
    σ .U = (R * v : ℝ) ∧
    σ .B = (R * (z - v) / 3 : ℝ) ∧
    MvPolynomial.eval σ modularThetaSourcePositiveGap =
      (R ^ (2 : ℕ) * (1 - z ^ (2 : ℕ)) : ℝ) ∧
    0 < (σ .Q).re

/-- Ray through the `X=100` seam, with projective clock ratio strictly between the
refined parabolic walls. -/
def modularThetaSourcePositiveRefinedParabolicRayState (s : ℝ) :
    ModularThetaSourcePositiveState → ℂ
  | .U => ((131 / 32 : ℝ) * s : ℝ)
  | .B => ((63 / 32 : ℝ) * s : ℝ)
  | .Q => ((6 * ((63 / 32 : ℝ) * s) ^ (2 : ℕ) + 100 * (1 - s ^ (2 : ℕ)) - 6) / 16 : ℝ)

@[simp] theorem modularThetaSourcePositiveRefinedParabolicRayState_zero :
    modularThetaSourcePositiveRefinedParabolicRayState 0 =
      modularThetaSourcePositiveSeamState 100 := by
  funext i
  cases i <;>
    norm_num [modularThetaSourcePositiveRefinedParabolicRayState,
      modularThetaSourcePositiveSeamState]

theorem eval_modularThetaSourcePositiveGap_refinedParabolicRayState (s : ℝ) :
    MvPolynomial.eval (modularThetaSourcePositiveRefinedParabolicRayState s)
      modularThetaSourcePositiveGap = (100 * (1 - s ^ (2 : ℕ)) : ℝ) := by
  simp [modularThetaSourcePositiveRefinedParabolicRayState,
    modularThetaSourcePositiveGap]
  ring

theorem modularThetaSourcePositiveRefinedParabolicRayState_mem
    {s : ℝ} (hs : 0 < s) (hs3 : s < 3 / 10) :
    StrictSourcePositiveRefinedParabolicClockCone
      (modularThetaSourcePositiveRefinedParabolicRayState s) := by
  have hs2 : s ^ (2 : ℕ) < (1 / 10 : ℝ) := by nlinarith [sq_nonneg (s - 3 / 10)]
  have hlower : (13 / 32 + s ^ (2 : ℕ) / 32 : ℝ) < 131 / 320 := by
    nlinarith
  have hupper : (131 / 320 : ℝ) < 33 / 80 + s ^ (2 : ℕ) / 16 := by
    nlinarith [sq_nonneg s]
  refine ⟨10, s, (131 / 320 : ℝ) * s, by norm_num, hs, hs3,
    mul_lt_mul_of_pos_right hlower hs,
    mul_lt_mul_of_pos_right hupper hs, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · simp [modularThetaSourcePositiveRefinedParabolicRayState]
    ring
  · simp [modularThetaSourcePositiveRefinedParabolicRayState]
    ring
  · rw [eval_modularThetaSourcePositiveGap_refinedParabolicRayState]
    norm_num
  · simp [modularThetaSourcePositiveRefinedParabolicRayState]
    norm_num [pow_two, Complex.mul_re]
    nlinarith

private theorem continuousAt_mvPolynomial_eval_refinedParabolicRay
    (P : ModularThetaSourcePositivePolynomial) :
    ContinuousAt
      (fun s : ℝ => MvPolynomial.eval
        (modularThetaSourcePositiveRefinedParabolicRayState s) P) 0 := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ => a) 0)
  | add p q hp hq =>
      have hf : (fun s => MvPolynomial.eval
          (modularThetaSourcePositiveRefinedParabolicRayState s) (p + q)) =
          fun s => MvPolynomial.eval
            (modularThetaSourcePositiveRefinedParabolicRayState s) p +
            MvPolynomial.eval
              (modularThetaSourcePositiveRefinedParabolicRayState s) q := by
        funext s
        simp
      rw [hf]
      convert hp.add hq using 1
      ext s
      rfl
  | mul_X p i hp =>
      have hi : ContinuousAt
          (fun s : ℝ => modularThetaSourcePositiveRefinedParabolicRayState s i) 0 := by
        cases i <;>
          simp only [modularThetaSourcePositiveRefinedParabolicRayState] <;>
          fun_prop
      have hf : (fun s => MvPolynomial.eval
          (modularThetaSourcePositiveRefinedParabolicRayState s)
            (p * MvPolynomial.X i)) =
          fun s => MvPolynomial.eval
            (modularThetaSourcePositiveRefinedParabolicRayState s) p *
            modularThetaSourcePositiveRefinedParabolicRayState s i := by
        funext s
        simp
      rw [hf]
      convert hp.mul hi using 1
      ext s
      rfl

/-- Refined projective clocks, exact reconstruction, source positivity, and the scale floor still
contain a strictly negative corrected C5 slope. -/
theorem exists_refinedParabolicClockCone_c5ExactCompletedSeamSlope_neg :
    ∃ s : ℝ,
      StrictSourcePositiveRefinedParabolicClockCone
        (modularThetaSourcePositiveRefinedParabolicRayState s) ∧
      (MvPolynomial.eval (modularThetaSourcePositiveRefinedParabolicRayState s)
        modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial).re < 0 := by
  let F : ℝ → ℝ := fun s =>
    (MvPolynomial.eval (modularThetaSourcePositiveRefinedParabolicRayState s)
      modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial).re
  have hF : ContinuousAt F 0 := by
    dsimp only [F]
    convert Complex.continuous_re.continuousAt.comp
      (continuousAt_mvPolynomial_eval_refinedParabolicRay
        modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial) using 1
    funext s
    rfl
  have hF0 : F 0 < 0 := by
    dsimp only [F]
    rw [modularThetaSourcePositiveRefinedParabolicRayState_zero]
    exact eval_modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial_hundred_re_neg
  have hevent : {s : ℝ | F s < 0} ∈ nhds 0 :=
    hF.eventually (Iio_mem_nhds hF0)
  rcases Metric.mem_nhds_iff.mp hevent with ⟨ε, hε, hball⟩
  let s := min (ε / 2) (1 / 10 : ℝ)
  have hs : 0 < s := lt_min (by linarith) (by norm_num)
  have hs3 : s < 3 / 10 := by
    dsimp only [s]
    have := min_le_right (ε / 2) (1 / 10 : ℝ)
    linarith
  have hsball : s ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs]
    dsimp only [s]
    have := min_le_left (ε / 2) (1 / 10 : ℝ)
    linarith
  exact ⟨s, modularThetaSourcePositiveRefinedParabolicRayState_mem hs hs3,
    hball hsball⟩

/-- Exact route kill: refined projective clock and scale inequalities alone cannot provide a
nonnegative corrected C5 first-contact barrier. -/
theorem not_forall_refinedParabolicClockCone_c5ExactCompletedSeamSlope_nonneg :
    ¬ ∀ σ : ModularThetaSourcePositiveState → ℂ,
      StrictSourcePositiveRefinedParabolicClockCone σ →
      0 ≤ (MvPolynomial.eval σ
        modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial).re := by
  intro h
  obtain ⟨s, hs, hneg⟩ :=
    exists_refinedParabolicClockCone_c5ExactCompletedSeamSlope_neg
  exact (not_lt_of_ge (h _ hs)) hneg

end

end HTGeometry

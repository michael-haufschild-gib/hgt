import GaloisForLFunctions.HTGeometry.ExactCompletedC5SeamSlopeChamberNoGo

/-!
# Exact completed C5 adapted physical-cone no-go

The static first-contact proposal used positive source coordinates, reconstructed modular gap in
`(0,20)`, and the global lower-clock law `5B < U+3B`.  This file kills that proposal inside its
physical gap cap.

At algebraic seam gap `9`, the corrected exact-completed C5 slope is strictly negative.  A
continuous perturbation enters the strict positive-source lower-clock chamber while retaining gap
in `(0,20)`.  Hence those static inequalities cannot force the C5 slope sign.  A surviving static
route must additionally couple the refined projective clock and scale constraints; an alternative
is history-dependent incidence of the actual theta orbit.
-/

open Complex Real

namespace HTGeometry

noncomputable section

private theorem continuousAt_mvPolynomial_eval_curve_nine
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : MvPolynomial ι ℂ) (g : ι → ℝ → ℂ) (x : ℝ)
    (hg : ∀ j, ContinuousAt (g j) x) :
    ContinuousAt (fun s => MvPolynomial.eval (fun j => g j s) P) x := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ => a) x)
  | add p q hp hq =>
      have hf : (fun s => MvPolynomial.eval (fun j => g j s) (p + q)) =
          fun s => MvPolynomial.eval (fun j => g j s) p +
            MvPolynomial.eval (fun j => g j s) q := by
        funext s
        simp
      rw [hf]
      convert hp.add hq using 1
      ext s
      rfl
  | mul_X p i hp =>
      have hf : (fun s => MvPolynomial.eval (fun j => g j s)
          (p * MvPolynomial.X i)) =
          fun s => MvPolynomial.eval (fun j => g j s) p * g i s := by
        funext s
        simp
      rw [hf]
      convert hp.mul (hg i) using 1
      ext s
      rfl

/-- Exact seam-scale sign inside the physical gap cap. -/
theorem modularThetaC5FixedActionSeamPolynomialReal_nine_neg :
    modularThetaC5FixedActionSeamPolynomialReal 9 < 0 := by
  norm_num [modularThetaC5FixedActionSeamPolynomialReal]

/-- The exact corrected-C5 seam separator has a transition wall strictly inside physical cap. -/
theorem exists_modularThetaC5FixedActionSeam_transition_wall :
    ∃ X ∈ Set.Ioo (9 : ℝ) (191 / 10),
      modularThetaC5FixedActionSeamPolynomialReal X = 0 := by
  apply intermediate_value_Ioo (by norm_num)
  · unfold modularThetaC5FixedActionSeamPolynomialReal
    fun_prop
  · exact ⟨modularThetaC5FixedActionSeamPolynomialReal_nine_neg,
      modularThetaC5FixedActionSeamPolynomialReal_pos_of_mem_physicalChamber
        (by norm_num) (by norm_num)⟩

/-- Exact corrected C5 slope is negative at source-positive seam gap `9`. -/
theorem eval_modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial_nine_re_neg :
    (MvPolynomial.eval (modularThetaSourcePositiveSeamState 9)
      modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial).re < 0 := by
  rw [← modularThetaSourcePositiveChart_c5ExactCompletedSeamSlopePolynomial]
  have hstate : modularThetaSourcePositiveSeamState 9 =
      modularThetaSourcePositiveSeamState ((3 : ℝ) ^ (2 : ℕ)) := by norm_num
  rw [hstate, eval_modularThetaSourcePositiveChartPullback_seam]
  rw [← eval_modularThetaGeneralLyapunovPullback_seam,
    modularThetaGeneralLyapunov_c5ExactCompletedSeamSlopePolynomial]
  rw [eval_modularThetaODENormalizedC5ExactCompletedSeamSlopePolynomial_seam,
    eval_modularThetaODENormalizedC5FixedActionSeamPolynomial_seam,
    eval_modularThetaODENormalizedSourceJet_zero]
  norm_num [modularThetaODESeamState,
    modularThetaC5FixedActionSeamPolynomial]

private theorem eventually_eval_c5ExactCompletedSeamSlope_neg_of_tendsto_nine
    (g : ModularThetaSourcePositiveState → ℝ → ℂ)
    (hg : ∀ i, ContinuousAt (g i) 0)
    (hgzero : (fun i => g i 0) = modularThetaSourcePositiveSeamState 9) :
    ∀ᶠ ε in nhds (0 : ℝ),
      (MvPolynomial.eval (fun i => g i ε)
        modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial).re < 0 := by
  have hcomplex : ContinuousAt
      (fun ε => MvPolynomial.eval (fun i => g i ε)
        modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial) 0 :=
    continuousAt_mvPolynomial_eval_curve_nine
      modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial g 0 hg
  have hreal : ContinuousAt
      (fun ε => (MvPolynomial.eval (fun i => g i ε)
        modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial).re) 0 := by
    exact Complex.continuous_re.continuousAt.comp hcomplex
  have hzero :
      (MvPolynomial.eval (fun i => g i 0)
        modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial).re < 0 := by
    rw [hgzero]
    exact eval_modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial_nine_re_neg
  exact hreal.eventually (Iio_mem_nhds hzero)

/-- Perturb seam gap `9` inside the strict adapted physical cone. -/
def modularThetaSourcePositiveC5SlopePhysicalConePerturbation (ε : ℝ) :
    ModularThetaSourcePositiveState → ℂ
  | .U => 3 * ε
  | .B => ε
  | .Q => 3 / 16

/-- Physical cap, source positivity, and lower-clock constraint do not force corrected C5 slope. -/
theorem exists_strictSourcePositiveCappedLowerClockCone_eval_c5ExactCompletedSeamSlope_neg :
    ∃ v : ModularThetaSourcePositiveState → ℂ,
      (∀ i, 0 < (v i).re) ∧
      0 < (MvPolynomial.eval v modularThetaSourcePositiveGap).re ∧
      (MvPolynomial.eval v modularThetaSourcePositiveGap).re < 20 ∧
      5 * (v .B).re < (v .U).re + 3 * (v .B).re ∧
      (MvPolynomial.eval v
        modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial).re < 0 := by
  let g : ModularThetaSourcePositiveState → ℝ → ℂ :=
    fun i ε => modularThetaSourcePositiveC5SlopePhysicalConePerturbation ε i
  have hg : ∀ i, ContinuousAt (g i) 0 := by
    intro i
    cases i
    · simpa [g, modularThetaSourcePositiveC5SlopePhysicalConePerturbation] using
        Complex.continuous_ofReal.continuousAt.const_mul (3 : ℂ)
    · simpa [g, modularThetaSourcePositiveC5SlopePhysicalConePerturbation] using
        Complex.continuous_ofReal.continuousAt
    · simpa [g, modularThetaSourcePositiveC5SlopePhysicalConePerturbation] using
        (continuousAt_const : ContinuousAt (fun _ : ℝ => (3 / 16 : ℂ)) 0)
  have hgzero : (fun i => g i 0) = modularThetaSourcePositiveSeamState 9 := by
    funext i
    cases i <;>
      norm_num [g, modularThetaSourcePositiveC5SlopePhysicalConePerturbation,
        modularThetaSourcePositiveSeamState]
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp
    (eventually_eval_c5ExactCompletedSeamSlope_neg_of_tendsto_nine g hg hgzero)
  let ε : ℝ := min (δ / 2) 1
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hεone : ε ≤ 1 := min_le_right _ _
  have hεδ : ε < δ := by
    have hle : ε ≤ δ / 2 := min_le_left _ _
    linarith
  have hslope :
      (MvPolynomial.eval (fun i => g i ε)
        modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial).re < 0 := by
    apply hnear
    simpa [Real.dist_eq, abs_of_pos hε] using hεδ
  refine ⟨fun i => g i ε, ?_, ?_, ?_, ?_, hslope⟩
  · intro i
    cases i
    · simp [g, modularThetaSourcePositiveC5SlopePhysicalConePerturbation, hε]
    · simp [g, modularThetaSourcePositiveC5SlopePhysicalConePerturbation, hε]
    · simp [g, modularThetaSourcePositiveC5SlopePhysicalConePerturbation]
  · simp only [modularThetaSourcePositiveGap, map_sub, map_add, map_mul, map_pow,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    simp [g, modularThetaSourcePositiveC5SlopePhysicalConePerturbation]
    norm_num [pow_two, Complex.mul_re]
    ring_nf
    nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hεone)]
  · simp only [modularThetaSourcePositiveGap, map_sub, map_add, map_mul, map_pow,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    simp [g, modularThetaSourcePositiveC5SlopePhysicalConePerturbation]
    norm_num [pow_two, Complex.mul_re]
    ring_nf
    nlinarith [sq_nonneg ε]
  · simp [g, modularThetaSourcePositiveC5SlopePhysicalConePerturbation]
    linarith

/-- Exact route kill for static first-contact arguments using source positivity, lower clock, and
the physical gap cap alone. -/
theorem not_forall_strictSourcePositiveCappedLowerClockCone_c5ExactCompletedSeamSlope_pos :
    ¬ ∀ v : ModularThetaSourcePositiveState → ℂ,
      (∀ i, 0 < (v i).re) →
      0 < (MvPolynomial.eval v modularThetaSourcePositiveGap).re →
      (MvPolynomial.eval v modularThetaSourcePositiveGap).re < 20 →
      5 * (v .B).re < (v .U).re + 3 * (v .B).re →
      0 < (MvPolynomial.eval v
        modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial).re := by
  intro h
  obtain ⟨v, hv, hgap0, hgap20, hclock, hslope⟩ :=
    exists_strictSourcePositiveCappedLowerClockCone_eval_c5ExactCompletedSeamSlope_neg
  linarith [h v hv hgap0 hgap20 hclock]

end

end HTGeometry

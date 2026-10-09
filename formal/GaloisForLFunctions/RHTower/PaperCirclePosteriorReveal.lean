import GaloisForLFunctions.RHTower.PaperCircleAdaptiveBoundary

/-! # Evidence pays for the posterior's spatial information

The exact complete-reveal cost is the relative entropy of the actual history
posterior against the uniform grid law. Its value is expected log likelihood
minus log evidence, and likelihood at most one bounds it by negative log evidence.
Thus adaptive completion admits a budget without an explicit grid-dimension term.
-/

open Filter
open scoped BigOperators NNReal
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem paperCircleHistoryPosterior_log (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) (x : Grid M) :
    Real.log (paperCircleHistoryPosterior a M k s x) =
      -(M * Real.log 2) + Real.log (paperCircleHistoryLikelihood a M k s x) -
        Real.log (paperCircleHistoryEvidence a M k s) := by
  rw [paperCircleHistoryPosterior_apply,
    Real.log_div (mul_pos (Period.side_pos M)
      (paperCircleHistoryLikelihood_pos a M k s x)).ne'
      (paperCircleHistoryEvidence_pos a M k s).ne',
    Real.log_mul (Period.side_pos M).ne' (paperCircleHistoryLikelihood_pos a M k s x).ne',
    side_pow_two, Real.log_inv, Real.log_pow]

/-- The posterior entropy, average log likelihood and evidence satisfy an exact balance. -/
theorem paperCircleHistoryPosterior_entropy_balance (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    (paperCircleHistoryPosterior a M k s).entropy +
      (paperCircleHistoryPosterior a M k s).Ex
        (fun x => Real.log (paperCircleHistoryLikelihood a M k s x)) =
      M * Real.log 2 + Real.log (paperCircleHistoryEvidence a M k s) := by
  have h (x : Grid M) : -Real.log (paperCircleHistoryPosterior a M k s x) =
      M * Real.log 2 - Real.log (paperCircleHistoryLikelihood a M k s x) +
        Real.log (paperCircleHistoryEvidence a M k s) := by
    rw [paperCircleHistoryPosterior_log]
    ring
  unfold Law.entropy Law.crossE
  simp_rw [h, Law.Ex_add, Law.Ex_sub, Law.Ex_const]
  ring

/-- The uniform-prior relative entropy has a fully paid native likelihood formula. -/
theorem paperCircleHistoryPosterior_kl_uniform (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    (paperCircleHistoryPosterior a M k s).kl (Law.uniform (Grid M)) =
      (paperCircleHistoryPosterior a M k s).Ex
        (fun x => Real.log (paperCircleHistoryLikelihood a M k s x)) -
      Real.log (paperCircleHistoryEvidence a M k s) := by
  have h : (paperCircleHistoryPosterior a M k s).crossE (Law.uniform (Grid M)) =
      M * Real.log 2 := by
    simp only [Law.crossE, uniform_side, side_pow_two, Real.log_inv, Real.log_pow,
      neg_neg, Law.Ex_const]
  rw [Law.kl, h]
  linarith [paperCircleHistoryPosterior_entropy_balance a M k s]

theorem paperCircleHistoryPosterior_kl_uniform_bounds (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    0 ≤ (paperCircleHistoryPosterior a M k s).kl (Law.uniform (Grid M)) ∧
      (paperCircleHistoryPosterior a M k s).kl (Law.uniform (Grid M)) ≤
        -Real.log (paperCircleHistoryEvidence a M k s) := by
  constructor
  · apply Law.kl_nonneg
    intro x _
    rw [uniform_side]
    exact Period.side_pos M
  · have h : (paperCircleHistoryPosterior a M k s).Ex
        (fun x => Real.log (paperCircleHistoryLikelihood a M k s x)) ≤ 0 := by
      calc
        _ ≤ (paperCircleHistoryPosterior a M k s).Ex (fun _ => 0) :=
          Law.Ex_mono _ (fun x => Real.log_nonpos
            (paperCircleHistoryLikelihood_pos a M k s x).le
            (paperCircleHistoryLikelihood_le_one a M k s x))
        _ = 0 := Law.Ex_const _ _
    rw [paperCircleHistoryPosterior_kl_uniform]
    linarith

/-- The complete spatial reveal measures exactly the information gained from the history. -/
theorem paperCircleHistoryFullReveal_kl (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    (paperCircleHistoryPosterior a M k s).Ex
      (fun x => (((paperCircleHistoryFullReveal a M k s).read x).map (Wire.due 0)).sum) =
      (paperCircleHistoryPosterior a M k s).kl (Law.uniform (Grid M)) := by
  rw [paperCircleHistoryFullReveal_entropy, paperCircleHistoryPosterior_kl_uniform]
  linarith [paperCircleHistoryPosterior_entropy_balance a M k s]

theorem paperCircleHistoryFullReveal_evidence_le (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    (paperCircleHistoryPosterior a M k s).Ex
      (fun x => (((paperCircleHistoryFullReveal a M k s).read x).map (Wire.due 0)).sum) ≤
      -Real.log (paperCircleHistoryEvidence a M k s) := by
  rw [paperCircleHistoryFullReveal_kl]
  exact (paperCircleHistoryPosterior_kl_uniform_bounds a M k s).2

/-- Evidence and the adaptive membership budget pay for complete spatial resolution. -/
theorem paperCircleHistory_certified_evidence_boundary_exists (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) (throughCold : Bool) :
    ∀ᶠ j : ℕ in atTop, ∃ road : Road j M (paperCircleHistoryBegin a M k s),
      PaperCircleHistoryBoundaryCertificate a M k s j road ∧
      (paperCircleHistoryPosterior a M k s).Ex
        (fun x => (((Wire.tape road).read x).map (Wire.due 0)).sum) ≤
        -Real.log (paperCircleHistoryEvidence a M k s) + Road.limitC * Thermal.H j := by
  filter_upwards [paperCircleHistory_certified_boundary_exists a M k s throughCold]
    with j hj
  obtain ⟨road, hc⟩ := hj
  refine ⟨road, hc, ?_⟩
  rw [hc.entropy_balance]
  have h := paperCircleHistoryFullReveal_evidence_le a M k s
  rw [paperCircleHistoryFullReveal_entropy] at h
  exact add_le_add h hc.roadCertificate.membership_mean

end
end RHTower

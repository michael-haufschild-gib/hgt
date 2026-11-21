import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BranchEvaluation
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Coordinate derivatives on analytic charts -/
open Filter Topology Set Metric
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
variable {n : ℕ}
private abbrev Param (n : ℕ) := Fin n → ℂ

private theorem line_hasDerivAt (x : Param n) (i : Fin n) :
    HasDerivAt (coordLine x i) (Pi.single i 1) 0 := by
  apply hasDerivAt_pi.mpr
  intro j
  by_cases hj : j=i
  · subst j
    simpa [coordLine] using (hasDerivAt_id (0:ℂ)).const_add (x i)
  · simpa [coordLine,hj,Pi.single_apply,Ne.symm hj] using (hasDerivAt_const (0:ℂ) (x j))

theorem coordLine_tendsto (x : Param n) (i : Fin n) : Tendsto (coordLine x i) (𝓝 0) (𝓝 x) := by
  simpa only [coordLine_zero] using (line_hasDerivAt x i).continuousAt.tendsto

theorem hasDerivAt_mixed_line {F : Param n → ℂ} {x : Param n} (h : DifferentiableAt ℂ F x) (i : Fin n) :
    HasDerivAt (fun t => F (coordLine x i t)) (fderiv ℂ F x (Pi.single i 1)) 0 := by
  have hf : HasFDerivAt F (fderiv ℂ F x) (coordLine x i 0) := by simpa using h.hasFDerivAt
  exact hf.comp_hasDerivAt 0 (line_hasDerivAt x i)

theorem mixed_analyticAt {F : Param n → ℂ} {x : Param n} (hf : AnalyticAt ℂ F x) (w : List (Fin n)) :
    AnalyticAt ℂ (mixed w F) x := by
  induction w with
  | nil => exact hf
  | cons i w ih =>
    let A := ContinuousLinearMap.apply ℂ ℂ (Pi.single i (1:ℂ) : Param n)
    apply ((A.analyticAt _).comp ih.fderiv).congr
    filter_upwards [ih.eventually_analyticAt] with y hy
    exact (hasDerivAt_mixed_line hy.differentiableAt i).deriv.symm

theorem hasDerivAt_next_mixed {F : Param n → ℂ} {x : Param n} (hf : AnalyticAt ℂ F x)
    (i : Fin n) (w : List (Fin n)) :
    HasDerivAt (fun t => mixed w F (coordLine x i t)) (mixed (i::w) F x) 0 := by
  have h := hasDerivAt_mixed_line (mixed_analyticAt hf w).differentiableAt i
  exact h.differentiableAt.hasDerivAt

/-- Mixed derivatives of an anchored gap are the differences of the energy derivatives. -/
theorem mixed_sub {F G : Param n → ℂ} (w : List (Fin n)) {x : Param n}
    (hF : AnalyticAt ℂ F x) (hG : AnalyticAt ℂ G x) :
    mixed w (fun y => F y - G y) x = mixed w F x - mixed w G x := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih =>
    have he : (fun t => mixed w (fun y => F y - G y) (coordLine x i t)) =ᶠ[𝓝 0]
        fun t => mixed w F (coordLine x i t) - mixed w G (coordLine x i t) := by
      filter_upwards [coordLine_tendsto x i (hF.eventually_analyticAt.and hG.eventually_analyticAt)] with t ht
      exact ih ht.1 ht.2
    exact he.deriv_eq.trans ((hasDerivAt_next_mixed hF i w).sub (hasDerivAt_next_mixed hG i w)).deriv

/-- Vanishing in all coordinate directions kills the full Fréchet derivative. -/
theorem fderiv_eq_zero_of_coordinate {F : Param n → ℂ} {x : Param n}
    (h : ∀ i, fderiv ℂ F x (Pi.single i 1) = 0) : fderiv ℂ F x = 0 := by
  ext v
  change fderiv ℂ F x v = 0
  rw [← Finset.univ_sum_single v,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  have hs : Pi.single i (v i) = v i • (Pi.single i 1 : Param n) := by
    funext j
    by_cases hj : j=i
    · subst j; simp
    · simp [hj]
  rw [hs,map_smul,h i,smul_zero]

end
end GaloisForLFunctions.HTGeometry.SpectralJets

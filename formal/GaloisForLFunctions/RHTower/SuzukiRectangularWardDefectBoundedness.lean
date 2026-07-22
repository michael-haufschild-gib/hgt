import GaloisForLFunctions.RHTower.CCMRectangularScrewCurvature

/-!
# Suzuki rectangular Ward-defect boundedness criterion

The exact Suzuki source-to-Weil isometry is stronger than necessary for RH.  Fix a positive
rectangular width and subtract any nonnegative source energy from the corresponding Xi screw
curvature.  If this Ward defect is merely eventually bounded below on the logarithmic aperture
mesh, then the screw curvature itself is eventually bounded below, and the existing
multiplicity-exact rectangular completeness theorem proves RH.

Conversely, false RH forces this defect below every real level cofinally, for every nonnegative
source energy.  Thus a source Gram may carry an error; the true frontier is semiboundedness of
that error, not exact equality with the completed Weil form.

No RH premise, positivity conjecture, estimate, Xi-zero location, or numerical computation occurs.
-/

open Complex

namespace RHTower

noncomputable section

/-- Difference between the fixed-width Xi screw curvature and an arbitrary source energy. -/
def suzukiRectangularWardDefect
    (L : ℝ) (sourceEnergy : ℕ → ℝ) (n : ℕ) : ℝ :=
  (xiScrewWindowCurvature L (Real.log n)).re - sourceEnergy n

/-- **Semibounded Ward-defect RH connector.**  Exact source isometry is unnecessary: any
nonnegative source energy whose subtraction leaves an eventually lower-bounded defect already
forces RH. -/
theorem riemannHypothesis_of_suzukiRectangularWardDefect_eventually_bddBelow
    {L : ℝ} (hL : 0 < L) (sourceEnergy : ℕ → ℝ)
    (henergy : ∀ n, 0 ≤ sourceEnergy n)
    (hdefect : ∃ B : ℝ, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      L ≤ Real.log n / 2 →
      B ≤ suzukiRectangularWardDefect L sourceEnergy n) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_xiScrewWindowCurvature_logSample_eventually_bddBelow hL]
  obtain ⟨B, N0, hB⟩ := hdefect
  refine ⟨B, N0, fun n hn hLn => ?_⟩
  have h := hB n hn hLn
  rw [suzukiRectangularWardDefect] at h
  linarith [henergy n]

/-- A squared Hilbert-source norm supplies the required nonnegative energy automatically. -/
theorem riemannHypothesis_of_suzukiRectangularHilbertWardDefect_eventually_bddBelow
    {H : Type*} [SeminormedAddCommGroup H]
    {L : ℝ} (hL : 0 < L) (sourceVector : ℕ → H)
    (hdefect : ∃ B : ℝ, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      L ≤ Real.log n / 2 →
      B ≤ suzukiRectangularWardDefect L
        (fun k => ‖sourceVector k‖ ^ 2) n) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_suzukiRectangularWardDefect_eventually_bddBelow
    hL (fun k => ‖sourceVector k‖ ^ 2) (fun _ => sq_nonneg _) hdefect

/-- **Hostile-audit converse.**  Under false RH, subtracting any nonnegative source energy makes
the Ward defect cofinally unbounded below.  A positive source square can never conceal the
rectangular divisor obstruction inside a semibounded error. -/
theorem not_riemannHypothesis_implies_suzukiRectangularWardDefect_cofinally_unbounded_below
    {L : ℝ} (hL : 0 < L) (hRH : ¬RiemannHypothesis)
    (sourceEnergy : ℕ → ℝ) (henergy : ∀ n, 0 ≤ sourceEnergy n) :
    ∀ B : ℝ, ∀ N0 : ℕ, ∃ n : ℕ,
      N0 ≤ n ∧ L ≤ Real.log n / 2 ∧
      suzukiRectangularWardDefect L sourceEnergy n < B := by
  intro B N0
  obtain ⟨n, hn, hLn, hcurvature⟩ :=
    not_riemannHypothesis_implies_xiScrewWindowCurvature_logSample_cofinally_unbounded_below
      hL hRH B N0
  refine ⟨n, hn, hLn, ?_⟩
  rw [suzukiRectangularWardDefect]
  linarith [henergy n]

/-- False RH forces the Ward defect of every Hilbert-source square below every real level
cofinally on the exact arithmetic aperture mesh. -/
theorem not_riemannHypothesis_implies_suzukiRectangularHilbertWardDefect_cofinally_unbounded_below
    {H : Type*} [SeminormedAddCommGroup H]
    {L : ℝ} (hL : 0 < L) (hRH : ¬RiemannHypothesis)
    (sourceVector : ℕ → H) :
    ∀ B : ℝ, ∀ N0 : ℕ, ∃ n : ℕ,
      N0 ≤ n ∧ L ≤ Real.log n / 2 ∧
      suzukiRectangularWardDefect L
        (fun k => ‖sourceVector k‖ ^ 2) n < B := by
  exact not_riemannHypothesis_implies_suzukiRectangularWardDefect_cofinally_unbounded_below
    hL hRH (fun k => ‖sourceVector k‖ ^ 2) (fun _ => sq_nonneg _)

end

end RHTower

import GaloisForLFunctions.RHTower.DivisorStationaryKernelMellinSymbol

namespace RHTower

open GaloisForLFunctions.HTGeometry
open Filter Topology

noncomputable section

/-- Complex points on the critical line. -/
abbrev PositiveDiagonalCriticalLinePoint := {z : ℂ // z.re = (1 : ℝ) / 2}

/-- Analyticity of a positive diagonal completion through its critical abscissa
forces convergence of every critical logarithmic moment and hence strict
positivity of every reflected even mixed jet. -/
theorem positiveDiagonal_criticalBoundary_dichotomy
    (D : PositiveDiagonalCompletionDirichletData 1) :
    (¬ AnalyticAt ℂ D.series (1 : ℂ)) ∨
      ((∀ k : ℕ, Summable (gdTwistTerm D.positiveCoeff
          positiveDirichletLogFrequency 1 k)) ∧
        ∀ (z : PositiveDiagonalCriticalLinePoint) (m : ℕ),
          mixedAddIteratedDeriv m m D.series z.1 (star z.1) =
              ((gdMoment D.positiveCoeff positiveDirichletLogFrequency
                1 (2 * m) : ℝ) : ℂ) ∧
            0 < (mixedAddIteratedDeriv m m D.series z.1 (star z.1)).re) := by
  by_cases hA : AnalyticAt ℂ D.series (1 : ℂ)
  · right
    have hcontDiff : ContDiffAt ℂ 1 D.series (1 : ℂ) := hA.contDiffAt
    have hdiff_eventually : ∀ᶠ z in 𝓝 (1 : ℂ), DifferentiableAt ℂ D.series z := by
      filter_upwards [hcontDiff.eventually (by norm_num)] with z hz
      exact hz.differentiableAt (by norm_num)
    have hgood : {z : ℂ | DifferentiableAt ℂ D.series z} ∈ 𝓝 (1 : ℂ) :=
      hdiff_eventually
    obtain ⟨r, hrpos, hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hgood
    let h : ℝ := r / 4
    let R : NNReal := ⟨r / 2, by positivity⟩
    let sigma : ℝ := 1 - r / 8
    have hshiftpos : 0 < h := by simp [h, hrpos]
    have hball : Metric.closedBall (((1 + h : ℝ) : ℂ)) (R : ℝ) ⊆
        Metric.closedBall (1 : ℂ) r := by
      intro z hz
      rw [Metric.mem_closedBall] at hz ⊢
      change dist z (((1 + h : ℝ) : ℂ)) ≤ r / 2 at hz
      calc
        dist z (1 : ℂ) ≤ dist z (((1 + h : ℝ) : ℂ)) +
            dist (((1 + h : ℝ) : ℂ)) (1 : ℂ) := dist_triangle _ _ _
        _ ≤ r / 2 + h := by
          gcongr
          simp [h, abs_of_pos hrpos]
        _ ≤ r := by dsimp [h]; linarith
    have hdiff : DifferentiableOn ℂ D.series
        (Metric.closedBall (((1 + h : ℝ) : ℂ)) (R : ℝ)) := by
      intro z hz
      exact (hrsub (hball hz)).differentiableWithinAt
    have hsum_left : Summable (gdTwistTerm D.positiveCoeff
        positiveDirichletLogFrequency sigma 0) := by
      apply general_landau_summable_transfer D.positiveCoeff_nonneg
        positiveDirichletLogFrequency_nonneg D.summable_at hshiftpos hdiff
      · intro s hs
        rfl
      · change 1 + h - r / 2 < sigma
        dsimp [sigma, h]
        linarith
    let Dleft : PositiveDiagonalCompletionDirichletData sigma :=
      { coeff := D.coeff
        coeff_nonneg := D.coeff_nonneg
        summable_at := by
          exact hsum_left.congr (fun n => rfl)
        positiveAtom := D.positiveAtom }
    have hcoeff : Dleft.positiveCoeff = D.positiveCoeff := by
      funext n
      rfl
    have hseries : Dleft.series = D.series := by
      unfold PositiveDiagonalCompletionDirichletData.series
      rw [hcoeff]
    have hsigma : sigma < 1 := by simp [sigma]; linarith
    have hmoment : ∀ k : ℕ, Summable (gdTwistTerm D.positiveCoeff
        positiveDirichletLogFrequency 1 k) := by
      intro k
      have hk := summable_gdTwistTerm Dleft.positiveCoeff_nonneg
        positiveDirichletLogFrequency_nonneg Dleft.summable_at
        (show 0 < 1 - sigma by linarith) k
      rw [hcoeff] at hk
      simpa [sigma] using hk
    refine ⟨hmoment, ?_⟩
    intro z m
    let zleft : {w : ℂ // sigma < 2 * w.re} := ⟨z.1, by
      rw [z.2]
      linarith⟩
    have heq := Dleft.mixed_conj_even_eq_moment zleft m
    have hpos := Dleft.re_mixed_conj_even_pos zleft m
    rw [hseries] at heq hpos
    rw [hcoeff] at heq
    constructor
    · simpa [zleft, z.2] using heq
    · simpa [zleft] using hpos
  · exact Or.inl hA

/-- The explicit finite-critical-energy datum from the boundary counterexample
cannot be analytic at the critical abscissa. -/
theorem not_analyticAt_v21BoundaryCounterexample_series :
    ¬ AnalyticAt ℂ v21BoundaryCounterexampleData.series (1 : ℂ) := by
  intro hA
  rcases positiveDiagonal_criticalBoundary_dichotomy
      v21BoundaryCounterexampleData with hnot | hregular
  · exact hnot hA
  · exact not_summable_v21BoundaryCounterexample_secondMoment
      (hregular.1 2)

end

end RHTower

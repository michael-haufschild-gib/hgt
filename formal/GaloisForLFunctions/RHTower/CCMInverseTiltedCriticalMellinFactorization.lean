import GaloisForLFunctions.RHTower.CCMInverseTiltedDyadicPrimeTomography
import GaloisForLFunctions.RHTower.XiCriticalMellinSourceFactorization

/-!
# The inverse-tilted prime source is the regularized critical-Mellin defect

The complete-divisor inverse-tilted dyadic prime source and the polar--prime
critical-Mellin channel are two coordinates on the same meromorphic germ.  After filling the
zeta pole at one, the inverse-tilted source is a nonvanishing Mellin multiple of the regularized
critical-Mellin defect plus a holomorphic correction on the whole source half-plane.

Consequently source holomorphy to the right of its critical polar line is equivalent to
holomorphy of the regularized critical-Mellin defect on the translated half-plane.  Combined with
the complete Xi-divisor tomography theorem, this gives an exact critical-Mellin formulation of
the Riemann hypothesis.  The result is an unconditional value-relation bridge; it does not prove
the remaining holomorphy statement.
-/

open Complex Filter Function Set

namespace RHTower

noncomputable section

/-- The polar--prime critical-Mellin defect with the zeta pole at `u = 0` filled before taking the
logarithmic derivative. -/
def regularizedCriticalMellinDefect (u : ℂ) : ℂ :=
  1 / (u + 1) + logDeriv regularizedRiemannZeta (u + 1)

/-- On its original Laplace half-plane, the regularized defect is the previously defined
continued polar--prime critical-Mellin defect. -/
theorem regularizedCriticalMellinDefect_eq_continued
    {u : ℂ} (hu : 0 < u.re) :
    regularizedCriticalMellinDefect u =
      continuedCriticalMellinDefect u := by
  have hu0 : u ≠ 0 := by
    intro h
    rw [h] at hu
    norm_num at hu
  have ht : u + 1 ≠ 1 := by
    exact fun h => hu0 (by linear_combination h)
  have hz : riemannZeta (u + 1) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by
      rw [Complex.add_re]
      norm_num
      linarith)
  rw [regularizedCriticalMellinDefect,
    continuedCriticalMellinDefect,
    logDeriv_regularizedRiemannZeta_eq ht hz, zetaLogDeriv,
    logDeriv_apply]
  have hcoord : u + 1 - 1 = u := by ring
  rw [hcoord]
  ring

/-- The explicit correction separating the inverse-tilted prime source from the regularized
critical-Mellin defect. -/
def inverseTiltedCriticalMellinCorrection (s : ℂ) : ℂ :=
  dslope inverseTiltedDyadicPoleNumerator (3 / 2) s -
    2 * inverseTiltedDyadicMellin s / (s - 1 / 2) -
    2 * inverseTiltedDyadicErrorSeries s

/-- **Exact source factorization.**  The inverse-tilted source is the translated regularized
critical-Mellin defect multiplied by its zero-free Mellin aperture, plus the explicit
quadrature correction. -/
theorem inverseTiltedDyadicContinuedSource_eq_criticalMellinDefect_add_correction
    (s : ℂ) :
    inverseTiltedDyadicContinuedSource s =
      2 * inverseTiltedDyadicMellin s *
          regularizedCriticalMellinDefect (s - 3 / 2) +
        inverseTiltedCriticalMellinCorrection s := by
  rw [inverseTiltedDyadicContinuedSource,
    regularizedCriticalMellinDefect,
    inverseTiltedCriticalMellinCorrection]
  have hcoord : s - 3 / 2 + 1 = s - 1 / 2 := by ring
  rw [hcoord]
  ring

/-- The correction term is holomorphic on the entire source continuation half-plane. -/
theorem analyticAt_inverseTiltedCriticalMellinCorrection
    {s : ℂ} (hs : 1 / 2 < s.re) :
    AnalyticAt ℂ inverseTiltedCriticalMellinCorrection s := by
  have hdivided : AnalyticAt ℂ
      (dslope inverseTiltedDyadicPoleNumerator (3 / 2)) s :=
    (differentiable_inverseTiltedDyadicPoleDividedDifference.differentiableOn.analyticOnNhd
      isOpen_univ) s (Set.mem_univ s)
  have hM : AnalyticAt ℂ inverseTiltedDyadicMellin s :=
    (differentiable_inverseTiltedDyadicMellin.differentiableOn.analyticOnNhd
      isOpen_univ) s (Set.mem_univ s)
  have hden : AnalyticAt ℂ (fun z : ℂ => z - 1 / 2) s := by
    fun_prop
  have hden0 : s - 1 / 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.sub_re] at hre
    linarith
  have hquot : AnalyticAt ℂ
      (fun z : ℂ => 2 * inverseTiltedDyadicMellin z / (z - 1 / 2)) s :=
    (analyticAt_const.mul hM).div hden hden0
  have herr : AnalyticAt ℂ inverseTiltedDyadicErrorSeries s :=
    (differentiableOn_inverseTiltedDyadicErrorSeries_rightHalf.analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)) s hs
  exact hdivided.sub hquot |>.sub (analyticAt_const.mul herr)

/-- **Source--defect holomorphy equivalence.**  Holomorphy of the complete inverse-tilted prime
source to the right of its critical polar line is exactly holomorphy of the regularized
critical-Mellin defect on the translated half-plane. -/
theorem inverseTilted_source_analytic_rightOne_iff_regularizedCriticalMellin_analytic_rightNegHalf :
    (∀ s : ℂ, 1 < s.re →
        AnalyticAt ℂ inverseTiltedDyadicContinuedSource s) ↔
      (∀ u : ℂ, -1 / 2 < u.re →
        AnalyticAt ℂ regularizedCriticalMellinDefect u) := by
  constructor
  · intro hsource u hu
    let s : ℂ := u + 3 / 2
    have hs : 1 < s.re := by
      dsimp only [s]
      rw [Complex.add_re]
      norm_num
      linarith
    have hsHalf : 1 / 2 < s.re := by linarith
    have hsourceAt := hsource s hs
    have hcorrAt :=
      analyticAt_inverseTiltedCriticalMellinCorrection hsHalf
    have hMbase : AnalyticAt ℂ inverseTiltedDyadicMellin (u + 3 / 2) :=
      (differentiable_inverseTiltedDyadicMellin.differentiableOn.analyticOnNhd
        isOpen_univ) (u + 3 / 2) (Set.mem_univ _)
    have hshift : AnalyticAt ℂ (fun z : ℂ => z + 3 / 2) u := by
      fun_prop
    have hMcomp : AnalyticAt ℂ
        (fun z : ℂ => inverseTiltedDyadicMellin (z + 3 / 2)) u :=
      AnalyticAt.comp (f := fun z : ℂ => z + 3 / 2) (x := u) hMbase hshift
    have hM : AnalyticAt ℂ (fun z : ℂ =>
        2 * inverseTiltedDyadicMellin (z + 3 / 2)) u :=
      analyticAt_const.mul hMcomp
    have hM0 : 2 * inverseTiltedDyadicMellin (u + 3 / 2) ≠ 0 := by
      apply mul_ne_zero
      · norm_num
      · apply inverseTiltedDyadicMellin_ne_zero_of_re_pos
        rw [Complex.add_re]
        norm_num
        linarith
    have hsourceAt' : AnalyticAt ℂ inverseTiltedDyadicContinuedSource
        (u + 3 / 2) := by
      simpa only [s] using hsourceAt
    have hcorrAt' : AnalyticAt ℂ inverseTiltedCriticalMellinCorrection
        (u + 3 / 2) := by
      simpa only [s] using hcorrAt
    have hsourceShift : AnalyticAt ℂ
        (fun z : ℂ => inverseTiltedDyadicContinuedSource (z + 3 / 2)) u :=
      AnalyticAt.comp (f := fun z : ℂ => z + 3 / 2) (x := u)
        hsourceAt' hshift
    have hcorrShift : AnalyticAt ℂ
        (fun z : ℂ => inverseTiltedCriticalMellinCorrection (z + 3 / 2)) u :=
      AnalyticAt.comp (f := fun z : ℂ => z + 3 / 2) (x := u)
        hcorrAt' hshift
    have hquot := (hsourceShift.sub hcorrShift).div hM hM0
    have hMne : ∀ᶠ z in nhds u,
        2 * inverseTiltedDyadicMellin (z + 3 / 2) ≠ 0 :=
      hM.continuousAt.eventually_ne hM0
    have heq : (fun z : ℂ =>
        (inverseTiltedDyadicContinuedSource (z + 3 / 2) -
          inverseTiltedCriticalMellinCorrection (z + 3 / 2)) /
            (2 * inverseTiltedDyadicMellin (z + 3 / 2))) =ᶠ[nhds u]
        regularizedCriticalMellinDefect := by
      filter_upwards [hMne] with z hz
      rw [inverseTiltedDyadicContinuedSource_eq_criticalMellinDefect_add_correction]
      have hcoord : z + 3 / 2 - 3 / 2 = z := by ring
      rw [hcoord]
      apply (div_eq_iff hz).2
      ring
    exact hquot.congr heq
  · intro hdefect s hs
    have hsHalf : 1 / 2 < s.re := by linarith
    have hu : -1 / 2 < (s - 3 / 2).re := by
      norm_num [Complex.sub_re]
      linarith
    have hD := hdefect (s - 3 / 2) hu
    have hMbase : AnalyticAt ℂ inverseTiltedDyadicMellin s :=
      (differentiable_inverseTiltedDyadicMellin.differentiableOn.analyticOnNhd
        isOpen_univ) s (Set.mem_univ _)
    have hM : AnalyticAt ℂ (fun z : ℂ =>
        2 * inverseTiltedDyadicMellin z) s :=
      analyticAt_const.mul hMbase
    have hDshift : AnalyticAt ℂ
        (fun z : ℂ => regularizedCriticalMellinDefect (z - 3 / 2)) s :=
      AnalyticAt.comp (f := fun z : ℂ => z - 3 / 2) (x := s)
        hD (by fun_prop)
    have hcorr :=
      analyticAt_inverseTiltedCriticalMellinCorrection hsHalf
    have hsum : AnalyticAt ℂ
        (fun z : ℂ =>
          2 * inverseTiltedDyadicMellin z *
              regularizedCriticalMellinDefect (z - 3 / 2) +
            inverseTiltedCriticalMellinCorrection z) s :=
      (hM.mul hDshift).add hcorr
    apply hsum.congr
    filter_upwards with z
    exact
      (inverseTiltedDyadicContinuedSource_eq_criticalMellinDefect_add_correction z).symm

/-- **Critical-Mellin RH criterion.**  RH is exactly holomorphy of the regularized polar--prime
critical-Mellin defect on `Re u > -1/2`. -/
theorem riemannHypothesis_iff_regularizedCriticalMellinDefect_analytic_rightNegHalf :
    RiemannHypothesis ↔
      ∀ u : ℂ, -1 / 2 < u.re →
        AnalyticAt ℂ regularizedCriticalMellinDefect u := by
  rw [riemannHypothesis_iff_inverseTiltedDyadic_analytic_rightOne,
    inverseTilted_source_analytic_rightOne_iff_regularizedCriticalMellin_analytic_rightNegHalf]

/-- Bundled inverse-tilted/critical-Mellin factorization and RH criterion. -/
theorem inverseTiltedCriticalMellinFactorization_capstone :
    (∀ s : ℂ,
      inverseTiltedDyadicContinuedSource s =
        2 * inverseTiltedDyadicMellin s *
            regularizedCriticalMellinDefect (s - 3 / 2) +
          inverseTiltedCriticalMellinCorrection s) ∧
    (∀ s : ℂ, 1 / 2 < s.re →
      AnalyticAt ℂ inverseTiltedCriticalMellinCorrection s) ∧
    (RiemannHypothesis ↔
      ∀ u : ℂ, -1 / 2 < u.re →
        AnalyticAt ℂ regularizedCriticalMellinDefect u) := by
  exact ⟨inverseTiltedDyadicContinuedSource_eq_criticalMellinDefect_add_correction,
    fun _ hs => analyticAt_inverseTiltedCriticalMellinCorrection hs,
    riemannHypothesis_iff_regularizedCriticalMellinDefect_analytic_rightNegHalf⟩

end

end RHTower

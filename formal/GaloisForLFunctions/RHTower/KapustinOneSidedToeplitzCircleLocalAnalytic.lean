import GaloisForLFunctions.HTGeometry.SmirnovToeplitzCircleL1
import GaloisForLFunctions.RHTower.KapustinOneSidedToeplitzAnalyticSymbol
import GaloisForLFunctions.RHTower.Suzuki.SuzukiShiftedXiFiniteDiskFactor

open Complex Filter MeasureTheory Metric Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Circle representative of the fixed one-sided Kapustin Toeplitz symbol. -/
def kapustinOneSidedToeplitzCircleSymbol (z : Circle) : ℂ :=
  kapustinOneSidedToeplitzSymbol (circleCayleyInverse z)

/-- Complex analytic square of the circle symbol away from the Cayley point `1`. -/
def kapustinOneSidedToeplitzCircleAnalyticSquare (z : ℂ) : ℂ :=
  kapustinOneSidedToeplitzAnalyticSquare
    (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv z)

theorem measurable_kapustinOneSidedToeplitzCircleSymbol :
    Measurable kapustinOneSidedToeplitzCircleSymbol :=
  continuous_kapustinOneSidedToeplitzSymbol.measurable.comp
    measurable_circleCayleyInverse

@[simp] theorem kapustinOneSidedToeplitzCircleSymbol_circleCayley (x : ℝ) :
    kapustinOneSidedToeplitzCircleSymbol (circleCayley x) =
      kapustinOneSidedToeplitzSymbol x := by
  simp [kapustinOneSidedToeplitzCircleSymbol]

theorem norm_kapustinOneSidedToeplitzCircleSymbol (z : Circle) :
    ‖kapustinOneSidedToeplitzCircleSymbol z‖ = 1 := by
  exact norm_kapustinOneSidedToeplitzSymbol _

/-- At every finite Cayley boundary point, the circle symbol agrees a.e. on an arc with one
globally measurable analytic square-root coefficient. -/
theorem exists_localAnalytic_kapustinOneSidedToeplitzCircleSymbol_with_square (x₀ : ℝ) :
    ∃ (L : ℂ → ℂ) (r : ℝ), Measurable L ∧ 0 < r ∧
      AnalyticAt ℂ L (circleCayley x₀ : ℂ) ∧
      Filter.Eventually (fun z : Circle =>
        dist (z : ℂ) (circleCayley x₀ : ℂ) < 2 * r →
          kapustinOneSidedToeplitzCircleSymbol z = L z) (ae circleLebesgue) ∧
      ∀ᶠ z in nhds (circleCayley x₀ : ℂ),
        L z ^ (2 : ℕ) = kapustinOneSidedToeplitzCircleAnalyticSquare z := by
  obtain ⟨h, hhMeas, hhAnalytic, _hh₀, hhTrace, hhSquare⟩ :=
    exists_measurable_analyticAt_eventuallyEq_kapustinOneSidedToeplitzSymbol_with_square x₀
  let z₀ : ℂ := (circleCayley x₀ : ℂ)
  have hz₀ne : z₀ ≠ 1 := by
    intro hz
    have hz' : realCayley x₀ = 1 := by simpa [z₀] using hz
    rw [realCayley] at hz'
    field_simp [real_add_I_ne_zero x₀] at hz'
    have him := congrArg Complex.im hz'
    norm_num at him
  have hinv₀ : GaloisForLFunctions.RHTower.suzukiUpperCayleyInv z₀ = (x₀ : ℂ) := by
    simpa [z₀, realCayley, lineCayley] using
      (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_lineCayley (z := (x₀ : ℂ))
        (real_add_I_ne_zero x₀))
  let L : ℂ → ℂ := fun z =>
    h (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv z)
  have hInvMeas : Measurable GaloisForLFunctions.RHTower.suzukiUpperCayleyInv := by
    unfold GaloisForLFunctions.RHTower.suzukiUpperCayleyInv
    fun_prop
  have hLMeas : Measurable L := hhMeas.comp hInvMeas
  have hInvAnalytic : AnalyticAt ℂ
      GaloisForLFunctions.RHTower.suzukiUpperCayleyInv z₀ := by
    unfold GaloisForLFunctions.RHTower.suzukiUpperCayleyInv
    exact analyticAt_const.mul
      ((analyticAt_const.add analyticAt_id).div
        (analyticAt_const.sub analyticAt_id)
        (sub_ne_zero.mpr hz₀ne.symm))
  have hhAtInv : AnalyticAt ℂ h
      (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv z₀) := by
    simpa [hinv₀] using hhAnalytic
  have hLAnalytic : AnalyticAt ℂ L z₀ := hhAtInv.comp hInvAnalytic
  obtain ⟨ε, hε, hTraceBall⟩ := Metric.mem_nhds_iff.mp hhTrace
  have hInvContinuous : ContinuousAt
      GaloisForLFunctions.RHTower.suzukiUpperCayleyInv z₀ :=
    hInvAnalytic.continuousAt
  have hInvNear : ∀ᶠ z in nhds z₀,
      GaloisForLFunctions.RHTower.suzukiUpperCayleyInv z ∈ ball (x₀ : ℂ) ε := by
    apply hInvContinuous
    rw [hinv₀]
    exact ball_mem_nhds _ hε
  obtain ⟨δ, hδ, hInvBall⟩ := Metric.mem_nhds_iff.mp hInvNear
  let r := δ / 3
  have hr : 0 < r := by dsimp [r]; positivity
  have hline : (fun x : ℝ =>
      if dist (circleCayley x : ℂ) z₀ < 2 * r then
        kapustinOneSidedToeplitzCircleSymbol (circleCayley x) else 0) =ᵐ[volume]
      fun x : ℝ =>
        if dist (circleCayley x : ℂ) z₀ < 2 * r then
          L (circleCayley x : ℂ) else 0 := by
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : dist (circleCayley x : ℂ) z₀ < 2 * r
    · simp only [if_pos hx, kapustinOneSidedToeplitzCircleSymbol_circleCayley]
      have hxδ : (circleCayley x : ℂ) ∈ ball z₀ δ := by
        rw [mem_ball, circleCayley_coe]
        exact hx.trans (by dsimp [r]; linarith)
      have hxInv := hInvBall hxδ
      have hInvX : GaloisForLFunctions.RHTower.suzukiUpperCayleyInv
          (circleCayley x : ℂ) = (x : ℂ) := by
        simpa [circleCayley_coe, realCayley, lineCayley] using
          (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_lineCayley
            (z := (x : ℂ)) (real_add_I_ne_zero x))
      have hxε : (x : ℂ) ∈ ball (x₀ : ℂ) ε := by
        change GaloisForLFunctions.RHTower.suzukiUpperCayleyInv
          (circleCayley x : ℂ) ∈ ball (x₀ : ℂ) ε at hxInv
        rwa [hInvX] at hxInv
      have hxRealBall : x ∈ (ball x₀ ε : Set ℝ) := by
        rw [mem_ball, Real.dist_eq]
        rw [mem_ball, Complex.dist_eq] at hxε
        simpa [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hxε
      have hxTrace := hTraceBall hxRealBall
      change kapustinOneSidedToeplitzSymbol x =
        h (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv _)
      rw [hInvX]
      exact hxTrace.symm
    · have hx' : ¬ dist (realCayley x) z₀ < 2 * r := by
        simpa only [circleCayley_coe] using hx
      simp [hx']
  let f : Circle → ℂ := fun z =>
    if dist (z : ℂ) z₀ < 2 * r then
      kapustinOneSidedToeplitzCircleSymbol z else 0
  let g : Circle → ℂ := fun z =>
    if dist (z : ℂ) z₀ < 2 * r then L z else 0
  have hfMeas : Measurable f := by
    dsimp [f]
    exact Measurable.ite
      (measurableSet_lt (by fun_prop) measurable_const)
      measurable_kapustinOneSidedToeplitzCircleSymbol measurable_const
  have hgMeas : Measurable g := by
    dsimp [g]
    exact Measurable.ite
      (measurableSet_lt (by fun_prop) measurable_const)
      (hLMeas.comp (by fun_prop)) measurable_const
  have hcircle : f =ᵐ[circleLebesgue] g :=
    circle_eventuallyEq_of_line_eventuallyEq hfMeas hgMeas hline
  have hInvTendsto : Tendsto
      GaloisForLFunctions.RHTower.suzukiUpperCayleyInv (nhds z₀)
        (nhds (x₀ : ℂ)) := by
    rw [← hinv₀]
    exact hInvContinuous
  have hLsq : ∀ᶠ z in nhds z₀,
      L z ^ (2 : ℕ) = kapustinOneSidedToeplitzCircleAnalyticSquare z := by
    exact hInvTendsto.eventually hhSquare
  refine ⟨L, r, hLMeas, hr, ?_, ?_, ?_⟩
  · simpa [z₀] using hLAnalytic
  · filter_upwards [hcircle] with z hz
    intro hdist
    change (if dist (z : ℂ) z₀ < 2 * r then
        kapustinOneSidedToeplitzCircleSymbol z else 0) =
      if dist (z : ℂ) z₀ < 2 * r then L (z : ℂ) else 0 at hz
    rw [if_pos (by simpa [z₀] using hdist),
      if_pos (by simpa [z₀] using hdist)] at hz
    exact hz
  · simpa [z₀] using hLsq

/-- At every finite Cayley boundary point, the circle symbol agrees a.e. on an arc with one
globally measurable analytic coefficient. -/
theorem exists_localAnalytic_kapustinOneSidedToeplitzCircleSymbol (x₀ : ℝ) :
    ∃ (L : ℂ → ℂ) (r : ℝ), Measurable L ∧ 0 < r ∧
      AnalyticAt ℂ L (circleCayley x₀ : ℂ) ∧
      Filter.Eventually (fun z : Circle =>
        dist (z : ℂ) (circleCayley x₀ : ℂ) < 2 * r →
          kapustinOneSidedToeplitzCircleSymbol z = L z) (ae circleLebesgue) := by
  obtain ⟨L, r, hLMeas, hr, hLanalytic, htrace, _hsquare⟩ :=
    exists_localAnalytic_kapustinOneSidedToeplitzCircleSymbol_with_square x₀
  exact ⟨L, r, hLMeas, hr, hLanalytic, htrace⟩

end

end RHTower

import GaloisForLFunctions.RHTower.KapustinToeplitzAnalyticSymbol
import GaloisForLFunctions.RHTower.KapustinOneSidedToeplitzPhase
import GaloisForLFunctions.HTGeometry.MeasurableAnalyticGerm
import GaloisForLFunctions.HTGeometry.MeasurableAnalyticSquareRoot

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Analytic square of the one-sided Kapustin Toeplitz symbol near the real line. -/
def kapustinOneSidedToeplitzAnalyticSquare (z : ℂ) : ℂ :=
  kapustinToeplitzAnalyticSymbol z * ((z + I) / (z - I)) ^ 4

theorem kapustinOneSidedToeplitzAnalyticSquare_ofReal (x : ℝ) :
    kapustinOneSidedToeplitzAnalyticSquare (x : ℂ) =
      kapustinOneSidedToeplitzSymbol x ^ 2 := by
  rw [kapustinOneSidedToeplitzAnalyticSquare,
    kapustinToeplitzAnalyticSymbol_ofReal]
  have hcayley : ((x : ℂ) + I) / ((x : ℂ) - I) =
      (starRingEnd ℂ) (realCayley x) := by
    rw [realCayley]
    simp only [map_div₀, map_sub, map_add, conj_ofReal, conj_I]
    rw [sub_neg_eq_add, ← sub_eq_add_neg]
  rw [hcayley, ← map_pow,
    conj_realCayley_pow_four_eq_exp_neg_eight_arctan]
  rw [kapustinToeplitzSymbol, kapustinToeplitzPhase,
    kapustinOneSidedToeplitzSymbol, kapustinOneSidedToeplitzPhase,
    ← Complex.exp_add, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem analyticAt_kapustinOneSidedToeplitzAnalyticSquare_ofReal (x : ℝ) :
    AnalyticAt ℂ kapustinOneSidedToeplitzAnalyticSquare (x : ℂ) := by
  have hcayley : AnalyticAt ℂ (fun z : ℂ => (z + I) / (z - I)) (x : ℂ) := by
    apply (analyticAt_id.add analyticAt_const).div
      (analyticAt_id.sub analyticAt_const)
    intro hx
    have him := congrArg Complex.im hx
    norm_num at him
  exact (analyticAt_kapustinToeplitzAnalyticSymbol_ofReal x).mul
    (hcayley.pow 4)

theorem kapustinOneSidedToeplitzAnalyticSquare_ofReal_ne_zero (x : ℝ) :
    kapustinOneSidedToeplitzAnalyticSquare (x : ℂ) ≠ 0 := by
  rw [kapustinOneSidedToeplitzAnalyticSquare_ofReal]
  exact pow_ne_zero 2 (norm_ne_zero_iff.mp (by
    rw [norm_kapustinOneSidedToeplitzSymbol]
    norm_num))

theorem continuous_kapustinOneSidedToeplitzPhase :
    Continuous kapustinOneSidedToeplitzPhase := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (hasDerivAt_kapustinReciprocalGammaPhase x).continuousAt.sub
    ((continuous_const.mul Real.continuous_arctan).continuousAt)

theorem continuous_kapustinOneSidedToeplitzSymbol :
    Continuous kapustinOneSidedToeplitzSymbol := by
  unfold kapustinOneSidedToeplitzSymbol
  exact (((Complex.continuous_ofReal.comp
    continuous_kapustinOneSidedToeplitzPhase).mul continuous_const).cexp)

/-- The one-sided Kapustin symbol is the real trace of a measurable analytic germ at every point. -/
theorem exists_measurable_analyticAt_eventuallyEq_kapustinOneSidedToeplitzSymbol
    (x₀ : ℝ) :
    ∃ h : ℂ → ℂ, Measurable h ∧ AnalyticAt ℂ h (x₀ : ℂ) ∧
      h (x₀ : ℂ) = kapustinOneSidedToeplitzSymbol x₀ ∧
      (fun x : ℝ => h (x : ℂ)) =ᶠ[nhds x₀] kapustinOneSidedToeplitzSymbol := by
  obtain ⟨g, hgMeas, hgAnalytic, hgerm⟩ :=
    exists_measurable_eventuallyEq_of_analyticAt
      (analyticAt_kapustinOneSidedToeplitzAnalyticSquare_ofReal x₀)
  have hga : g (x₀ : ℂ) = kapustinOneSidedToeplitzSymbol x₀ ^ 2 := by
    rw [← kapustinOneSidedToeplitzAnalyticSquare_ofReal x₀]
    exact (hgerm.self_of_nhds).symm
  have hU₀ : kapustinOneSidedToeplitzSymbol x₀ ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [norm_kapustinOneSidedToeplitzSymbol]; norm_num)
  obtain ⟨h, hhMeas, hhAnalytic, hh₀, hhsq⟩ :=
    exists_measurable_analyticAt_sq_eq_of_value hgMeas hgAnalytic hga.symm hU₀
  refine ⟨h, hhMeas, hhAnalytic, hh₀, ?_⟩
  have hsqComplex : ∀ᶠ z in nhds (x₀ : ℂ),
      h z ^ 2 = kapustinOneSidedToeplitzAnalyticSquare z := by
    filter_upwards [hhsq, hgerm] with z hsq heq
    rw [hsq, ← heq]
  have hsqReal : ∀ᶠ x : ℝ in nhds x₀,
      h (x : ℂ) ^ 2 = kapustinOneSidedToeplitzSymbol x ^ 2 := by
    have hmap : Tendsto Complex.ofReal (nhds x₀) (nhds (x₀ : ℂ)) :=
      Complex.continuous_ofReal.continuousAt
    filter_upwards [hmap.eventually hsqComplex] with x hx
    simpa only [kapustinOneSidedToeplitzAnalyticSquare_ofReal] using hx
  have hhContinuous : ContinuousAt (fun x : ℝ => h (x : ℂ)) x₀ :=
    hhAnalytic.continuousAt.comp Complex.continuous_ofReal.continuousAt
  have hsumContinuous : ContinuousAt
      (fun x : ℝ => h (x : ℂ) + kapustinOneSidedToeplitzSymbol x) x₀ :=
    hhContinuous.add continuous_kapustinOneSidedToeplitzSymbol.continuousAt
  have hsum₀ : h (x₀ : ℂ) + kapustinOneSidedToeplitzSymbol x₀ ≠ 0 := by
    rw [hh₀]
    intro hzero
    have hmul : (2 : ℂ) * kapustinOneSidedToeplitzSymbol x₀ = 0 := by
      simpa [two_mul] using hzero
    exact hU₀ ((mul_eq_zero.mp hmul).resolve_left (by norm_num))
  have hsum : ∀ᶠ x : ℝ in nhds x₀,
      h (x : ℂ) + kapustinOneSidedToeplitzSymbol x ≠ 0 :=
    hsumContinuous.eventually_ne hsum₀
  filter_upwards [hsqReal, hsum] with x hsq hne
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp ?_).resolve_right hne
  calc
    (h (x : ℂ) - kapustinOneSidedToeplitzSymbol x) *
        (h (x : ℂ) + kapustinOneSidedToeplitzSymbol x) =
      h (x : ℂ) ^ 2 - kapustinOneSidedToeplitzSymbol x ^ 2 := by ring
    _ = 0 := by rw [hsq, sub_self]

end

end RHTower

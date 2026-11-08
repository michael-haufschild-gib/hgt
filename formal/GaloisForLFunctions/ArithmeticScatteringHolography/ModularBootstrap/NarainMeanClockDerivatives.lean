import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanClockDisk
import GaloisForLFunctions.HTGeometry.HolomorphicRealTaylor
import GaloisForLFunctions.RHTower.RealJetsOfHolomorphic

/-!
# Arithmetic saving for every derivative of the Narain clock

A uniform complex disk estimate and Cauchy bounds give one factorial rate and one threshold for all derivative orders. Restriction to the real axis identifies the literal physical remainder.
-/

open Complex RHTower Filter Topology
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Cauchy estimates preserve one arithmetic saving and one threshold for every clock derivative. -/
theorem exists_narainMeanClock_factorial_universal_vk_bound (Y Z : Height) :
    ∃ C L₀ : ℝ, 0 < C ∧
      ∀ L : ℝ, L₀ ≤ L → ∀ n : ℕ,
        ‖iteratedDeriv n (narainMeanClockSchwartz Y Z : ℝ → ℂ) L‖ ≤
          ((n.factorial : ℝ) * C / (Real.pi / 16) ^ n) * Real.exp (-(L * vkHadamardWidth L / 128)) := by
  obtain ⟨C, hC, hbound⟩ := exists_narainMeanClock_disk_universal_vk_bound Y Z
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp hbound
  refine ⟨C, L₀, hC, ?_⟩
  intro L hL n
  have hA : ∀ z ∈ Metric.ball (L : ℂ) (Real.pi / 8),
      AnalyticAt ℂ (narainMeanComplexClock Y Z) z := by
    intro z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have him : |z.im| < Real.pi / 8 := by
      have h := (Complex.abs_im_le_norm (z - (L : ℂ))).trans_lt hz
      simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using h
    exact analyticAt_narainMeanComplexClock Y Z
      (him.trans (by nlinarith only [Real.pi_pos]))
  have hdiff : DifferentiableOn ℂ (narainMeanComplexClock Y Z)
      (Metric.ball (L : ℂ) (Real.pi / 8)) :=
    fun z hz => (hA z hz).differentiableAt.differentiableWithinAt
  have hdc : DiffContOnCl ℂ (narainMeanComplexClock Y Z)
      (Metric.ball (L : ℂ) (Real.pi / 16)) :=
    hdiff.diffContOnCl_ball (Metric.closedBall_subset_ball (by nlinarith only [Real.pi_pos]))
  have hCauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (show 0 < Real.pi / 16 by positivity) hdc
    (fun z hz => hL₀ L hL z (Metric.sphere_subset_closedBall hz))
  have hreal : (narainMeanClockSchwartz Y Z : ℝ → ℂ) =
      fun x : ℝ => narainMeanComplexClock Y Z (x : ℂ) :=
    funext (fun x => (narainMeanComplexClock_ofReal Y Z x).symm)
  rw [hreal, GaloisForLFunctions.RHTower.iteratedDeriv_ofReal_comp hA n L
    (by simp only [sub_self, abs_zero]; positivity)]
  exact hCauchy.trans_eq (by ring)

/-- Every derivative of the literal normalized physical remainder has a common factorial arithmetic bound. -/
theorem narainScalarHeatAverage_clock_derivatives_universal_vk (Y Z : Height) :
    ∃ C L₀ : ℝ, 0 < C ∧
      ∀ L : ℝ, L₀ ≤ L → ∀ n : ℕ,
        ‖iteratedDeriv n (fun x : ℝ => (Real.exp (x / 2) : ℂ) *
          ((Real.exp (-x) : ℂ) * narainScalarHeatAverage Y Z (Real.exp (-x)) -
            (3 / (Real.pi : ℂ)) * (x : ℂ) - narainAverageConstant Y Z)) L‖ ≤
          ((n.factorial : ℝ) * C / (Real.pi / 16) ^ n) * Real.exp (-(L * vkHadamardWidth L / 128)) := by
  have hf : (narainMeanClockSchwartz Y Z : ℝ → ℂ) =
      fun x : ℝ => (Real.exp (x / 2) : ℂ) *
        ((Real.exp (-x) : ℂ) * narainScalarHeatAverage Y Z (Real.exp (-x)) -
          (3 / (Real.pi : ℂ)) * (x : ℂ) - narainAverageConstant Y Z) :=
    funext (narainMeanClockSchwartz_apply Y Z)
  simpa only [hf] using exists_narainMeanClock_factorial_universal_vk_bound Y Z

#print axioms exists_narainMeanClock_factorial_universal_vk_bound
#print axioms narainScalarHeatAverage_clock_derivatives_universal_vk
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

import GaloisForLFunctions.HTGeometry.PartialBoundaryApproximationForcesSmallValues
import GaloisForLFunctions.HTGeometry.RiemannZetaMeromorphic
import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheTailOfAReturnCarriesTheZero

/-!
# A partial zeta return transports a zero or creates a small value

Around a zeta zero, relative recurrence on a circle with one short arc removed has an
exact alternative: a zero in the translated disc, carried by every finite Euler tail,
or an exponentially small relative zeta value on the omitted arc.

This applies to each individual return and makes no assertion about the density or
existence of return heights.
-/

open Complex Metric Real Set
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

private theorem analyticOnNhd_zeta_translate_closedBall {c : ℂ} {R : ℝ}
    (hupper : c.re + R < 1) (τ : ℝ) :
    AnalyticOnNhd ℂ (fun z => riemannZeta (z + (τ : ℂ) * I)) (closedBall c R) := by
  intro z hz
  have hre : (z + (τ : ℂ) * I).re < 1 := by
    simpa using lt_of_le_of_lt (RHTower.re_le_of_mem_closedBall hz) hupper
  have hne : z + (τ : ℂ) * I ≠ 1 := by
    intro heq
    rw [heq] at hre
    exact (lt_irrefl (1 : ℝ)) hre
  exact (HTGeometry.analyticAt_riemannZeta hne).comp
    (f := fun w : ℂ => w + (τ : ℂ) * I) (x := z)
    (analyticAt_id.add analyticAt_const)

/-- A partial return about an actual zeta zero either transports a zero, hence a zero
of every finite Euler tail, or forces a deep relative small value on the missing arc. -/
theorem zeta_partial_return_zero_or_small_value {ρ : ℂ} {R δ η : ℝ}
    (hρ : riemannZeta ρ = 0) (hR : 0 < R) (hupper : ρ.re + R < 1)
    (hδ : 0 < δ) (hδπ : δ ≤ 2 * π) (hη : 0 < η) (τ : ℝ)
    (hreturn : ∀ θ ∈ Icc δ (2 * π),
      ‖riemannZeta (circleMap ρ R θ + (τ : ℂ) * I) - riemannZeta (circleMap ρ R θ)‖ ≤
        η * ‖riemannZeta (circleMap ρ R θ + (τ : ℂ) * I)‖) :
    (∃ w ∈ closedBall (ρ + (τ : ℂ) * I) R,
      riemannZeta w = 0 ∧ ∀ y : ℕ, eulerTail y w = 0) ∨
    ∃ θ ∈ Icc 0 δ,
      (Real.exp (-(2 * π - δ) * Real.log η / δ) - 1) *
        ‖riemannZeta (circleMap ρ R θ + (τ : ℂ) * I)‖ ≤
          ‖riemannZeta (circleMap ρ R θ)‖ := by
  have hf : AnalyticOnNhd ℂ riemannZeta (closedBall ρ R) := by
    simpa using analyticOnNhd_zeta_translate_closedBall hupper 0
  rcases zero_or_shortArc_small_value hR hδ hδπ hη hf
    (analyticOnNhd_zeta_translate_closedBall hupper τ) hρ hreturn with hz | hs
  · obtain ⟨z, hz, hzeta⟩ := hz
    refine Or.inl ⟨z + (τ : ℂ) * I, ?_, hzeta, ?_⟩
    · simpa only [mem_closedBall, dist_add_right] using hz
    · intro y
      simp only [eulerTail, hzeta, zero_mul]
  · exact Or.inr hs

#print axioms zeta_partial_return_zero_or_small_value

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

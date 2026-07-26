import GaloisForLFunctions.RHTower.DeningerArithmeticFiniteJetInterpolation

/-!
# Geometric exhaustion of the Xi jet divisor

The centered Xi divisor is finite in every closed disk.  Taking the disk of radius `n` gives a
monotone finite exhaustion by actual source points

`S_n = {rho | ‖xiSpectralPointSupport rho‖ ≤ n}`.

Unlike an arbitrary countable exhaustion, this one records the geometric separation needed for
local Taylor approximation and the compact-open jet interpolation argument.
-/

open Complex Filter Metric Set

namespace RHTower

noncomputable section

/-- Xi divisor points whose centered spectral coordinate lies in a closed disk form a finite set. -/
theorem deningerXiSupport_closedBall_finite (R : ℝ) :
    {rho : XiDivisorSupport |
      xiSpectralPointSupport rho ∈ Metric.closedBall 0 R}.Finite := by
  have hcod : (XiC ⁻¹' {0}ᶜ) ∈
      codiscreteWithin (Set.univ : Set ℂ) :=
    XiC_analytic.preimage_zero_mem_codiscreteWithin
      (x := 0) XiC_zero_ne (Set.mem_univ 0) isConnected_univ
  have hcodK : (XiC ⁻¹' {0}ᶜ) ∈
      codiscreteWithin (Metric.closedBall (0 : ℂ) R) :=
    Filter.codiscreteWithin_mono (Set.subset_univ _) hcod
  have hzeroFinite :
      {z ∈ Metric.closedBall (0 : ℂ) R | XiC z = 0}.Finite := by
    refine
      ((isCompact_closedBall (0 : ℂ) R).finite_diff_of_mem_codiscreteWithin
        hcodK).subset ?_
    intro z hz
    rw [Set.mem_sep_iff] at hz
    exact ⟨hz.1, by simp [Set.mem_preimage, hz.2]⟩
  apply Set.Finite.of_finite_image
    (f := xiSpectralPointSupport)
    (hzeroFinite.subset ?_)
    xiSpectralPointSupport_injective.injOn
  intro z hz
  obtain ⟨rho, hrho, rfl⟩ := hz
  exact
    ⟨hrho, XiC_xiSpectralPointSupport_eq_zero_source rho⟩

/-- Finite Xi support packet in the centered closed disk of natural radius `n`. -/
def deningerXiSupportClosedBallFinset
    (n : ℕ) : Finset XiDivisorSupport :=
  (deningerXiSupport_closedBall_finite n).toFinset

@[simp]
theorem mem_deningerXiSupportClosedBallFinset
    (n : ℕ) (rho : XiDivisorSupport) :
    rho ∈ deningerXiSupportClosedBallFinset n ↔
      ‖xiSpectralPointSupport rho‖ ≤ n := by
  rw [deningerXiSupportClosedBallFinset,
    Set.Finite.mem_toFinset]
  simp [Metric.mem_closedBall]

/-- Closed-disk support packets increase with the radius. -/
theorem deningerXiSupportClosedBallFinset_mono :
    Monotone deningerXiSupportClosedBallFinset := by
  intro m n hmn rho hrho
  rw [mem_deningerXiSupportClosedBallFinset] at hrho ⊢
  exact hrho.trans (by exact_mod_cast hmn)

/-- Every Xi divisor point enters the geometric exhaustion at some natural radius. -/
theorem deningerXiSupportClosedBallFinset_covers
    (rho : XiDivisorSupport) :
    ∃ n, rho ∈ deningerXiSupportClosedBallFinset n := by
  obtain ⟨n, hn⟩ :=
    exists_nat_ge ‖xiSpectralPointSupport rho‖
  exact
    ⟨n,
      (mem_deningerXiSupportClosedBallFinset n rho).2 hn⟩

/-- The geometric support packets tend to the top finset filter. -/
theorem deningerXiSupportClosedBallFinset_tendsto_atTop :
    Tendsto deningerXiSupportClosedBallFinset atTop atTop :=
  deningerXiSupportClosedBallFinset_mono.tendsto_atTop_finset
    deningerXiSupportClosedBallFinset_covers

end

end RHTower

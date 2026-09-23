import GaloisForLFunctions.RHTower.SuzukiNonabelianCartanWardCompletion
import GaloisForLFunctions.PNTPlus.Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Cofinal equivalence of Suzuki's nonabelian Cartan and completed Ward sources

The opposite-root `SL₂` source constructed in
`SuzukiNonabelianCartanWardCompletion` differs from the literal completed Suzuki Green source by
twice a positive cubic Cartan remainder.  The earlier module proves the sharp finite-aperture bound

`0 ≤ R_A ≤ log(A)^(3 : ℕ) / (24 * sqrt(A))`.

This file closes the cofinal question: the majorant tends to zero, hence the nonlinear Cartan
source and the completed prime--polar--Gamma Ward source are asymptotically identical.  It also
proves that uniform boundedness of the prime-labelled nonabelian source is exactly RH, equivalently
the existing atomic--continuous compensation law.  Thus nonlinear Stokes fusion preserves the
literal Suzuki endpoint without inserting a fitted coefficient or leaving a bounded ambiguity.

No RH premise, Xi-zero location, computation, or unproved order law is used.
-/

open Complex Filter Function Set Topology
open scoped Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

open _root_.RHTower

/-- The explicit cubic Cartan majorant vanishes along natural apertures. -/
theorem tendsto_suzukiStokesCartanCubicMajorant : Tendsto
    (fun A : ℕ => Real.log (A : ℝ) ^ 3 / (24 * Real.sqrt (A : ℝ)))
    atTop (𝓝 0) := by
  have hreal : Tendsto
      (fun x : ℝ => Real.log x ^ (3 : ℝ) / x ^ (1 / 2 : ℝ))
      atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_pow_atTop (1 / 2) 3 (by norm_num)
  have hnat : Tendsto (fun A : ℕ => (A : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hcomp : Tendsto
      (fun A : ℕ => Real.log (A : ℝ) ^ (3 : ℝ) / (A : ℝ) ^ (1 / 2 : ℝ))
      atTop (𝓝 0) := hreal.comp hnat
  have hsqrt :
      (fun A : ℕ => Real.log (A : ℝ) ^ 3 / (24 * Real.sqrt (A : ℝ))) =
        fun A : ℕ => (1 / 24 : ℝ) *
          (Real.log (A : ℝ) ^ (3 : ℝ) / (A : ℝ) ^ (1 / 2 : ℝ)) := by
    funext A
    rw [Real.sqrt_eq_rpow]
    norm_num [Real.rpow_natCast]
    ring
  rw [hsqrt]
  simpa using (tendsto_const_nhds.mul hcomp)

/-- The total nonlinear correction in the prime-labelled `SL₂` source vanishes cofinally. -/
theorem tendsto_suzukiStokesCartanCubicRemainderMass : Tendsto
    (fun A : ℕ => suzukiStokesCartanCubicRemainderMass (A + 2))
    atTop (𝓝 0) := by
  have hmajor : Tendsto
      (fun A : ℕ => Real.log ((A + 2 : ℕ) : ℝ) ^ 3 /
        (24 * Real.sqrt ((A + 2 : ℕ) : ℝ))) atTop (𝓝 0) :=
    tendsto_suzukiStokesCartanCubicMajorant.comp (tendsto_add_atTop_nat 2)
  apply squeeze_zero
  · intro A
    exact suzukiStokesCartanCubicRemainderMass_nonneg (by omega : 2 ≤ A + 2)
  · intro A
    exact suzukiStokesCartanCubicRemainderMass_le_log_cube_div_sqrt
      (by omega : 2 ≤ A + 2)
  · exact hmajor

/-- **Cofinal source identification.**  The nonlinear nonabelian Cartan observable and the
literal completed Suzuki Green source differ by a quantity tending to zero. -/
theorem tendsto_suzukiCompletedStokesCartanWardObservable_sub_green : Tendsto
    (fun N : ℕ =>
      suzukiCompletedStokesCartanWardObservable (N + 2) -
        unitRieszSuzukiGreen (Real.log ((N + 2 : ℕ) : ℝ)))
    atTop (𝓝 0) := by
  have h : Tendsto
      (fun N : ℕ => 2 * suzukiStokesCartanCubicRemainderMass (N + 2))
      atTop (𝓝 0) := by
    simpa using tendsto_suzukiStokesCartanCubicRemainderMass.const_mul 2
  refine h.congr' ?_
  filter_upwards with N
  rw [suzukiCompletedStokesCartanWardObservable_eq_green_add_remainder]
  ring

/-- Uniform boundedness of the completed prime-labelled nonabelian Cartan source. -/
def SuzukiCompletedStokesCartanWardObservableBounded : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
    |suzukiCompletedStokesCartanWardObservable (N + 2)| ≤ B

/-- The nonabelian source has exactly the same boundedness content as the literal positive
atomic--continuous Ward compensation. -/
theorem suzukiCompletedStokesCartanWardObservableBounded_iff_atomicContinuous :
    SuzukiCompletedStokesCartanWardObservableBounded ↔
      SuzukiWardAtomicContinuousImbalanceBounded := by
  constructor
  · rintro ⟨B, hB, hcartan⟩
    obtain ⟨C, hC, hrem⟩ :=
      exists_uniform_bound_suzukiStokesCartanCubicRemainderMass
    refine ⟨B + 2 * C, by positivity, fun N => ?_⟩
    rw [← unitRieszSuzukiGreen_eq_primeCharge_sub_regularWardMass]
    have heq := suzukiCompletedStokesCartanWardObservable_eq_green_add_remainder N
    have hsub : unitRieszSuzukiGreen (Real.log ((N + 2 : ℕ) : ℝ)) =
        suzukiCompletedStokesCartanWardObservable (N + 2) -
          2 * suzukiStokesCartanCubicRemainderMass (N + 2) := by
      linarith
    rw [hsub]
    calc
      |suzukiCompletedStokesCartanWardObservable (N + 2) -
          2 * suzukiStokesCartanCubicRemainderMass (N + 2)| ≤
          |suzukiCompletedStokesCartanWardObservable (N + 2)| +
            |2 * suzukiStokesCartanCubicRemainderMass (N + 2)| := abs_sub _ _
      _ ≤ B + 2 * C := by
        have hrem0 := suzukiStokesCartanCubicRemainderMass_nonneg
          (by omega : 2 ≤ N + 2)
        rw [abs_of_nonneg (mul_nonneg (by norm_num) hrem0)]
        linarith [hcartan N, hrem (N + 2) (by omega : 2 ≤ N + 2)]
  · rintro ⟨B, hB, hgreen⟩
    obtain ⟨C, hC, hrem⟩ :=
      exists_uniform_bound_suzukiStokesCartanCubicRemainderMass
    refine ⟨B + 2 * C, by positivity, fun N => ?_⟩
    have hgreen' :
        |unitRieszSuzukiGreen (Real.log ((N + 2 : ℕ) : ℝ))| ≤ B := by
      rw [unitRieszSuzukiGreen_eq_primeCharge_sub_regularWardMass]
      exact hgreen N
    rw [suzukiCompletedStokesCartanWardObservable_eq_green_add_remainder]
    calc
      |unitRieszSuzukiGreen (Real.log ((N + 2 : ℕ) : ℝ)) +
          2 * suzukiStokesCartanCubicRemainderMass (N + 2)| ≤
          |unitRieszSuzukiGreen (Real.log ((N + 2 : ℕ) : ℝ))| +
            |2 * suzukiStokesCartanCubicRemainderMass (N + 2)| := abs_add_le _ _
      _ ≤ B + 2 * C := by
        have hrem0 := suzukiStokesCartanCubicRemainderMass_nonneg
          (by omega : 2 ≤ N + 2)
        rw [abs_of_nonneg (mul_nonneg (by norm_num) hrem0)]
        linarith [hgreen', hrem (N + 2) (by omega : 2 ≤ N + 2)]

/-- **Nonabelian Suzuki endpoint.**  Uniform control of the literal completed Cartan source is
equivalent to RH.  This is an unconditional equivalence theorem, not an assertion of the still
missing arithmetic boundedness producer. -/
theorem riemannHypothesis_iff_suzukiCompletedStokesCartanWardObservableBounded :
    RiemannHypothesis ↔ SuzukiCompletedStokesCartanWardObservableBounded := by
  rw [riemannHypothesis_iff_suzukiWardAtomicContinuousImbalanceBounded]
  exact suzukiCompletedStokesCartanWardObservableBounded_iff_atomicContinuous.symm

end

end GaloisForLFunctions.RHTower

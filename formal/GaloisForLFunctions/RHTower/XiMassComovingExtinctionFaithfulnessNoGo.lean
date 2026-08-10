import GaloisForLFunctions.RHTower.XiMassAdaptiveApertureFaithfulnessWall
import GaloisForLFunctions.RHTower.XiMassComovingPrimeExtinction

/-!
# Co-moving source extinction is exactly divisor-signal extinction

The co-moving mass `a(u)=|u|+2` makes the complete bottom prime source tend to zero.  This looks like
an unconditional closure of the vertical source bound until the moving carrier is compared with
its conserved charge.

C52 shows the same schedule caps every fixed divisor boost exponent.  The source vanishes because
the linearly widening mass cone suppresses both source and off-line receiver.  This file welds the
two statements and closes co-moving extinction as a false RH mechanism.  Its positive survivor is
the sharp scale separation: source control must be obtained in a sublinear mass regime, where
`u/a(u)` can diverge, rather than by kinematic extinction.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The co-moving mass is admissible at every time. -/
theorem half_le_xiComovingMass (u : ℝ) : 1 / 2 ≤ xiComovingMass u := by
  linarith [xiComovingMass_ge_two u]

/-- On nonnegative time, co-moving aperture is at least the linear scale with slope one. -/
theorem time_le_xiComovingMass {u : ℝ} (hu : 0 ≤ u) : u ≤ xiComovingMass u := by
  rw [xiComovingMass, abs_of_nonneg hu]
  linarith

/-- Every fixed divisor boost exponent is capped by its original conserved charge along the
co-moving mass schedule. -/
theorem xiMassComoving_boost_le_charge {u : ℝ} (hu : 0 ≤ u) (q : XiZeroCopy) :
    u * |((xiMassFamily (half_le_xiComovingMass u)).pt q).im| ≤
      (xiPoissonPoint q).re * |(xiPoissonPoint q).im| := by
  simpa using xiMassFamily_linearAperture_boost_le
    (half_le_xiComovingMass u) (show (0 : ℝ) < 1 by norm_num)
    (show (1 : ℝ) * u ≤ xiComovingMass u by
      simpa using time_le_xiComovingMass hu) q

/-- Exponential off-line amplification is capped as well. -/
theorem xiMassComoving_expBoost_le_charge {u : ℝ} (hu : 0 ≤ u) (q : XiZeroCopy) :
    Real.exp (u * |((xiMassFamily (half_le_xiComovingMass u)).pt q).im|) ≤
      Real.exp ((xiPoissonPoint q).re * |(xiPoissonPoint q).im|) := by
  exact Real.exp_le_exp.mpr (xiMassComoving_boost_le_charge hu q)

/-- The co-moving boost exponent of every fixed divisor copy fails to diverge. -/
theorem xiMassComoving_boost_not_tendsto_atTop (q : XiZeroCopy) :
    ¬ Tendsto
      (fun n : ℕ => (n : ℝ) *
        |((xiMassFamily (half_le_xiComovingMass n)).pt q).im|)
      atTop atTop := by
  apply xiMassFamily_linearSchedule_boost_not_tendsto_atTop
    (a := fun n : ℕ => xiComovingMass n)
    (ha := fun n => half_le_xiComovingMass n)
    (kappa := 1) (by norm_num)
  exact Eventually.of_forall fun n => by
    simpa using time_le_xiComovingMass (show 0 ≤ (n : ℝ) by positivity)

/-- The co-moving exponential detector of every fixed divisor copy fails to diverge. -/
theorem xiMassComoving_expBoost_not_tendsto_atTop (q : XiZeroCopy) :
    ¬ Tendsto
      (fun n : ℕ => Real.exp ((n : ℝ) *
        |((xiMassFamily (half_le_xiComovingMass n)).pt q).im|))
      atTop atTop := by
  apply xiMassFamily_linearSchedule_expBoost_not_tendsto_atTop
    (a := fun n : ℕ => xiComovingMass n)
    (ha := fun n => half_le_xiComovingMass n)
    (kappa := 1) (by norm_num)
  exact Eventually.of_forall fun n => by
    simpa using time_le_xiComovingMass (show 0 ≤ (n : ℝ) by positivity)

/-- **C53 extinction/faithfulness weld.**  The literal prime source tends to zero along the
co-moving schedule, while every fixed divisor boost simultaneously loses divergent amplification.
The source limit is therefore an erasure law, not an RH estimate. -/
theorem xiMassComoving_primeExtinction_and_divisorErasure
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) (q : XiZeroCopy) :
    Tendsto
        (fun u : ℝ => xiMassBottomPrimeIntegral (xiComovingMass u) 1
          ((sigma : ℂ) + u * I))
        atTop (𝓝 0) ∧
      ¬ Tendsto
        (fun n : ℕ => Real.exp ((n : ℝ) *
          |((xiMassFamily (half_le_xiComovingMass n)).pt q).im|))
        atTop atTop :=
  ⟨tendsto_xiMassBottomPrimeIntegral_comoving_zero hsigma,
    xiMassComoving_expBoost_not_tendsto_atTop q⟩

end

end RHTower

import GaloisForLFunctions.HTGeometry.GammaHypertranscendental
import GaloisForLFunctions.HTGeometry.GammaPeriodicConstraintCorona

/-!
# A pointed Gamma source is not effective

Multiplication by a nonconstant period-one exponential gauge preserves the Gamma unit-shift
constraint and its value at the regular point `1`.  Hence a bare rank-one source equation plus one
point does not reconstruct even the analytic function.  This is the concrete obstruction behind
the joint-fixed-gauge criterion.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Gamma twisted by the first nonconstant period-one Fourier gauge. -/
def gammaPeriodicGaugeTwist (z : ℂ) : ℂ :=
  gammaPeriodicMode 1 z * Complex.Gamma z

/-- The periodic twist obeys exactly the same Gamma source equation. -/
theorem gammaPeriodicGaugeTwist_add_one (z : ℂ) (hz : z ≠ 0) :
    gammaPeriodicGaugeTwist (z + 1) = z * gammaPeriodicGaugeTwist z := by
  rw [gammaPeriodicGaugeTwist, gammaPeriodicMode_add_one,
    Complex.Gamma_add_one z hz, gammaPeriodicGaugeTwist]
  ring

/-- The twist and Gamma have the same regular pointing at `1`. -/
theorem gammaPeriodicGaugeTwist_one :
    gammaPeriodicGaugeTwist 1 = Complex.Gamma 1 := by
  simp [gammaPeriodicGaugeTwist, gammaPeriodicMode, gammaPeriodicFrequency]

/-- The periodic gauge is already nontrivial at the half point. -/
theorem gammaPeriodicMode_one_half :
    gammaPeriodicMode 1 (1 / 2) = -1 := by
  rw [gammaPeriodicMode, gammaPeriodicFrequency]
  convert Complex.exp_pi_mul_I using 1
  push_cast
  ring_nf

/-- Despite the common source equation and pointing, the periodic twist is not Gamma. -/
theorem gammaPeriodicGaugeTwist_ne_gamma :
    gammaPeriodicGaugeTwist ≠ Complex.Gamma := by
  intro h
  have hhalf := congrFun h (1 / 2)
  rw [gammaPeriodicGaugeTwist, gammaPeriodicMode_one_half, neg_one_mul] at hhalf
  have hgamma : Complex.Gamma (1 / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have hre := congrArg Complex.re hn
    norm_num at hre
    have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  exact hgamma (neg_eq_self.mp hhalf)

/-- The untwisted member of the pointed source fibre is genuinely hypertranscendental. -/
theorem gamma_pointedSource_member_hypertranscendental :
    Hypertranscendental Complex.Gamma :=
  hypertranscendental_gamma

end

end GaloisForLFunctions.HTGeometry

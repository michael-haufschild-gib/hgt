import GaloisForLFunctions.RHTower.ConstrainedProlateOperator

/-!
# Spectrum of the exact zero-integral prolate compression

This module applies the compact positive greedy spectral exhaustion to the actual constrained
carrier
`ran(Pₐ) ∩ 1_[−a,a]ᗮ`.  It supplies the concentration and leakage eigenvalue sequences without
assuming simplicity, Fuchs asymptotics, or a Weil comparison.
-/

noncomputable section

open scoped InnerProduct InnerProductSpace

namespace RHTower

noncomputable def constrainedProlateConcentrationValue (a : ℝ) (n : ℕ) : ℝ :=
  ContinuousLinearMap.svVal (H := constrainedProlateSubspace a)
    (constrainedProlateConcentration a) n

noncomputable def constrainedProlateMode (a : ℝ) (n : ℕ) :
    constrainedProlateSubspace a :=
  ContinuousLinearMap.svVec (H := constrainedProlateSubspace a)
    (constrainedProlateConcentration a) n

theorem constrainedProlateConcentrationValue_nonneg (a : ℝ) (n : ℕ) :
    0 ≤ constrainedProlateConcentrationValue a n :=
  ContinuousLinearMap.svVal_nonneg (H := constrainedProlateSubspace a) _ n

theorem constrainedProlateConcentrationValue_antitone (a : ℝ) :
    Antitone (constrainedProlateConcentrationValue a) :=
  ContinuousLinearMap.svVal_antitone (H := constrainedProlateSubspace a) _

/-- The constrained greedy modes satisfy the exact concentration eigen-equation. -/
theorem constrainedProlateConcentration_apply_mode (a : ℝ) (n : ℕ) :
    constrainedProlateConcentration a (constrainedProlateMode a n) =
      (constrainedProlateConcentrationValue a n : ℂ) • constrainedProlateMode a n :=
  ContinuousLinearMap.apply_svVec (H := constrainedProlateSubspace a) _ n

theorem constrainedProlateMode_orthogonal_of_ne
    (a : ℝ) {m n : ℕ} (hmn : m ≠ n) :
    inner ℂ (constrainedProlateMode a m) (constrainedProlateMode a n) = 0 :=
  ContinuousLinearMap.inner_svVec_svVec_of_ne (H := constrainedProlateSubspace a) _ hmn

noncomputable def constrainedProlateLeakageValue (a : ℝ) (n : ℕ) : ℝ :=
  1 - constrainedProlateConcentrationValue a n

/-- The same constrained modes diagonalize leakage with complementary eigenvalues. -/
theorem constrainedProlateLeakage_apply_mode (a : ℝ) (n : ℕ) :
    constrainedProlateLeakage a (constrainedProlateMode a n) =
      (constrainedProlateLeakageValue a n : ℂ) • constrainedProlateMode a n := by
  rw [constrainedProlateLeakage, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, constrainedProlateConcentration_apply_mode]
  simp only [constrainedProlateLeakageValue, Complex.ofReal_sub, Complex.ofReal_one]
  module

end RHTower

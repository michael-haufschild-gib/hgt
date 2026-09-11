import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFullCollisionHankelStrata
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFullConeSpectralEnergy

/-! # Every full Hankel rank stratum is realized by actual full-support Gibbs states -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The full realizable cone has exact intrinsic rank equal to its number of nonzero prescribed masses. -/
theorem egbFixedChargeAGibbsFullCone_full_hankel_rank (n k j : ℕ) (R A B : NNReal) :
    (egbFixedChargeAGibbsFullCollisionHankelMatrix n (j + 3) 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B)).rank =
      (if R = 0 then 0 else 1) + (if A = 0 then 0 else 1) + (if B = 0 then 0 else 1) := by
  classical
  have ha : egbFixedChargeAGibbsFullConeAmplitude n k R A B ^ 2 ≠ 0 :=
    (egbFixedChargeAGibbsFullConeScale_pos n k R A B).ne'
  rw [egbFixedChargeAGibbsFullCollisionHankelMatrix_rank_strata]
  unfold egbFixedChargeAGibbsFullCollisionActiveModeCount egbFixedChargeAGibbsCollisionActiveModeCount
  rw [egbFixedChargeAGibbsFullCone_discarded_energy, egbFixedChargeAGibbsFullCone_slow_energy,
    egbFixedChargeAGibbsFullCone_fast_energy]
  simp only [mul_eq_zero, ha, false_or]
  simp only [NNReal.coe_eq_zero]
  split_ifs <;> omega

/-- Every positive-time finite block has the exact two-sector rank, independent of the erased mass. -/
theorem egbFixedChargeAGibbsFullCone_positive_hankel_rank (n k o d : ℕ) (R A B : NNReal) :
    (egbFixedChargeAGibbsCollisionHankelMatrix n o d 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B)).rank =
      min d ((if A = 0 then 0 else 1) + (if B = 0 then 0 else 1)) := by
  classical
  have ha : egbFixedChargeAGibbsFullConeAmplitude n k R A B ^ 2 ≠ 0 :=
    (egbFixedChargeAGibbsFullConeScale_pos n k R A B).ne'
  rw [egbFixedChargeAGibbsCollisionHankelMatrix_rank_classification]
  unfold egbFixedChargeAGibbsCollisionActiveModeCount
  rw [egbFixedChargeAGibbsFullCone_slow_energy, egbFixedChargeAGibbsFullCone_fast_energy]
  simp only [mul_eq_zero, ha, false_or, NNReal.coe_eq_zero]
  split_ifs <;> rfl

/-- The first transition loses exactly one rank precisely off the face where the prescribed erased mass is zero. -/
theorem egbFixedChargeAGibbsFullCone_hankel_rank_drop_exact (n k o j : ℕ) (R A B : NNReal) :
    (egbFixedChargeAGibbsFullCollisionHankelMatrix n (j + 3) 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B)).rank =
      (egbFixedChargeAGibbsCollisionHankelMatrix n o (j + 3) 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B)).rank +
        (if R = 0 then 0 else 1) := by
  classical
  rw [egbFixedChargeAGibbsFullCone_full_hankel_rank, egbFixedChargeAGibbsFullCone_positive_hankel_rank]
  split_ifs <;> omega

end
end GaloisForLFunctions.HTGeometry

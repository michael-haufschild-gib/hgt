import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Occupation

/-! # Thermal comparison of exactly occupied prime bands -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization

open Filter Topology Set MeasureTheory _root_.RHTower VacuumCalibration

/-- The unnormalized Gibbs weight of all configurations with exactly k occupied modes. -/
def coefficient (S : Finset Nat.Primes) (s : ℝ) (k : ℕ) :=
  finiteSquarefreePartition S s * atom S s k

private def rawEnergy {S : Finset Nat.Primes} {k : ℕ} (R : BreadthSubset k ↥S) :=
  finiteSquarefreeHamiltonian S ((squarefreeOccupationEquiv S).symm R.val)

private theorem coefficient_sum (S : Finset Nat.Primes) (s : ℝ) (k : ℕ) :
    coefficient S s k = ∑ R : BreadthSubset k ↥S, Real.exp (-s*rawEnergy R) := by
  let h : Ioi (0:ℝ) := ⟨1,show (0:ℝ) < 1 from zero_lt_one⟩
  rw [coefficient,← slice_mass S s h k,slice,atomic_mass,NNReal.coe_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro R _
  change finiteSquarefreePartition S s*finiteSquarefreeBornWeight S s _ = _
  rw [finiteSquarefreeBornWeight_eq]
  exact mul_div_cancel₀ _ (finiteSquarefreePartition_pos S s).ne'

private theorem energy_bounds {c d : ℝ} (h : Ioi (0:ℝ)) {k : ℕ} (R : BreadthSubset k ↥(added c d h)) :
    k*c/h.val ≤ rawEnergy R ∧ rawEnergy R ≤ k*d/h.val := by
  have he : rawEnergy R*h.val = ∑ p ∈ R.val,location h p.val := by
    rw [rawEnergy,finiteSquarefreeHamiltonian_eq_sum_occupation,
      show squarefreeOccupationFinset ((squarefreeOccupationEquiv _).symm R.val) = R.val from
        (squarefreeOccupationEquiv _).apply_symm_apply R.val,mul_comm,Finset.mul_sum]
    rfl
  rw [div_le_iff₀ h.property,le_div_iff₀ h.property,he]
  constructor
  · calc (k:ℝ)*c = ∑ _p ∈ R.val,c := by simp only [Finset.sum_const,R.property,nsmul_eq_mul]
         _ ≤ _ := Finset.sum_le_sum fun p _ => ((mem_added c d h p.val).mp p.property).1.le
  · calc _ ≤ ∑ _p ∈ R.val,d := Finset.sum_le_sum fun p _ => ((mem_added c d h p.val).mp p.property).2
         _ = _ := by simp only [Finset.sum_const,R.property,nsmul_eq_mul]

/-- Each fixed-count weight is multiplied by exp(t E) under the change from inverse temperature 1 to 1−t. -/
private theorem tilt_sum (S : Finset Nat.Primes) (t : ℝ) (k : ℕ) :
    coefficient S (1-t) k = ∑ R : BreadthSubset k ↥S, Real.exp (t*rawEnergy R)*Real.exp (-rawEnergy R) := by
  rw [coefficient_sum]
  exact Finset.sum_congr rfl fun R _ => by rw [← Real.exp_add]; congr 1; ring

/-- On a positive tilt, the two band endpoints bound every configuration's Gibbs multiplier. -/
theorem coefficient_tilt_pos (c d : ℝ) (h : Ioi (0:ℝ)) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    Real.exp (t*(k*c/h.val))*coefficient (added c d h) 1 k ≤ coefficient (added c d h) (1-t) k ∧
    coefficient (added c d h) (1-t) k ≤ Real.exp (t*(k*d/h.val))*coefficient (added c d h) 1 k := by
  rw [tilt_sum,coefficient_sum]
  simp only [neg_one_mul,Finset.mul_sum]
  constructor
  · exact Finset.sum_le_sum fun R _ => mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (energy_bounds h R).1 ht)) (Real.exp_pos _).le
  · exact Finset.sum_le_sum fun R _ => mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (energy_bounds h R).2 ht)) (Real.exp_pos _).le

/-- On a negative tilt, the upper endpoint supplies the smaller Gibbs multiplier. -/
theorem coefficient_tilt_neg (c d : ℝ) (h : Ioi (0:ℝ)) {t : ℝ} (ht : t ≤ 0) (k : ℕ) :
    Real.exp (t*(k*d/h.val))*coefficient (added c d h) 1 k ≤ coefficient (added c d h) (1-t) k ∧
    coefficient (added c d h) (1-t) k ≤ Real.exp (t*(k*c/h.val))*coefficient (added c d h) 1 k := by
  rw [tilt_sum,coefficient_sum]
  simp only [neg_one_mul,Finset.mul_sum]
  constructor
  · exact Finset.sum_le_sum fun R _ => mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (energy_bounds h R).2 ht)) (Real.exp_pos _).le
  · exact Finset.sum_le_sum fun R _ => mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (energy_bounds h R).1 ht)) (Real.exp_pos _).le

/-- At the critical temperature, each fixed-count coefficient depends asymptotically only on logarithmic width. -/
theorem coefficient_limit {c d : ℝ} (hc : 0 < c) (hcd : c < d) (k : ℕ) :
    Tendsto (fun h => coefficient (added c d h) 1 k) criticalApproach (𝓝 (Real.log (d/c)^k/k.factorial)) := by
  have H := (partition_limit hc hcd 0).mul (atom_limit hc hcd 0 k)
  have hm : mass c d 0 = Real.log (d/c) := by
    simp only [mass,neg_zero,zero_mul,Real.exp_zero,integral_one_div_of_pos hc (hc.trans hcd)]
  simpa only [coefficient,zero_mul,add_zero,hm,Real.exp_neg,← mul_div_assoc,← mul_assoc,
    mul_inv_cancel₀ (Real.exp_pos _).ne',one_mul] using H

#print axioms coefficient_tilt_pos
#print axioms coefficient_tilt_neg
#print axioms coefficient_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization

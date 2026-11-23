import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OccupationProbabilities.TraceTelescope
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.Waves

/-! # Spectral moments as moments of occupation probabilities -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap InnerProductSpace

/-- Born probability of a label in the normalized omitted wave. -/
def occupationProbability (v : MissingWave) (k : ℕ+) := ‖v.val k‖^2/‖v.val‖^2

/-- Probability mass weighted by one squared heat eigenvalue. -/
def heatedMass (v : MissingWave) (n : ℕ) := ‖defectVector v (number n)‖^2

theorem heatedMass_eq (v : MissingWave) (n : ℕ) :
    heatedMass v n = occupationWeight n*occupationProbability v (number n) := by
  change ‖((‖v.val‖⁻¹:ℝ):ℂ)*(criticalOperator v.val (number n))‖^2 = _
  rw [critical_apply,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    Real.norm_of_nonneg (attenuation_pos _).le,occupationWeight,occupationProbability]
  simp only [mul_pow,inv_pow,div_eq_mul_inv]
  ring

private theorem lp_sq_sum (x : Gas) :
    HasSum (fun n : ℕ => ‖x (number n)‖^2) (‖x‖^2) := by
  rw [gas_norm_sq]
  exact (gas_coords_summable x).hasSum

theorem heatedMass_sum (v : MissingWave) : HasSum (heatedMass v) (‖defectVector v‖^2) :=
  lp_sq_sum _

theorem occupationProbability_sum (v : MissingWave) : HasSum (fun n => occupationProbability v (number n)) 1 := by
  have h := (lp_sq_sum v.val).div_const (‖v.val‖^2)
  simpa only [occupationProbability,div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr (missingWave_ne_zero v)))] using h

private theorem native_power_at (x : Gas) (n m : ℕ) :
    (squareHeat.val^m) x (number n) = ((occupationWeight n^m:ℝ):ℂ)*x (number n) := by
  induction m with
  | zero => simp only [pow_zero,one_apply_eq_self,Complex.ofReal_one,one_mul]
  | succ m ih =>
    rw [pow_succ' squareHeat.val]
    change (attenuation (number n):ℂ)*((attenuation (number n):ℂ)*((squareHeat.val^m) x (number n))) = _
    have ha : (occupationWeight n:ℂ) = (attenuation (number n):ℂ)^2 := Complex.ofReal_pow _ _
    rw [ih,pow_succ' (occupationWeight n),Complex.ofReal_mul,ha]
    ring

/-- Native moments sample precisely the discrete measure with masses `heatedMass`. -/
theorem nativeVectorMoment_eq_sum (v : MissingWave) (m : ℕ) :
    nativeVectorMoment v m = ((∑' n, occupationWeight n^m*heatedMass v n:ℝ):ℂ) := by
  let x := defectVector v
  rw [nativeVectorMoment,lp.inner_eq_tsum,← Equiv.pnatEquivNat.symm.tsum_eq,Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  change inner ℂ ((squareHeat.val^m) x (number n)) (x (number n)) = _
  rw [native_power_at]
  change inner ℂ (((occupationWeight n^m:ℝ):ℂ) • x (number n)) (x (number n)) = _
  rw [inner_smul_left,Complex.conj_ofReal,Complex.ofReal_mul]
  congr 1
  change inner ℂ (x (number n)) (x (number n)) = ((‖x (number n)‖^2:ℝ):ℂ)
  rw [RCLike.inner_apply,Complex.mul_conj,Complex.sq_norm]

theorem heatedMoment_summable (v : MissingWave) (m : ℕ) :
    Summable (fun n => occupationWeight n^m*heatedMass v n) := by
  apply (heatedMass_sum v).summable.of_nonneg_of_le
  · intro n
    exact mul_nonneg (pow_nonneg (occupationWeight_pos n).le _) (sq_nonneg _)
  · intro n
    exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (occupationWeight_pos n).le (occupation_in_unit n).2)

#print axioms heatedMass_eq
#print axioms heatedMass_sum
#print axioms occupationProbability_sum
#print axioms nativeVectorMoment_eq_sum
#print axioms heatedMoment_summable

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

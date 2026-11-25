import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.EulerFunctional
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.Trace

/-! # Generating functional of the marks in the finite Born wave -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks

open Filter Topology Set MeasureTheory _root_.RHTower

/-- A configuration contributes one factor of the test at each of its occupied prime energies. -/
def reading (S : Finset Nat.Primes) (s : ℝ) (h : Ioi (0:ℝ)) (f : ℝ → ℂ) :=
  ∑ x : SquarefreeBitConfig S, (finiteSquarefreeBornWeight S s x:ℂ)*
    ∏ p ∈ squarefreeOccupationFinset x, f (location h p.val)

/-- Exponential tilt of the scale-invariant intensity at thermal drift a. -/
def tilt (a v : ℝ) : ℂ := (Real.exp (-a*v):ℝ)

private theorem continuous_tilt (a : ℝ) : Continuous (tilt a) :=
  Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))

private theorem one_prime (a : ℝ) (h : Ioi (0:ℝ)) (p : Nat.Primes) :
    (squarefreePrimeNome (1+a*h.val) p:ℂ) = tilt a (location h p)/(p.val:ℂ) := by
  rw [squarefreePrimeNome_eq_exp,show -(1+a*h.val)*squarefreePrimeEnergy p =
    -a*location h p-squarefreePrimeEnergy p by unfold location; ring,Real.exp_sub]
  simp only [squarefreePrimeEnergy,Real.exp_log (Nat.cast_pos.mpr p.property.pos),Complex.ofReal_div,
    tilt,Complex.ofReal_natCast]

private theorem heat_product (S : Finset Nat.Primes) (s : ℝ) (x : SquarefreeBitConfig S) :
    (Real.exp (-s*finiteSquarefreeHamiltonian S x):ℂ) =
      ∏ p ∈ squarefreeOccupationFinset x, (squarefreePrimeNome s p.val:ℂ) := by
  simp only [squarefreePrimeNome_eq_exp,← Complex.ofReal_prod,← Real.exp_sum,← Finset.mul_sum,
    finiteSquarefreeHamiltonian_eq_sum_occupation]

private theorem subset_sum (S : Finset Nat.Primes) (g : ↥S → ℂ) :
    (∑ x : SquarefreeBitConfig S, ∏ p ∈ squarefreeOccupationFinset x, g p) = ∏ p : ↥S, (1+g p) := by
  classical
  rw [Finset.prod_one_add,Finset.powerset_univ]
  exact (squarefreeOccupationEquiv S).sum_comp (fun T => ∏ p ∈ T, g p)

/-- Exact generating functional as a quotient of two finite marked Euler products. -/
theorem reading_eq (c d a : ℝ) (h : Ioi (0:ℝ)) (f : ℝ → ℂ) :
    reading (added c d h) (1+a*h.val) h f =
      euler c d h (fun v => f v*tilt a v)/euler c d h (tilt a) := by
  let S := added c d h
  let s := 1+a*h.val
  let g (p : ↥S) := (squarefreePrimeNome s p.val:ℂ)*f (location h p.val)
  have hZ : (finiteSquarefreePartition S s:ℂ) = euler c d h (tilt a) := by
    rw [finiteSquarefreePartition,Complex.ofReal_prod,euler,
      ← Finset.prod_coe_sort S (fun p => 1+tilt a (location h p)/(p.val:ℂ))]
    simp only [Complex.ofReal_add,Complex.ofReal_one,s,one_prime]
  calc reading S s h f = (∑ x, ∏ p ∈ squarefreeOccupationFinset x, g p)/(finiteSquarefreePartition S s:ℂ) := by
         rw [reading,Finset.sum_div]
         apply Finset.sum_congr rfl
         intro x _
         rw [finiteSquarefreeBornWeight_eq,Complex.ofReal_div,heat_product,div_mul_eq_mul_div,
           ← Finset.prod_mul_distrib]
       _ = _ := by
         rw [subset_sum,hZ]
         apply congrArg (fun n : ℂ => n/euler c d h (tilt a))
         rw [euler,← Finset.prod_coe_sort S (fun p =>
           1+f (location h p)*tilt a (location h p)/(p.val:ℂ))]
         apply Finset.prod_congr rfl
         intro p _
         unfold g s
         rw [one_prime]
         ring

/-- Generating exponent for the limiting marked process at thermal drift a. -/
def exponent (c d a : ℝ) (f : ℝ → ℂ) := ∫ v in c..d, (f v-1)*tilt a v/(v:ℂ)

/-- Every continuous complex test of the actual occupied locations has the Poisson generating functional. -/
theorem reading_limit {c d : ℝ} (hc : 0 < c) (hcd : c < d) (a : ℝ) (f : ℝ → ℂ) (hf : Continuous f) :
    Tendsto (fun h => reading (added c d h) (1+a*h.val) h f) criticalApproach
      (𝓝 (Complex.exp (exponent c d a f))) := by
  have hi (g : ℝ → ℂ) (hg : Continuous g) :
      IntervalIntegrable (fun v => g v/(v:ℂ)) volume c d := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hcd.le]
    exact hg.continuousOn.div Complex.continuous_ofReal.continuousOn
      (fun v hv => Complex.ofReal_ne_zero.mpr (hc.trans_le hv.1).ne')
  have H := (euler_limit hc hcd _ (hf.mul (continuous_tilt a))).div
    (euler_limit hc hcd _ (continuous_tilt a)) (Complex.exp_ne_zero _)
  rw [← Complex.exp_sub,← intervalIntegral.integral_sub (hi _ (hf.mul (continuous_tilt a)))
    (hi _ (continuous_tilt a))] at H
  have he : (∫ v in c..d, f v*tilt a v/(v:ℂ)-tilt a v/(v:ℂ)) = exponent c d a f := by
    apply intervalIntegral.integral_congr
    intro v _
    ring
  simp only [Pi.mul_apply] at H
  rw [he] at H
  exact H.congr (fun h => (reading_eq c d a h f).symm)

/-- Marking each location by w exp(zv) reads the count and total energy of the same configuration. -/
theorem joint_eq_reading (S : Finset Nat.Primes) (s : ℝ) (h : Ioi (0:ℝ)) (w z : ℂ) :
    jointMoment S s h w z = reading S s h (fun v => w*Complex.exp (z*(v:ℂ))) := by
  unfold jointMoment reading
  apply Finset.sum_congr rfl
  intro x _
  have hv : (packetEnergy S h x:ℂ) = ∑ p ∈ squarefreeOccupationFinset x, (location h p.val:ℂ) := by
    simp only [packetEnergy,finiteSquarefreeHamiltonian_eq_sum_occupation,location,Finset.mul_sum,
      Complex.ofReal_sum]
  rw [Finset.prod_mul_distrib,Finset.prod_const,← Complex.exp_sum,← Finset.mul_sum,← hv,mul_assoc]

theorem joint_limit {c d : ℝ} (hc : 0 < c) (hcd : c < d) (a : ℝ) (w z : ℂ) :
    Tendsto (fun h => jointMoment (added c d h) (1+a*h.val) h w z) criticalApproach
      (𝓝 (Complex.exp (exponent c d a (fun v => w*Complex.exp (z*(v:ℂ)))))) := by
  exact (reading_limit hc hcd a _ (by fun_prop)).congr (fun h => (joint_eq_reading _ _ h w z).symm)

#print axioms reading_eq
#print axioms reading_limit
#print axioms joint_eq_reading
#print axioms joint_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks

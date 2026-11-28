import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities.Channels
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CompositionRigidity

/-! # Complex powers of positive shares and the two integer phase references -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay

open scoped ComplexConjugate

/-- Complex amplitude of a positive branch share. -/
def power (z : ℂ) (x : ℝ) := Complex.exp (z*(Real.log x:ℂ))

theorem power_ne (z : ℂ) (x : ℝ) : power z x≠0 := Complex.exp_ne_zero _

theorem power_add (z w : ℂ) (x : ℝ) : power (z+w) x=power z x*power w x := by
  simp only [power,add_mul,Complex.exp_add]

theorem unit_power (z : ℂ) : power z 1=1 := by simp [power]

theorem power_at_one {x : ℝ} (hx : 0<x) : power 1 x=(x:ℂ) := by
  rw [power,one_mul,←Complex.ofReal_exp,Real.exp_log hx]

theorem power_mul (z : ℂ) {x y : ℝ} (hx : 0<x) (hy : 0<y) :
    power z (x*y)=power z x*power z y := by
  simp only [power,Real.log_mul hx.ne' hy.ne',Complex.ofReal_add,mul_add,Complex.exp_add]

theorem power_nat (z : ℂ) {x : ℝ} (hx : 0<x) (k : ℕ) : power z (x^k)=(power z x)^k := by
  induction k with
  | zero => simp only [pow_zero,unit_power]
  | succ k ih => rw [pow_succ,power_mul z (pow_pos hx k) hx,ih,pow_succ]

theorem paired_power (w s : ℂ) (x : ℝ) :
    conj (power w x)*power s x=power (conj w+s) x := by
  simp only [power,←Complex.exp_conj,map_mul,Complex.conj_ofReal,add_mul,Complex.exp_add]

/-- The integers supplied by the second and third binomial coefficients
determine even the imaginary part of the exponent. -/
theorem power_refs_injective : Function.Injective (fun z : ℂ => (power z 2,power z 3)) := by
  intro z v h
  have same (s : ℂ) (n : ℕ+) : heat (-s) n=power s n.val := by simp only [heat,neg_neg,energy,power]
  apply neg_injective
  apply two_prime_heat_injective
  change (heat (-z) 2,heat (-z) 3)=(heat (-v) 2,heat (-v) 3)
  simp only [same]
  exact h

theorem two_three (z : ℂ) (two : power z 2=2) (three : power z 3=3) : z=1 := by
  apply power_refs_injective
  change (power z 2,power z 3)=(power 1 2,power 1 3)
  rw [two,three,power_at_one (by norm_num : 0<(2:ℝ)),power_at_one (by norm_num : 0<(3:ℝ))]
  norm_num

#print axioms paired_power
#print axioms power_refs_injective
#print axioms two_three

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay

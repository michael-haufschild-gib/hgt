import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay.Powers
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.SquareTest.Odds

/-! # Coherent shell overlaps of repeated copies of one physical prime -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay

open Finset ModeCapacities SquareTest
open scoped ComplexConjugate

def rayOverlap (w s : ℂ) (u v : ℕ → ℝ) (p : Nat.Primes) (k : ℕ) :=
  ∑ j ∈ range (k+1),
    conj (kernel w u v (rayState p j) (rayState p (k-j))) *
      kernel s u v (rayState p j) (rayState p (k-j))

def share (u v : ℕ → ℝ) (p : Nat.Primes) := u p.val/(u p.val+v p.val)

theorem share_pos {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) (p : Nat.Primes) :
    0<share u v p := div_pos (hu p) (add_pos (hu p) (hv p))

theorem share_sum {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) (p : Nat.Primes) :
    share u v p+share v u p=1 := by
  rw [share,share,add_comm (v p.val) (u p.val),←add_div,div_self (add_pos (hu p) (hv p)).ne']

/-- Polynomial in the two complex elementary readings. Each occupation
multiplicity retains its own complex power. -/
def polynomial (z a b : ℂ) (k : ℕ) :=
  ∑ j ∈ range (k+1), power z (k.choose j:ℝ)*a^j*b^(k-j)

theorem amplitude_ray (z : ℂ) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v)
    (p : Nat.Primes) (j k : ℕ) :
    kernel z u v (rayState p j) (rayState p k)=
      power z ((j+k).choose j:ℝ)*(power z (share u v p))^j*(power z (share v u p))^k := by
  change power z (branch u v (p.val^j) (p.val^k))=_
  rw [branch_on_ray,prime_ray (hu p) (hv p),binomial]
  have hx := share_pos hu hv p
  have hy := share_pos hv hu p
  have hbin : 0<((j+k).choose j:ℝ) := Nat.cast_pos.mpr (Nat.choose_pos (Nat.le_add_right j k))
  have Y : v p.val/(u p.val+v p.val)=share v u p := by rw [share,add_comm]
  change power z (_*((share u v p)^j*(v p.val/(u p.val+v p.val))^k))=_
  rw [Y,power_mul z hbin (mul_pos (pow_pos hx j) (pow_pos hy k)),
    power_mul z (pow_pos hx j) (pow_pos hy k),power_nat z hx,power_nat z hy,mul_assoc]

private theorem paired_ray (w s : ℂ) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v)
    (p : Nat.Primes) (j k : ℕ) :
    conj (kernel w u v (rayState p j) (rayState p k))*kernel s u v (rayState p j) (rayState p k)=
      power (conj w+s) ((j+k).choose j:ℝ) *
        (power (conj w+s) (share u v p))^j * (power (conj w+s) (share v u p))^k :=
  (paired_power w s _).trans (amplitude_ray (conj w+s) hu hv p j k)

theorem ray_polynomial (w s : ℂ) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v)
    (p : Nat.Primes) (k : ℕ) :
    rayOverlap w s u v p k=polynomial (conj w+s)
      (power (conj w+s) (share u v p)) (power (conj w+s) (share v u p)) k := by
  apply sum_congr rfl
  intro j hj
  have le : j≤k := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [paired_ray w s hu hv p,show j+(k-j)=k by omega]

theorem polynomial_one (z a b : ℂ) : polynomial z a b 1=a+b := by
  rw [polynomial,Finset.sum_range_succ _ 1,Finset.sum_range_one]
  norm_num [unit_power]
  ring

theorem polynomial_two (z a b : ℂ) : polynomial z a b 2=a^2+power z 2*a*b+b^2 := by
  rw [polynomial,Finset.sum_range_succ _ 2,Finset.sum_range_succ _ 1,Finset.sum_range_one]
  norm_num [Nat.choose_succ_succ,unit_power]
  ring

theorem polynomial_three (z a b : ℂ) :
    polynomial z a b 3=a^3+power z 3*(a^2*b+a*b^2)+b^3 := by
  rw [polynomial,Finset.sum_range_succ _ 3,Finset.sum_range_succ _ 2,Finset.sum_range_succ _ 1,Finset.sum_range_one]
  norm_num [Nat.choose_succ_succ,unit_power]
  ring

#print axioms amplitude_ray
#print axioms ray_polynomial
#print axioms polynomial_three

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay

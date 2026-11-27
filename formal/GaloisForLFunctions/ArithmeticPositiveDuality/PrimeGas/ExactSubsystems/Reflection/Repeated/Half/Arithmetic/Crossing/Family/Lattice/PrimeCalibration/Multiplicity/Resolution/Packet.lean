import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Resolution.Variation
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Stationarity

/-! # Cubic resolution of the calibrated packet at the isometry line -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Resolution

open Finset Filter Real
open scoped Topology
open _root_.HTGeometry (finiteGibbsStateWeight)

def spectrum (p q : Nat.Primes) (i : States p) := log q.val * centered (levels (packet p)) i

def reading (p q : Nat.Primes) (d : ℝ) :=
  lawDefect (finiteGibbsStateWeight d (primeModes q (packet p))) 1

def tangent (p q : Nat.Primes) (d : ℝ) :=
  deriv (lawDefect (finiteGibbsStateWeight d (primeModes q (packet p)))) 1

/-- The dilation in moment order differentiates the same trace in damping. -/
theorem readings (p q : Nat.Primes) (d : ℝ) :
    reading p q d=oddTrace (spectrum p q) d ∧ tangent p q d=d*variation (spectrum p q) 1 d := by
  let P := finiteGibbsStateWeight d (primeModes q (packet p))
  have law : lawDefect P = fun v => oddTrace (spectrum p q) (v*d) := by
    funext v
    rw [gibbs_defect]
    apply sum_congr rfl
    intro i _
    simp only [oddTerm,spectrum,mul_assoc,neg_mul]
  have lin : HasDerivAt (fun v : ℝ => v*d) d 1 := by
    simpa only [id_eq,one_mul] using (hasDerivAt_id (1 : ℝ)).mul_const d
  have diff := (variation_deriv (spectrum p q) 0 (1*d)).comp 1 lin
  rw [variation_zero_order] at diff
  change lawDefect P 1=_ ∧ deriv (lawDefect P) 1=_
  constructor
  · simp only [law,one_mul]
  · rw [law,mul_comm d (variation (spectrum p q) 1 d)]
    simpa only [Function.comp_def,one_mul] using diff.deriv

theorem centered_occupation (p : Nat.Primes) (i : States p) :
    centered (levels (packet p)) i=(packet p i : ℝ)-27/2 := by
  have size := packet_sum p (fun _ => (1 : ℕ))
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_one,Nat.cast_id] at size
  change Fintype.card (States p)=p.val*6+threshold p*6 at size
  have mass := packet_sum p (fun k => (k : ℝ))
  have hp := p.property.pos
  have nz : (Fintype.card (States p) : ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  change (packet p i : ℝ)-(∑ j, (packet p j : ℝ))/(Fintype.card (States p) : ℝ)=_
  congr 1
  apply (div_eq_iff nz).mpr
  rw [size,Nat.cast_add,Nat.cast_mul,Nat.cast_mul]
  norm_num at mass ⊢
  linarith only [mass]

/-- The whole third centered moment is the difference between the two
multiplicities, scaled by the cube of the elementary prime energy. -/
theorem packet_third_moment (p q : Nat.Primes) :
    moment (spectrum p q) 3=2304*(p.val-1 : ℝ)^2*(log q.val)^3 := by
  simp only [moment,spectrum,centered_occupation,mul_pow,←mul_sum]
  rw [packet_sum p (fun k => ((k : ℝ)-27/2)^3)]
  simp only [threshold,Nat.cast_add,Nat.cast_mul,Nat.cast_sub p.property.one_lt.le,Nat.cast_one]
  norm_num
  ring

def cubic (p q : Nat.Primes) : ℝ := 768*(p.val-1 : ℝ)^2*(log q.val)^3

theorem cubic_pos (p q : Nat.Primes) : 0<cubic p q := by
  have hp : (1 : ℝ)<p.val := Nat.one_lt_cast.mpr p.property.one_lt
  have hq := log_pos_prime q
  unfold cubic
  positivity

/-- Both readings vanish cubically. The tangent's leading coefficient
is three times the value reading's coefficient. -/
theorem cubic_readings (p q : Nat.Primes) :
    Tendsto (fun d => reading p q d/d^3) (𝓝[≠] 0) (𝓝 (cubic p q)) ∧
    Tendsto (fun d => tangent p q d/d^3) (𝓝[≠] 0) (𝓝 (3*cubic p q)) := by
  let E := spectrum p q
  have vanish (k : ℕ) (hk : k<3) : variation E k 0=0 := by
    interval_cases k
    · simp only [variation_origin,moment,pow_zero,sub_self]
    · simp only [variation_origin,moment,pow_one,sum_neg_distrib,E,spectrum,←mul_sum,
        sum_centered,mul_zero,neg_zero,sub_self]
    · simp only [variation_origin,moment,neg_sq,sub_self]
  have coeff : variation E 3 0 = 2*moment E 3 := by
    simp only [variation_origin,moment,Odd.neg_pow (show Odd 3 from ⟨1,rfl⟩),sum_neg_distrib,
      sub_neg_eq_add,two_mul]
  have h := joint_limit E 2 vanish
  change Tendsto _ _ (𝓝 (variation E 3 0/(Nat.factorial 3 : ℝ))) ∧
    Tendsto _ _ (𝓝 (variation E 3 0/(Nat.factorial 2 : ℝ))) at h
  rw [coeff,show moment E 3=_ from packet_third_moment p q] at h
  have c₁ : 2*(2304*(p.val-1 : ℝ)^2*log q.val^3)/(Nat.factorial 3 : ℝ)=cubic p q := by
    norm_num [Nat.factorial,cubic]; ring
  have c₂ : 2*(2304*(p.val-1 : ℝ)^2*log q.val^3)/(Nat.factorial 2 : ℝ)=3*cubic p q := by
    norm_num [Nat.factorial,cubic]; ring
  rw [c₁,c₂] at h
  simpa only [fun d => (readings p q d).1,fun d => (readings p q d).2] using h

#print axioms readings
#print axioms centered_occupation
#print axioms packet_third_moment
#print axioms cubic_pos
#print axioms cubic_readings

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Resolution

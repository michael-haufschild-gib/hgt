import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay.Duality

/-! # Two occupations need not identify the imaginary part of the dual partner -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay

open ModeCapacities
open scoped ComplexConjugate

private def shifted : ℂ := 1+((2*Real.pi/Real.log 2:ℝ):ℂ)*Complex.I

private theorem shift_ne_one : shifted≠1 := by
  intro h
  have H := congrArg Complex.im h
  simp only [shifted,Complex.add_im,Complex.one_im,Complex.mul_I_im,Complex.ofReal_re,zero_add] at H
  exact (div_pos (mul_pos (by norm_num) Real.pi_pos) (Real.log_pos (by norm_num : 1<(2:ℝ)))).ne' H

private theorem shift_two : power shifted 2=2 := by
  have nz : ((Real.log 2:ℝ):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num : 1<(2:ℝ))).ne'
  have phase : shifted*(Real.log 2:ℂ)=(Real.log 2:ℂ)+2*Real.pi*Complex.I := by
    simp only [shifted,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat]
    field_simp [nz]
  rw [power,phase,Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one,←Complex.ofReal_exp,
    Real.exp_log (by norm_num : 0<(2:ℝ)),Complex.ofReal_ofNat]

private theorem shift_half : power shifted (1/2)=(1/2:ℂ) := by
  have eqn := power_mul shifted (by norm_num : 0<(2:ℝ)) (by norm_num : 0<(1/2:ℝ))
  rw [show (2:ℝ)*(1/2)=1 by norm_num,unit_power,shift_two] at eqn
  linear_combination -eqn / 2

/-- At balanced capacities the first two occupations are blind to a
nonzero logarithmic phase period. The cubic shell distinguishes it. -/
theorem two_shells_insufficient (p : Nat.Primes) :
    ∃ w s : ℂ, rayOverlap w s 1 1 p 1=1 ∧ rayOverlap w s 1 1 p 2=1 ∧
      rayOverlap w s 1 1 p 3≠1 ∧ w≠1-conj s := by
  have pos : positive (1 : ℕ → ℝ) := fun _ => zero_lt_one
  have half : share 1 1 p=1/2 := by norm_num [share]
  have read (k : ℕ) : rayOverlap 0 shifted 1 1 p k=polynomial shifted (1/2) (1/2) k := by
    rw [ray_polynomial 0 shifted pos pos p k,map_zero,zero_add,half,shift_half]
  have first : rayOverlap 0 shifted 1 1 p 1=1 := by rw [read,polynomial_one]; norm_num
  have second : rayOverlap 0 shifted 1 1 p 2=1 := by rw [read,polynomial_two,shift_two]; norm_num
  have diff : (0:ℂ)≠1-conj shifted := by
    intro h
    have H := congrArg conj h
    simp only [map_zero,map_sub,map_one,Complex.conj_conj] at H
    exact shift_ne_one (by linear_combination H)
  exact ⟨0,shifted,first,second,fun h => diff ((triple_iff 0 shifted pos pos p).mp ⟨first,second,h⟩),diff⟩

#print axioms two_shells_insufficient

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay

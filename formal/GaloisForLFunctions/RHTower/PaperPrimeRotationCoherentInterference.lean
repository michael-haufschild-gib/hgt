import GaloisForLFunctions.RHTower.PaperPrimeRotationCoherentKernel
import GaloisForLFunctions.HTGeometry.ImaginaryWindowKernel

/-! # Relative prime signs survive the coherent Gram limit

The fixed primes two and three give a literal interference witness. All
finite ordinary determinants remain one, but the two Gram limits differ.
-/

namespace RHTower
open GaloisForLFunctions.HTGeometry
noncomputable section
open scoped Classical

private def coherentPrime (n : ℕ) (h : n.Prime) : Nat.Primes := ⟨n, h⟩

local notation "p₂" => coherentPrime 2 Nat.prime_two
local notation "p₃" => coherentPrime 3 Nat.prime_three

theorem paperPrimeCoherentEnergy_eq_integral (s : Finset Nat.Primes) (a : Nat.Primes → ℂ) :
    paperPrimeCoherentEnergy s a = ∫ x in (0 : ℝ)..1,
      ‖∑ p ∈ s, a p * (Real.log p : ℂ) * paperRotationPhase (-Real.log p * x)‖ ^ 2 := by
  unfold paperPrimeCoherentEnergy finitePhaseEnergy
  congr 1
  funext x
  have he : finitePhasePacket s (paperPrimeCoherentLimitCoefficient a)
      (fun p => -Real.log p) x = -Complex.I *
        ∑ p ∈ s, a p * (Real.log p : ℂ) * paperRotationPhase (-Real.log p * x) := by
    rw [finitePhasePacket, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [paperPrimeCoherentLimitCoefficient, Complex.ofReal_neg]
    ring
  rw [he, norm_mul, norm_neg, Complex.norm_I, one_mul]

theorem paperPrimeCoherentKernel_re (p r : Nat.Primes) :
    (paperPrimeCoherentKernel p r).re =
      Real.log p * Real.log r * Real.sinc (Real.log p - Real.log r) := by
  rw [paperPrimeCoherentKernel, Complex.mul_re, Complex.mul_re, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero,
    zero_add, forwardWindowKernel_imaginary_re]

theorem paperPrimeCoherentKernel_conj (p r : Nat.Primes) :
    starRingEnd ℂ (paperPrimeCoherentKernel p r) = paperPrimeCoherentKernel r p := by
  rw [paperPrimeCoherentKernel, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
    forwardWindowKernel_imaginary_conj, paperPrimeCoherentKernel]
  rw [neg_sub]
  ring

theorem paperPrimeCoherentKernel_two_three_re_pos :
    0 < (paperPrimeCoherentKernel p₂ p₃).re := by
  rw [paperPrimeCoherentKernel_re]
  apply mul_pos (mul_pos p₂.2.log_pos p₃.2.log_pos)
  apply sinc_pos_of_abs_lt_pi
  change |Real.log 2 - Real.log 3| < Real.pi
  have h23 : Real.log (2 : ℝ) < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  rw [abs_of_neg (sub_neg.mpr h23)]
  have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
    (by norm_num : (3 / 2 : ℝ) ≠ 1)
  rw [Real.log_div (by norm_num) (by norm_num)] at h
  linarith [Real.pi_gt_three]

theorem paperPrimeCoherentEnergy_two_three_interference :
    paperPrimeCoherentEnergy {p₂, p₃} (fun p => if p = p₃ then -1 else 1) <
      paperPrimeCoherentEnergy {p₂, p₃} (fun _ => 1) := by
  have h23 : p₂ ≠ p₃ := by
    intro h
    have := congrArg Subtype.val h
    norm_num [coherentPrime] at this
  have hplus := congrArg Complex.re
    (paperPrimeCoherentEnergy_eq_kernel {p₂, p₃} (fun _ => 1))
  have hminus := congrArg Complex.re
    (paperPrimeCoherentEnergy_eq_kernel {p₂, p₃} (fun p => if p = p₃ then -1 else 1))
  have hsym : (paperPrimeCoherentKernel p₃ p₂).re = (paperPrimeCoherentKernel p₂ p₃).re := by
    rw [← paperPrimeCoherentKernel_conj]
    simp
  simp only [Finset.sum_pair (ι := Nat.Primes) h23] at hplus hminus
  simp [h23, hsym] at hplus hminus
  linarith [paperPrimeCoherentKernel_two_three_re_pos]

theorem paperPrimeCoherentGramLimit_two_three_interference :
    Real.exp (paperPrimeCoherentEnergy {p₂, p₃} (fun p => if p = p₃ then -1 else 1)) <
      Real.exp (paperPrimeCoherentEnergy {p₂, p₃} (fun _ => 1)) :=
  Real.exp_lt_exp.mpr paperPrimeCoherentEnergy_two_three_interference

end
end RHTower

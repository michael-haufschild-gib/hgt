import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities.Channels
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Isometry

/-! # Conservation of the prime-dependent routing experiment -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities

open Finset CoassociativeSplitting

private theorem two_row (s : ℂ) (u v : ℕ → ℝ) :
    shell (kernel s u v) 2=shell (amplitude s (u 2) (v 2)) 2 := by
  let p : Nat.Primes := ⟨2,Nat.prime_two⟩
  have ray (j k : ℕ) := branch_on_ray u v p j k
  have first : branch u v 1 2=probability (u 2) (v 2) 1 2 := by simpa [p] using ray 0 1
  have last : branch u v 2 1=probability (u 2) (v 2) 2 1 := by simpa [p] using ray 1 0
  funext x
  by_cases h : x.1*x.2=2
  · have prod : x.1.val*x.2.val=2 := congrArg PNat.val h
    obtain a|a := Nat.prime_two.eq_one_or_self_of_dvd x.1.val ⟨x.2.val,prod.symm⟩
    · have b : x.2.val=2 := by simpa only [a,one_mul] using prod
      simp only [shell,if_pos h,kernel,amplitude,a,b,first]
    · have b : x.2.val=1 := by rw [a] at prod; omega
      simp only [shell,if_pos h,kernel,amplitude,a,b,last]
  · simp only [shell,if_neg h]

/-- Even when capacities are chosen separately for each prime, a single
prime shell determines the unique full-space isometry line. -/
theorem conserving_iff (s : ℂ) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) :
    isometric (kernel s u v) ↔ s.re=1/2 := by
  rw [CoassociativeSplitting.isometric_iff]
  constructor
  · intro normed
    have H := normed 2
    rw [two_row] at H
    exact (shell_iff s (hu ⟨2,Nat.prime_two⟩) (hv ⟨2,Nat.prime_two⟩) 2 (by norm_num)).mp H
  · intro re n
    have H := finite_shell (kernel s u v) n
    simp only [kernel_norm s hu hv,show 2*s.re=1 by linarith only [re],Real.rpow_one] at H
    change HasSum _ (∑ d : n.val.divisorsAntidiagonal, branch u v d.val.1 d.val.2) at H
    rwa [univ_eq_attach,sum_attach _ (fun d : ℕ × ℕ => branch u v d.1 d.2),branch_sum hu hv] at H

#print axioms conserving_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities

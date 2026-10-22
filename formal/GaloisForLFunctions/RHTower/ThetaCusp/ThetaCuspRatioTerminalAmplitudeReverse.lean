import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioTerminalAmplitudePolynomial
import Mathlib.Algebra.Polynomial.Reverse

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section

theorem amplitudePoly_degree (n : ℕ) : (amplitudePoly n).natDegree≤n := by
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (amplitudePoly_coeff_above n)

def amplitudeReverse (n : ℕ) : Polynomial ℂ := (amplitudePoly n).reflect n
def amplitudeNextExact (n : ℕ) : ℂ := amplitudeNext n-if n=0 then 3 else 0
def amplitudeThirdExact (n : ℕ) : ℂ := amplitudeThird n-if n=1 then 15/4 else 0

theorem amplitudeReverse_zero (n : ℕ) : (amplitudeReverse n).coeff 0=2 := by
  simp [amplitudeReverse,amplitudePoly_coeff_top]

theorem amplitudeReverse_one (n : ℕ) :
    (amplitudeReverse n).coeff 1=amplitudeNextExact n := by
  cases n with
  | zero => norm_num [amplitudeReverse,amplitudePoly,amplitudeNextExact,amplitudeNext,
      Polynomial.revAt]
  | succ n =>
    rw [amplitudeReverse,Polynomial.coeff_reflect,
      Polynomial.revAt_le (show 1≤n+1 by omega)]
    simpa [amplitudeNextExact] using amplitudePoly_coeff_next n

theorem amplitudeReverse_two (n : ℕ) :
    (amplitudeReverse n).coeff 2=amplitudeThirdExact n := by
  cases n with
  | zero => norm_num [amplitudeReverse,amplitudePoly,amplitudeThirdExact,amplitudeThird,
      Polynomial.revAt]
  | succ n =>
    cases n with
    | zero => norm_num [amplitudeReverse,amplitudePoly,amplitudeThirdExact,amplitudeThird,
        Polynomial.revAt,add_mul,Polynomial.coeff_X]
    | succ n =>
      rw [amplitudeReverse,Polynomial.coeff_reflect,
        Polynomial.revAt_le (show 2≤n+1+1 by omega)]
      simpa [amplitudeThirdExact,Nat.add_assoc] using amplitudePoly_coeff_third n

theorem amplitude_product_reverse (i j : ℕ) :
    (amplitudePoly i*amplitudePoly j).reflect (i+j)=
      amplitudeReverse i*amplitudeReverse j := by
  exact Polynomial.reflect_mul _ _ (amplitudePoly_degree i) (amplitudePoly_degree j)

theorem amplitude_product_top (i j : ℕ) :
    (amplitudePoly i*amplitudePoly j).coeff (i+j)=4 := by
  have h := congrArg (fun P : Polynomial ℂ => P.coeff 0)
    (amplitude_product_reverse i j)
  norm_num [Polynomial.revAt_zero,amplitudeReverse_zero] at h
  exact h

theorem amplitude_product_next (i j : ℕ) (hn : 1 ≤ i + j) :
    (amplitudePoly i*amplitudePoly j).coeff (i+j-1)=
      2*(amplitudeNextExact i+amplitudeNextExact j) := by
  have h := congrArg (fun P : Polynomial ℂ => P.coeff 1)
    (amplitude_product_reverse i j)
  rw [Polynomial.coeff_reflect,Polynomial.revAt_le hn,Polynomial.mul_coeff_one,
    amplitudeReverse_zero,amplitudeReverse_zero,amplitudeReverse_one,
    amplitudeReverse_one] at h
  linear_combination h

theorem amplitude_product_third (i j : ℕ) (hn : 2 ≤ i + j) :
    (amplitudePoly i*amplitudePoly j).coeff (i+j-2)=
      2*(amplitudeThirdExact i+amplitudeThirdExact j)+
        amplitudeNextExact i*amplitudeNextExact j := by
  have h := congrArg (fun P : Polynomial ℂ => P.coeff 2)
    (amplitude_product_reverse i j)
  rw [Polynomial.coeff_reflect,Polynomial.revAt_le hn,
    Polynomial.coeff_mul (amplitudeReverse i) (amplitudeReverse j) 2] at h
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun r s => (amplitudeReverse i).coeff r*(amplitudeReverse j).coeff s) 2] at h
  norm_num [Finset.sum_range_succ,amplitudeReverse_zero,amplitudeReverse_one,
    amplitudeReverse_two] at h
  linear_combination h

end
end HTGeometry.ThetaRatioSource.TerminalKinetic

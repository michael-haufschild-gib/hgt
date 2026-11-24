import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.CompositionBoundary.NaturalBoundary
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.CompositionBoundary.UnitCircleZeros
import GaloisForLFunctions.ArithmeticIncidencePositivity.BiLatticeTrainWitness

/-! # All convergent zeros of the prepared prime response -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open _root_.RHTower.PrimeCoShift

/-- Spacing in clock time between successive zeros. -/
def primeZeroSpacing (p : Nat.Primes) := Real.pi/(2*energy (primePNat p))

theorem primeZeroSpacing_pos (p : Nat.Primes) : 0 < primeZeroSpacing p :=
  div_pos Real.pi_pos (mul_pos (by norm_num) (prime_energy_pos p))

def primeZeroPoint (p : Nat.Primes) (j : ℤ) : ℂ :=
  ((1/2:ℝ):ℂ) + ((((j:ℝ)+1/2)*primeZeroSpacing p:ℝ):ℂ)*Complex.I

theorem primeZeroPoint_re (p : Nat.Primes) (j : ℤ) : (primeZeroPoint p j).re = 1/2 := by
  simp [primeZeroPoint]

private theorem square_clock_iff (p : Nat.Primes) (s : ℂ) :
    compositionClock p s^2 = -1 ↔ ∃ j : ℤ, s = primeZeroPoint p j := by
  let L : ℂ := energy (primePNat p)
  have hL : L ≠ 0 := Complex.ofReal_ne_zero.mpr (prime_energy_pos p).ne'
  change Complex.exp ((2*s-1)*L)^2 = -1 ↔ _
  rw [← Complex.exp_nat_mul,← Complex.exp_pi_mul_I,Complex.exp_eq_exp_iff_exists_int]
  have point (j : ℤ) : primeZeroPoint p j = 1/2+((j:ℂ)+1/2)*((Real.pi:ℂ)/(2*L))*Complex.I := by
    unfold primeZeroPoint primeZeroSpacing
    push_cast
    rfl
  constructor
  · rintro ⟨j,hj⟩
    refine ⟨j,?_⟩
    rw [point]
    change 2*((2*s-1)*L) = (Real.pi:ℂ)*Complex.I+(j:ℂ)*(2*(Real.pi:ℂ)*Complex.I) at hj
    calc
      s = (2*((2*s-1)*L)+2*L)/(4*L) := by field_simp [hL]; ring
      _ = _ := by rw [hj]; field_simp [hL]; ring
  · rintro ⟨j,rfl⟩
    refine ⟨j,?_⟩
    rw [point]
    push_cast
    field_simp [hL]
    ring

/-- All actual zeros of this response are noncontinuable finite boundary values at odd half-spacings. -/
theorem lacunary_zero_iff (p : Nat.Primes) (s : ℂ) :
    (finiteSplit (lacunaryOmission p) s ∧ compositionResponse (lacunaryOmission p) s = 0) ↔
      ∃ j : ℤ, s = primeZeroPoint p j := by
  have hn (hs : 1/2 ≤ s.re) : 1 ≤ ‖compositionClock p s‖ := by
    rw [compositionClock_norm,Real.one_le_exp_iff]
    exact mul_nonneg (by linarith only [hs]) (prime_energy_pos p).le
  have he (hs : 1/2 ≤ s.re) : compositionResponse (lacunaryOmission p) s = U0.u0 (compositionClock p s) :=
    (lacunary_response_eq p hs).trans (congrArg U0.u0 (compositionClock_heat p s))
  constructor
  · rintro ⟨hf,hz⟩
    have hs := (lacunary_split_iff p s).mp hf
    exact (square_clock_iff p s).mp ((companion_zero_iff (hn hs)).mp ((he hs).symm.trans hz))
  · intro h
    have hs : 1/2 ≤ s.re := by obtain ⟨j,rfl⟩ := h; exact (primeZeroPoint_re p j).ge
    exact ⟨(lacunary_split_iff p s).mpr hs,(he hs).trans ((companion_zero_iff (hn hs)).mpr ((square_clock_iff p s).mpr h))⟩

private theorem primeZeroPoint_im (p : Nat.Primes) (j : ℤ) :
    (primeZeroPoint p j).im = (((j:ℝ)+1/2)/energy (primePNat p))*(Real.pi/2) := by
  simp only [primeZeroPoint,Complex.add_im,Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,
    Complex.I_im,mul_one,zero_mul,add_zero,zero_add,primeZeroSpacing]
  ring

/-- An exact response zero determines its elementary species, even though the union of the zeros is dense on the line. -/
theorem lacunary_zero_prime_unique {p q : Nat.Primes} {s : ℂ}
    (hp : finiteSplit (lacunaryOmission p) s ∧ compositionResponse (lacunaryOmission p) s = 0)
    (hq : finiteSplit (lacunaryOmission q) s ∧ compositionResponse (lacunaryOmission q) s = 0) : p = q := by
  obtain ⟨j,hj⟩ := (lacunary_zero_iff p s).mp hp
  obtain ⟨k,hk⟩ := (lacunary_zero_iff q s).mp hq
  have ht := congrArg Complex.im (hj.symm.trans hk)
  rw [primeZeroPoint_im,primeZeroPoint_im] at ht
  have hc := (div_eq_div_iff (prime_energy_pos p).ne' (prime_energy_pos q).ne').mp
    (mul_right_cancel₀ (half_pos Real.pi_pos).ne' ht)
  by_contra hne
  have hcoef : ((-(2*k+1):ℤ):ℝ)*Real.log (p:ℕ)+((2*j+1:ℤ):ℝ)*Real.log (q:ℕ) = 0 := by
    change ((-(2*k+1):ℤ):ℝ)*energy (primePNat p)+((2*j+1:ℤ):ℝ)*energy (primePNat q) = 0
    push_cast
    linear_combination 2*hc
  have h := ArithmeticIncidencePositivity.logPrime_pair_independent p.property q.property
    (fun e => hne (Subtype.ext e)) _ _ hcoef
  omega

#print axioms lacunary_zero_prime_unique
#print axioms primeZeroSpacing_pos
#print axioms primeZeroPoint_re
#print axioms lacunary_zero_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

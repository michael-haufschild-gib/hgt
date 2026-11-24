import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RapidZeros.ClockReadout
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.CompositionBoundary.ClockZeros

/-! # Prescribed antipodal times of repeated prime insertions -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology
open _root_.RHTower.PrimeCoShift

/-- A block of j+1 quanta of the specified elementary species. -/
def resonantBlock (p : Nat.Primes) (j : ℕ) := primeRayLabel p (j+1)

/-- Time of a half-turn for the inserted block. -/
def resonantTime (p : Nat.Primes) (j : ℕ) := primeZeroSpacing p/((j:ℝ)+1)

theorem resonantTime_pos (p : Nat.Primes) (j : ℕ) : 0 < resonantTime p j :=
  div_pos (primeZeroSpacing_pos p) (by positivity)

theorem resonantTime_tendsto (p : Nat.Primes) : Tendsto (resonantTime p) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (primeZeroSpacing p)
  change Tendsto (fun j : ℕ => primeZeroSpacing p/((j:ℝ)+1)) atTop (𝓝 0)
  simpa only [mul_one_div,mul_zero] using h

theorem resonantBlock_escapes (p : Nat.Primes) (n : ℕ+) :
    ∀ᶠ j in atTop, (n:ℕ) < (resonantBlock p j).val := by
  filter_upwards [eventually_gt_atTop (n:ℕ)] with j hj
  change (n:ℕ) < (p:ℕ)^(j+1)
  exact (hj.trans (Nat.lt_succ_self j)).trans (Nat.lt_pow_self p.property.one_lt)

/-- At the prescribed time destructive interference is independent of the initial state. -/
theorem resonantBlock_phase (p : Nat.Primes) (j : ℕ) :
    splitPhase (resonantTime p j) (resonantBlock p j) = -1 := by
  have he : -2*resonantTime p j*energy (resonantBlock p j) = -Real.pi := by
    rw [resonantBlock,energy_primeRayLabel,resonantTime,primeZeroSpacing,Nat.cast_add,Nat.cast_one]
    field_simp [(prime_energy_pos p).ne',show (j:ℝ)+1 ≠ 0 by positivity]
  rw [splitPhase_eq_exp,he,Complex.ofReal_neg,neg_mul,Complex.exp_neg,Complex.exp_pi_mul_I,inv_neg,inv_one]

#print axioms resonantTime_pos
#print axioms resonantTime_tendsto
#print axioms resonantBlock_escapes
#print axioms resonantBlock_phase

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

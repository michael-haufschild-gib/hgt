import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.ClockAliases
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.Selections
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CoherentShiftReadings

/-! # Equilibrium thermometry and the zeta partition from two return events -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open _root_.RHTower.PrimeCoShift
local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Born probability of the clock's return in a normalized Gibbs-amplitude vector. -/
def gibbsClockReturn (χ : ℕ+ → Circle) (β : TraceTemperature) (p : Nat.Primes) (D : ℕ+) : ℝ :=
  selectedMass (fun n => ‖coherentVector χ β n‖^2) (fun n => occupationPhase (primeClockTime p D) n = 1)

/-- Boltzmann weight for a whole block of prime quanta. -/
def gibbsBlockRatio (β : TraceTemperature) (p : Nat.Primes) (D : ℕ+) : ℝ :=
  Real.exp (-β.val*((D.val:ℝ)*energy (primePNat p)))

private theorem ratio_lt (β : TraceTemperature) (p : Nat.Primes) (D : ℕ+) : gibbsBlockRatio β p D < 1 := by
  apply Real.exp_lt_one_iff.mpr
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (zero_lt_one.trans β.property))
    (mul_pos (Nat.cast_pos.mpr D.pos) (prime_energy_pos p))

private theorem zeta_real_pos (β : TraceTemperature) : 0 < (riemannZeta β.val).re := by
  rw [← thermalWeight_partition,Complex.ofReal_re]
  exact (thermalWeight_pos β 1).trans_le ((thermalWeight_summable β).le_tsum 1 (fun n _ => (thermalWeight_pos β n).le))

/-- The return fiber is a geometric ladder of energies; the denominator retains the full gas trace. -/
theorem gibbsClockReturn_eq (χ : ℕ+ → Circle) (β : TraceTemperature) (p : Nat.Primes) (D : ℕ+) :
    gibbsClockReturn χ β p D = (1 - gibbsBlockRatio β p D)⁻¹ / (riemannZeta β.val).re := by
  let A (k : ℕ) := primeRayLabel p (k*D.val)
  let f (n : ℕ+) := if occupationPhase (primeClockTime p D) n = 1 then ‖coherentVector χ β n‖^2 else 0
  have hinj : Function.Injective A := fun _ _ h => Nat.mul_right_cancel D.pos (primeRayLabel_injective p h)
  have hf (n : ℕ+) : occupationPhase (primeClockTime p D) n = 1 ↔ n ∈ Set.range A := by
    rw [primeClock_phase_one]
    constructor
    · rintro ⟨e,rfl,k,rfl⟩
      exact ⟨k,by simp only [A,Nat.mul_comm]⟩
    · rintro ⟨k,rfl⟩
      exact ⟨k*D.val,rfl,dvd_mul_left _ _⟩
  have hsupport : Function.support f ⊆ Set.range A := by
    intro n hn
    by_contra h
    exact hn (if_neg (mt (hf n).mp h))
  change ∑' n, f n = _
  rw [← hinj.tsum_eq hsupport]
  have hterm (k : ℕ) : f (A k) = gibbsBlockRatio β p D ^ k / (riemannZeta β.val).re := by
    rw [show f (A k) = ‖coherentVector χ β (A k)‖^2 from if_pos ((hf _).mpr ⟨k,rfl⟩),coherentVector_shell]
    congr 1
    dsimp only [A]
    rw [thermalWeight,energy_primeRayLabel,gibbsBlockRatio,← Real.exp_nat_mul,Nat.cast_mul]
    congr 1
    ring
  simp_rw [hterm]
  have hr : 0 ≤ gibbsBlockRatio β p D := (Real.exp_pos _).le
  rw [tsum_div_const,tsum_geometric_of_lt_one hr (ratio_lt β p D)]

/-- One and two block turns separate the local Boltzmann factor from the unknown partition function. -/
theorem gibbsClockReturn_ratio (χ : ℕ+ → Circle) (β : TraceTemperature) (p : Nat.Primes) :
    gibbsClockReturn χ β p 1 / gibbsClockReturn χ β p 2 = 1 + gibbsBlockRatio β p 1 := by
  have he : gibbsBlockRatio β p 2 = (gibbsBlockRatio β p 1)^2 := by
    rw [gibbsBlockRatio,gibbsBlockRatio,sq,← Real.exp_add]
    congr 1
    norm_num
    ring
  have h₁ := (sub_pos.mpr (ratio_lt β p 1)).ne'
  have h₂ := (sub_pos.mpr (ratio_lt β p 2)).ne'
  rw [he] at h₂
  rw [gibbsClockReturn_eq,gibbsClockReturn_eq,he]
  field_simp [h₁,h₂,(zeta_real_pos β).ne']
  ring

/-- Two return readings give the inverse temperature explicitly. -/
theorem gibbsClockReturn_temperature (χ : ℕ+ → Circle) (β : TraceTemperature) (p : Nat.Primes) :
    -Real.log (gibbsClockReturn χ β p 1 / gibbsClockReturn χ β p 2 - 1) / energy (primePNat p) = β.val := by
  rw [gibbsClockReturn_ratio,add_sub_cancel_left,gibbsBlockRatio,Real.log_exp]
  have h₁ : ((1:ℕ+).val:ℝ) = 1 := by norm_num
  rw [h₁,one_mul,neg_mul,neg_neg,mul_div_cancel_right₀ _ (prime_energy_pos p).ne']

/-- The same two probabilities give the absolute partition function of all occupations. -/
theorem gibbsClockReturn_partition (χ : ℕ+ → Circle) (β : TraceTemperature) (p : Nat.Primes) :
    (gibbsClockReturn χ β p 1 *
      (2 - gibbsClockReturn χ β p 1 / gibbsClockReturn χ β p 2))⁻¹ = (riemannZeta β.val).re := by
  rw [gibbsClockReturn_ratio,gibbsClockReturn_eq]
  have h : 2 - (1 + gibbsBlockRatio β p 1) = 1 - gibbsBlockRatio β p 1 := by ring
  rw [h]
  field_simp [(sub_pos.mpr (ratio_lt β p 1)).ne',(zeta_real_pos β).ne']

#print axioms gibbsClockReturn_eq
#print axioms gibbsClockReturn_ratio
#print axioms gibbsClockReturn_temperature
#print axioms gibbsClockReturn_partition

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

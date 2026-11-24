import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.Calibration.BlockDeletion

/-! # Gibbs returns with a finite independent energy level -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open _root_.RHTower.PrimeCoShift
local instance spectatorEventDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- Sum over the spectator vacuum and each of its distinguished excited states.
The total arithmetic label of an excited state over occupation `n` is `q*n`. -/
def spectatorSum (q : Nat.Primes) (g : ℕ) (w : ℕ+ → ℝ) : ℝ :=
  (∑' n, w n) + ∑ _i : Fin g, ∑' n, w (primePNat q * n)

/-- Partition of the finite spectator alone. -/
def spectatorWeight (β : TraceTemperature) (q : Nat.Primes) (g : ℕ) : ℝ :=
  1 + g * thermalWeight β (primePNat q)

theorem spectatorWeight_pos (β : TraceTemperature) (q : Nat.Primes) (g : ℕ) :
    0 < spectatorWeight β q g :=
  add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (Nat.cast_nonneg _) (thermalWeight_pos β _).le)

/-- The actual sum over both independent sets of occupations factors. -/
theorem spectatorPartition_eq (β : TraceTemperature) (q : Nat.Primes) (g : ℕ) :
    spectatorSum q g (thermalWeight β) = spectatorWeight β q g * (riemannZeta β.val).re := by
  have hz : (∑' n, thermalWeight β n) = (riemannZeta β.val).re :=
    congrArg Complex.re (thermalWeight_partition β)
  have hw (n : ℕ+) : thermalWeight β (primePNat q*n) =
      thermalWeight β (primePNat q) * thermalWeight β n := by
    rw [thermalWeight,energy_mul,mul_add,Real.exp_add]
    rfl
  unfold spectatorSum spectatorWeight
  simp only [hw,tsum_mul_left,hz,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

/-- A foreign prime factor rules out every phase-one occupation of a prime clock. -/
theorem foreignPrime_no_return {p q : Nat.Primes} (hpq : p ≠ q) (D n : ℕ+) :
    occupationPhase (primeClockTime p D) (primePNat q*n) ≠ 1 := by
  intro h
  obtain ⟨k,hk,_⟩ := (primeClock_phase_one p D _).mp h
  have hd : q.val ∣ p.val^k := ⟨n.val,(congrArg PNat.val hk).symm⟩
  exact hpq (Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.property p.property).mp
    (q.property.dvd_of_dvd_pow hd)).symm)

/-- Equilibrium probability of observing phase one on the combined gas. -/
def spectatorReturn (β : TraceTemperature) (p : Nat.Primes) (D : ℕ+) (q : Nat.Primes) (g : ℕ) : ℝ :=
  spectatorSum q g (fun n => if occupationPhase (primeClockTime p D) n = 1 then thermalWeight β n else 0) /
    spectatorSum q g (thermalWeight β)

/-- Only the spectator vacuum contributes to the return numerator. -/
theorem spectatorReturn_eq (χ : ℕ+ → Circle) (β : TraceTemperature) {p q : Nat.Primes}
    (hpq : p ≠ q) (D : ℕ+) (g : ℕ) :
    spectatorReturn β p D q g = gibbsClockReturn χ β p D / spectatorWeight β q g := by
  let P := fun n => occupationPhase (primeClockTime p D) n = 1
  have hb : gibbsClockReturn χ β p D = selectedMass (thermalWeight β) P / (riemannZeta β.val).re := by
    unfold gibbsClockReturn selectedMass
    rw [← tsum_div_const]
    apply tsum_congr
    intro n
    by_cases h : P n
    · simp only [P] at h
      simp only [P,if_pos h,coherentVector_shell]
    · simp only [P] at h
      simp only [P,if_neg h,zero_div]
  rw [spectatorReturn,spectatorPartition_eq,hb]
  simp only [spectatorSum,if_neg (foreignPrime_no_return hpq D _),tsum_zero,Finset.sum_const_zero,add_zero]
  change selectedMass (thermalWeight β) P / _ = _
  rw [div_div,mul_comm (spectatorWeight β q g)]

/-- Ratios between any two harmonics of the same clock are insensitive to the spectator. -/
theorem spectatorReturn_ratio (χ : ℕ+ → Circle) (β : TraceTemperature) {p q : Nat.Primes}
    (hpq : p ≠ q) (D E : ℕ+) (g : ℕ) :
    spectatorReturn β p D q g / spectatorReturn β p E q g =
      gibbsClockReturn χ β p D / gibbsClockReturn χ β p E := by
  rw [spectatorReturn_eq χ β hpq D,spectatorReturn_eq χ β hpq E]
  exact div_div_div_cancel_right₀ (spectatorWeight_pos β q g).ne' _ _

#print axioms spectatorWeight_pos
#print axioms spectatorPartition_eq
#print axioms foreignPrime_no_return
#print axioms spectatorReturn_eq
#print axioms spectatorReturn_ratio

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

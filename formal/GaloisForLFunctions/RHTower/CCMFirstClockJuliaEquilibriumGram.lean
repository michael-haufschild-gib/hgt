import GaloisForLFunctions.RHTower.GammaSewnMobiusJuliaPrimeOrderAttenuation
import GaloisForLFunctions.HTGeometry.CharacteristicDefectGramCapacity

/-!
# Coherent Julia equilibrium Gram on the reduced CCM first clock

The reduced first-clock source is a literal continuous-positive-plus-prime-good-minus-prime-bad
functional.  Earlier Julia transport multiplied each prime tower by one diagonal attenuation
factor.  This file identifies those diagonal factors as origin correlations of the canonical
Julia equilibrium kernel and restores the missing cross-prime Gram.

For every finite prime packet, the Julia-deformed completed source is exactly its correlation
with the origin.  Source-level compound-Poisson positivity bounds the square of the bad origin
correlation by its full coherent cross-prime energy.  Consequently any negative deformed completed
source forces at least its squared excursion into the outer-prime coherent energy.  This is the
positive replacement demanded by the independent-prime harmonic capacity obstruction: bad mass
cannot be treated as a collection of unrelated scalar channels.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- One prime's nonnegative term in the reduced first-clock good source. -/
def ccmFirstClockReducedGoodPrimeTerm (L : ℝ) (p : Nat.Primes) : ℝ :=
  ccmFirstClockStableTowerTerm L p +
    ccmFirstClockSmallSquarePositiveTerm L p

/-- One prime's nonnegative term in the reduced first-clock bad residual. -/
def ccmFirstClockReducedBadPrimeTerm (L : ℝ) (p : Nat.Primes) : ℝ :=
  if ccmFirstClockPrimePowerLength L p = 1 then
    -ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) p
  else if ccmFirstClockPrimePowerLength L p = 2 ∧ (p : ℕ) < 5 then
    max (-ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) p) 0
  else
    0

/-- Literal cellwise reduced decomposition on every admitted prime. -/
theorem ccmFirstClockPrimePowerTowerMass_eq_reducedGoodPrimeTerm_sub_bad
    {L : ℝ} (p : Nat.Primes)
    (hpCut : (p : ℕ) ≤ ⌊Real.exp L⌋₊) :
    ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) p =
      ccmFirstClockReducedGoodPrimeTerm L p -
        ccmFirstClockReducedBadPrimeTerm L p := by
  exact ccmFirstClockPrimePowerTowerTerm_eq_reducedGood_sub_bad
    ((Nat.mem_primesLE).2 ⟨hpCut, p.property⟩)

theorem ccmFirstClockReducedGoodPrimeTerm_nonneg
    {L : ℝ} (hL : 0 < L) (p : Nat.Primes)
    (hpCut : (p : ℕ) ≤ ⌊Real.exp L⌋₊) :
    0 ≤ ccmFirstClockReducedGoodPrimeTerm L p := by
  rw [ccmFirstClockReducedGoodPrimeTerm]
  apply add_nonneg
  · rw [ccmFirstClockStableTowerTerm]
    split_ifs with hstable
    · rcases hstable with hthree | ⟨htwo, hpFive⟩
      · exact
          (ccmFirstClockPrimePowerTowerMass_firstClock_pos_of_three_le
            hL p.property hpCut hthree).le
      · exact
          ccmFirstClockPrimePowerTowerMass_firstClock_nonneg_of_length_two_of_five_le
            hL p.property hpCut htwo hpFive
    · exact le_rfl
  · rw [ccmFirstClockSmallSquarePositiveTerm]
    split_ifs
    · exact le_max_right _ _
    · exact le_rfl

theorem ccmFirstClockReducedBadPrimeTerm_nonneg
    {L : ℝ} (hL : 0 < L) (p : Nat.Primes)
    (hpCut : (p : ℕ) ≤ ⌊Real.exp L⌋₊) :
    0 ≤ ccmFirstClockReducedBadPrimeTerm L p := by
  rw [ccmFirstClockReducedBadPrimeTerm]
  split_ifs with hOne hSmall
  · exact neg_nonneg.mpr
      (ccmFirstClockPrimePowerTowerMass_firstClock_nonpos_of_length_one
        hL p.property hpCut hOne)
  · exact le_max_right _ _
  · exact le_rfl

/-- Arithmetic Julia attenuation is exactly the equilibrium kernel's correlation with the
origin at the scaled prime logarithm. -/
theorem gammaSewnMobiusJuliaPrimeAttenuation_eq_equilibriumKernel
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    gammaSewnMobiusJuliaPrimeAttenuation x p =
      HTGeometry.juliaDefectAttenuationKernel
        (x * Real.log (p : ℝ)) := by
  have hpLog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.property.one_lt)).ne'
  rw [gammaSewnMobiusJuliaPrimeAttenuation_eq_profile hx,
    HTGeometry.juliaDefectAttenuationKernel_eq_profile
      (mul_ne_zero hx.ne' hpLog)]

/-- Good reduced prime source correlated with the Julia equilibrium origin. -/
def ccmFirstClockJuliaGoodOriginCorrelation
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) : ℝ :=
  ∑ i, HTGeometry.juliaDefectAttenuationKernel
      (x * Real.log (p i : ℝ)) *
    ccmFirstClockReducedGoodPrimeTerm L (p i)

/-- Bad reduced prime source correlated with the Julia equilibrium origin. -/
def ccmFirstClockJuliaBadOriginCorrelation
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) : ℝ :=
  ∑ i, HTGeometry.juliaDefectAttenuationKernel
      (x * Real.log (p i : ℝ)) *
    ccmFirstClockReducedBadPrimeTerm L (p i)

/-- Full continuous-plus-reduced-prime Julia origin correlation.  Continuous reflection budget
sits at the origin, hence receives the normalized diagonal value one. -/
def ccmFirstClockJuliaCompletedOriginCorrelation
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) : ℝ :=
  ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) +
    ccmFirstClockJuliaGoodOriginCorrelation x L p -
      ccmFirstClockJuliaBadOriginCorrelation x L p

/-- Literal diagonally Julia-attenuated version of the completed reduced first-clock packet. -/
def ccmFirstClockJuliaAttenuatedCompletedPacket
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) : ℝ :=
  ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) +
    ∑ i, gammaSewnMobiusJuliaPrimeAttenuation x (p i) *
      ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) (p i)

/-- **Exact source action.**  On every admitted finite prime packet, diagonal Julia attenuation
is the origin column of the full equilibrium Gram acting on the literal reduced
good-minus-bad source. -/
theorem ccmFirstClockJuliaAttenuatedCompletedPacket_eq_originCorrelation
    {N : ℕ} {x L : ℝ} (hx : 0 < x) (p : Fin N → Nat.Primes)
    (hpCut : ∀ i, (p i : ℕ) ≤ ⌊Real.exp L⌋₊) :
    ccmFirstClockJuliaAttenuatedCompletedPacket x L p =
      ccmFirstClockJuliaCompletedOriginCorrelation x L p := by
  have hprime :
    (∑ i, gammaSewnMobiusJuliaPrimeAttenuation x (p i) *
        ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) (p i)) =
      ccmFirstClockJuliaGoodOriginCorrelation x L p -
        ccmFirstClockJuliaBadOriginCorrelation x L p := by
    calc
      _ = ∑ i, gammaSewnMobiusJuliaPrimeAttenuation x (p i) *
          (ccmFirstClockReducedGoodPrimeTerm L (p i) -
            ccmFirstClockReducedBadPrimeTerm L (p i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [ccmFirstClockPrimePowerTowerMass_eq_reducedGoodPrimeTerm_sub_bad
          (p i) (hpCut i)]
    _ = (∑ i, gammaSewnMobiusJuliaPrimeAttenuation x (p i) *
          ccmFirstClockReducedGoodPrimeTerm L (p i)) -
        ∑ i, gammaSewnMobiusJuliaPrimeAttenuation x (p i) *
          ccmFirstClockReducedBadPrimeTerm L (p i) := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
    _ = ccmFirstClockJuliaGoodOriginCorrelation x L p -
        ccmFirstClockJuliaBadOriginCorrelation x L p := by
        unfold ccmFirstClockJuliaGoodOriginCorrelation
          ccmFirstClockJuliaBadOriginCorrelation
        congr 1 <;> apply Finset.sum_congr rfl <;> intro i _
        all_goals
          rw [gammaSewnMobiusJuliaPrimeAttenuation_eq_equilibriumKernel hx]
  rw [ccmFirstClockJuliaAttenuatedCompletedPacket,
    ccmFirstClockJuliaCompletedOriginCorrelation, hprime]
  ring

/-- Coherent cross-prime energy carried by the reduced bad first-clock source. -/
def ccmFirstClockJuliaBadCoherentEnergy
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) : ℝ :=
  ∑ i, ∑ j,
    ccmFirstClockReducedBadPrimeTerm L (p i) *
      HTGeometry.juliaDefectAttenuationKernel
        (x * Real.log (p j : ℝ) - x * Real.log (p i : ℝ)) *
      ccmFirstClockReducedBadPrimeTerm L (p j)

/-- The coherent Julia energy is bounded by the square of total bad mass. -/
theorem ccmFirstClockJuliaBadCoherentEnergy_le_totalBadMass_sq
    {N : ℕ} {x L : ℝ} (hL : 0 < L) (p : Fin N → Nat.Primes)
    (hpCut : ∀ i, (p i : ℕ) ≤ ⌊Real.exp L⌋₊) :
    ccmFirstClockJuliaBadCoherentEnergy x L p ≤
      (∑ i, ccmFirstClockReducedBadPrimeTerm L (p i)) ^ (2 : ℕ) := by
  rw [ccmFirstClockJuliaBadCoherentEnergy]
  calc
    (∑ i, ∑ j,
        ccmFirstClockReducedBadPrimeTerm L (p i) *
          HTGeometry.juliaDefectAttenuationKernel
            (x * Real.log (p j : ℝ) - x * Real.log (p i : ℝ)) *
          ccmFirstClockReducedBadPrimeTerm L (p j)) ≤
        ∑ i, ∑ j,
          ccmFirstClockReducedBadPrimeTerm L (p i) * 1 *
            ccmFirstClockReducedBadPrimeTerm L (p j) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (HTGeometry.juliaDefectAttenuationKernel_le_one _)
          (ccmFirstClockReducedBadPrimeTerm_nonneg hL (p i) (hpCut i)))
        (ccmFirstClockReducedBadPrimeTerm_nonneg hL (p j) (hpCut j))
    _ = (∑ i, ccmFirstClockReducedBadPrimeTerm L (p i)) ^ (2 : ℕ) := by
      simp only [mul_one]
      calc
        (∑ i, ∑ j,
            ccmFirstClockReducedBadPrimeTerm L (p i) *
              ccmFirstClockReducedBadPrimeTerm L (p j)) =
            ∑ i, ccmFirstClockReducedBadPrimeTerm L (p i) *
              ∑ j, ccmFirstClockReducedBadPrimeTerm L (p j) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
        _ = _ := by rw [← Finset.sum_mul, pow_two]

/-- **Coherent bad-channel capacity law.**  The bad origin correlation cannot exceed the full
cross-prime equilibrium Gram energy in square. -/
theorem ccmFirstClockJuliaBadOriginCorrelation_sq_le_coherentEnergy
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) :
    ccmFirstClockJuliaBadOriginCorrelation x L p ^ (2 : ℕ) ≤
      ccmFirstClockJuliaBadCoherentEnergy x L p := by
  simpa only [ccmFirstClockJuliaBadOriginCorrelation,
    ccmFirstClockJuliaBadCoherentEnergy, mul_comm] using
      (HTGeometry.juliaDefectAttenuationKernel_anchorCorrelation_sq_le_gramEnergy
        (fun i => x * Real.log (p i : ℝ))
        (fun i => ccmFirstClockReducedBadPrimeTerm L (p i)))

/-- **Julia bad-channel energy sandwich.**  Origin correlation, coherent cross-prime energy,
and total bad mass form one unconditional hierarchy on every admitted finite packet. -/
theorem ccmFirstClockJulia_badChannel_energySandwich
    {N : ℕ} {x L : ℝ} (hL : 0 < L) (p : Fin N → Nat.Primes)
    (hpCut : ∀ i, (p i : ℕ) ≤ ⌊Real.exp L⌋₊) :
    ccmFirstClockJuliaBadOriginCorrelation x L p ^ (2 : ℕ) ≤
        ccmFirstClockJuliaBadCoherentEnergy x L p ∧
      ccmFirstClockJuliaBadCoherentEnergy x L p ≤
        (∑ i, ccmFirstClockReducedBadPrimeTerm L (p i)) ^ (2 : ℕ) :=
  ⟨ccmFirstClockJuliaBadOriginCorrelation_sq_le_coherentEnergy x L p,
    ccmFirstClockJuliaBadCoherentEnergy_le_totalBadMass_sq hL p hpCut⟩

theorem ccmFirstClockJuliaGoodOriginCorrelation_nonneg
    {N : ℕ} {x L : ℝ} (hL : 0 < L) (p : Fin N → Nat.Primes)
    (hpCut : ∀ i, (p i : ℕ) ≤ ⌊Real.exp L⌋₊) :
    0 ≤ ccmFirstClockJuliaGoodOriginCorrelation x L p := by
  rw [ccmFirstClockJuliaGoodOriginCorrelation]
  exact Finset.sum_nonneg fun i _ => mul_nonneg
    (HTGeometry.juliaDefectAttenuationKernel_pos _).le
    (ccmFirstClockReducedGoodPrimeTerm_nonneg hL (p i) (hpCut i))

theorem ccmFirstClockJuliaBadOriginCorrelation_nonneg
    {N : ℕ} {x L : ℝ} (hL : 0 < L) (p : Fin N → Nat.Primes)
    (hpCut : ∀ i, (p i : ℕ) ≤ ⌊Real.exp L⌋₊) :
    0 ≤ ccmFirstClockJuliaBadOriginCorrelation x L p := by
  rw [ccmFirstClockJuliaBadOriginCorrelation]
  exact Finset.sum_nonneg fun i _ => mul_nonneg
    (HTGeometry.juliaDefectAttenuationKernel_pos _).le
    (ccmFirstClockReducedBadPrimeTerm_nonneg hL (p i) (hpCut i))

/-- **Negative-excursion rigidity.**  Any negative continuous-plus-prime Julia-deformed
first-clock source forces at least its squared excursion into coherent bad-prime energy.  This is
strictly stronger information than the diagonal statement that outer-prime weights are positive. -/
theorem ccmFirstClockJulia_negative_completedSource_forces_badCoherentEnergy
    {N : ℕ} {x L : ℝ} (hL : 0 < L) (p : Fin N → Nat.Primes)
    (hpCut : ∀ i, (p i : ℕ) ≤ ⌊Real.exp L⌋₊)
    (hneg : ccmFirstClockJuliaCompletedOriginCorrelation x L p < 0) :
    ccmFirstClockJuliaCompletedOriginCorrelation x L p ^ (2 : ℕ) ≤
      ccmFirstClockJuliaBadCoherentEnergy x L p := by
  have hperiod : (2 * Real.pi / L) * L = 2 * Real.pi := by
    field_simp
  have hbudget :
      0 < ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) :=
    ccmFirstClockContinuousHalfWaveBudget_pos hL hperiod
  have hgood :
      0 ≤ ccmFirstClockJuliaGoodOriginCorrelation x L p :=
    ccmFirstClockJuliaGoodOriginCorrelation_nonneg hL p hpCut
  have hbad :
      0 ≤ ccmFirstClockJuliaBadOriginCorrelation x L p :=
    ccmFirstClockJuliaBadOriginCorrelation_nonneg hL p hpCut
  have hsourceLeBad :
      -ccmFirstClockJuliaCompletedOriginCorrelation x L p ≤
        ccmFirstClockJuliaBadOriginCorrelation x L p := by
    rw [ccmFirstClockJuliaCompletedOriginCorrelation]
    linarith
  have hsquare :
      ccmFirstClockJuliaCompletedOriginCorrelation x L p ^ (2 : ℕ) ≤
        ccmFirstClockJuliaBadOriginCorrelation x L p ^ (2 : ℕ) := by
    nlinarith
  exact hsquare.trans
    (ccmFirstClockJuliaBadOriginCorrelation_sq_le_coherentEnergy
      x L p)

/-- **Arithmetic-facing coherent-capacity law.**  If the literal Julia-attenuated completed
first-clock packet is negative, its squared excursion is carried by the coherent cross-prime bad
energy.  The auxiliary origin-correlation interface is eliminated using the exact source action. -/
theorem ccmFirstClockJulia_negative_attenuatedCompletedPacket_forces_badCoherentEnergy
    {N : ℕ} {x L : ℝ} (hx : 0 < x) (hL : 0 < L)
    (p : Fin N → Nat.Primes)
    (hpCut : ∀ i, (p i : ℕ) ≤ ⌊Real.exp L⌋₊)
    (hneg : ccmFirstClockJuliaAttenuatedCompletedPacket x L p < 0) :
    ccmFirstClockJuliaAttenuatedCompletedPacket x L p ^ (2 : ℕ) ≤
      ccmFirstClockJuliaBadCoherentEnergy x L p := by
  rw [ccmFirstClockJuliaAttenuatedCompletedPacket_eq_originCorrelation hx p hpCut]
  exact ccmFirstClockJulia_negative_completedSource_forces_badCoherentEnergy
    hL p hpCut (by
      simpa only [ccmFirstClockJuliaAttenuatedCompletedPacket_eq_originCorrelation
        hx p hpCut] using hneg)

/-- Any negative Julia-attenuated completed packet is bounded in magnitude by total bad mass;
the coherent energy is the intermediate certificate. -/
theorem ccmFirstClockJulia_negative_attenuatedCompletedPacket_sq_le_totalBadMass_sq
    {N : ℕ} {x L : ℝ} (hx : 0 < x) (hL : 0 < L)
    (p : Fin N → Nat.Primes)
    (hpCut : ∀ i, (p i : ℕ) ≤ ⌊Real.exp L⌋₊)
    (hneg : ccmFirstClockJuliaAttenuatedCompletedPacket x L p < 0) :
    ccmFirstClockJuliaAttenuatedCompletedPacket x L p ^ (2 : ℕ) ≤
      (∑ i, ccmFirstClockReducedBadPrimeTerm L (p i)) ^ (2 : ℕ) :=
  (ccmFirstClockJulia_negative_attenuatedCompletedPacket_forces_badCoherentEnergy
      hx hL p hpCut hneg).trans
    (ccmFirstClockJuliaBadCoherentEnergy_le_totalBadMass_sq hL p hpCut)

end

end RHTower

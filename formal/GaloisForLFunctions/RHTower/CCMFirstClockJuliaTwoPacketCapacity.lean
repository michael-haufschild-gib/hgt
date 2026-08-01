import GaloisForLFunctions.RHTower.CCMFirstClockJuliaEquilibriumGram

/-!
# Two-packet Julia capacity on the CCM first clock

The Julia equilibrium kernel controls the complete signed prime-power packet, without first
splitting its coefficients into good and bad parts.  Its coherent prime energy and the energy of
the packet augmented by the continuous archimedean budget are therefore nonnegative directly.

For the admitted prime window, the source decomposition identifies that signed energy with good
energy plus bad energy minus twice their mixed correlation.  The universal two-packet Cauchy law
also makes the corresponding two-channel determinant nonnegative.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Origin correlation of the literal first-clock prime-power coefficients. -/
def ccmFirstClockJuliaPrimePowerOriginCorrelation
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) : ℝ :=
  ∑ i, HTGeometry.juliaDefectAttenuationKernel
      (x * Real.log (p i : ℝ)) *
    ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) (p i)

/-- Coherent Julia energy of the literal signed prime-power packet. -/
def ccmFirstClockJuliaPrimePowerCoherentEnergy
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) : ℝ :=
  GaloisForLFunctions.HTGeometry.realKernelPacketEnergy
    HTGeometry.juliaDefectAttenuationKernel
    (fun i => x * Real.log (p i : ℝ))
    (fun i => ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) (p i))

/-- Coherent Julia energy of the archimedean budget and all literal prime-power coefficients. -/
def ccmFirstClockJuliaCompletedCoherentEnergy
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) : ℝ :=
  GaloisForLFunctions.HTGeometry.realKernelPacketEnergy
    HTGeometry.juliaDefectAttenuationKernel
    (Fin.cases 0 (fun i => x * Real.log (p i : ℝ)))
    (Fin.cases (ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L))
      (fun i => ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) (p i)))

/-- Coherent Julia energy of the reduced good prime channel. -/
def ccmFirstClockJuliaGoodCoherentEnergy
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) : ℝ :=
  ∑ i, ∑ j,
    ccmFirstClockReducedGoodPrimeTerm L (p i) *
      HTGeometry.juliaDefectAttenuationKernel
        (x * Real.log (p j : ℝ) - x * Real.log (p i : ℝ)) *
      ccmFirstClockReducedGoodPrimeTerm L (p j)

/-- Mixed Julia correlation of a reduced good packet with a reduced bad packet. -/
def ccmFirstClockJuliaGoodBadCoherentCorrelation
    {N M : ℕ} (x L : ℝ)
    (p : Fin N → Nat.Primes) (q : Fin M → Nat.Primes) : ℝ :=
  ∑ i, ∑ j,
    ccmFirstClockReducedGoodPrimeTerm L (p i) *
      HTGeometry.juliaDefectAttenuationKernel
        (x * Real.log (q j : ℝ) - x * Real.log (p i : ℝ)) *
      ccmFirstClockReducedBadPrimeTerm L (q j)

/-- Arithmetic Julia attenuation is the origin correlation of the literal prime-power packet;
no good/bad decomposition or prime-window cutoff is needed. -/
theorem ccmFirstClockJuliaAttenuatedCompletedPacket_eq_continuousBudget_add_primePowerOrigin
    {N : ℕ} {x : ℝ} (hx : 0 < x) (L : ℝ) (p : Fin N → Nat.Primes) :
    ccmFirstClockJuliaAttenuatedCompletedPacket x L p =
      ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) +
        ccmFirstClockJuliaPrimePowerOriginCorrelation x L p := by
  rw [ccmFirstClockJuliaAttenuatedCompletedPacket,
    ccmFirstClockJuliaPrimePowerOriginCorrelation]
  apply congrArg (fun z => ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) + z)
  apply Finset.sum_congr rfl
  intro i _
  rw [gammaSewnMobiusJuliaPrimeAttenuation_eq_equilibriumKernel hx]
  ring

/-- The literal signed prime-power packet has nonnegative coherent Julia energy. -/
theorem ccmFirstClockJuliaPrimePowerCoherentEnergy_nonneg
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) :
    0 ≤ ccmFirstClockJuliaPrimePowerCoherentEnergy x L p := by
  exact GaloisForLFunctions.HTGeometry.realKernelPacketEnergy_nonneg_of_positiveDefinite
    HTGeometry.juliaDefectAttenuationKernel
    HTGeometry.positiveDefiniteOnReal_juliaDefectAttenuationKernel _ _

/-- The archimedean-plus-prime packet has nonnegative coherent Julia energy. -/
theorem ccmFirstClockJuliaCompletedCoherentEnergy_nonneg
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) :
    0 ≤ ccmFirstClockJuliaCompletedCoherentEnergy x L p := by
  exact GaloisForLFunctions.HTGeometry.realKernelPacketEnergy_nonneg_of_positiveDefinite
    HTGeometry.juliaDefectAttenuationKernel
    HTGeometry.positiveDefiniteOnReal_juliaDefectAttenuationKernel _ _

/-- Exact archimedean/prime decomposition of complete coherent energy. -/
theorem ccmFirstClockJuliaCompletedCoherentEnergy_eq_arch_prime
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) :
    ccmFirstClockJuliaCompletedCoherentEnergy x L p =
      ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) ^ 2 +
        2 * ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) *
          ccmFirstClockJuliaPrimePowerOriginCorrelation x L p +
        ccmFirstClockJuliaPrimePowerCoherentEnergy x L p := by
  simp only [ccmFirstClockJuliaCompletedCoherentEnergy,
    ccmFirstClockJuliaPrimePowerCoherentEnergy,
    ccmFirstClockJuliaPrimePowerOriginCorrelation,
    GaloisForLFunctions.HTGeometry.realKernelPacketEnergy, Fin.sum_univ_succ,
    Fin.cases_zero, Fin.cases_succ, HTGeometry.juliaDefectAttenuationKernel_zero,
    sub_zero, zero_sub, HTGeometry.juliaDefectAttenuationKernel_neg]
  rw [Finset.sum_add_distrib]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_mul]
  ring

/-- **Completed-packet capacity.**  The literal Julia-attenuated completed first-clock value is
bounded in square by the coherent energy of the complete archimedean-plus-prime packet. -/
theorem ccmFirstClockJuliaAttenuatedCompletedPacket_sq_le_completedCoherentEnergy
    {N : ℕ} {x : ℝ} (hx : 0 < x) (L : ℝ) (p : Fin N → Nat.Primes) :
    ccmFirstClockJuliaAttenuatedCompletedPacket x L p ^ 2 ≤
      ccmFirstClockJuliaCompletedCoherentEnergy x L p := by
  let T : Fin (N + 1) → ℝ :=
    Fin.cases 0 (fun i => x * Real.log (p i : ℝ))
  let B : Fin (N + 1) → ℝ :=
    Fin.cases (ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L))
      (fun i => ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) (p i))
  have h := HTGeometry.juliaDefectAttenuationKernel_anchorCorrelation_sq_le_gramEnergy T B
  have horigin :
      (∑ i, B i * HTGeometry.juliaDefectAttenuationKernel (T i)) =
        ccmFirstClockJuliaAttenuatedCompletedPacket x L p := by
    simp only [Fin.sum_univ_succ, T, B, Fin.cases_zero, Fin.cases_succ,
      HTGeometry.juliaDefectAttenuationKernel_zero, mul_one]
    rw [ccmFirstClockJuliaAttenuatedCompletedPacket]
    apply congrArg (fun z => ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) + z)
    apply Finset.sum_congr rfl
    intro i _
    rw [gammaSewnMobiusJuliaPrimeAttenuation_eq_equilibriumKernel hx]
    ring
  rw [horigin] at h
  simpa only [ccmFirstClockJuliaCompletedCoherentEnergy,
    GaloisForLFunctions.HTGeometry.realKernelPacketEnergy] using h

/-- The deviation from the continuous budget is controlled by the literal signed prime energy.
This removes the cutoff, bad-channel, and negative-excursion interfaces from the capacity law. -/
theorem ccmFirstClockJulia_attenuatedCompletedPacket_sub_continuousBudget_sq_le_primeEnergy
    {N : ℕ} {x : ℝ} (hx : 0 < x) (L : ℝ) (p : Fin N → Nat.Primes) :
    (ccmFirstClockJuliaAttenuatedCompletedPacket x L p -
        ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L)) ^ 2 ≤
      ccmFirstClockJuliaPrimePowerCoherentEnergy x L p := by
  rw [ccmFirstClockJuliaAttenuatedCompletedPacket_eq_continuousBudget_add_primePowerOrigin
    hx L p]
  ring_nf
  simpa only [ccmFirstClockJuliaPrimePowerOriginCorrelation,
    ccmFirstClockJuliaPrimePowerCoherentEnergy,
    GaloisForLFunctions.HTGeometry.realKernelPacketEnergy, mul_comm] using
      (HTGeometry.juliaDefectAttenuationKernel_anchorCorrelation_sq_le_gramEnergy
        (fun i => x * Real.log (p i : ℝ))
        (fun i => ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) (p i)))

/-- Good/bad mixed correlation obeys the two-packet Julia capacity law. -/
theorem ccmFirstClockJuliaGoodBadCoherentCorrelation_sq_le_energy_mul_energy
    {N M : ℕ} (x L : ℝ)
    (p : Fin N → Nat.Primes) (q : Fin M → Nat.Primes) :
    ccmFirstClockJuliaGoodBadCoherentCorrelation x L p q ^ 2 ≤
      ccmFirstClockJuliaGoodCoherentEnergy x L p *
        ccmFirstClockJuliaBadCoherentEnergy x L q := by
  simpa only [ccmFirstClockJuliaGoodBadCoherentCorrelation,
    ccmFirstClockJuliaGoodCoherentEnergy,
    ccmFirstClockJuliaBadCoherentEnergy] using
      (HTGeometry.juliaDefectAttenuationKernel_packetCross_sq_le_energy_mul_energy
        (fun i => x * Real.log (p i : ℝ))
        (fun i => ccmFirstClockReducedGoodPrimeTerm L (p i))
        (fun j => x * Real.log (q j : ℝ))
        (fun j => ccmFirstClockReducedBadPrimeTerm L (q j)))

/-- The Julia good/bad two-channel determinant is nonnegative. -/
theorem ccmFirstClockJuliaGoodBadCoherentDeterminant_nonneg
    {N M : ℕ} (x L : ℝ)
    (p : Fin N → Nat.Primes) (q : Fin M → Nat.Primes) :
    0 ≤ ccmFirstClockJuliaGoodCoherentEnergy x L p *
        ccmFirstClockJuliaBadCoherentEnergy x L q -
      ccmFirstClockJuliaGoodBadCoherentCorrelation x L p q ^ 2 :=
  sub_nonneg.mpr
    (ccmFirstClockJuliaGoodBadCoherentCorrelation_sq_le_energy_mul_energy x L p q)

/-- On the admitted prime window, literal signed prime energy is good energy plus bad energy minus
twice their mixed coherent correlation. -/
theorem ccmFirstClockJuliaPrimePowerCoherentEnergy_eq_good_add_bad_sub_two_cross
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes)
    (hpCut : ∀ i, (p i : ℕ) ≤ ⌊Real.exp L⌋₊) :
    ccmFirstClockJuliaPrimePowerCoherentEnergy x L p =
      ccmFirstClockJuliaGoodCoherentEnergy x L p +
        ccmFirstClockJuliaBadCoherentEnergy x L p -
          2 * ccmFirstClockJuliaGoodBadCoherentCorrelation x L p p := by
  simp only [ccmFirstClockJuliaPrimePowerCoherentEnergy,
    ccmFirstClockJuliaGoodCoherentEnergy,
    ccmFirstClockJuliaBadCoherentEnergy,
    ccmFirstClockJuliaGoodBadCoherentCorrelation,
    GaloisForLFunctions.HTGeometry.realKernelPacketEnergy]
  simp_rw [ccmFirstClockPrimePowerTowerMass_eq_reducedGoodPrimeTerm_sub_bad (hpCut := hpCut _),
    sub_mul, mul_sub, Finset.sum_sub_distrib]
  have hsym :
      (∑ i, ∑ j,
        ccmFirstClockReducedBadPrimeTerm L (p i) *
          HTGeometry.juliaDefectAttenuationKernel
            (x * Real.log (p j : ℝ) - x * Real.log (p i : ℝ)) *
          ccmFirstClockReducedGoodPrimeTerm L (p j)) =
      ∑ i, ∑ j,
        ccmFirstClockReducedGoodPrimeTerm L (p i) *
          HTGeometry.juliaDefectAttenuationKernel
            (x * Real.log (p j : ℝ) - x * Real.log (p i : ℝ)) *
          ccmFirstClockReducedBadPrimeTerm L (p j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show x * Real.log (p i : ℝ) - x * Real.log (p j : ℝ) =
        -(x * Real.log (p j : ℝ) - x * Real.log (p i : ℝ)) by ring,
      HTGeometry.juliaDefectAttenuationKernel_neg]
    ring
  rw [hsym]
  ring

/-- Good/bad interference cannot exceed half of their total coherent energy on the admitted
prime window. -/
theorem two_mul_ccmFirstClockJuliaGoodBadCoherentCorrelation_le_energy_add_energy
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes)
    (hpCut : ∀ i, (p i : ℕ) ≤ ⌊Real.exp L⌋₊) :
    2 * ccmFirstClockJuliaGoodBadCoherentCorrelation x L p p ≤
      ccmFirstClockJuliaGoodCoherentEnergy x L p +
        ccmFirstClockJuliaBadCoherentEnergy x L p := by
  have hnonneg := ccmFirstClockJuliaPrimePowerCoherentEnergy_nonneg x L p
  rw [ccmFirstClockJuliaPrimePowerCoherentEnergy_eq_good_add_bad_sub_two_cross
    x L p hpCut] at hnonneg
  linarith

end

end RHTower

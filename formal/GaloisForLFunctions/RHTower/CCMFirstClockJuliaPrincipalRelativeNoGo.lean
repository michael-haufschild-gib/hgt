import GaloisForLFunctions.HTGeometry.TwoChannelRelativeCapacityNoGo
import GaloisForLFunctions.RHTower.CCMFirstClockJuliaCoherentEnergyDiagonalFloor
import GaloisForLFunctions.RHTower.GammaJuliaEndpointCorrectionHilbertSchmidtDressing

/-!
# Principal-relative Julia-current no-go

The surviving Route-J proposal moves a diagonal counterterm before good/bad projection.  This file
closes the natural channel-linear, finite-packet-hereditary, and anchored-Schur implementations of
that proposal.

Every prime in the sixth-power block is an actual pure-bad source cell: its reduced good term is
zero and its reduced bad term is strictly positive.  Hence a two-channel linear current whose
pure-bad diagonal is cancelled cannot orient even one such arithmetic cell.  Independently, the
canonical anchored Schur residual fails to dominate its removed anchor correlation throughout the
source-faithful zero-scale regime.

The results are unconditional.  They leave only a globally nonhereditary all-prime current based
on a new arithmetic cross-block identity.
-/

open Set Finset Filter Topology
open scoped BigOperators

noncomputable section
namespace RHTower

/-- Source-faithful Julia de-attenuation eventually makes the removed one-node anchor correlation
strictly larger than its canonical anchored Schur residual. -/
theorem eventually_not_juliaSchurResidual_orients_sourceFaithfulAnchor
    (node mass : ℝ) (hmass : mass ≠ 0) :
    ∀ᶠ x : ℝ in 𝓝 0,
      ¬ GaloisForLFunctions.HTGeometry.oneNodeAnchorSquare
          (HTGeometry.juliaDefectAttenuationKernel (x * node)) mass ≤
        GaloisForLFunctions.HTGeometry.oneNodeAnchoredSchurResidual
          (HTGeometry.juliaDefectAttenuationKernel (x * node)) mass := by
  have harg : Tendsto (fun x : ℝ => x * node) (𝓝 0) (𝓝 0) := by
    have h := (tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0)).const_mul node
    simpa [mul_comm] using h
  have hcoefficient : Tendsto
      (fun x : ℝ => HTGeometry.juliaDefectAttenuationKernel (x * node))
      (𝓝 0) (𝓝 1) :=
    HTGeometry.tendsto_juliaDefectAttenuationKernel_zero.comp harg
  have hsquare : Tendsto
      (fun x : ℝ => HTGeometry.juliaDefectAttenuationKernel (x * node) ^ 2)
      (𝓝 0) (𝓝 (1 ^ 2)) := hcoefficient.pow 2
  have hevent : ∀ᶠ x : ℝ in 𝓝 0,
      1 / 2 < HTGeometry.juliaDefectAttenuationKernel (x * node) ^ 2 :=
    (tendsto_order.1 hsquare).1 (1 / 2) (by norm_num)
  filter_upwards [hevent] with x hx
  exact
    GaloisForLFunctions.HTGeometry.not_oneNodeAnchorSquare_le_anchoredSchurResidual_of_half_lt_sq
      hmass hx

/-- A length-one prime tower has no reduced good component. -/
theorem ccmFirstClockReducedGoodPrimeTerm_eq_zero_of_length_one
    {L : ℝ} (p : Nat.Primes)
    (hlength : ccmFirstClockPrimePowerLength L p = 1) :
    ccmFirstClockReducedGoodPrimeTerm L p = 0 := by
  rw [ccmFirstClockReducedGoodPrimeTerm, ccmFirstClockStableTowerTerm,
    ccmFirstClockSmallSquarePositiveTerm]
  simp [hlength]

/-- Every prime in the sixth-power block is a pure-bad reduced source cell. -/
theorem ccmFirstClockJuliaSixthPower_block_goodTerm_eq_zero
    {m p : ℕ} (hm : 25 ≤ m)
    (hp : p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4)) :
    ccmFirstClockReducedGoodPrimeTerm (ccmFirstClockJuliaSixthPowerAperture m)
      ⟨p, (mem_suzukiMangoldtFivePrimeBlock.mp hp).1⟩ = 0 := by
  exact ccmFirstClockReducedGoodPrimeTerm_eq_zero_of_length_one _
    (ccmFirstClockJuliaSixthPower_block_primePowerLength_eq_one hm hp)

/-- Every sixth-power-block bad term is strictly positive, not merely nonnegative. -/
theorem ccmFirstClockJuliaSixthPower_block_badTerm_pos
    {m p : ℕ} (hm : 25 ≤ m)
    (hp : p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4)) :
    0 < ccmFirstClockReducedBadPrimeTerm (ccmFirstClockJuliaSixthPowerAperture m)
      ⟨p, (mem_suzukiMangoldtFivePrimeBlock.mp hp).1⟩ := by
  let q : Nat.Primes := ⟨p, (mem_suzukiMangoldtFivePrimeBlock.mp hp).1⟩
  let bad := ccmFirstClockReducedBadPrimeTerm
    (ccmFirstClockJuliaSixthPowerAperture m) q
  have hm0 : 0 < m := by omega
  have hL : 0 < ccmFirstClockJuliaSixthPowerAperture m := by
    rw [ccmFirstClockJuliaSixthPowerAperture]
    exact mul_pos (by norm_num)
      (Real.log_pos (by exact_mod_cast (show 1 < m by omega)))
  have hpCut : (q : ℕ) ≤ ⌊Real.exp (ccmFirstClockJuliaSixthPowerAperture m)⌋₊ := by
    rw [ccmFirstClockJuliaSixthPower_cutoff hm0]
    obtain ⟨_, _, hpUpper⟩ := mem_suzukiMangoldtFivePrimeBlock.mp hp
    dsimp only [q]
    calc
      p ≤ 5 * m ^ 4 := hpUpper
      _ ≤ m ^ 2 * m ^ 4 := Nat.mul_le_mul_right _ (by nlinarith)
      _ = m ^ 6 := by ring
  have hbadNonneg : 0 ≤ bad :=
    ccmFirstClockReducedBadPrimeTerm_nonneg hL q hpCut
  have hlower := ccmFirstClockJuliaSixthPower_block_badTerm_sq_lower hm hp
  have hpPrime := (mem_suzukiMangoldtFivePrimeBlock.mp hp).1
  have hlowerPos : 0 < (1 / 4 : ℝ) * Real.log (p : ℝ) ^ 2 / p := by
    have hlog : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast hpPrime.one_lt)
    have hpReal : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos hlog)) hpReal
  change 0 < bad
  by_contra hnot
  have hzero : bad = 0 := le_antisymm (not_lt.mp hnot) hbadNonneg
  dsimp only [bad, q] at hzero
  rw [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hlower
  linarith

/-- **Arithmetic pre-projection no-go.**  On every actual pure-bad sixth-power source cell, a
channel-linear current whose pure-bad diagonal weight is zero cannot dominate the squared signed
excursion.  The contradiction occurs before any good/bad packet is scalarized. -/
theorem ccmFirstClockJuliaSixthPower_block_not_oriented_by_badDiagonalNullLinearCurrent
    {m p : ℕ} (hm : 25 ≤ m)
    (hp : p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4))
    (goodWeight mixedWeight badWeight : ℝ) (hbadWeight : badWeight = 0) :
    ¬ (GaloisForLFunctions.HTGeometry.twoChannelSignedExcursion
          (ccmFirstClockReducedGoodPrimeTerm (ccmFirstClockJuliaSixthPowerAperture m)
            ⟨p, (mem_suzukiMangoldtFivePrimeBlock.mp hp).1⟩)
          (ccmFirstClockReducedBadPrimeTerm (ccmFirstClockJuliaSixthPowerAperture m)
            ⟨p, (mem_suzukiMangoldtFivePrimeBlock.mp hp).1⟩) ^ 2 ≤
        GaloisForLFunctions.HTGeometry.twoChannelLinearCurrent
          goodWeight mixedWeight badWeight
          (ccmFirstClockReducedGoodPrimeTerm (ccmFirstClockJuliaSixthPowerAperture m)
            ⟨p, (mem_suzukiMangoldtFivePrimeBlock.mp hp).1⟩)
          (ccmFirstClockReducedBadPrimeTerm (ccmFirstClockJuliaSixthPowerAperture m)
            ⟨p, (mem_suzukiMangoldtFivePrimeBlock.mp hp).1⟩)) := by
  rw [ccmFirstClockJuliaSixthPower_block_goodTerm_eq_zero hm hp, hbadWeight]
  simp only [GaloisForLFunctions.HTGeometry.twoChannelSignedExcursion,
    GaloisForLFunctions.HTGeometry.twoChannelLinearCurrent, zero_sub, neg_sq,
    mul_zero, zero_mul]
  have hbad := ccmFirstClockJuliaSixthPower_block_badTerm_pos hm hp
  nlinarith [sq_pos_of_pos hbad]

/-- The existing Gamma--Julia endpoint-correction Hilbert--Schmidt dressing cannot orient the
original Route-J excursion on any pure-bad sixth-power cell.  Its squared diagonal gain is at most
one half, whereas faithful domination of a nonzero cell requires gain at least one. -/
theorem ccmFirstClockJuliaSixthPower_block_not_oriented_by_endpointCorrectionDressing
    {m p : ℕ} (hm : 25 ≤ m)
    (hp : p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4)) :
    let q : Nat.Primes := ⟨p, (mem_suzukiMangoldtFivePrimeBlock.mp hp).1⟩
    let bad := ccmFirstClockReducedBadPrimeTerm
      (ccmFirstClockJuliaSixthPowerAperture m) q
    ¬ bad ^ 2 ≤ (gammaJuliaEndpointCorrectionMultiplier q 0 * bad) ^ 2 := by
  dsimp only
  let q : Nat.Primes := ⟨p, (mem_suzukiMangoldtFivePrimeBlock.mp hp).1⟩
  let bad := ccmFirstClockReducedBadPrimeTerm
    (ccmFirstClockJuliaSixthPowerAperture m) q
  have hbad : 0 < bad :=
    ccmFirstClockJuliaSixthPower_block_badTerm_pos hm hp
  have hmult := gammaJuliaEndpointCorrectionMultiplier_sq_le_half q 0
  intro hdominates
  have hbadSq : 0 < bad ^ 2 := sq_pos_of_pos hbad
  have hfactor :
      (gammaJuliaEndpointCorrectionMultiplier q 0 * bad) ^ 2 =
        gammaJuliaEndpointCorrectionMultiplier q 0 ^ 2 * bad ^ 2 := by
    ring
  rw [hfactor] at hdominates
  nlinarith [mul_le_mul_of_nonneg_right hmult hbadSq.le]

end RHTower

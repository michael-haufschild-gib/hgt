import GaloisForLFunctions.HTGeometry.TwoChannelRelativeCapacityNoGo
import GaloisForLFunctions.RHTower.CCMFirstClockJuliaCoherentEnergyDiagonalFloor
import GaloisForLFunctions.RHTower.CCMFirstClockTailLowerBoundCompleteness
import GaloisForLFunctions.RHTower.GammaJuliaEndpointCorrectionHilbertSchmidtDressing
import GaloisForLFunctions.RHTower.GammaSewnMobiusJuliaSourceTransport
import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardCofinalBoundaryLift

/-!
# Principal-relative Julia-current no-go and endpoint classification

The principal-relative Route-J proposal moves a diagonal counterterm before good/bad projection.
This file closes the natural channel-linear, finite-packet-hereditary, anchored-Schur,
diagonal-null Julia, and existing exterior-current implementations of that proposal.

Every prime in the sixth-power block is an actual pure-bad source cell: its reduced good term is
zero and its reduced bad term is strictly positive.  Hence a two-channel linear current whose
pure-bad diagonal is cancelled cannot orient even one such arithmetic cell.  Independently, the
canonical anchored Schur residual fails to dominate its removed anchor correlation throughout the
source-faithful zero-scale regime.

The results are unconditional.  A globally positive quadratic cross-block current is also closed:
a null diagonal annihilates its row.  The final section audits the genuinely indefinite
diagonal-null Julia current on the full sixth-power prime block and proves that the existing exact
calibrated Julia--Euler exterior seam has zero scalar quadratic energy by antisymmetry.

Finally, the unrestricted residual capacity existential is proved equivalent to the literal
first-clock eventual lower floor, RH, and Route R's four-unit Ward boundary-lift endpoint.  The
reverse negative-part witness is target-defined and is not asserted to be a source construction.
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

/-! ## The ambient-indefinite diagonal-null Julia candidate -/

/-- Every sixth-power-block bad coefficient has a coarse unsquared lower bound.  This converts the
Chebyshev theta mass into a quadratic-size total bad mass without a prime-gap input. -/
theorem ccmFirstClockJuliaSixthPower_block_badTerm_lower {m p : ℕ}
    (hm : 25 ≤ m) (hp : p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4)) :
    Real.log (p : ℝ) / (6 * (m : ℝ) ^ 2) ≤
      ccmFirstClockReducedBadNatTerm (ccmFirstClockJuliaSixthPowerAperture m) p := by
  have hpPrime := (mem_suzukiMangoldtFivePrimeBlock.mp hp).1
  have hpUpper := (mem_suzukiMangoldtFivePrimeBlock.mp hp).2.2
  have hmR : (0 : ℝ) < m := by positivity
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    (Real.log_pos (by exact_mod_cast hpPrime.one_lt)).le
  have hb : 0 ≤
      ccmFirstClockReducedBadNatTerm (ccmFirstClockJuliaSixthPowerAperture m) p := by
    rw [ccmFirstClockReducedBadNatTerm_of_prime _ hpPrime]
    exact (ccmFirstClockJuliaSixthPower_block_badTerm_pos hm hp).le
  have hsqLower := ccmFirstClockJuliaSixthPower_block_badTerm_sq_lower hm hp
  rw [← ccmFirstClockReducedBadNatTerm_of_prime _ hpPrime] at hsqLower
  have hpUpperR : (p : ℝ) ≤ 5 * (m : ℝ) ^ 4 := by exact_mod_cast hpUpper
  have hscale :
      (Real.log (p : ℝ) / (6 * (m : ℝ) ^ 2)) ^ 2 ≤
        (1 / 4 : ℝ) * Real.log (p : ℝ) ^ 2 / p := by
    have hden : (0 : ℝ) < 6 * (m : ℝ) ^ 2 := by positivity
    have hfourp : (4 : ℝ) * p ≤ 36 * (m : ℝ) ^ 4 := by nlinarith
    rw [div_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos hden) hpR).2
    nlinarith [sq_nonneg (Real.log (p : ℝ))]
  have hsq :
      (Real.log (p : ℝ) / (6 * (m : ℝ) ^ 2)) ^ 2 ≤
        ccmFirstClockReducedBadNatTerm
          (ccmFirstClockJuliaSixthPowerAperture m) p ^ 2 := hscale.trans hsqLower
  nlinarith

/-- A block bad square is at most its undamped one-mode square. -/
theorem ccmFirstClockJuliaSixthPower_block_badTerm_sq_upper {m p : ℕ}
    (hm : 25 ≤ m) (hp : p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4)) :
    ccmFirstClockReducedBadNatTerm (ccmFirstClockJuliaSixthPowerAperture m) p ^ 2 ≤
      Real.log (p : ℝ) ^ 2 / p := by
  have hpPrime := (mem_suzukiMangoldtFivePrimeBlock.mp hp).1
  let theta :=
    (2 * Real.pi / ccmFirstClockJuliaSixthPowerAperture m) * Real.log (p : ℝ)
  have hsinLower := Real.neg_one_le_sin theta
  have hsinUpper := Real.sin_le_one theta
  have hsinSq : Real.sin theta ^ 2 ≤ 1 := by nlinarith
  rw [ccmFirstClockReducedBadNatTerm_of_prime _ hpPrime,
    ccmFirstClockJuliaSixthPower_block_badTerm_eq hm hp]
  rw [show (2 * Real.pi / ccmFirstClockJuliaSixthPowerAperture m) *
      Real.log (p : ℝ) = theta by rfl]
  have hrSq := criticalPrimeTowerRadius_sq p
  have hfactor : 0 ≤ Real.log (p : ℝ) ^ 2 * criticalPrimeTowerRadius p ^ 2 := by
    positivity
  calc
    (-(Real.log (p : ℝ) * criticalPrimeTowerRadius p * Real.sin theta)) ^ 2 =
        (Real.log (p : ℝ) ^ 2 * criticalPrimeTowerRadius p ^ 2) *
          Real.sin theta ^ 2 := by ring
    _ ≤ (Real.log (p : ℝ) ^ 2 * criticalPrimeTowerRadius p ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left hsinSq hfactor
    _ = Real.log (p : ℝ) ^ 2 / p := by
      rw [hrSq]
      ring

/-- Uniform block version of the one-mode square upper bound. -/
theorem ccmFirstClockJuliaSixthPower_block_badTerm_sq_coarse_upper {m p : ℕ}
    (hm : 25 ≤ m) (hp : p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4)) :
    ccmFirstClockReducedBadNatTerm (ccmFirstClockJuliaSixthPowerAperture m) p ^ 2 ≤
      13 * Real.log (m : ℝ) ^ 2 / (m : ℝ) ^ 4 := by
  obtain ⟨hpPrime, hpLower, hpUpper⟩ := mem_suzukiMangoldtFivePrimeBlock.mp hp
  have hmR : (0 : ℝ) < m := by positivity
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hlogm : 0 ≤ Real.log (m : ℝ) :=
    (Real.log_pos (by exact_mod_cast (show 1 < m by omega))).le
  have hpPow : p ≤ m ^ 5 := by
    calc
      p ≤ 5 * m ^ 4 := hpUpper
      _ ≤ m * m ^ 4 := Nat.mul_le_mul_right _ (by omega)
      _ = m ^ 5 := by ring
  have hlogp : Real.log (p : ℝ) ≤ 5 * Real.log (m : ℝ) := by
    have hpPowR : (p : ℝ) ≤ (m : ℝ) ^ 5 := by exact_mod_cast hpPow
    have h := Real.log_le_log hpR hpPowR
    rw [Real.log_pow] at h
    norm_num at h
    exact h
  have hlogp0 : 0 ≤ Real.log (p : ℝ) :=
    (Real.log_pos (by exact_mod_cast hpPrime.one_lt)).le
  have hlogSq : Real.log (p : ℝ) ^ 2 ≤ 25 * Real.log (m : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (5 * Real.log (m : ℝ) - Real.log (p : ℝ))]
  have hpLowerR : 2 * (m : ℝ) ^ 4 < (p : ℝ) := by exact_mod_cast hpLower
  have hraw := ccmFirstClockJuliaSixthPower_block_badTerm_sq_upper hm hp
  calc
    ccmFirstClockReducedBadNatTerm (ccmFirstClockJuliaSixthPowerAperture m) p ^ 2 ≤
        Real.log (p : ℝ) ^ 2 / p := hraw
    _ ≤ 25 * Real.log (m : ℝ) ^ 2 / p :=
      div_le_div_of_nonneg_right hlogSq hpR.le
    _ ≤ 13 * Real.log (m : ℝ) ^ 2 / (m : ℝ) ^ 4 := by
      apply (div_le_div_iff₀ hpR (pow_pos hmR 4)).2
      nlinarith [sq_nonneg (Real.log (m : ℝ))]

/-- Chebyshev theta mass forces quadratic-size unsquared bad mass on the sixth-power block. -/
theorem ccmFirstClockJuliaSixthPower_block_badMass_lower {m : ℕ}
    (hm : 25 ≤ m) (hmCheb : Real.exp 20 ≤ ((m ^ 4 : ℕ) : ℝ)) :
    (m : ℝ) ^ 2 / 24 ≤
      ∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
        ccmFirstClockReducedBadNatTerm (ccmFirstClockJuliaSixthPowerAperture m) p := by
  have hmR : (0 : ℝ) < m := by positivity
  have hcheb := chebyshev_fivePrimeBlock_logMass_floor hmCheb
  calc
    (m : ℝ) ^ 2 / 24 =
        (1 / (6 * (m : ℝ) ^ 2)) * (((m ^ 4 : ℕ) : ℝ) / 4) := by
      push_cast
      field_simp
      ring
    _ ≤ (1 / (6 * (m : ℝ) ^ 2)) *
        ∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4), Real.log (p : ℝ) := by
      exact mul_le_mul_of_nonneg_left hcheb (by positivity)
    _ = ∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
        Real.log (p : ℝ) / (6 * (m : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      ring
    _ ≤ ∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
        ccmFirstClockReducedBadNatTerm
          (ccmFirstClockJuliaSixthPowerAperture m) p := by
      exact Finset.sum_le_sum fun p hp =>
        ccmFirstClockJuliaSixthPower_block_badTerm_lower hm hp

/-- The macroscopic prime block has the trivial sharp ambient-cardinality ceiling needed to sum
the pointwise bad-square bound. -/
theorem card_suzukiMangoldtFivePrimeBlock_fourthPower_le {m : ℕ} :
    (suzukiMangoldtFivePrimeBlock (m ^ 4)).card ≤ 5 * m ^ 4 := by
  have hsubset : suzukiMangoldtFivePrimeBlock (m ^ 4) ⊆ Finset.Icc 1 (5 * m ^ 4) := by
    intro p hp
    obtain ⟨hpPrime, _hpLower, hpUpper⟩ := mem_suzukiMangoldtFivePrimeBlock.mp hp
    exact Finset.mem_Icc.mpr ⟨hpPrime.pos, hpUpper⟩
  have hcard := Finset.card_le_card hsubset
  rw [Nat.card_Icc] at hcard
  simpa using hcard

/-- The total bad diagonal on the block is only logarithmic-square, while its total mass is
quadratic in `m`. -/
theorem ccmFirstClockJuliaSixthPower_block_badDiagonal_upper {m : ℕ}
    (hm : 25 ≤ m) :
    (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
      ccmFirstClockReducedBadNatTerm (ccmFirstClockJuliaSixthPowerAperture m) p ^ 2) ≤
      65 * Real.log (m : ℝ) ^ 2 := by
  have hmR : (0 : ℝ) < m := by positivity
  calc
    (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
      ccmFirstClockReducedBadNatTerm (ccmFirstClockJuliaSixthPowerAperture m) p ^ 2) ≤
        ∑ _p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
          13 * Real.log (m : ℝ) ^ 2 / (m : ℝ) ^ 4 := by
      exact Finset.sum_le_sum fun p hp =>
        ccmFirstClockJuliaSixthPower_block_badTerm_sq_coarse_upper hm hp
    _ = ((suzukiMangoldtFivePrimeBlock (m ^ 4)).card : ℝ) *
        (13 * Real.log (m : ℝ) ^ 2 / (m : ℝ) ^ 4) := by simp
    _ ≤ ((5 * m ^ 4 : ℕ) : ℝ) *
        (13 * Real.log (m : ℝ) ^ 2 / (m : ℝ) ^ 4) := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_suzukiMangoldtFivePrimeBlock_fourthPower_le (m := m))
        (by positivity)
    _ = 65 * Real.log (m : ℝ) ^ 2 := by
      push_cast
      field_simp
      ring

/-- Exact ordered pair mass on the block has a quartic-minus-logarithmic lower bound. -/
theorem ccmFirstClockJuliaSixthPower_block_badPairMass_lower {m : ℕ}
    (hm : 25 ≤ m) (hmCheb : Real.exp 20 ≤ ((m ^ 4 : ℕ) : ℝ)) :
    (m : ℝ) ^ 4 / 576 - 65 * Real.log (m : ℝ) ^ 2 ≤
      (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
        ccmFirstClockReducedBadNatTerm
          (ccmFirstClockJuliaSixthPowerAperture m) p) ^ 2 -
      ∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
        ccmFirstClockReducedBadNatTerm
          (ccmFirstClockJuliaSixthPowerAperture m) p ^ 2 := by
  let block := suzukiMangoldtFivePrimeBlock (m ^ 4)
  let bad := ccmFirstClockReducedBadNatTerm (ccmFirstClockJuliaSixthPowerAperture m)
  have hmass := ccmFirstClockJuliaSixthPower_block_badMass_lower hm hmCheb
  have hdiag := ccmFirstClockJuliaSixthPower_block_badDiagonal_upper hm
  have hmass0 : 0 ≤ ∑ p ∈ block, bad p := by
    apply Finset.sum_nonneg
    intro p hp
    have hpPrime := (mem_suzukiMangoldtFivePrimeBlock.mp hp).1
    dsimp only [bad]
    rw [ccmFirstClockReducedBadNatTerm_of_prime _ hpPrime]
    exact (ccmFirstClockJuliaSixthPower_block_badTerm_pos hm hp).le
  have hlower0 : 0 ≤ (m : ℝ) ^ 2 / 24 := by positivity
  have hmassSq : ((m : ℝ) ^ 2 / 24) ^ 2 ≤ (∑ p ∈ block, bad p) ^ 2 :=
    (sq_le_sq₀ hlower0 hmass0).2 (by simpa only [block, bad] using hmass)
  dsimp only [block, bad] at hmassSq ⊢
  nlinarith

/-- Logarithmic separation inside the whole multiplicative prime block is bounded independently of
the aperture.  This is the uniformity needed to pass a zero Julia scale through a moving block. -/
theorem abs_log_sub_log_le_two_of_mem_suzukiMangoldtFivePrimeBlock_fourthPower
    {m p q : ℕ} (hm : 25 ≤ m)
    (hp : p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4))
    (hq : q ∈ suzukiMangoldtFivePrimeBlock (m ^ 4)) :
    |Real.log (q : ℝ) - Real.log (p : ℝ)| ≤ 2 := by
  obtain ⟨hpPrime, hpLower, hpUpper⟩ := mem_suzukiMangoldtFivePrimeBlock.mp hp
  obtain ⟨hqPrime, hqLower, hqUpper⟩ := mem_suzukiMangoldtFivePrimeBlock.mp hq
  have hmR : (0 : ℝ) < m := by positivity
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
  have hpLowerR : 2 * (m : ℝ) ^ 4 < (p : ℝ) := by exact_mod_cast hpLower
  have hqLowerR : 2 * (m : ℝ) ^ 4 < (q : ℝ) := by exact_mod_cast hqLower
  have hpUpperR : (p : ℝ) ≤ 5 * (m : ℝ) ^ 4 := by exact_mod_cast hpUpper
  have hqUpperR : (q : ℝ) ≤ 5 * (m : ℝ) ^ 4 := by exact_mod_cast hqUpper
  have hpLogLowerRaw := Real.log_lt_log (by positivity : 0 < 2 * (m : ℝ) ^ 4) hpLowerR
  have hqLogLowerRaw := Real.log_lt_log (by positivity : 0 < 2 * (m : ℝ) ^ 4) hqLowerR
  have hpLogUpperRaw := Real.log_le_log hpR hpUpperR
  have hqLogUpperRaw := Real.log_le_log hqR hqUpperR
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hpLogLowerRaw hqLogLowerRaw
  rw [Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hpLogUpperRaw hqLogUpperRaw
  norm_num at hpLogLowerRaw hqLogLowerRaw hpLogUpperRaw hqLogUpperRaw
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogFive := Real.log_five_lt_d9
  rw [abs_le]
  constructor <;> nlinarith

/-- Literal diagonal-null Julia cross-prime energy on the sixth-power block.  Its zero diagonal
makes it ambient-indefinite, while positive Julia off-diagonal entries make it copositive on the
actual nonnegative bad masses. -/
def ccmFirstClockJuliaSixthPowerBlockOffDiagonalEnergy (x : ℝ) (m : ℕ) : ℝ :=
  GaloisForLFunctions.HTGeometry.finsetOffDiagonalKernelEnergy
    (suzukiMangoldtFivePrimeBlock (m ^ 4))
    (fun p q => HTGeometry.juliaDefectAttenuationKernel
      (x * (Real.log (q : ℝ) - Real.log (p : ℝ))))
    (ccmFirstClockReducedBadNatTerm (ccmFirstClockJuliaSixthPowerAperture m))

/-- Any uniform off-diagonal Julia-kernel floor transfers the quartic pair-mass floor to the
diagonal-null current. -/
theorem ccmFirstClockJuliaSixthPowerBlockOffDiagonalEnergy_lower
    {x kappa : ℝ} {m : ℕ} (hkappa : 0 ≤ kappa) (hm : 25 ≤ m)
    (hmCheb : Real.exp 20 ≤ ((m ^ 4 : ℕ) : ℝ))
    (hkernel : ∀ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
      ∀ q ∈ suzukiMangoldtFivePrimeBlock (m ^ 4), p ≠ q →
        kappa ≤ HTGeometry.juliaDefectAttenuationKernel
          (x * (Real.log (q : ℝ) - Real.log (p : ℝ)))) :
    kappa * ((m : ℝ) ^ 4 / 576 - 65 * Real.log (m : ℝ) ^ 2) ≤
      ccmFirstClockJuliaSixthPowerBlockOffDiagonalEnergy x m := by
  let block := suzukiMangoldtFivePrimeBlock (m ^ 4)
  let bad := ccmFirstClockReducedBadNatTerm (ccmFirstClockJuliaSixthPowerAperture m)
  let kernel := fun p q : ℕ => HTGeometry.juliaDefectAttenuationKernel
    (x * (Real.log (q : ℝ) - Real.log (p : ℝ)))
  have hpair := ccmFirstClockJuliaSixthPower_block_badPairMass_lower hm hmCheb
  have hmass : ∀ p ∈ block, 0 ≤ bad p := by
    intro p hp
    have hpPrime := (mem_suzukiMangoldtFivePrimeBlock.mp hp).1
    dsimp only [bad]
    rw [ccmFirstClockReducedBadNatTerm_of_prime _ hpPrime]
    exact (ccmFirstClockJuliaSixthPower_block_badTerm_pos hm hp).le
  have henergy :=
    GaloisForLFunctions.HTGeometry.kappa_mul_pairMass_le_finsetOffDiagonalKernelEnergy
      block kernel bad hmass (by simpa only [block, kernel] using hkernel)
  have hscaled := mul_le_mul_of_nonneg_left hpair hkappa
  dsimp only [block, kernel, bad] at henergy hscaled ⊢
  exact hscaled.trans henergy

/-- Uniform source-faithful kernel floor: one zero-scale neighbourhood works simultaneously for
every sixth-power block because all block log-ratios have bounded size. -/
theorem eventually_half_le_juliaKernel_on_every_sixthPowerBlock :
    ∀ᶠ x : ℝ in 𝓝 0, ∀ m : ℕ, 25 ≤ m →
      ∀ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
      ∀ q ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
        (1 / 2 : ℝ) ≤ HTGeometry.juliaDefectAttenuationKernel
          (x * (Real.log (q : ℝ) - Real.log (p : ℝ))) := by
  have hkernelLimit := HTGeometry.tendsto_juliaDefectAttenuationKernel_zero
  have hhalf : ∀ᶠ y : ℝ in 𝓝 0,
      (1 / 2 : ℝ) < HTGeometry.juliaDefectAttenuationKernel y :=
    (tendsto_order.1 hkernelLimit).1 (1 / 2) (by norm_num)
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp hhalf
  have hxBall : Metric.ball (0 : ℝ) (epsilon / 2) ∈ 𝓝 0 :=
    Metric.ball_mem_nhds 0 (half_pos hepsilon)
  filter_upwards [hxBall] with x hx
  intro m hm p hp q hq
  have hdiff :=
    abs_log_sub_log_le_two_of_mem_suzukiMangoldtFivePrimeBlock_fourthPower hm hp hq
  have hxAbs : |x| < epsilon / 2 := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
    exact hx
  have hargAbs : |x * (Real.log (q : ℝ) - Real.log (p : ℝ))| < epsilon := by
    rw [abs_mul]
    calc
      |x| * |Real.log (q : ℝ) - Real.log (p : ℝ)| ≤ |x| * 2 :=
        mul_le_mul_of_nonneg_left hdiff (abs_nonneg x)
      _ < (epsilon / 2) * 2 := mul_lt_mul_of_pos_right hxAbs (by norm_num)
      _ = epsilon := by ring
  have hmem :
      x * (Real.log (q : ℝ) - Real.log (p : ℝ)) ∈ Metric.ball (0 : ℝ) epsilon := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact hargAbs
  exact (hball hmem).le

/-- Therefore every sufficiently source-faithful Julia scale has a quartic-minus-logarithmic
lower floor on the diagonal-null block current. -/
theorem eventually_ccmFirstClockJuliaSixthPowerBlockOffDiagonalEnergy_lower :
    ∀ᶠ x : ℝ in 𝓝 0, ∀ m : ℕ, 25 ≤ m →
      Real.exp 20 ≤ ((m ^ 4 : ℕ) : ℝ) →
      (1 / 2 : ℝ) *
          ((m : ℝ) ^ 4 / 576 - 65 * Real.log (m : ℝ) ^ 2) ≤
        ccmFirstClockJuliaSixthPowerBlockOffDiagonalEnergy x m := by
  filter_upwards [eventually_half_le_juliaKernel_on_every_sixthPowerBlock] with x hx
  intro m hm hmCheb
  exact ccmFirstClockJuliaSixthPowerBlockOffDiagonalEnergy_lower
    (by norm_num) hm hmCheb (fun p hp q hq _hne => hx m hm p hp q hq)

/-! ## Existing sign-changing Julia--Euler exterior current -/

/-- The calibrated finite-aperture Julia--Euler cell is antisymmetric.  Its sign-changing content
is a genuine exterior orientation, not a symmetric capacity kernel. -/
theorem gammaSewnMobiusJuliaCalibratedEulerExteriorCell_swap
    (x u : ℝ) (i j : Nat.Primes × ℕ) :
    gammaSewnMobiusJuliaCalibratedEulerExteriorCell x u j i =
      -gammaSewnMobiusJuliaCalibratedEulerExteriorCell x u i j := by
  unfold gammaSewnMobiusJuliaCalibratedEulerExteriorCell
    gammaSewnRecoveredEulerAmplitudeExteriorCell
    gammaSewnMobiusJuliaPrimeLogExteriorSeam
  rw [gammaSewnMobiusApertureBoundaryExteriorCell_swap]
  ring

/-- Scalar quadratic energy of the exact calibrated Julia--Euler exterior current on a finite
prime-power packet. -/
def gammaSewnMobiusJuliaCalibratedEulerExteriorScalarEnergy
    (x u : ℝ) (packet : Finset (Nat.Primes × ℕ))
    (mass : Nat.Primes × ℕ → ℝ) : ℝ :=
  GaloisForLFunctions.HTGeometry.finsetOffDiagonalKernelEnergy packet
    (gammaSewnMobiusJuliaCalibratedEulerExteriorCell x u) mass

/-- The exact sign-changing Julia--Euler current cannot be scalarized into Route-J capacity: every
finite packet energy is identically zero by antisymmetric cancellation. -/
theorem gammaSewnMobiusJuliaCalibratedEulerExteriorScalarEnergy_eq_zero
    (x u : ℝ) (packet : Finset (Nat.Primes × ℕ))
    (mass : Nat.Primes × ℕ → ℝ) :
    gammaSewnMobiusJuliaCalibratedEulerExteriorScalarEnergy x u packet mass = 0 := by
  exact
    GaloisForLFunctions.HTGeometry.finsetOffDiagonalKernelEnergy_eq_zero_of_antisymmetric
      packet (gammaSewnMobiusJuliaCalibratedEulerExteriorCell x u) mass
      (gammaSewnMobiusJuliaCalibratedEulerExteriorCell_swap x u)

/-- **Source-faithful Krein no-go.**  For every Julia scale tending to zero along the cofinal
sixth-power apertures, the diagonal-null off-diagonal current is unbounded.  Removing the diagonal
therefore does not rescue the natural ambient-indefinite Julia kernel. -/
theorem ccmFirstClockJuliaSixthPowerBlockOffDiagonalEnergy_unbounded_of_scale_tendsto_zero
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop (𝓝 0)) (C : ℝ) :
    ∃ m : ℕ, C < ccmFirstClockJuliaSixthPowerBlockOffDiagonalEnergy (scale m) m := by
  have hnear :=
    hscale.eventually eventually_ccmFirstClockJuliaSixthPowerBlockOffDiagonalEnergy_lower
  obtain ⟨M, hM⟩ := (eventually_atTop.1 hnear)
  obtain ⟨m, hmLarge⟩ := exists_nat_gt
    (max (M : ℝ) (max (Real.exp 20) (max 300 (2304 * (|C| + 1)))))
  have hMReal : (M : ℝ) < (m : ℝ) :=
    (le_max_left _ _).trans_lt hmLarge
  have hMm : M ≤ m := by exact_mod_cast hMReal.le
  have houter :
      max (Real.exp 20) (max 300 (2304 * (|C| + 1))) < (m : ℝ) :=
    (le_max_right (M : ℝ) _).trans_lt hmLarge
  have hinner : max 300 (2304 * (|C| + 1)) < (m : ℝ) :=
    (le_max_right (Real.exp 20) _).trans_lt houter
  have hm300 : (300 : ℝ) < m :=
    (le_max_left 300 (2304 * (|C| + 1))).trans_lt hinner
  have hm25 : 25 ≤ m := by exact_mod_cast (show (25 : ℝ) ≤ m by linarith)
  have hmExp : Real.exp 20 < (m : ℝ) :=
    (le_max_left (Real.exp 20) (max 300 (2304 * (|C| + 1)))).trans_lt houter
  have hmNatPos : 0 < m := by omega
  have hmPowNat : m ≤ m ^ 4 := by
    simpa using (Nat.pow_le_pow_right hmNatPos (show 1 ≤ 4 by omega) : m ^ 1 ≤ m ^ 4)
  have hmCheb : Real.exp 20 ≤ ((m ^ 4 : ℕ) : ℝ) := by
    exact hmExp.le.trans (by exact_mod_cast hmPowNat)
  have hlower := hM m hMm m hm25 hmCheb
  have hmTarget : 2304 * (|C| + 1) < (m : ℝ) :=
    (le_max_right 300 (2304 * (|C| + 1))).trans_lt hinner
  have hCsmall : C < (m : ℝ) / 2304 := by
    have hCabs : C ≤ |C| := le_abs_self C
    have habs : |C| + 1 < (m : ℝ) / 2304 := by
      exact (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2304)).2 (by nlinarith)
    linarith
  have hmPowReal : (m : ℝ) ≤ (m : ℝ) ^ 4 := by exact_mod_cast hmPowNat
  have hCquartic : C < (m : ℝ) ^ 4 / 2304 :=
    hCsmall.trans_le (div_le_div_of_nonneg_right hmPowReal (by norm_num))
  have hmR : (0 : ℝ) < m := by positivity
  have hlog0 : 0 ≤ Real.log (m : ℝ) :=
    (Real.log_pos (by exact_mod_cast (show 1 < m by omega))).le
  have hlogLe : Real.log (m : ℝ) ≤ (m : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hmR
    linarith
  have hlogSq : Real.log (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((m : ℝ) - Real.log (m : ℝ))]
  have hmSq : (74880 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have hquartic : 74880 * (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 4 := by
    have h := mul_le_mul_of_nonneg_right hmSq (sq_nonneg (m : ℝ))
    nlinarith
  have hlogQuartic : 74880 * Real.log (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 4 :=
    (mul_le_mul_of_nonneg_left hlogSq (by norm_num)).trans hquartic
  have hpolynomial :
      (m : ℝ) ^ 4 / 2304 ≤
        (1 / 2 : ℝ) * ((m : ℝ) ^ 4 / 576 - 65 * Real.log (m : ℝ) ^ 2) := by
    nlinarith
  exact ⟨m, hCquartic.trans_le (hpolynomial.trans hlower)⟩

/-! ## Terminal classification of an unrestricted residual capacity -/

/-- Widest literal-source version of the residual Route-J capacity request.  It deliberately
imposes no representation condition on `capacity`: this is the endpoint existential left after
forgetting whether a proposed current is Julia, Krein, nonlinear, or source-constructed. -/
def CCMFirstClockPrincipalRelativeCapacityOnTail : Prop :=
  ∃ (capacity : ℝ → ℝ) (M A : ℝ),
    0 ≤ M ∧ Real.pi / 2 ≤ A ∧
      ∀ L : ℝ, A ≤ L →
        0 ≤ capacity L ∧
        capacity L ≤ M ∧
        (ccmPublishedSourceSineCoefficient (L / 2) (2 * Real.pi / L) < 0 →
          ccmPublishedSourceSineCoefficient (L / 2) (2 * Real.pi / L) ^ 2 ≤
            capacity L)

/-- Any uniformly bounded negative-excursion capacity gives the literal first clock a fixed lower
floor.  This direction uses only the inequalities in the capacity interface. -/
theorem ccmFirstClockPublishedSourceEventuallyBoundedBelow_of_principalRelativeCapacityOnTail
    (hcapacity : CCMFirstClockPrincipalRelativeCapacityOnTail) :
    CCMFirstClockPublishedSourceEventuallyBoundedBelow := by
  obtain ⟨capacity, M, A, hM, hA, hcapacity⟩ := hcapacity
  refine ⟨M + 1, A, by linarith, hA, ?_⟩
  intro L hL
  let source := ccmPublishedSourceSineCoefficient (L / 2) (2 * Real.pi / L)
  have hdata := hcapacity L hL
  by_cases hsource : source < 0
  · have hsquare : source ^ 2 ≤ M := (hdata.2.2 hsource).trans hdata.2.1
    dsimp only [source] at hsquare ⊢
    nlinarith [sq_nonneg (source + 1)]
  · have hsource0 : 0 ≤ source := le_of_not_gt hsource
    dsimp only [source] at hsource0 ⊢
    linarith

/-- Canonical negative-part capacity.  This is the exact target-defined witness used only for the
reverse logical classification; it is not claimed as a source mechanism. -/
def ccmFirstClockCanonicalNegativePartCapacity (L : ℝ) : ℝ :=
  let source := ccmPublishedSourceSineCoefficient (L / 2) (2 * Real.pi / L)
  if source < 0 then source ^ 2 else 0

/-- A tail lower floor supplies the target-defined negative-part witness.  This proves logical
completeness of the unrestricted interface and identifies why the witness itself is representation
theatre rather than independent Julia information. -/
theorem principalRelativeCapacityOnTail_of_ccmFirstClockPublishedSourceEventuallyBoundedBelow
    (hbounded : CCMFirstClockPublishedSourceEventuallyBoundedBelow) :
    CCMFirstClockPrincipalRelativeCapacityOnTail := by
  obtain ⟨C, A, hC, hA, hsource⟩ := hbounded
  let source := fun L : ℝ =>
    ccmPublishedSourceSineCoefficient (L / 2) (2 * Real.pi / L)
  refine ⟨ccmFirstClockCanonicalNegativePartCapacity, C ^ 2, A,
    sq_nonneg C, hA, ?_⟩
  intro L hL
  have hfloor := hsource L hL
  by_cases hneg : source L < 0
  · have hneg0 : 0 ≤ -source L := by linarith
    have hle : -source L ≤ C := by
      dsimp only [source] at hfloor ⊢
      linarith
    have hsquare : (-source L) ^ 2 ≤ C ^ 2 :=
      (sq_le_sq₀ hneg0 hC).2 hle
    rw [ccmFirstClockCanonicalNegativePartCapacity]
    rw [if_pos hneg]
    refine ⟨sq_nonneg _, ?_, ?_⟩
    · nlinarith
    · intro _hnegative
      rfl
  · rw [ccmFirstClockCanonicalNegativePartCapacity]
    rw [if_neg hneg]
    exact ⟨le_rfl, sq_nonneg C, fun h => (hneg h).elim⟩

/-- **Route-J endpoint completeness.**  Once representation data are forgotten, existence of a
bounded principal-relative capacity is exactly Route A's eventual lower-floor property. -/
theorem ccmFirstClockPrincipalRelativeCapacityOnTail_iff_eventuallyBoundedBelow :
    CCMFirstClockPrincipalRelativeCapacityOnTail ↔
      CCMFirstClockPublishedSourceEventuallyBoundedBelow :=
  ⟨ccmFirstClockPublishedSourceEventuallyBoundedBelow_of_principalRelativeCapacityOnTail,
    principalRelativeCapacityOnTail_of_ccmFirstClockPublishedSourceEventuallyBoundedBelow⟩

/-- The unrestricted residual capacity interface is exactly RH, not an independent mechanism. -/
theorem ccmFirstClockPrincipalRelativeCapacityOnTail_iff_rh :
    CCMFirstClockPrincipalRelativeCapacityOnTail ↔ RiemannHypothesis := by
  rw [ccmFirstClockPrincipalRelativeCapacityOnTail_iff_eventuallyBoundedBelow,
    ccmFirstClockPublishedSourceEventuallyBoundedBelow_iff_rh]

/-- Endpoint ownership bridge: the unrestricted residual Route-J interface and Route R's actual
four-unit Ward boundary-lift law are equivalent because both are exact RH criteria.  This theorem
classifies endpoints; the nontrivial source transport itself is supplied by Route R's singular
Möbius--Gamma/Xi Julia construction. -/
theorem ccmFirstClockPrincipalRelativeCapacityOnTail_iff_continuedXiWardFourUnitBoundaryLiftLaw :
    CCMFirstClockPrincipalRelativeCapacityOnTail ↔
      ContinuedXiWardFourUnitBoundaryLiftLaw := by
  rw [ccmFirstClockPrincipalRelativeCapacityOnTail_iff_rh,
    riemannHypothesis_iff_continuedXiWardFourUnitBoundaryLiftLaw]

end RHTower

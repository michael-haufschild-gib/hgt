import GaloisForLFunctions.HTGeometry.NonnegativeKernelDiagonalCapacity
import GaloisForLFunctions.RHTower.CCMFirstClockJuliaTwoPacketCapacity
import GaloisForLFunctions.RHTower.SuzukiMangoldtMacroscopicPrimeBlock

open Set Finset Filter Topology
open scoped BigOperators

/-!
# Julia coherent-energy diagonal floor

The literal reduced bad first-clock source has an unavoidable arithmetic diagonal in its Julia
coherent energy.  At apertures `L_m = 6 log m`, primes in `(2m⁴, 5m⁴]` contribute exactly one
prime-power mode in a uniformly negative sine chamber.  A Chebyshev block bound then forces the
full bad energy above `log m / 20`, independently of Julia scale.  Thus the unrenormalized energy
budget required by Route J is impossible.

The same module proves the complementary zero-scale law: every fixed full packet converges to
rank-one energy, the square of its total bad mass.  All results are unconditional.
-/

noncomputable section
namespace RHTower

/-- Source-faithful sixth-power aperture `L_m = 6 log m`. -/
def ccmFirstClockJuliaSixthPowerAperture (m : ℕ) : ℝ := 6 * Real.log (m : ℝ)

/-- Exact source cutoff at the sixth-power aperture. -/
theorem ccmFirstClockJuliaSixthPower_cutoff {m : ℕ} (hm : 0 < m) :
    ⌊Real.exp (ccmFirstClockJuliaSixthPowerAperture m)⌋₊ = m ^ 6 := by
  have hexponent : ccmFirstClockJuliaSixthPowerAperture m = Real.log ((m : ℝ) ^ 6) := by
    rw [ccmFirstClockJuliaSixthPowerAperture, Real.log_pow]
    norm_num
  rw [hexponent, Real.exp_log (by positivity), ← Nat.cast_pow,
    Nat.floor_natCast]

/-- Every prime in `(2m⁴, 5m⁴]` has exactly one admitted power at `L_m`. -/
theorem ccmFirstClockJuliaSixthPower_block_primePowerLength_eq_one {m p : ℕ} (hm : 25 ≤ m)
    (hp : p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4)) :
    ccmFirstClockPrimePowerLength (ccmFirstClockJuliaSixthPowerAperture m) p = 1 := by
  obtain ⟨hpPrime, hpLower, hpUpper⟩ := mem_suzukiMangoldtFivePrimeBlock.mp hp
  have hm0 : 0 < m := by omega
  have hpOne : 1 < p := hpPrime.one_lt
  have hpCut : p ≤ m ^ 6 := by
    calc
      p ≤ 5 * m ^ 4 := hpUpper
      _ ≤ m ^ 2 * m ^ 4 := by
        exact Nat.mul_le_mul_right (m ^ 4) (by nlinarith)
      _ = m ^ 6 := by ring
  have hpSq : m ^ 6 < p * p := by
    have hpow : m ^ 6 < 4 * m ^ 8 := by
      have h68 : m ^ 6 ≤ m ^ 8 := Nat.pow_le_pow_right hm0 (by omega)
      have h8pos : 0 < m ^ 8 := pow_pos hm0 _
      omega
    have hsq : (2 * m ^ 4) ^ 2 < p ^ 2 :=
      (sq_lt_sq₀ (by omega) (by omega)).2 hpLower
    calc
      m ^ 6 < 4 * m ^ 8 := hpow
      _ = (2 * m ^ 4) ^ 2 := by ring
      _ < p ^ 2 := hsq
      _ = p * p := by ring
  rw [ccmFirstClockPrimePowerLength, ccmFirstClockJuliaSixthPower_cutoff hm0, Nat.log_eq_one_iff]
  exact ⟨hpSq, hpOne, hpCut⟩

/-- Sine is at most `-1/2` on the terminal chamber `[4π/3, 3π/2]`. -/
theorem half_le_neg_sin_of_four_pi_div_three_le_of_le_three_pi_div_two {theta : ℝ}
    (hlower : 4 * Real.pi / 3 ≤ theta)
    (hupper : theta ≤ 3 * Real.pi / 2) :
    (1 / 2 : ℝ) ≤ -Real.sin theta := by
  let u := theta - Real.pi
  have huLower : Real.pi / 6 ≤ u := by
    dsimp only [u]
    nlinarith [Real.pi_pos]
  have huUpper : u ≤ Real.pi / 2 := by
    dsimp only [u]
    nlinarith
  have hleft : -(Real.pi / 2) ≤ Real.pi / 6 := by
    nlinarith [Real.pi_pos]
  have hmono := Real.strictMonoOn_sin.monotoneOn
    ⟨hleft, by nlinarith [Real.pi_pos]⟩ ⟨by linarith, huUpper⟩ huLower
  have hsin : Real.sin theta = -Real.sin u := by
    rw [show theta = u + Real.pi by simp only [u]; ring, Real.sin_add_pi]
  rw [hsin, neg_neg, ← Real.sin_pi_div_six]
  exact hmono

/-- The complete one-mode prime block lies in the terminal negative sine chamber. -/
theorem ccmFirstClockJuliaSixthPower_block_phase {m p : ℕ} (hm : 25 ≤ m)
    (hp : p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4)) :
    4 * Real.pi / 3 <
        (2 * Real.pi / ccmFirstClockJuliaSixthPowerAperture m) * Real.log (p : ℝ) ∧
      (2 * Real.pi / ccmFirstClockJuliaSixthPowerAperture m) * Real.log (p : ℝ) ≤
        3 * Real.pi / 2 := by
  obtain ⟨hpPrime, hpLower, hpUpper⟩ := mem_suzukiMangoldtFivePrimeBlock.mp hp
  have hmR : (0 : ℝ) < m := by positivity
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogFive : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  have hlog25 : Real.log (25 : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hm)
  have hlog25eq : Real.log (25 : ℝ) = 2 * Real.log 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlogFiveBudget : Real.log 5 ≤ Real.log (m : ℝ) / 2 := by
    rw [hlog25eq] at hlog25
    linarith
  have hpLowerR : 2 * (m : ℝ) ^ 4 < (p : ℝ) := by
    exact_mod_cast hpLower
  have hpUpperR : (p : ℝ) ≤ 5 * (m : ℝ) ^ 4 := by
    exact_mod_cast hpUpper
  have hlogLowerRaw := Real.log_lt_log (by positivity : 0 < 2 * (m : ℝ) ^ 4) hpLowerR
  have hlogUpperRaw := Real.log_le_log hpR hpUpperR
  have hlogLower : 4 * Real.log (m : ℝ) < Real.log (p : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity),
      Real.log_pow] at hlogLowerRaw
    norm_num at hlogLowerRaw
    nlinarith
  have hlogUpper : Real.log (p : ℝ) ≤ (9 / 2 : ℝ) * Real.log m := by
    rw [Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) (by positivity),
      Real.log_pow] at hlogUpperRaw
    norm_num at hlogUpperRaw
    nlinarith
  have hscale : 0 < 2 * Real.pi / ccmFirstClockJuliaSixthPowerAperture m := by
    rw [ccmFirstClockJuliaSixthPowerAperture]
    positivity
  constructor
  · calc
      4 * Real.pi / 3 =
          (2 * Real.pi / ccmFirstClockJuliaSixthPowerAperture m) * (4 * Real.log (m : ℝ)) := by
            rw [ccmFirstClockJuliaSixthPowerAperture]
            field_simp
            ring
      _ < (2 * Real.pi / ccmFirstClockJuliaSixthPowerAperture m) * Real.log (p : ℝ) :=
        mul_lt_mul_of_pos_left hlogLower hscale
  · calc
      (2 * Real.pi / ccmFirstClockJuliaSixthPowerAperture m) * Real.log (p : ℝ) ≤
          (2 * Real.pi / ccmFirstClockJuliaSixthPowerAperture m) *
            ((9 / 2 : ℝ) * Real.log (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogUpper hscale.le
      _ = 3 * Real.pi / 2 := by
        rw [ccmFirstClockJuliaSixthPowerAperture]
        field_simp
        ring

/-- Exact one-mode formula for the reduced bad coefficient on the prime block. -/
theorem ccmFirstClockJuliaSixthPower_block_badTerm_eq {m p : ℕ} (hm : 25 ≤ m)
    (hp : p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4)) :
    ccmFirstClockReducedBadPrimeTerm (ccmFirstClockJuliaSixthPowerAperture m)
        ⟨p, (mem_suzukiMangoldtFivePrimeBlock.mp hp).1⟩ =
      -(Real.log (p : ℝ) * criticalPrimeTowerRadius p *
        Real.sin ((2 * Real.pi / ccmFirstClockJuliaSixthPowerAperture m) * Real.log (p : ℝ))) := by
  have hpPrime := (mem_suzukiMangoldtFivePrimeBlock.mp hp).1
  have hlength := ccmFirstClockJuliaSixthPower_block_primePowerLength_eq_one hm hp
  have hlength' : Nat.log p ⌊Real.exp (ccmFirstClockJuliaSixthPowerAperture m)⌋₊ = 1 := by
    exact hlength
  rw [ccmFirstClockReducedBadPrimeTerm, if_pos hlength,
    ccmFirstClockPrimePowerTowerMass_eq_geometric hpPrime, hlength']
  simp [firstClockGeometricTower]
  ring

/-- Pointwise squared lower bound for each block bad coefficient. -/
theorem ccmFirstClockJuliaSixthPower_block_badTerm_sq_lower {m p : ℕ} (hm : 25 ≤ m)
    (hp : p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4)) :
    (1 / 4 : ℝ) * Real.log (p : ℝ) ^ 2 / p ≤
      ccmFirstClockReducedBadPrimeTerm (ccmFirstClockJuliaSixthPowerAperture m)
        ⟨p, (mem_suzukiMangoldtFivePrimeBlock.mp hp).1⟩ ^ 2 := by
  let q : Nat.Primes := ⟨p, (mem_suzukiMangoldtFivePrimeBlock.mp hp).1⟩
  let b := ccmFirstClockReducedBadPrimeTerm (ccmFirstClockJuliaSixthPowerAperture m) q
  let d := (1 / 2 : ℝ) * Real.log (p : ℝ) * criticalPrimeTowerRadius p
  have hpPrime := (mem_suzukiMangoldtFivePrimeBlock.mp hp).1
  have hpCutNat : p ≤ m ^ 6 := by
    simpa only [ccmFirstClockJuliaSixthPower_cutoff (show 0 < m by omega)] using
      (Nat.log_eq_one_iff.mp (ccmFirstClockJuliaSixthPower_block_primePowerLength_eq_one hm hp)).2.2
  have hm0 : 0 < m := by omega
  have hL : 0 < ccmFirstClockJuliaSixthPowerAperture m := by
    rw [ccmFirstClockJuliaSixthPowerAperture]
    exact mul_pos (by norm_num)
      (Real.log_pos (by exact_mod_cast (show 1 < m by omega)))
  have hpCut : (q : ℕ) ≤ ⌊Real.exp (ccmFirstClockJuliaSixthPowerAperture m)⌋₊ := by
    simpa only [q, ccmFirstClockJuliaSixthPower_cutoff hm0] using hpCutNat
  have hb : 0 ≤ b := ccmFirstClockReducedBadPrimeTerm_nonneg hL q hpCut
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    (Real.log_pos (by exact_mod_cast hpPrime.one_lt)).le
  have hradius : 0 ≤ criticalPrimeTowerRadius p :=
    (criticalPrimeTowerRadius_pos hpPrime.pos).le
  have hphase := ccmFirstClockJuliaSixthPower_block_phase hm hp
  have hsin := half_le_neg_sin_of_four_pi_div_three_le_of_le_three_pi_div_two hphase.1.le hphase.2
  have hdb : d ≤ b := by
    dsimp only [b, d]
    rw [ccmFirstClockJuliaSixthPower_block_badTerm_eq hm hp]
    have hmul := mul_le_mul_of_nonneg_left hsin
      (mul_nonneg hlogp hradius)
    nlinarith
  have hd : 0 ≤ d := mul_nonneg (mul_nonneg (by norm_num) hlogp) hradius
  have hsq : d ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hd hb).2 hdb
  calc
    (1 / 4 : ℝ) * Real.log (p : ℝ) ^ 2 / p = d ^ 2 := by
      dsimp only [d]
      rw [div_eq_mul_inv, ← criticalPrimeTowerRadius_sq]
      ring
    _ ≤ b ^ 2 := hsq

/-- Totalized natural-prime interface to the reduced bad coefficient. -/
def ccmFirstClockReducedBadNatTerm (L : ℝ) (p : ℕ) : ℝ :=
  if hp : p.Prime then ccmFirstClockReducedBadPrimeTerm L ⟨p, hp⟩ else 0

/-- Totalized bad coefficient agrees with the subtype coefficient on primes. -/
@[simp] theorem ccmFirstClockReducedBadNatTerm_of_prime (L : ℝ) {p : ℕ} (hp : p.Prime) :
    ccmFirstClockReducedBadNatTerm L p = ccmFirstClockReducedBadPrimeTerm L ⟨p, hp⟩ := by
  simp [ccmFirstClockReducedBadNatTerm, hp]

/-- Convert phase weight to the Chebyshev-compatible logarithmic block weight. -/
theorem ccmFirstClockJuliaSixthPower_block_weighted_lower {m p : ℕ} (hm : 25 ≤ m)
    (hp : p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4)) :
    Real.log (m : ℝ) / (5 * (m : ℝ) ^ 4) * Real.log (p : ℝ) ≤
      (1 / 4 : ℝ) * Real.log (p : ℝ) ^ 2 / p := by
  obtain ⟨hpPrime, hpLower, hpUpper⟩ := mem_suzukiMangoldtFivePrimeBlock.mp hp
  have hmR : (0 : ℝ) < m := by positivity
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hpLowerR : 2 * (m : ℝ) ^ 4 < (p : ℝ) := by exact_mod_cast hpLower
  have hpUpperR : (p : ℝ) ≤ 5 * (m : ℝ) ^ 4 := by exact_mod_cast hpUpper
  have hlogLowerRaw := Real.log_lt_log (by positivity : 0 < 2 * (m : ℝ) ^ 4) hpLowerR
  have hlogLower : 4 * Real.log (m : ℝ) ≤ Real.log (p : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity),
      Real.log_pow] at hlogLowerRaw
    norm_num at hlogLowerRaw
    linarith
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    (Real.log_pos (by exact_mod_cast hpPrime.one_lt)).le
  have hlogProduct :
      4 * Real.log (m : ℝ) * Real.log (p : ℝ) ≤
        Real.log (p : ℝ) ^ 2 := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hlogLower hlogp
  have hinv : (5 * (m : ℝ) ^ 4)⁻¹ ≤ (p : ℝ)⁻¹ :=
    inv_anti₀ hpR hpUpperR
  calc
    Real.log (m : ℝ) / (5 * (m : ℝ) ^ 4) * Real.log (p : ℝ) =
        (1 / 4 : ℝ) * (4 * Real.log (m : ℝ) * Real.log (p : ℝ)) *
          (5 * (m : ℝ) ^ 4)⁻¹ := by ring
    _ ≤ (1 / 4 : ℝ) * Real.log (p : ℝ) ^ 2 *
          (5 * (m : ℝ) ^ 4)⁻¹ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogProduct (by norm_num)) (by positivity)
    _ ≤ (1 / 4 : ℝ) * Real.log (p : ℝ) ^ 2 * (p : ℝ)⁻¹ := by
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = (1 / 4 : ℝ) * Real.log (p : ℝ) ^ 2 / p := by ring

/-- Chebyshev prime mass forces the block diagonal above `log m / 20`. -/
theorem ccmFirstClockJuliaSixthPower_block_diagonal_lower {m : ℕ} (hm : 25 ≤ m)
    (hmCheb : Real.exp 20 ≤ ((m ^ 4 : ℕ) : ℝ)) :
    Real.log (m : ℝ) / 20 ≤
      ∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
        ccmFirstClockReducedBadNatTerm (ccmFirstClockJuliaSixthPowerAperture m) p ^ 2 := by
  have hmR : (0 : ℝ) < m := by positivity
  have hlogm : 0 ≤ Real.log (m : ℝ) :=
    (Real.log_pos (by exact_mod_cast (show 1 < m by omega))).le
  have hcheb := chebyshev_fivePrimeBlock_logMass_floor hmCheb
  calc
    Real.log (m : ℝ) / 20 =
        (Real.log (m : ℝ) / (5 * (m : ℝ) ^ 4)) *
          (((m ^ 4 : ℕ) : ℝ) / 4) := by
      push_cast
      field_simp
      ring
    _ ≤ (Real.log (m : ℝ) / (5 * (m : ℝ) ^ 4)) *
          ∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4), Real.log (p : ℝ) := by
      exact mul_le_mul_of_nonneg_left hcheb (by positivity)
    _ = ∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
          Real.log (m : ℝ) / (5 * (m : ℝ) ^ 4) * Real.log (p : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
          (1 / 4 : ℝ) * Real.log (p : ℝ) ^ 2 / p := by
      exact Finset.sum_le_sum fun p hp ↦ ccmFirstClockJuliaSixthPower_block_weighted_lower hm hp
    _ ≤ ∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
          ccmFirstClockReducedBadNatTerm (ccmFirstClockJuliaSixthPowerAperture m) p ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      rw [ccmFirstClockReducedBadNatTerm_of_prime _ (mem_suzukiMangoldtFivePrimeBlock.mp hp).1]
      exact ccmFirstClockJuliaSixthPower_block_badTerm_sq_lower hm hp

/-- A literal bad packet's complete diagonal survives its pointwise nonnegative Julia kernel. -/
theorem ccmFirstClockJuliaBadDiagonalEnergy_le_coherentEnergy
    {N : ℕ} {x L : ℝ} (hL : 0 < L) (p : Fin N → Nat.Primes)
    (hpCut : ∀ i, (p i : ℕ) ≤ ⌊Real.exp L⌋₊) :
    ∑ i, ccmFirstClockReducedBadPrimeTerm L (p i) ^ 2 ≤
      ccmFirstClockJuliaBadCoherentEnergy x L p := by
  simpa only [ccmFirstClockJuliaBadCoherentEnergy,
    GaloisForLFunctions.HTGeometry.realKernelPacketEnergy] using
    (GaloisForLFunctions.HTGeometry.realKernelPacketDiagonal_le_energy_of_nonneg
      HTGeometry.juliaDefectAttenuationKernel
      (fun y ↦ (HTGeometry.juliaDefectAttenuationKernel_pos y).le)
      HTGeometry.juliaDefectAttenuationKernel_zero
      (fun i ↦ x * Real.log (p i : ℝ))
      (fun i ↦ ccmFirstClockReducedBadPrimeTerm L (p i))
      (fun i ↦ ccmFirstClockReducedBadPrimeTerm_nonneg hL (p i) (hpCut i)))

/-- Full admitted-prime Julia energy retains every squared reduced bad coefficient. -/
theorem ccmFirstClockJuliaFullBadDiagonalEnergy_le_coherentEnergy {x L : ℝ} (hL : 0 < L) :
    ∑ p ∈ Nat.primesLE ⌊Real.exp L⌋₊, ccmFirstClockReducedBadNatTerm L p ^ 2 ≤
      ccmFirstClockJuliaBadCoherentEnergy x L
        (ccmFirstClockAdmittedPrimePacket L) := by
  have hpacket := ccmFirstClockJuliaBadDiagonalEnergy_le_coherentEnergy (x := x) hL
    (ccmFirstClockAdmittedPrimePacket L)
    (ccmFirstClockAdmittedPrimePacket_le_cutoff L)
  calc
    ∑ p ∈ Nat.primesLE ⌊Real.exp L⌋₊, ccmFirstClockReducedBadNatTerm L p ^ 2 =
        ∑ i, ccmFirstClockReducedBadPrimeTerm L
          (ccmFirstClockAdmittedPrimePacket L i) ^ 2 := by
      rw [← sum_ccmFirstClockAdmittedPrimePacket L (fun p ↦ ccmFirstClockReducedBadNatTerm L p ^ 2)]
      apply Finset.sum_congr rfl
      intro i _
      rw [ccmFirstClockReducedBadNatTerm_of_prime _ (ccmFirstClockAdmittedPrimePacket L i).property]
      congr 2
    _ ≤ ccmFirstClockJuliaBadCoherentEnergy x L
        (ccmFirstClockAdmittedPrimePacket L) := hpacket

/-- Aperture-independent logarithmic lower floor for the literal full bad coherent energy. -/
theorem ccmFirstClockJuliaFullBadCoherentEnergy_sixthPower_lower {m : ℕ} (hm : 25 ≤ m)
    (hmCheb : Real.exp 20 ≤ ((m ^ 4 : ℕ) : ℝ)) (x : ℝ) :
    Real.log (m : ℝ) / 20 ≤
      ccmFirstClockJuliaBadCoherentEnergy x (ccmFirstClockJuliaSixthPowerAperture m)
        (ccmFirstClockAdmittedPrimePacket (ccmFirstClockJuliaSixthPowerAperture m)) := by
  have hm0 : 0 < m := by omega
  have hL : 0 < ccmFirstClockJuliaSixthPowerAperture m := by
    rw [ccmFirstClockJuliaSixthPowerAperture]
    exact mul_pos (by norm_num)
      (Real.log_pos (by exact_mod_cast (show 1 < m by omega)))
  have hsubset : suzukiMangoldtFivePrimeBlock (m ^ 4) ⊆
      Nat.primesLE ⌊Real.exp (ccmFirstClockJuliaSixthPowerAperture m)⌋₊ := by
    intro p hp
    obtain ⟨hpPrime, _hpLower, hpUpper⟩ :=
      mem_suzukiMangoldtFivePrimeBlock.mp hp
    rw [ccmFirstClockJuliaSixthPower_cutoff hm0, Nat.mem_primesLE]
    constructor
    · calc
        p ≤ 5 * m ^ 4 := hpUpper
        _ ≤ m ^ 2 * m ^ 4 := Nat.mul_le_mul_right _ (by nlinarith)
        _ = m ^ 6 := by ring
    · exact hpPrime
  have hblockFull :
      ∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
          ccmFirstClockReducedBadNatTerm (ccmFirstClockJuliaSixthPowerAperture m) p ^ 2 ≤
        ∑ p ∈ Nat.primesLE ⌊Real.exp (ccmFirstClockJuliaSixthPowerAperture m)⌋₊,
          ccmFirstClockReducedBadNatTerm (ccmFirstClockJuliaSixthPowerAperture m) p ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun _ _ _ ↦ sq_nonneg _)
  exact (ccmFirstClockJuliaSixthPower_block_diagonal_lower hm hmCheb).trans
    (hblockFull.trans (ccmFirstClockJuliaFullBadDiagonalEnergy_le_coherentEnergy hL))

/-- At zero Julia scale, a fixed full packet becomes rank-one coherent. -/
theorem tendsto_ccmFirstClockJuliaFullBadCoherentEnergy_zero (L : ℝ) :
    Tendsto (fun x ↦ ccmFirstClockJuliaBadCoherentEnergy x L
        (ccmFirstClockAdmittedPrimePacket L))
      (𝓝 0)
      (𝓝 ((∑ i, ccmFirstClockReducedBadPrimeTerm L
        (ccmFirstClockAdmittedPrimePacket L i)) ^ 2)) := by
  simpa only [ccmFirstClockJuliaBadCoherentEnergy,
    GaloisForLFunctions.HTGeometry.realKernelPacketEnergy] using
    (GaloisForLFunctions.HTGeometry.realKernelPacketEnergy_scale_tendsto_mass_sq
      HTGeometry.juliaDefectAttenuationKernel
      HTGeometry.tendsto_juliaDefectAttenuationKernel_zero
      (fun i ↦ Real.log (ccmFirstClockAdmittedPrimePacket L i : ℝ))
      (fun i ↦ ccmFirstClockReducedBadPrimeTerm L
        (ccmFirstClockAdmittedPrimePacket L i)))

/-- Literal full-window bad energy is unbounded along sixth-power apertures, uniformly in scale. -/
theorem ccmFirstClockJuliaFullBadCoherentEnergy_unbounded_uniformly_in_scale (C : ℝ) :
    ∃ m : ℕ, ∀ x : ℝ,
      C < ccmFirstClockJuliaBadCoherentEnergy x (ccmFirstClockJuliaSixthPowerAperture m)
        (ccmFirstClockAdmittedPrimePacket (ccmFirstClockJuliaSixthPowerAperture m)) := by
  have hlog : Tendsto (fun m : ℕ ↦ Real.log (m : ℝ) / 20) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const
      (by norm_num)
  have hC : ∀ᶠ m : ℕ in atTop, C + 1 ≤ Real.log (m : ℝ) / 20 :=
    hlog.eventually_ge_atTop (C + 1)
  have hExp : ∀ᶠ m : ℕ in atTop, Real.exp 20 ≤ (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (Real.exp 20)
  have hTwentyFive : ∀ᶠ m : ℕ in atTop, 25 ≤ m := eventually_ge_atTop 25
  have hEvent : ∀ᶠ m : ℕ in atTop,
      25 ≤ m ∧ Real.exp 20 ≤ ((m ^ 4 : ℕ) : ℝ) ∧
        C < Real.log (m : ℝ) / 20 := by
    filter_upwards [hC, hExp, hTwentyFive] with m hmC hmExp hm25
    have hmPowNat : m ≤ m ^ 4 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < m)
        (by omega : 1 ≤ 4)
    have hmPow : (m : ℝ) ≤ ((m ^ 4 : ℕ) : ℝ) := by exact_mod_cast hmPowNat
    exact ⟨hm25, hmExp.trans hmPow, by linarith⟩
  obtain ⟨m, hm25, hmCheb, hmC⟩ := hEvent.exists
  exact ⟨m, fun x ↦ hmC.trans_le (ccmFirstClockJuliaFullBadCoherentEnergy_sixthPower_lower hm25 hmCheb x)⟩

end RHTower

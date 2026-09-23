import GaloisForLFunctions.RHTower.CCMFirstClockJuliaPrincipalRelativeNoGo
import GaloisForLFunctions.RHTower.HighExponentShellFusionConservation

/-!
# Source-fusion superselection boundary for the first-clock Julia route

Finite common-character fusion exposes a canonical centered transverse energy. On the
source-faithful sixth-power pure-bad prime block, that energy is at most the uncentered bad
diagonal, hence only logarithmic-square, while the squared source excursion is quartic. Thus plain
centering cannot supply the missing Route-J domination.

The infinite-shell endpoint is independently singular: neither a Bessel realization with constant
unit response nor the orthogonal Hilbert codiagonal gives a stable post-fusion selector. These
unconditional results close regular centered fusion, not the surviving singular pre-fusion
source-orientation problem.
-/

open Set Finset Filter Topology
open scoped BigOperators

noncomputable section
namespace RHTower

/-- Centered label energy of the pure-bad sixth-power prime block. -/
def ccmFirstClockJuliaSixthPowerBlockCenteredFusionEnergy (m : ℕ) : ℝ :=
  let block := suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ))
  let bad :=
    ccmFirstClockReducedBadNatTerm (ccmFirstClockJuliaSixthPowerAperture m)
  let mean := (∑ p ∈ block, bad p) / (block.card : ℝ)
  ∑ p ∈ block, (bad p - mean) ^ (2 : ℕ)

/-- Centering removes exactly the squared fused mass divided by label count. -/
theorem ccmFirstClockJuliaSixthPowerBlockCenteredFusionEnergy_eq
    {m : ℕ} (hcard : (suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ))).Nonempty) :
    ccmFirstClockJuliaSixthPowerBlockCenteredFusionEnergy m =
      (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ)),
          ccmFirstClockReducedBadNatTerm
            (ccmFirstClockJuliaSixthPowerAperture m) p ^ (2 : ℕ)) -
        (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ)),
          ccmFirstClockReducedBadNatTerm
            (ccmFirstClockJuliaSixthPowerAperture m) p) ^ (2 : ℕ) /
          ((suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ))).card : ℝ) := by
  let block := suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ))
  let bad :=
    ccmFirstClockReducedBadNatTerm (ccmFirstClockJuliaSixthPowerAperture m)
  let total := ∑ p ∈ block, bad p
  let mean := total / (block.card : ℝ)
  have hcardNat : block.card ≠ 0 := Finset.card_ne_zero.mpr (by simpa [block] using hcard)
  have hcardReal : (block.card : ℝ) ≠ 0 := by exact_mod_cast hcardNat
  have hmean :
      (block.card : ℝ) * mean = total := by
    dsimp only [mean]
    field_simp
  unfold ccmFirstClockJuliaSixthPowerBlockCenteredFusionEnergy
  dsimp only
  change (∑ p ∈ block, (bad p - mean) ^ (2 : ℕ)) =
    (∑ p ∈ block, bad p ^ (2 : ℕ)) - total ^ (2 : ℕ) / (block.card : ℝ)
  have hcross :
      (∑ p ∈ block, 2 * bad p * mean) = 2 * mean * total := by
    calc
      (∑ p ∈ block, 2 * bad p * mean) =
          ∑ p ∈ block, bad p * (2 * mean) := by
            apply Finset.sum_congr rfl
            intro p hp
            ring
      _ = (∑ p ∈ block, bad p) * (2 * mean) := by
            rw [Finset.sum_mul]
      _ = 2 * mean * total := by
            dsimp only [total]
            ring
  rw [show (∑ p ∈ block, (bad p - mean) ^ (2 : ℕ)) =
      (∑ p ∈ block, bad p ^ (2 : ℕ)) -
        2 * mean * total + (block.card : ℝ) * mean ^ (2 : ℕ) by
      simp only [sub_sq, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_const, nsmul_eq_mul]
      rw [hcross]]
  rw [← hmean]
  field_simp
  ring

/-- Centered fusion energy is nonnegative because it is a sum of squares. -/
theorem ccmFirstClockJuliaSixthPowerBlockCenteredFusionEnergy_nonneg (m : ℕ) :
    0 ≤ ccmFirstClockJuliaSixthPowerBlockCenteredFusionEnergy m := by
  unfold ccmFirstClockJuliaSixthPowerBlockCenteredFusionEnergy
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Any arithmetic block with the proved positive bad-mass floor is nonempty. -/
theorem suzukiMangoldtFivePrimeBlock_fourthPower_nonempty
    {m : ℕ} (hm : 25 ≤ m)
    (hmCheb : Real.exp 20 ≤ ((m ^ (4 : ℕ) : ℕ) : ℝ)) :
    (suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ))).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hmass :=
    ccmFirstClockJuliaSixthPower_block_badMass_lower hm hmCheb
  rw [hempty] at hmass
  simp only [Finset.sum_empty] at hmass
  have hmR : (0 : ℝ) < m := by positivity
  nlinarith

/-- Centering can only remove nonnegative fused mass, hence transverse energy is at most the
uncentered diagonal. -/
theorem ccmFirstClockJuliaSixthPowerBlockCenteredFusionEnergy_le_diagonal
    {m : ℕ} (hm : 25 ≤ m)
    (hmCheb : Real.exp 20 ≤ ((m ^ (4 : ℕ) : ℕ) : ℝ)) :
    ccmFirstClockJuliaSixthPowerBlockCenteredFusionEnergy m ≤
      ∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ)),
        ccmFirstClockReducedBadNatTerm
          (ccmFirstClockJuliaSixthPowerAperture m) p ^ (2 : ℕ) := by
  rw [ccmFirstClockJuliaSixthPowerBlockCenteredFusionEnergy_eq
    (suzukiMangoldtFivePrimeBlock_fourthPower_nonempty hm hmCheb)]
  have hcard :
      (0 : ℝ) <
        ((suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ))).card : ℝ) := by
    exact_mod_cast
      (Finset.card_pos.mpr
        (suzukiMangoldtFivePrimeBlock_fourthPower_nonempty hm hmCheb))
  have hquot :
      0 ≤
        (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ)),
          ccmFirstClockReducedBadNatTerm
            (ccmFirstClockJuliaSixthPowerAperture m) p) ^ (2 : ℕ) /
          ((suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ))).card : ℝ) :=
    div_nonneg (sq_nonneg _) hcard.le
  linarith

/-- Plain centered fusion is only logarithmic-square on the arithmetic pure-bad block. -/
theorem ccmFirstClockJuliaSixthPowerBlockCenteredFusionEnergy_upper
    {m : ℕ} (hm : 25 ≤ m)
    (hmCheb : Real.exp 20 ≤ ((m ^ (4 : ℕ) : ℕ) : ℝ)) :
    ccmFirstClockJuliaSixthPowerBlockCenteredFusionEnergy m ≤
      65 * Real.log (m : ℝ) ^ (2 : ℕ) :=
  (ccmFirstClockJuliaSixthPowerBlockCenteredFusionEnergy_le_diagonal hm hmCheb).trans
    (ccmFirstClockJuliaSixthPower_block_badDiagonal_upper hm)

/-- On every sufficiently large certified arithmetic block, centered fusion energy is strictly
smaller than the squared pure-bad excursion mass. -/
theorem ccmFirstClockJuliaSixthPowerBlockCenteredFusionEnergy_lt_badMass_sq
    {m : ℕ} (hm : 300 ≤ m)
    (hmCheb : Real.exp 20 ≤ ((m ^ (4 : ℕ) : ℕ) : ℝ)) :
    ccmFirstClockJuliaSixthPowerBlockCenteredFusionEnergy m <
      (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ)),
        ccmFirstClockReducedBadNatTerm
          (ccmFirstClockJuliaSixthPowerAperture m) p) ^ (2 : ℕ) := by
  have hm25 : 25 ≤ m := hm.trans' (by norm_num)
  have henergy :=
    ccmFirstClockJuliaSixthPowerBlockCenteredFusionEnergy_upper hm25 hmCheb
  have hmass :=
    ccmFirstClockJuliaSixthPower_block_badMass_lower hm25 hmCheb
  let block := suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ))
  let bad :=
    ccmFirstClockReducedBadNatTerm (ccmFirstClockJuliaSixthPowerAperture m)
  have hmass0 : 0 ≤ ∑ p ∈ block, bad p := by
    apply Finset.sum_nonneg
    intro p hp
    have hpPrime := (mem_suzukiMangoldtFivePrimeBlock.mp hp).1
    dsimp only [bad]
    rw [ccmFirstClockReducedBadNatTerm_of_prime _ hpPrime]
    exact (ccmFirstClockJuliaSixthPower_block_badTerm_pos hm25 hp).le
  have hlower0 : 0 ≤ (m : ℝ) ^ (2 : ℕ) / 24 := by positivity
  have hmassSq :
      ((m : ℝ) ^ (2 : ℕ) / 24) ^ (2 : ℕ) ≤ (∑ p ∈ block, bad p) ^ (2 : ℕ) :=
    (sq_le_sq₀ hlower0 hmass0).2 (by simpa only [block, bad] using hmass)
  have hmR : (0 : ℝ) < m := by positivity
  have hlog0 : 0 ≤ Real.log (m : ℝ) :=
    (Real.log_pos (by exact_mod_cast (show 1 < m by omega))).le
  have hlogLe : Real.log (m : ℝ) ≤ (m : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hmR
    linarith
  have hlogSq : Real.log (m : ℝ) ^ (2 : ℕ) ≤ (m : ℝ) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg ((m : ℝ) - Real.log (m : ℝ))]
  have hmSq : (74880 : ℝ) ≤ (m : ℝ) ^ (2 : ℕ) := by
    have hmReal : (300 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hquartic : 74880 * (m : ℝ) ^ (2 : ℕ) ≤ (m : ℝ) ^ (4 : ℕ) := by
    have h := mul_le_mul_of_nonneg_right hmSq (sq_nonneg (m : ℝ))
    nlinarith
  have hlogQuartic : 74880 * Real.log (m : ℝ) ^ (2 : ℕ) ≤ (m : ℝ) ^ (4 : ℕ) :=
    (mul_le_mul_of_nonneg_left hlogSq (by norm_num)).trans hquartic
  dsimp only [block, bad] at hmassSq
  nlinarith [pow_pos hmR 4]

/-- **Regular source-fusion boundary for Route J.** Plain finite centering cannot dominate the
arithmetic pure-bad excursion. At the infinite-shell endpoint, neither a Bessel realization with
constant unit response nor the orthogonal Hilbert codiagonal supplies a stable replacement. -/
theorem ccmFirstClock_sourceFusion_regularHilbert_noGo
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u : ℕ → E) (B : ℝ)
    (hB : GaloisForLFunctions.HasBesselBound u B)
    {m : ℕ} (hm : 300 ≤ m)
    (hmCheb : Real.exp 20 ≤ ((m ^ (4 : ℕ) : ℕ) : ℝ)) :
    ccmFirstClockJuliaSixthPowerBlockCenteredFusionEnergy m <
        (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ)),
          ccmFirstClockReducedBadNatTerm
            (ccmFirstClockJuliaSixthPowerAperture m) p) ^ (2 : ℕ) ∧
      (¬ ∃ y : E, ∀ i, inner ℂ (u i) y = 1) ∧
      ¬ IsSequentiallyClosableBetween shellCodiagonal shellLabelEmbedding := by
  exact ⟨ccmFirstClockJuliaSixthPowerBlockCenteredFusionEnergy_lt_badMass_sq hm hmCheb,
    highShell_no_stableHilbert_unitFusion u B hB⟩

end RHTower

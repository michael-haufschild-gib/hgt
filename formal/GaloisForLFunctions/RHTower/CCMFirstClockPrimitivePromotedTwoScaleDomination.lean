import GaloisForLFunctions.RHTower.CCMFirstClockPrimitivePromotedExteriorSource

/-!
# Two-scale domination by the primitive-promoted anchored source

The primitive-promoted modular exterior has the necessary cellwise amplitude, but that alone does
not prove packet domination.  This module supplies an explicit source-only finite core.

Take the first-clock block at scale `n` and a second block at the fixed dilation `2^32 n`.  Center
the squared-height modular jet at `log n / 2` and phase it at scale `1/64`.  Every cross pair has a
uniformly positive centered-height and sine gap.  Elementary Chebyshev mass bounds then give a
linear lower bound for the cross energy.  On `n=m^4` it dominates the complete certified
first-clock bad-mass square.

The large fixed dilation is deliberately crude: it isolates existence of source domination from
the still-open cofinal uniform-budget problem.  No Xi zero, target sign, numerical experiment, or
RH input occurs.
-/

open Set Finset Filter Topology
open scoped BigOperators

noncomputable section
namespace RHTower
namespace PrimitivePromotedTwoScale

theorem radius_ge_inv_three_sqrt
    {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hpUpper : p ≤ 5 * n) :
    (3 * Real.sqrt (n : ℝ))⁻¹ ≤ criticalPrimeTowerRadius p := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hc : 0 ≤ (3 * Real.sqrt (n : ℝ))⁻¹ := by positivity
  have hr := (criticalPrimeTowerRadius_pos hp.pos).le
  apply (sq_le_sq₀ hc hr).1
  rw [criticalPrimeTowerRadius_sq]
  have hcSq :
      ((3 * Real.sqrt (n : ℝ))⁻¹) ^ 2 =
        (9 * (n : ℝ))⁻¹ := by
    rw [inv_pow, mul_pow, Real.sq_sqrt hnR.le]
    ring
  rw [hcSq]
  have hpNine : (p : ℝ) ≤ 9 * (n : ℝ) := by
    exact_mod_cast (hpUpper.trans (by omega : 5 * n ≤ 9 * n))
  simpa only [one_div] using one_div_le_one_div_of_le hpR hpNine

theorem radius_le_inv_sqrt
    {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hpLower : n < p) :
    criticalPrimeTowerRadius p ≤ (Real.sqrt (n : ℝ))⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hc : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ := by positivity
  have hr := (criticalPrimeTowerRadius_pos hp.pos).le
  apply (sq_le_sq₀ hr hc).1
  rw [criticalPrimeTowerRadius_sq]
  have hcSq :
      ((Real.sqrt (n : ℝ))⁻¹) ^ 2 = ((n : ℝ))⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hnR.le]
  rw [hcSq]
  have hnp : (n : ℝ) ≤ p := by
    exact_mod_cast hpLower.le
  simpa only [one_div] using one_div_le_one_div_of_le hnR hnp

/-- A coarse source-only upper bound for logarithmic prime mass in the fivefold block. -/
theorem fivePrimeBlock_logMass_upper
    {n : ℕ} (hn : 0 < n) :
    ∑ p ∈ suzukiMangoldtFivePrimeBlock n, Real.log p ≤
      10 * (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [suzukiMangoldtFivePrimeBlock,
    sum_log_windowPrimes (by nlinarith [hnR] :
      2 * (n : ℝ) ≤ 5 * (n : ℝ))]
  have hthetaNonneg := Chebyshev.theta_nonneg (2 * (n : ℝ))
  have hthetaUpper :=
    Chebyshev.theta_le_log4_mul_x
      (show (0 : ℝ) ≤ 5 * (n : ℝ) by positivity)
  have hlog4 : Real.log 4 < 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    have h := Real.log_lt_sub_one_of_pos (x := (2 : ℝ))
      (by norm_num) (by norm_num)
    linarith
  nlinarith

/-- The promoted primitive mass of a Chebyshev block has square-root lower scale. -/
theorem promotedMass_lower
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) :
    Real.sqrt (n : ℝ) / 12 ≤
      ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
        xiGammaEulerPrimitiveDepthZeroAmplitude p := by
  have hnPos : 0 < n := by
    have : (0 : ℝ) < n := (Real.exp_pos 20).trans_le hn
    exact_mod_cast this
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hterm :
      ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          (3 * Real.sqrt (n : ℝ))⁻¹ * Real.log (p : ℝ) ≤
        ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          xiGammaEulerPrimitiveDepthZeroAmplitude p := by
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hpPrime, _hpLower, hpUpper⟩ :=
      mem_suzukiMangoldtFivePrimeBlock.mp hp
    unfold xiGammaEulerPrimitiveDepthZeroAmplitude
    have h :=
      mul_le_mul_of_nonneg_left
        (radius_ge_inv_three_sqrt hnPos hpPrime hpUpper)
        (Real.log_nonneg
          (by exact_mod_cast hpPrime.one_le : (1 : ℝ) ≤ (p : ℝ)))
    nlinarith
  have hmass := chebyshev_fivePrimeBlock_logMass_floor hn
  calc
    Real.sqrt (n : ℝ) / 12 =
        (3 * Real.sqrt (n : ℝ))⁻¹ * ((n : ℝ) / 4) := by
      field_simp
      nlinarith [Real.sq_sqrt hnR.le]
    _ ≤ (3 * Real.sqrt (n : ℝ))⁻¹ *
        ∑ p ∈ suzukiMangoldtFivePrimeBlock n, Real.log p := by
      exact mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
        (3 * Real.sqrt (n : ℝ))⁻¹ * Real.log p := by
      rw [Finset.mul_sum]
    _ ≤ _ := hterm

/-- The same promoted mass has a coarse square-root upper scale. -/
theorem promotedMass_upper
    {n : ℕ} (hn : 0 < n) :
    ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
        xiGammaEulerPrimitiveDepthZeroAmplitude p ≤
      10 * Real.sqrt (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hterm :
      ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          xiGammaEulerPrimitiveDepthZeroAmplitude p ≤
        ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          (Real.sqrt (n : ℝ))⁻¹ * Real.log (p : ℝ) := by
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hpPrime, hpLower, _hpUpper⟩ :=
      mem_suzukiMangoldtFivePrimeBlock.mp hp
    unfold xiGammaEulerPrimitiveDepthZeroAmplitude
    have h :=
      mul_le_mul_of_nonneg_left
        (radius_le_inv_sqrt hn hpPrime (by omega))
        (Real.log_nonneg
          (by exact_mod_cast hpPrime.one_le : (1 : ℝ) ≤ (p : ℝ)))
    nlinarith
  have hmass := fivePrimeBlock_logMass_upper hn
  calc
    ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
        xiGammaEulerPrimitiveDepthZeroAmplitude p ≤
      ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
        (Real.sqrt (n : ℝ))⁻¹ * Real.log p := hterm
    _ = (Real.sqrt (n : ℝ))⁻¹ *
        ∑ p ∈ suzukiMangoldtFivePrimeBlock n, Real.log p := by
      rw [Finset.mul_sum]
    _ ≤ (Real.sqrt (n : ℝ))⁻¹ * (10 * (n : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = 10 * Real.sqrt (n : ℝ) := by
      field_simp
      nlinarith [Real.sq_sqrt hnR.le]

/-- Complete hard-block bad mass has a coarse linear squared upper bound. -/
theorem badMass_sq_upper
    {m : ℕ} (hm : 25 ≤ m) :
    (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
      ccmFirstClockReducedBadNatTerm
        (ccmFirstClockJuliaSixthPowerAperture m) p) ^ 2 ≤
      100 * ((m ^ 4 : ℕ) : ℝ) := by
  have hnPos : 0 < m ^ 4 := by positivity
  have hbadNonneg :
      0 ≤ ∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
        ccmFirstClockReducedBadNatTerm
          (ccmFirstClockJuliaSixthPowerAperture m) p := by
    apply Finset.sum_nonneg
    intro p hp
    have hpPrime := (mem_suzukiMangoldtFivePrimeBlock.mp hp).1
    rw [ccmFirstClockReducedBadNatTerm_of_prime _ hpPrime]
    exact (ccmFirstClockJuliaSixthPower_block_badTerm_pos hm hp).le
  have hsum :
      ∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
          ccmFirstClockReducedBadNatTerm
            (ccmFirstClockJuliaSixthPowerAperture m) p ≤
        ∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
          xiGammaEulerPrimitiveDepthZeroAmplitude p := by
    apply Finset.sum_le_sum
    intro p hp
    exact (xiGammaEulerPrimitive_block_badTerm_sandwich hm hp).2
  have hamp := promotedMass_upper hnPos
  have hten : 0 ≤ 10 * Real.sqrt (((m ^ 4 : ℕ) : ℝ)) := by
    positivity
  have hsq := (sq_le_sq₀ hbadNonneg hten).2 (hsum.trans hamp)
  have hsqrt :
      Real.sqrt (((m ^ 4 : ℕ) : ℝ)) ^ 2 =
        ((m ^ 4 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  nlinarith

/-- Fixed source dilation separating two independently supplied Chebyshev blocks. -/
def sourceDilation : ℕ := 2 ^ 32

theorem sourceDilation_pos : 0 < sourceDilation := by
  norm_num [sourceDilation]

theorem sourceDilation_log :
    Real.log (sourceDilation : ℝ) =
      32 * Real.log 2 := by
  rw [sourceDilation, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  norm_num

/-- Height relative to the source anchor `log n / 2`. -/
def relativeHeight (n p : ℕ) : ℝ :=
  Real.log (p : ℝ) / 2 - Real.log (n : ℝ) / 2

theorem low_relativeHeight_mem
    {n p : ℕ} (hn : 0 < n)
    (hp : p ∈ suzukiMangoldtFivePrimeBlock n) :
    relativeHeight n p ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hpPrime, hpLower, hpUpper⟩ :=
    mem_suzukiMangoldtFivePrimeBlock.mp hp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hnp : (n : ℝ) < p := by
    have : 2 * (n : ℝ) < p := by exact_mod_cast hpLower
    nlinarith
  have hlogLower := Real.log_lt_log hnR hnp
  have hpUpperR : (p : ℝ) ≤ 5 * (n : ℝ) := by
    exact_mod_cast hpUpper
  have hlogUpper := Real.log_le_log hpR hpUpperR
  rw [Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) hnR.ne'] at hlogUpper
  have hlog5 : Real.log (5 : ℝ) < 2 := by
    nlinarith [Real.log_five_lt_d9]
  constructor <;> unfold relativeHeight <;> linarith

theorem high_relativeHeight_mem
    {n q : ℕ} (hn : 0 < n)
    (hq : q ∈ suzukiMangoldtFivePrimeBlock (sourceDilation * n)) :
    relativeHeight n q ∈ Set.Icc (8 : ℝ) 17 := by
  obtain ⟨hqPrime, hqLower, hqUpper⟩ :=
    mem_suzukiMangoldtFivePrimeBlock.mp hq
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : (0 : ℝ) < sourceDilation := by
    exact_mod_cast sourceDilation_pos
  have hKn : (0 : ℝ) < sourceDilation * (n : ℝ) := by
    positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
  have hKnq : sourceDilation * (n : ℝ) < (q : ℝ) := by
    have : 2 * (sourceDilation * (n : ℝ)) < (q : ℝ) := by
      exact_mod_cast hqLower
    nlinarith
  have hlogLower := Real.log_lt_log hKn hKnq
  rw [Real.log_mul hK.ne' hnR.ne', sourceDilation_log] at hlogLower
  have hqUpperR :
      (q : ℝ) ≤ 5 * (sourceDilation * (n : ℝ)) := by
    exact_mod_cast hqUpper
  have hlogUpper := Real.log_le_log hqR hqUpperR
  rw [Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) hKn.ne',
    Real.log_mul hK.ne' hnR.ne', sourceDilation_log] at hlogUpper
  have hlog2lo : (1 / 2 : ℝ) < Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hlog2hi : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := (2 : ℝ))
      (by norm_num) (by norm_num)
    linarith
  have hlog5 : Real.log (5 : ℝ) < 2 := by
    nlinarith [Real.log_five_lt_d9]
  constructor <;> unfold relativeHeight <;> nlinarith

/-- Fixed source phase used on the separated blocks. -/
def twoScalePhase : ℝ := 1 / 64

/-- Cross pair of the Gamma-anchored squared-height jet. -/
def anchoredCrossPair (n p q : ℕ) : ℝ :=
  xiGammaEulerPrimitiveDepthZeroAmplitude p *
    xiGammaEulerPrimitiveDepthZeroAmplitude q *
      (relativeHeight n q ^ 2 - relativeHeight n p ^ 2) *
        Real.sin (twoScalePhase *
          (relativeHeight n q - relativeHeight n p))

/-- Every low/high cross pair pays at least three promoted amplitude products. -/
theorem anchoredCrossPair_lower
    {n p q : ℕ} (hn : 0 < n)
    (hp : p ∈ suzukiMangoldtFivePrimeBlock n)
    (hq : q ∈ suzukiMangoldtFivePrimeBlock (sourceDilation * n)) :
    3 * xiGammaEulerPrimitiveDepthZeroAmplitude p *
        xiGammaEulerPrimitiveDepthZeroAmplitude q ≤
      anchoredCrossPair n p q := by
  have hpPrime := (mem_suzukiMangoldtFivePrimeBlock.mp hp).1
  have hqPrime := (mem_suzukiMangoldtFivePrimeBlock.mp hq).1
  have hpRel := low_relativeHeight_mem hn hp
  have hqRel := high_relativeHeight_mem hn hq
  rcases hpRel with ⟨hpRel0, hpRel1⟩
  rcases hqRel with ⟨hqRel8, hqRel17⟩
  let d := relativeHeight n q - relativeHeight n p
  have hdLower : 7 ≤ d := by
    dsimp only [d]
    linarith
  have hdUpper : d ≤ 17 := by
    dsimp only [d]
    linarith
  have hcenter :
      60 ≤ relativeHeight n q ^ 2 - relativeHeight n p ^ 2 := by
    have hpSq : relativeHeight n p ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (relativeHeight n p - 1)]
    have hqSq : 64 ≤ relativeHeight n q ^ 2 := by
      nlinarith [sq_nonneg (relativeHeight n q - 8)]
    linarith
  have hphase0 : 0 ≤ twoScalePhase * d := by
    unfold twoScalePhase
    positivity
  have hphasePi : twoScalePhase * d ≤ Real.pi / 2 := by
    unfold twoScalePhase
    nlinarith [Real.pi_gt_three]
  have hJordan := Real.mul_le_sin hphase0 hphasePi
  have hpiInv : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
    exact (le_div_iff₀ Real.pi_pos).2 (by
      nlinarith [Real.pi_le_four])
  have hphaseLower : (1 / 10 : ℝ) ≤ twoScalePhase * d := by
    unfold twoScalePhase
    nlinarith
  have hsin : (1 / 20 : ℝ) ≤ Real.sin (twoScalePhase * d) := by
    have hmul := mul_le_mul_of_nonneg_right hpiInv hphase0
    calc
      (1 / 20 : ℝ) ≤ (1 / 2 : ℝ) * (twoScalePhase * d) := by
        nlinarith
      _ ≤ (2 / Real.pi) * (twoScalePhase * d) := hmul
      _ ≤ Real.sin (twoScalePhase * d) := hJordan
  have ha : 0 ≤ xiGammaEulerPrimitiveDepthZeroAmplitude p := by
    exact mul_nonneg
      (Real.log_nonneg
        (by exact_mod_cast hpPrime.one_le : (1 : ℝ) ≤ (p : ℝ)))
      (criticalPrimeTowerRadius_pos hpPrime.pos).le
  have hb : 0 ≤ xiGammaEulerPrimitiveDepthZeroAmplitude q := by
    exact mul_nonneg
      (Real.log_nonneg
        (by exact_mod_cast hqPrime.one_le : (1 : ℝ) ≤ (q : ℝ)))
      (criticalPrimeTowerRadius_pos hqPrime.pos).le
  unfold anchoredCrossPair
  dsimp only [d] at hsin
  have hkernel :
      3 ≤ (relativeHeight n q ^ 2 - relativeHeight n p ^ 2) *
        Real.sin (twoScalePhase *
          (relativeHeight n q - relativeHeight n p)) := by
    nlinarith
  nlinarith [mul_nonneg ha hb]

/-- Symmetric low/high cross energy of the anchored modular source. -/
def anchoredTwoScaleEnergy (n : ℕ) : ℝ :=
  2 * ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
    ∑ q ∈ suzukiMangoldtFivePrimeBlock (sourceDilation * n),
      anchoredCrossPair n p q

theorem anchoredTwoScaleEnergy_lower_product
    {n : ℕ} (hn : 0 < n) :
    6 *
        (∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          xiGammaEulerPrimitiveDepthZeroAmplitude p) *
        (∑ q ∈ suzukiMangoldtFivePrimeBlock (sourceDilation * n),
          xiGammaEulerPrimitiveDepthZeroAmplitude q) ≤
      anchoredTwoScaleEnergy n := by
  have hdouble :
      ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          ∑ q ∈ suzukiMangoldtFivePrimeBlock (sourceDilation * n),
            3 * xiGammaEulerPrimitiveDepthZeroAmplitude p *
              xiGammaEulerPrimitiveDepthZeroAmplitude q ≤
        ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          ∑ q ∈ suzukiMangoldtFivePrimeBlock (sourceDilation * n),
            anchoredCrossPair n p q := by
    apply Finset.sum_le_sum
    intro p hp
    apply Finset.sum_le_sum
    intro q hq
    exact anchoredCrossPair_lower hn hp hq
  have hfactor :
      (∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          ∑ q ∈ suzukiMangoldtFivePrimeBlock (sourceDilation * n),
            3 * xiGammaEulerPrimitiveDepthZeroAmplitude p *
              xiGammaEulerPrimitiveDepthZeroAmplitude q) =
        3 *
          (∑ p ∈ suzukiMangoldtFivePrimeBlock n,
            xiGammaEulerPrimitiveDepthZeroAmplitude p) *
          (∑ q ∈ suzukiMangoldtFivePrimeBlock (sourceDilation * n),
            xiGammaEulerPrimitiveDepthZeroAmplitude q) := by
    calc
      ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          ∑ q ∈ suzukiMangoldtFivePrimeBlock (sourceDilation * n),
            3 * xiGammaEulerPrimitiveDepthZeroAmplitude p *
              xiGammaEulerPrimitiveDepthZeroAmplitude q =
        ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          (3 * xiGammaEulerPrimitiveDepthZeroAmplitude p) *
            (∑ q ∈ suzukiMangoldtFivePrimeBlock (sourceDilation * n),
              xiGammaEulerPrimitiveDepthZeroAmplitude q) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mul_sum]
      _ = (∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          3 * xiGammaEulerPrimitiveDepthZeroAmplitude p) *
            (∑ q ∈ suzukiMangoldtFivePrimeBlock (sourceDilation * n),
              xiGammaEulerPrimitiveDepthZeroAmplitude q) := by
        rw [Finset.sum_mul]
      _ = 3 *
          (∑ p ∈ suzukiMangoldtFivePrimeBlock n,
            xiGammaEulerPrimitiveDepthZeroAmplitude p) *
          (∑ q ∈ suzukiMangoldtFivePrimeBlock (sourceDilation * n),
            xiGammaEulerPrimitiveDepthZeroAmplitude q) := by
        congr 1
        rw [Finset.mul_sum]
  unfold anchoredTwoScaleEnergy
  calc
    6 *
          (∑ p ∈ suzukiMangoldtFivePrimeBlock n,
            xiGammaEulerPrimitiveDepthZeroAmplitude p) *
          (∑ q ∈ suzukiMangoldtFivePrimeBlock (sourceDilation * n),
            xiGammaEulerPrimitiveDepthZeroAmplitude q) =
        2 * (3 *
          (∑ p ∈ suzukiMangoldtFivePrimeBlock n,
            xiGammaEulerPrimitiveDepthZeroAmplitude p) *
          (∑ q ∈ suzukiMangoldtFivePrimeBlock (sourceDilation * n),
            xiGammaEulerPrimitiveDepthZeroAmplitude q)) := by ring
    _ = 2 * (∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          ∑ q ∈ suzukiMangoldtFivePrimeBlock (sourceDilation * n),
            3 * xiGammaEulerPrimitiveDepthZeroAmplitude p *
              xiGammaEulerPrimitiveDepthZeroAmplitude q) := by rw [hfactor]
    _ ≤ 2 * (∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          ∑ q ∈ suzukiMangoldtFivePrimeBlock (sourceDilation * n),
            anchoredCrossPair n p q) :=
      mul_le_mul_of_nonneg_left hdouble (by norm_num)

theorem sqrt_sourceDilation_mul
    (n : ℕ) :
    Real.sqrt (((sourceDilation * n : ℕ) : ℝ)) =
      65536 * Real.sqrt (n : ℝ) := by
  have hKCast : (sourceDilation : ℝ) = (65536 : ℝ) ^ 2 := by
    norm_num [sourceDilation]
  rw [Nat.cast_mul, Real.sqrt_mul (by positivity :
    (0 : ℝ) ≤ sourceDilation), hKCast,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 65536)]

/-- The anchored two-scale source energy has a uniform linear lower floor. -/
theorem anchoredTwoScaleEnergy_linear_lower
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) :
    100 * (n : ℝ) ≤ anchoredTwoScaleEnergy n := by
  have hnPos : 0 < n := by
    have : (0 : ℝ) < n := (Real.exp_pos 20).trans_le hn
    exact_mod_cast this
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hKn :
      Real.exp 20 ≤ ((sourceDilation * n : ℕ) : ℝ) := by
    have hKOne : 1 ≤ sourceDilation := by
      norm_num [sourceDilation]
    have hnle : (n : ℝ) ≤ ((sourceDilation * n : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_mul_of_pos_left n sourceDilation_pos
    exact hn.trans hnle
  have hlow := promotedMass_lower hn
  have hhigh := promotedMass_lower hKn
  rw [sqrt_sourceDilation_mul] at hhigh
  have hprod :
      (65536 / 144 : ℝ) * (n : ℝ) ≤
        (∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          xiGammaEulerPrimitiveDepthZeroAmplitude p) *
        (∑ q ∈ suzukiMangoldtFivePrimeBlock (sourceDilation * n),
          xiGammaEulerPrimitiveDepthZeroAmplitude q) := by
    have hsqrt := Real.sq_sqrt hnR.le
    have hlowNonneg : 0 ≤
        ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          xiGammaEulerPrimitiveDepthZeroAmplitude p := by
      have := Real.sqrt_nonneg (n : ℝ)
      nlinarith
    have hhighNonneg : 0 ≤
        ∑ q ∈ suzukiMangoldtFivePrimeBlock (sourceDilation * n),
          xiGammaEulerPrimitiveDepthZeroAmplitude q := by
      have := Real.sqrt_nonneg (n : ℝ)
      nlinarith
    have hmul1 :=
      mul_le_mul_of_nonneg_left hhigh
        (by positivity : 0 ≤ Real.sqrt (n : ℝ) / 12)
    have hmul2 :=
      mul_le_mul_of_nonneg_right hlow hhighNonneg
    nlinarith [hmul1.trans hmul2]
  have henergy := anchoredTwoScaleEnergy_lower_product hnPos
  nlinarith

/-- **Source domination theorem.**  The explicit anchored two-scale current dominates the full
certified first-clock bad-mass square. -/
theorem anchoredTwoScaleEnergy_dominates_badMass
    {m : ℕ} (hm : 25 ≤ m)
    (hmCheb : Real.exp 20 ≤ ((m ^ 4 : ℕ) : ℝ)) :
    (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
      ccmFirstClockReducedBadNatTerm
        (ccmFirstClockJuliaSixthPowerAperture m) p) ^ 2 ≤
      anchoredTwoScaleEnergy (m ^ 4) := by
  exact (badMass_sq_upper hm).trans
    (anchoredTwoScaleEnergy_linear_lower hmCheb)

end PrimitivePromotedTwoScale
end RHTower

import GaloisForLFunctions.RHTower.CCMFirstClockSourcePhasedExteriorCurrent

/-!
# Bounded-polarization no-go for the first-clock exterior current

The source-height phase construction turns the calibrated real antisymmetric Julia--Gamma
exterior cell into a nonzero Hermitian scalar current.  Phase wrapping cannot repair its
quantitative deficit.  This module proves a stronger, phase-free statement.

For arbitrary complex multipliers of norm at most `B`, a rank-two exterior cell

`aᵢ aⱼ (hᵢ - hⱼ)`

on a packet of height diameter `D` has Hermitian scalar energy at most

`B² D (∑ᵢ aᵢ)²`.

On the first-clock macroscopic prime block at Euler depth zero, `D ≤ 1` and elementary
Chebyshev--Cauchy estimates give `(∑ aᵢ)² = O(m⁴ / log(m⁴))`, whereas the certified squared
pure-bad mass is at least `m⁴ / 576`.  Thus every bounded polarization, including arbitrary
packet-dependent wrapped phases, eventually fails Route J's domination requirement.

No phase sign, phase-flow, no-wrap, zero, or RH hypothesis occurs.
-/

open Set Finset Filter Topology
open scoped BigOperators

noncomputable section
namespace RHTower

/-- Hermitian scalarization of `i` times a real rank-two exterior cell against arbitrary complex
multipliers. -/
def boundedPolarizedExteriorHermitianEnergy
    {ι : Type*} (packet : Finset ι) (amplitude height : ι → ℝ)
    (multiplier : ι → ℂ) : ℂ :=
  ∑ i ∈ packet, ∑ j ∈ packet,
    star (multiplier i) *
      (Complex.I *
        (amplitude i * amplitude j * (height i - height j) : ℝ)) *
      multiplier j

/-- Universal diameter bound for every bounded complex polarization of a rank-two exterior cell. -/
theorem abs_re_boundedPolarizedExteriorHermitianEnergy_le
    {ι : Type*} (packet : Finset ι) (amplitude height : ι → ℝ)
    (multiplier : ι → ℂ) (B D : ℝ)
    (hamp : ∀ i ∈ packet, 0 ≤ amplitude i)
    (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hmultiplier : ∀ i ∈ packet, ‖multiplier i‖ ≤ B)
    (hdiameter : ∀ i ∈ packet, ∀ j ∈ packet,
      |height i - height j| ≤ D) :
    |(boundedPolarizedExteriorHermitianEnergy
      packet amplitude height multiplier).re| ≤
      B ^ 2 * D * (∑ i ∈ packet, amplitude i) ^ 2 := by
  let term := fun i j =>
    star (multiplier i) *
      (Complex.I *
        (amplitude i * amplitude j * (height i - height j) : ℝ)) *
      multiplier j
  have hterm :
      ∀ i ∈ packet, ∀ j ∈ packet,
        ‖term i j‖ ≤ B ^ 2 * D * (amplitude i * amplitude j) := by
    intro i hi j hj
    have hai : 0 ≤ amplitude i := hamp i hi
    have haj : 0 ≤ amplitude j := hamp j hj
    have haij : 0 ≤ amplitude i * amplitude j := mul_nonneg hai haj
    have hzi : 0 ≤ ‖multiplier i‖ := norm_nonneg _
    have hzj : 0 ≤ ‖multiplier j‖ := norm_nonneg _
    have hmiddle :
        |amplitude i * amplitude j * (height i - height j)| ≤
          amplitude i * amplitude j * D := by
      rw [abs_mul, abs_of_nonneg haij]
      exact mul_le_mul_of_nonneg_left (hdiameter i hi j hj) haij
    dsimp only [term]
    simp only [norm_mul, norm_star, Complex.norm_I, one_mul,
      Complex.norm_real]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hai, abs_of_nonneg haj]
    calc
      ‖multiplier i‖ *
          (amplitude i * amplitude j * |height i - height j|) *
          ‖multiplier j‖
          ≤ ‖multiplier i‖ * (amplitude i * amplitude j * D) *
              ‖multiplier j‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left
                  (hdiameter i hi j hj) haij) hzi) hzj
      _ ≤ B * (amplitude i * amplitude j * D) *
              ‖multiplier j‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (hmultiplier i hi) (mul_nonneg haij hD)) hzj
      _ ≤ B * (amplitude i * amplitude j * D) * B := by
            exact mul_le_mul_of_nonneg_left
              (hmultiplier j hj) (mul_nonneg hB (mul_nonneg haij hD))
      _ = B ^ 2 * D * (amplitude i * amplitude j) := by ring
  have hnorm :
      ‖boundedPolarizedExteriorHermitianEnergy
          packet amplitude height multiplier‖ ≤
        ∑ i ∈ packet, ∑ j ∈ packet,
          B ^ 2 * D * (amplitude i * amplitude j) := by
    unfold boundedPolarizedExteriorHermitianEnergy
    calc
      ‖∑ i ∈ packet, ∑ j ∈ packet, term i j‖
          ≤ ∑ i ∈ packet, ‖∑ j ∈ packet, term i j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i ∈ packet, ∑ j ∈ packet, ‖term i j‖ := by
        exact Finset.sum_le_sum fun i hi => norm_sum_le _ _
      _ ≤ ∑ i ∈ packet, ∑ j ∈ packet,
          B ^ 2 * D * (amplitude i * amplitude j) := by
        exact Finset.sum_le_sum fun i hi =>
          Finset.sum_le_sum fun j hj => hterm i hi j hj
  have hfactor :
      (∑ i ∈ packet, ∑ j ∈ packet,
          B ^ 2 * D * (amplitude i * amplitude j)) =
        B ^ 2 * D * (∑ i ∈ packet, amplitude i) ^ 2 := by
    calc
      (∑ i ∈ packet, ∑ j ∈ packet,
          B ^ 2 * D * (amplitude i * amplitude j)) =
          B ^ 2 * D *
            (∑ i ∈ packet, ∑ j ∈ packet,
              amplitude i * amplitude j) := by
        symm
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = B ^ 2 * D *
          ((∑ i ∈ packet, amplitude i) *
            (∑ j ∈ packet, amplitude j)) := by
        rw [Finset.sum_mul_sum]
      _ = B ^ 2 * D * (∑ i ∈ packet, amplitude i) ^ 2 := by ring
  exact (Complex.abs_re_le_norm _).trans (hnorm.trans_eq hfactor)

/-- Euler depth-zero amplitude on the macroscopic prime block. -/
def ccmFirstClockEulerDepthZeroExteriorAmplitude (p : ℕ) : ℝ :=
  Real.sqrt (Real.log (p : ℝ) / p)

/-- Euler depth-zero half-height on the macroscopic prime block. -/
def ccmFirstClockEulerDepthZeroExteriorHeight (p : ℕ) : ℝ :=
  Real.log (p : ℝ) / 2

/-- At source parameter zero and valuation depth zero, the literal Euler amplitude is exactly the
prime-block amplitude used below. -/
theorem xiGammaEulerBoundaryRealAmplitude_zero_depthZero_eq
    {p : ℕ} (hp : Nat.Prime p) :
    xiGammaEulerBoundaryRealAmplitude 0 (⟨p, hp⟩, 0) =
      ccmFirstClockEulerDepthZeroExteriorAmplitude p := by
  unfold xiGammaEulerBoundaryRealAmplitude
    ccmFirstClockEulerDepthZeroExteriorAmplitude
    xiGammaEulerValuationNat
  norm_num

/-- At valuation depth zero, the literal Euler half-height is one half of the prime logarithm. -/
theorem xiGammaEulerBoundaryHalfHeight_depthZero_eq
    {p : ℕ} (hp : Nat.Prime p) :
    xiGammaEulerBoundaryHalfHeight ⟨p, hp⟩ 0 =
      ccmFirstClockEulerDepthZeroExteriorHeight p := by
  unfold xiGammaEulerBoundaryHalfHeight
    ccmFirstClockEulerDepthZeroExteriorHeight
  norm_num
  ring

/-- The abstract rank-two block cell is literally the calibrated Euler boundary exterior cell. -/
theorem xiGammaEulerBoundaryExteriorCell_zero_depthZero_eq
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    xiGammaEulerBoundaryExteriorCell 0 (⟨p, hp⟩, 0) (⟨q, hq⟩, 0) =
      ccmFirstClockEulerDepthZeroExteriorAmplitude p *
        ccmFirstClockEulerDepthZeroExteriorAmplitude q *
          (ccmFirstClockEulerDepthZeroExteriorHeight p -
            ccmFirstClockEulerDepthZeroExteriorHeight q) := by
  rw [xiGammaEulerBoundaryExteriorCell,
    xiGammaEulerBoundaryRealAmplitude_zero_depthZero_eq hp,
    xiGammaEulerBoundaryRealAmplitude_zero_depthZero_eq hq,
    xiGammaEulerBoundaryHalfHeight_depthZero_eq hp,
    xiGammaEulerBoundaryHalfHeight_depthZero_eq hq]

/-- Arbitrarily polarized Euler exterior energy on the first-clock macroscopic prime block. -/
def ccmFirstClockEulerDepthZeroBoundedExteriorEnergy
    (m : ℕ) (multiplier : ℕ → ℂ) : ℂ :=
  boundedPolarizedExteriorHermitianEnergy
    (suzukiMangoldtFivePrimeBlock (m ^ 4))
    ccmFirstClockEulerDepthZeroExteriorAmplitude
    ccmFirstClockEulerDepthZeroExteriorHeight
    multiplier

/-- Euler depth-zero amplitudes are nonnegative. -/
theorem ccmFirstClockEulerDepthZeroExteriorAmplitude_nonneg (p : ℕ) :
    0 ≤ ccmFirstClockEulerDepthZeroExteriorAmplitude p := by
  exact Real.sqrt_nonneg _

/-- The Euler half-height diameter on every first-clock block is at most one. -/
theorem ccmFirstClockEulerDepthZeroExteriorHeight_diameter_le_one
    {m p q : ℕ} (hm : 25 ≤ m)
    (hp : p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4))
    (hq : q ∈ suzukiMangoldtFivePrimeBlock (m ^ 4)) :
    |ccmFirstClockEulerDepthZeroExteriorHeight p -
      ccmFirstClockEulerDepthZeroExteriorHeight q| ≤ 1 := by
  have hlog :=
    abs_log_sub_log_le_two_of_mem_suzukiMangoldtFivePrimeBlock_fourthPower
      hm hp hq
  unfold ccmFirstClockEulerDepthZeroExteriorHeight
  rw [show Real.log (p : ℝ) / 2 - Real.log (q : ℝ) / 2 =
      -(Real.log (q : ℝ) - Real.log (p : ℝ)) / 2 by ring,
    abs_div, abs_neg]
  norm_num
  linarith

/-- The logarithmic mass of the width-five prime block has the elementary Chebyshev upper bound. -/
theorem suzukiMangoldtFivePrimeBlock_logMass_upper
    {n : ℕ} :
    (∑ p ∈ suzukiMangoldtFivePrimeBlock n, Real.log (p : ℝ)) ≤
      5 * (n : ℝ) * Real.log 4 := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have htheta :=
    Chebyshev.theta_le_log4_mul_x
      (show (0 : ℝ) ≤ 5 * (n : ℝ) by positivity)
  rw [suzukiMangoldtFivePrimeBlock,
    sum_log_windowPrimes
      (show 2 * (n : ℝ) ≤ 5 * (n : ℝ) by nlinarith)]
  nlinarith [Chebyshev.theta_nonneg (2 * (n : ℝ))]

/-- Block cardinality times its lower logarithmic edge is at most its logarithmic mass. -/
theorem card_mul_log_two_mul_le_suzukiMangoldtFivePrimeBlock_logMass
    {n : ℕ} (hn : 1 ≤ n) :
    ((suzukiMangoldtFivePrimeBlock n).card : ℝ) *
        Real.log (2 * (n : ℝ)) ≤
      ∑ p ∈ suzukiMangoldtFivePrimeBlock n, Real.log (p : ℝ) := by
  calc
    ((suzukiMangoldtFivePrimeBlock n).card : ℝ) *
          Real.log (2 * (n : ℝ)) =
        ∑ _p ∈ suzukiMangoldtFivePrimeBlock n,
          Real.log (2 * (n : ℝ)) := by simp
    _ ≤ ∑ p ∈ suzukiMangoldtFivePrimeBlock n, Real.log (p : ℝ) := by
      exact Finset.sum_le_sum fun p hp => by
        obtain ⟨hpPrime, hpLower, _hpUpper⟩ :=
          mem_suzukiMangoldtFivePrimeBlock.mp hp
        exact Real.log_le_log
          (by positivity : (0 : ℝ) < 2 * (n : ℝ))
          (by exact_mod_cast hpLower.le)

/-- Sum of squared Euler depth-zero amplitudes has a fixed block bound. -/
theorem sum_sq_ccmFirstClockEulerDepthZeroExteriorAmplitude_le
    {n : ℕ} (hn : 1 ≤ n) :
    (∑ p ∈ suzukiMangoldtFivePrimeBlock n,
      ccmFirstClockEulerDepthZeroExteriorAmplitude p ^ 2) ≤
      (5 / 2 : ℝ) * Real.log 4 := by
  have hnR : (0 : ℝ) < n := by positivity
  have hterm :
      ∀ p ∈ suzukiMangoldtFivePrimeBlock n,
        ccmFirstClockEulerDepthZeroExteriorAmplitude p ^ 2 ≤
          Real.log (p : ℝ) / (2 * (n : ℝ)) := by
    intro p hp
    obtain ⟨hpPrime, hpLower, _hpUpper⟩ :=
      mem_suzukiMangoldtFivePrimeBlock.mp hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have hlogp : 0 ≤ Real.log (p : ℝ) :=
      (Real.log_pos (by exact_mod_cast hpPrime.one_lt)).le
    have hpLowerR : 2 * (n : ℝ) < (p : ℝ) := by exact_mod_cast hpLower
    rw [ccmFirstClockEulerDepthZeroExteriorAmplitude,
      Real.sq_sqrt (div_nonneg hlogp hpR.le)]
    exact div_le_div_of_nonneg_left hlogp
      (by positivity : (0 : ℝ) < 2 * (n : ℝ)) hpLowerR.le
  calc
    (∑ p ∈ suzukiMangoldtFivePrimeBlock n,
        ccmFirstClockEulerDepthZeroExteriorAmplitude p ^ 2)
        ≤ ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
            Real.log (p : ℝ) / (2 * (n : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = (∑ p ∈ suzukiMangoldtFivePrimeBlock n, Real.log (p : ℝ)) /
          (2 * (n : ℝ)) := by rw [Finset.sum_div]
    _ ≤ (5 * (n : ℝ) * Real.log 4) / (2 * (n : ℝ)) :=
      div_le_div_of_nonneg_right suzukiMangoldtFivePrimeBlock_logMass_upper
        (by positivity)
    _ = (5 / 2 : ℝ) * Real.log 4 := by field_simp

/-- Chebyshev plus Cauchy gives the exact logarithmic saving for the total exterior amplitude. -/
theorem sq_sum_ccmFirstClockEulerDepthZeroExteriorAmplitude_le
    {n : ℕ} (hn : 1 ≤ n) :
    (∑ p ∈ suzukiMangoldtFivePrimeBlock n,
      ccmFirstClockEulerDepthZeroExteriorAmplitude p) ^ 2 ≤
      (25 / 2 : ℝ) * Real.log 4 ^ 2 *
        (n : ℝ) / Real.log (2 * (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by positivity
  have hnOneR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogTwoN : 0 < Real.log (2 * (n : ℝ)) :=
    Real.log_pos (by nlinarith)
  have hcardMass :=
    card_mul_log_two_mul_le_suzukiMangoldtFivePrimeBlock_logMass hn
  have hmassUpper :=
    suzukiMangoldtFivePrimeBlock_logMass_upper (n := n)
  have hcard :
      ((suzukiMangoldtFivePrimeBlock n).card : ℝ) ≤
        5 * (n : ℝ) * Real.log 4 / Real.log (2 * (n : ℝ)) := by
    apply (le_div_iff₀ hlogTwoN).2
    exact hcardMass.trans hmassUpper
  have hsq :=
    sum_sq_ccmFirstClockEulerDepthZeroExteriorAmplitude_le hn
  have hcs :
      (∑ p ∈ suzukiMangoldtFivePrimeBlock n,
        ccmFirstClockEulerDepthZeroExteriorAmplitude p) ^ 2 ≤
        ((suzukiMangoldtFivePrimeBlock n).card : ℝ) *
          ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
            ccmFirstClockEulerDepthZeroExteriorAmplitude p ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hsqNonneg :
      0 ≤ ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
        ccmFirstClockEulerDepthZeroExteriorAmplitude p ^ 2 :=
    Finset.sum_nonneg fun p _ => sq_nonneg _
  have hlogFour : 0 ≤ Real.log 4 := (Real.log_pos (by norm_num)).le
  calc
    (∑ p ∈ suzukiMangoldtFivePrimeBlock n,
        ccmFirstClockEulerDepthZeroExteriorAmplitude p) ^ 2
        ≤ ((suzukiMangoldtFivePrimeBlock n).card : ℝ) *
          ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
            ccmFirstClockEulerDepthZeroExteriorAmplitude p ^ 2 := hcs
    _ ≤ (5 * (n : ℝ) * Real.log 4 / Real.log (2 * (n : ℝ))) *
          ((5 / 2 : ℝ) * Real.log 4) :=
      mul_le_mul hcard hsq hsqNonneg
        (by positivity)
    _ = (25 / 2 : ℝ) * Real.log 4 ^ 2 *
          (n : ℝ) / Real.log (2 * (n : ℝ)) := by ring

/-- Every unit-bounded complex polarization of the first-clock Euler exterior block has only
`m⁴ / log(m⁴)`-scale scalar energy. -/
theorem abs_re_ccmFirstClockEulerDepthZeroBoundedExteriorEnergy_le
    {m : ℕ} (hm : 25 ≤ m) (multiplier : ℕ → ℂ)
    (hmultiplier : ∀ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
      ‖multiplier p‖ ≤ 1) :
    |(ccmFirstClockEulerDepthZeroBoundedExteriorEnergy m multiplier).re| ≤
      (25 / 2 : ℝ) * Real.log 4 ^ 2 *
        ((m ^ 4 : ℕ) : ℝ) / Real.log (2 * ((m ^ 4 : ℕ) : ℝ)) := by
  have hmOne : 1 ≤ m ^ 4 := one_le_pow₀ (by omega : 1 ≤ m)
  have hgeneric :=
    abs_re_boundedPolarizedExteriorHermitianEnergy_le
      (suzukiMangoldtFivePrimeBlock (m ^ 4))
      ccmFirstClockEulerDepthZeroExteriorAmplitude
      ccmFirstClockEulerDepthZeroExteriorHeight multiplier 1 1
      (fun p _ => ccmFirstClockEulerDepthZeroExteriorAmplitude_nonneg p)
      (by norm_num) (by norm_num) hmultiplier
      (fun p hp q hq =>
        ccmFirstClockEulerDepthZeroExteriorHeight_diameter_le_one hm hp hq)
  norm_num at hgeneric
  exact hgeneric.trans
    (sq_sum_ccmFirstClockEulerDepthZeroExteriorAmplitude_le hmOne)

/-- Beyond an explicit symbolic threshold, every unit-bounded polarization is strictly smaller
than the certified squared pure-bad mass on the same first-clock block. -/
theorem ccmFirstClockEulerDepthZeroBoundedExteriorEnergy_lt_badMass_sq
    {m : ℕ} (hmLarge : Real.exp 7201 < (m : ℝ))
    (multiplier : ℕ → ℂ)
    (hmultiplier : ∀ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
      ‖multiplier p‖ ≤ 1) :
    |(ccmFirstClockEulerDepthZeroBoundedExteriorEnergy m multiplier).re| <
      (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
        ccmFirstClockReducedBadNatTerm
          (ccmFirstClockJuliaSixthPowerAperture m) p) ^ 2 := by
  have hmPos : (0 : ℝ) < m := (Real.exp_pos 7201).trans hmLarge
  have hm25 : 25 ≤ m := by
    have hexp := Real.add_one_le_exp (7201 : ℝ)
    exact_mod_cast (show (25 : ℝ) ≤ m by linarith)
  have hmCheb : Real.exp 20 ≤ ((m ^ 4 : ℕ) : ℝ) := by
    have h20 : Real.exp 20 < Real.exp 7201 :=
      Real.exp_lt_exp.mpr (by norm_num)
    have hmLePow : m ≤ m ^ 4 := by
      have hmNatPos : 0 < m := by exact_mod_cast hmPos
      simpa using
        (Nat.pow_le_pow_right hmNatPos (show 1 ≤ 4 by omega) :
          m ^ 1 ≤ m ^ 4)
    exact (h20.trans hmLarge).le.trans (by exact_mod_cast hmLePow)
  have hlogm : 7201 < Real.log (m : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos 7201) hmLarge
    rwa [Real.log_exp] at h
  have hlogDen :
      28800 < Real.log (2 * ((m ^ 4 : ℕ) : ℝ)) := by
    have hmNe : (m : ℝ) ≠ 0 := ne_of_gt hmPos
    rw [show ((m ^ 4 : ℕ) : ℝ) = (m : ℝ) ^ 4 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero 4 hmNe),
      Real.log_pow]
    norm_num
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have henergy :=
    abs_re_ccmFirstClockEulerDepthZeroBoundedExteriorEnergy_le
      hm25 multiplier hmultiplier
  have hlogFour : Real.log 4 < 2 := by
    rw [Real.log_four_eq]
    nlinarith [Real.log_two_lt_d9]
  have hlogFour0 : 0 ≤ Real.log 4 := (Real.log_pos (by norm_num)).le
  have hmPowPos : (0 : ℝ) < ((m ^ 4 : ℕ) : ℝ) := by positivity
  have hdenPos : 0 < Real.log (2 * ((m ^ 4 : ℕ) : ℝ)) := by linarith
  have hcoarse :
      (25 / 2 : ℝ) * Real.log 4 ^ 2 *
          ((m ^ 4 : ℕ) : ℝ) / Real.log (2 * ((m ^ 4 : ℕ) : ℝ)) <
        ((m ^ 4 : ℕ) : ℝ) / 576 := by
    have hlogSq : Real.log 4 ^ 2 < 4 := by nlinarith
    apply (div_lt_iff₀ hdenPos).2
    have hdenScaled : 50 * 576 < Real.log (2 * ((m ^ 4 : ℕ) : ℝ)) := by
      norm_num
      simpa only [Nat.cast_pow] using hlogDen
    nlinarith
  have hbadMass :=
    ccmFirstClockJuliaSixthPower_block_badMass_lower hm25 hmCheb
  have hbadNonneg :
      0 ≤ ∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
        ccmFirstClockReducedBadNatTerm
          (ccmFirstClockJuliaSixthPowerAperture m) p := by
    apply Finset.sum_nonneg
    intro p hp
    have hpPrime := (mem_suzukiMangoldtFivePrimeBlock.mp hp).1
    rw [ccmFirstClockReducedBadNatTerm_of_prime _ hpPrime]
    exact (ccmFirstClockJuliaSixthPower_block_badTerm_pos hm25 hp).le
  have hbadSq :
      ((m ^ 4 : ℕ) : ℝ) / 576 ≤
        (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
          ccmFirstClockReducedBadNatTerm
            (ccmFirstClockJuliaSixthPowerAperture m) p) ^ 2 := by
    have hmassSq :=
      (sq_le_sq₀ (by positivity : 0 ≤ (m : ℝ) ^ 2 / 24) hbadNonneg).2 hbadMass
    push_cast at hmassSq ⊢
    nlinarith
  exact henergy.trans_lt (hcoarse.trans_le hbadSq)

/-- Consequently no unit-bounded polarization can dominate the first-clock pure-bad block mass. -/
theorem not_ccmFirstClock_badMass_sq_le_EulerDepthZeroBoundedExteriorEnergy_re
    {m : ℕ} (hmLarge : Real.exp 7201 < (m : ℝ))
    (multiplier : ℕ → ℂ)
    (hmultiplier : ∀ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
      ‖multiplier p‖ ≤ 1) :
    ¬ (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ 4),
        ccmFirstClockReducedBadNatTerm
          (ccmFirstClockJuliaSixthPowerAperture m) p) ^ 2 ≤
      (ccmFirstClockEulerDepthZeroBoundedExteriorEnergy m multiplier).re := by
  have hstrict :=
    ccmFirstClockEulerDepthZeroBoundedExteriorEnergy_lt_badMass_sq
      hmLarge multiplier hmultiplier
  intro hdominates
  exact (not_le_of_gt hstrict)
    (hdominates.trans (le_abs_self _))

end RHTower

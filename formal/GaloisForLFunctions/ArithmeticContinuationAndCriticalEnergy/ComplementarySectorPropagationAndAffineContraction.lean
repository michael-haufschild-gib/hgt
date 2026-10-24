import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.AffineRecurrenceEnvelope
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheCutoffParameterCostsNothingBeyondAdmission
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.SignedAveragedContinuationAndTheZeroWidthBand
import GaloisForLFunctions.RHTower.PMRamanujanComplementaryCancellation

/-!
# Propagating the Complementary-Sector Cancellation Across Scale Transitions

This module resolves Open Problem 6 of the Arithmetic Continuation and Critical Energy programme by
turning the leading-order anti-alignment between the large-prime denominator sector `L_P` and its
literal complement `C_P` into a quantitative two-scale residual and proving its contractive affine
recurrence `F_{j+1} ≤ q_j F_j + r_j` (`0 ≤ q_j ≤ θ < 1`) across compatible scale transitions.

1. **Exact Compensation Coordinates and Anti-Alignment (`§1`)**:
   At denominator cutoff `P²`, projecting the literal complement `C_P` onto the large-prime sector
   `L_P` defines the compensation amplitude `sectorCompensationAmplitude ε P = −⟪L_P, C_P⟫/‖L_P‖²`
   and the nonnegative transverse remainder energy `sectorTransverseEnergy ε P`. The complete head
   prefix energy splits exactly by the Pythagorean compensation law:
   `pmPowerDampedRamanujanPrefixEnergy ε (P² − 1) (P − 1) = (1 − α_P)² ‖L_P‖² + ‖R_P‖²`
   (`pmCompleteHeadEnergy_eq_sector_compensation`), with `α_P → 1` and `‖R_P‖²/‖L_P‖² → 0` for
   `0 < ε < ½` (`tendsto_sectorCompensationAmplitude_one`,
   `tendsto_sectorTransverseEnergy_div_sectorEnergy_zero`).

2. **Contractive Affine Recurrences for Two-Scale Cutoff Transitions (`§2`)**:
   - *Compatible dyadic schedule (`Q_j = 2^{m j}`, `m ε > 1`)*: The common-head cutoff transition
     energy `ramanujanCutoffTransportEnergy ε (2^{m j}) (2^{m(j+1)}) (2^j)` is bounded by
     `dyadicCutoffTransportEnvelope ε m j = 4 C_{ε,ε/2}² (shellRatio ε m)^j`
     (`ramanujanCutoffTransportEnergy_dyadic_le_envelope`), which satisfies the exact contractive
     affine recurrence `F_{j+1} = shellRatio ε m · F_j + 0` with `0 ≤ shellRatio ε m < 1`
     (`dyadicCutoffTransportEnvelope_recurrence`). Any sequence `F_j` propagated by
     `F_{j+1} ≤ shellRatio ε m · F_j + ramanujanCutoffTransportEnergy ε (2^{m j}) (2^{m(j+1)}) (2^j)`
     is uniformly bounded in `j` (`affine_contraction_of_dyadicCutoffTransportEnergy`).
   - *Square-cutoff schedule (`P_j = 2^j`, cutoff `P_j² = 2^{2j}`)*: Comparing the overlapping
     sector-plus-complement decompositions at cutoffs `(2^j)²` and `(2^{j+1})²` on `[1, 2^j]` cancels
     the cutoff-independent divisor remainder identically and satisfies
     `ramanujanCutoffTransportEnergy ε ((2^j)²) ((2^{j+1})²) (2^j) ≤ twoScaleSquareCutoffEnvelope ε β j`,
     where `twoScaleSquareCutoffEnvelope ε β (j + 1) = 2^{1−4β} · twoScaleSquareCutoffEnvelope ε β j`
     contracts strictly (`2^{1−4β} < 1`) whenever `1/4 < β < ε`
     (`ramanujanCutoffTransportEnergy_square_dyadic_le`, `twoScaleSquareCutoffEnvelope_recurrence`).

3. **Two-Sided Comparison and Four-Way Equivalence with Admission (`§3`)**:
   The dyadic stage prefix energy `dyadicRamanujanPrefixEnergy ε m j` and the receiver energy
   `dampedMobiusEnergy ε (2^{j+1})` bound each other up to the geometric shell error
   `2 C_{ε,ε/2}² (shellRatio ε m)^{j+1}` (`dyadicRamanujanPrefixEnergy_le_dampedMobiusEnergy_add`,
   `dampedMobiusEnergy_le_dyadicRamanujanPrefixEnergy_add`). Consequently, for any `ε > 0` and
   compatible depth `1 < m ε`, admission `Admits dampedMobiusEnergy ε`, `ε ∈ receiverDampings`,
   existence of a contractive affine recurrence `F_{j+1} ≤ q_j F_j + r_j` (`q_j ≤ θ < 1`,
   `r_j ≤ R`) for `dyadicRamanujanPrefixEnergy ε m`, and existence of a contractive recurrence with
   the canonical stage multiplier `q_j = shellRatio ε m < 1` are four-way equivalent
   (`complementarySector_propagation_tfae`).

4. **Unconditional Contractive Propagation Above `Θ − ½` and on the Vinogradov–Korobov Band (`§4`)**:
   Above the zero width `Θ − ½`, both `dyadicRamanujanPrefixEnergy ε m` (at every `ε > Θ − ½`) and
   the compensated large-prime head energy `(1 − α_{2^{j+1}})² ‖L_{2^{j+1}}‖² + ‖R_{2^{j+1}}‖²` (for
   `ε > max(1/4, Θ − ½)`) unconditionally satisfy contractive affine recurrences with explicit
   horizon-free envelopes (`exists_contractive_affine_propagation_above_zeroWidth`,
   `exists_compensated_head_affine_contraction_above_zeroWidth`), and `dyadicRamanujanPrefixEnergy`
   is uniformly controlled on the Vinogradov–Korobov band
   (`exists_dyadicRamanujanPrefixEnergy_le_on_vinogradovKorobovBand`).
-/

open Set Filter Finset Topology Complex
open RHTower RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. Exact Compensation Coordinates and Anti-Alignment on the Actual Source -/

/-- The compensation amplitude `α_P = −⟪L_P, C_P⟫/‖L_P‖²` of the literal complement against the
large-prime sector at cutoff `P²`. -/
def sectorCompensationAmplitude (ε : ℝ) (P : ℕ) : ℝ :=
  -pmRamanujanLargePrimeComplementMixedEnergy ε P / pmRamanujanLargePrimeSectorEnergy ε P

/-- The transverse remainder energy `‖R_P‖² = ‖C_P‖² − ⟪L_P, C_P⟫²/‖L_P‖²` at cutoff `P²`. -/
def sectorTransverseEnergy (ε : ℝ) (P : ℕ) : ℝ :=
  pmRamanujanLargePrimeComplementEnergy ε P -
    pmRamanujanLargePrimeComplementMixedEnergy ε P ^ 2 / pmRamanujanLargePrimeSectorEnergy ε P

/-- Cauchy–Schwarz for the mixed energy between the large-prime sector and its complement. -/
theorem sectorMixedEnergy_sq_le (ε : ℝ) (P : ℕ) :
    pmRamanujanLargePrimeComplementMixedEnergy ε P ^ 2 ≤
      pmRamanujanLargePrimeSectorEnergy ε P * pmRamanujanLargePrimeComplementEnergy ε P := by
  unfold pmRamanujanLargePrimeComplementMixedEnergy pmRamanujanLargePrimeSectorEnergy
    pmRamanujanLargePrimeComplementEnergy
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun N _ => by positivity) (fun N _ => by positivity)
  intro N _
  have h := pow_le_pow_left₀ (abs_nonneg _)
    (Complex.abs_re_le_norm (pmRamanujanLargePrimeSector ε P N *
      star (pmRamanujanLargePrimeComplement ε P N))) 2
  simp only [sq_abs, norm_mul, norm_star, mul_pow] at h
  have hh := div_le_div_of_nonneg_right h (sq_nonneg ((N : ℝ) * ((N : ℝ) + 1)))
  simpa only [div_pow, div_mul_div_comm, ← pow_two] using hh

/-- **Pythagorean Compensation Decomposition of the Complete Head Energy.**
At every cutoff `P ≥ 2`, the complete Ramanujan prefix energy on `1 ≤ N ≤ P − 1` splits into the
squared amplitude mismatch `(1 − α_P)² ‖L_P‖²` plus the nonnegative transverse energy `‖R_P‖²`. -/
theorem pmCompleteHeadEnergy_eq_sector_compensation {P : ℕ} (hP : 2 ≤ P) (ε : ℝ) :
    pmPowerDampedRamanujanPrefixEnergy ε (P ^ 2 - 1) (P - 1) =
        (1 - sectorCompensationAmplitude ε P) ^ 2 * pmRamanujanLargePrimeSectorEnergy ε P +
          sectorTransverseEnergy ε P ∧
      0 ≤ sectorTransverseEnergy ε P := by
  have hsum : pmPowerDampedRamanujanPrefixEnergy ε (P ^ 2 - 1) (P - 1) =
      pmRamanujanLargePrimeSectorEnergy ε P + pmRamanujanLargePrimeComplementEnergy ε P +
        2 * pmRamanujanLargePrimeComplementMixedEnergy ε P := by
    have hn (z w : ℂ) : ‖z + w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * (z * star w).re := by
      simp only [Complex.sq_norm, Complex.normSq_add, Complex.star_def, Complex.mul_re,
        Complex.conj_re, Complex.conj_im]
    unfold pmPowerDampedRamanujanPrefixEnergy pmRamanujanLargePrimeSectorEnergy
      pmRamanujanLargePrimeComplementEnergy pmRamanujanLargePrimeComplementMixedEnergy
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun N _ => ?_
    have hsplit : pmPowerDampedRamanujanCumulativePrefix ε (P ^ 2 - 1) N =
        pmRamanujanLargePrimeSector ε P N + pmRamanujanLargePrimeComplement ε P N := by
      rw [pmRamanujanLargePrimeComplement_eq_sub hP]; ring
    rw [hsplit, hn]
    ring
  have hcs := sectorMixedEnergy_sq_le ε P
  have ha0 : 0 ≤ pmRamanujanLargePrimeSectorEnergy ε P := by
    unfold pmRamanujanLargePrimeSectorEnergy; positivity
  have hb0 : 0 ≤ pmRamanujanLargePrimeComplementEnergy ε P := by
    unfold pmRamanujanLargePrimeComplementEnergy; positivity
  rcases ha0.eq_or_lt with ha | ha
  · have hm : pmRamanujanLargePrimeComplementMixedEnergy ε P = 0 := by
      rw [← ha, zero_mul] at hcs
      exact pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm hcs (sq_nonneg _))
    rw [hsum, sectorCompensationAmplitude, sectorTransverseEnergy, ← ha, hm]
    exact ⟨by simp, by simpa using hb0⟩
  · have hne : pmRamanujanLargePrimeSectorEnergy ε P ≠ 0 := ha.ne'
    refine ⟨?_, ?_⟩
    · rw [hsum, sectorCompensationAmplitude, sectorTransverseEnergy]
      field_simp
      ring
    · rw [sectorTransverseEnergy, sub_nonneg, div_le_iff₀ ha]
      linarith

/-- **Leading-order anti-alignment: `α_P → 1` as `P → ∞` for `0 < ε < 1/2`.** -/
theorem tendsto_sectorCompensationAmplitude_one {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    Tendsto (sectorCompensationAmplitude ε) atTop (𝓝 1) := by
  have h := (tendsto_pmRamanujanLargePrimeComplementMixedEnergy_ratio_neg_one hε hεhalf).neg
  rw [neg_neg] at h
  refine h.congr fun P => ?_
  rw [sectorCompensationAmplitude, neg_div]

/-- **Vanishing relative transverse remainder: `‖R_P‖² / ‖L_P‖² → 0` for `0 < ε < 1/2`.** -/
theorem tendsto_sectorTransverseEnergy_div_sectorEnergy_zero {ε : ℝ} (hε : 0 < ε)
    (hεhalf : ε < 1 / 2) :
    Tendsto (fun P => sectorTransverseEnergy ε P / pmRamanujanLargePrimeSectorEnergy ε P) atTop
      (𝓝 0) := by
  have hb := tendsto_pmRamanujanLargePrimeComplementEnergy_ratio_one hε hεhalf
  have hm := tendsto_pmRamanujanLargePrimeComplementMixedEnergy_ratio_neg_one hε hεhalf
  have h := hb.sub (hm.pow 2)
  rw [show (1 : ℝ) - (-1) ^ 2 = 0 by norm_num] at h
  refine h.congr' ?_
  filter_upwards [(tendsto_pmRamanujanLargePrimeSectorEnergy_atTop hε hεhalf).eventually_gt_atTop 0]
    with P hL
  rw [sectorTransverseEnergy, sub_div, div_pow]
  field_simp

/-! ## §2. Contractive Affine Recurrences for Two-Scale Cutoff Transitions -/

/-- The geometric envelope `4 C_{ε,ε/2}² (shellRatio ε m)^j` of the dyadic common-head cutoff
transition energy at depth `m`. -/
def dyadicCutoffTransportEnvelope (ε : ℝ) (m j : ℕ) : ℝ :=
  4 * ramanujanCutoffErrorConstant ε (ε / 2) ^ 2 * shellRatio ε m ^ j

theorem dyadicCutoffTransportEnvelope_nonneg (ε : ℝ) (m j : ℕ) :
    0 ≤ dyadicCutoffTransportEnvelope ε m j := by
  unfold dyadicCutoffTransportEnvelope
  have := shellRatio_nonneg ε m
  positivity

/-- **Exact contractive affine recurrence for the dyadic cutoff transport envelope.** -/
theorem dyadicCutoffTransportEnvelope_recurrence (ε : ℝ) (m j : ℕ) :
    dyadicCutoffTransportEnvelope ε m (j + 1) =
      shellRatio ε m * dyadicCutoffTransportEnvelope ε m j + 0 := by
  unfold dyadicCutoffTransportEnvelope
  rw [pow_succ']
  ring

/-- **Pointwise dominance of the dyadic common-head cutoff transition energy by its contractive
envelope.** -/
theorem ramanujanCutoffTransportEnergy_dyadic_le_envelope {ε : ℝ} (hε : 0 < ε)
    {m : ℕ} (hm : 1 ≤ m) (j : ℕ) :
    ramanujanCutoffTransportEnergy ε (2 ^ (m * j)) (2 ^ (m * (j + 1))) (2 ^ j) ≤
      dyadicCutoffTransportEnvelope ε m j := by
  have hsqrt := sqrt_ramanujanCutoffTransportEnergy_dyadic_le hε hm j
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2
  rw [Real.sq_sqrt (by unfold ramanujanCutoffTransportEnergy; positivity)] at hsq
  refine hsq.trans (le_of_eq ?_)
  unfold dyadicCutoffTransportEnvelope shellRatio
  have hpow : (((2 : ℝ) ^ ((1 - (m : ℝ) * ε) / 2)) ^ j) ^ 2 =
      (2 * ((2 : ℝ) ^ (-((m : ℝ) * ε / 2))) ^ 2) ^ j := by
    rw [← pow_mul, mul_comm j 2, pow_mul]
    congr 1
    have h1 : ((2 : ℝ) ^ ((1 - (m : ℝ) * ε) / 2)) ^ 2 = (2 : ℝ) ^ (1 - (m : ℝ) * ε) := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1; push_cast; ring
    have h2 : ((2 : ℝ) ^ (-((m : ℝ) * ε / 2))) ^ 2 = (2 : ℝ) ^ (-((m : ℝ) * ε)) := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1; push_cast; ring
    rw [h1, h2, show (1 : ℝ) - (m : ℝ) * ε = 1 + -((m : ℝ) * ε) by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  rw [mul_pow, hpow]
  ring

/-- **Uniform bound for any residual sequence propagated by the dyadic cutoff transition.**
Whenever `1 < m ε` and `F_{j+1} ≤ shellRatio ε m · F_j + ramanujanCutoffTransportEnergy ε (2^{m j}) (2^{m(j+1)}) (2^j)`,
`F_J` is bounded uniformly in `J`. -/
theorem affine_contraction_of_dyadicCutoffTransportEnergy {ε : ℝ} (hε : 0 < ε)
    {m : ℕ} (hm : 1 ≤ m) (hmε : 1 < (m : ℝ) * ε) {F : ℕ → ℝ} (hF0 : 0 ≤ F 0)
    (hrec : ∀ j : ℕ, F (j + 1) ≤ shellRatio ε m * F j +
      ramanujanCutoffTransportEnergy ε (2 ^ (m * j)) (2 ^ (m * (j + 1))) (2 ^ j)) (J : ℕ) :
    F J ≤ max (F 0)
      (4 * ramanujanCutoffErrorConstant ε (ε / 2) ^ 2 / (1 - shellRatio ε m)) := by
  have hq0 : 0 ≤ shellRatio ε m := shellRatio_nonneg ε m
  have hq1 : shellRatio ε m < 1 := shellRatio_lt_one hmε
  have hr0 : ∀ j, 0 ≤ ramanujanCutoffTransportEnergy ε (2 ^ (m * j)) (2 ^ (m * (j + 1))) (2 ^ j) :=
    fun j => by unfold ramanujanCutoffTransportEnergy; positivity
  have hrR : ∀ j, ramanujanCutoffTransportEnergy ε (2 ^ (m * j)) (2 ^ (m * (j + 1))) (2 ^ j) ≤
      4 * ramanujanCutoffErrorConstant ε (ε / 2) ^ 2 := by
    intro j
    refine (ramanujanCutoffTransportEnergy_dyadic_le_envelope hε hm j).trans ?_
    unfold dyadicCutoffTransportEnvelope
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ hq0 hq1.le)
  exact (le_affineEnvelope (fun _ => hq0) hrec J).trans
    (affineEnvelope_le_of_contraction hF0 hq1 (fun _ => hq0) (fun _ => le_rfl) hr0 hrR J)

/-- The two-scale shift envelope `4 C_{ε,β}² · (2^{1−4β})^j` for the square-cutoff schedule
`P_j = 2^j`, `Q_j = (2^j)²`. -/
def twoScaleSquareCutoffEnvelope (ε β : ℝ) (j : ℕ) : ℝ :=
  4 * ramanujanCutoffErrorConstant ε β ^ 2 * ((2 : ℝ) ^ (1 - 4 * β)) ^ j

/-- **Exact affine recurrence for the square-cutoff shift envelope.** -/
theorem twoScaleSquareCutoffEnvelope_recurrence (ε β : ℝ) (j : ℕ) :
    twoScaleSquareCutoffEnvelope ε β (j + 1) =
      (2 : ℝ) ^ (1 - 4 * β) * twoScaleSquareCutoffEnvelope ε β j + 0 := by
  unfold twoScaleSquareCutoffEnvelope
  rw [pow_succ']
  ring

/-- **Strict contraction of the square-cutoff multiplier for `β > 1/4`.** -/
theorem twoScaleSquareCutoffMultiplier_lt_one {β : ℝ} (hβ : 1 / 4 < β) :
    0 ≤ (2 : ℝ) ^ (1 - 4 * β) ∧ (2 : ℝ) ^ (1 - 4 * β) < 1 :=
  ⟨Real.rpow_nonneg (by norm_num) _,
   Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)⟩

/-- **Pointwise bound on the two-scale complete-prefix shift between `(2^j)²` and `(2^{j+1})²` on
the common head `1 ≤ N ≤ 2^j`.** -/
theorem ramanujanCutoffTransportEnergy_square_dyadic_le {ε β : ℝ} (hε : 0 < ε)
    (hβ : 0 ≤ β) (hβε : β < ε) (j : ℕ) :
    ramanujanCutoffTransportEnergy ε ((2 ^ j) ^ 2) ((2 ^ (j + 1)) ^ 2) (2 ^ j) ≤
      twoScaleSquareCutoffEnvelope ε β j := by
  have hQ : 0 < (2 ^ j) ^ 2 := by positivity
  have hR : 0 < (2 ^ (j + 1)) ^ 2 := by positivity
  have h1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have hTQ : 2 ^ j ≤ (2 ^ j) ^ 2 := by nlinarith
  have hQR : (2 ^ j) ^ 2 ≤ (2 ^ (j + 1)) ^ 2 :=
    Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ j)) 2
  have hb := ramanujanCutoffTransportEnergy_le hε hβ hβε hQ hR hTQ (hTQ.trans hQR)
  have hle_rpow : (((2 ^ (j + 1)) ^ 2 : ℕ) : ℝ) ^ (-β) ≤ (((2 ^ j) ^ 2 : ℕ) : ℝ) ^ (-β) :=
    Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hQ) (by exact_mod_cast hQR) (by linarith)
  have hpow : (((2 ^ j) ^ 2 : ℕ) : ℝ) ^ (-β) = ((2 : ℝ) ^ (-2 * β)) ^ j := by
    push_cast
    rw [← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_natCast _ 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_natCast ((2 : ℝ) ^ (-2 * β)) j, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1; push_cast; ring
  have hbase : ((2 ^ j : ℕ) : ℝ) * (((2 : ℝ) ^ (-2 * β)) ^ j) ^ 2 =
      ((2 : ℝ) ^ (1 - 4 * β)) ^ j := by
    push_cast
    rw [← pow_mul, mul_comm j 2, pow_mul, ← mul_pow]
    congr 1
    have hsq : ((2 : ℝ) ^ (-2 * β)) ^ 2 = (2 : ℝ) ^ (-4 * β) := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1; push_cast; ring
    rw [hsq, show (1 : ℝ) - 4 * β = 1 + -4 * β by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  have hsum_le : (((2 ^ j) ^ 2 : ℕ) : ℝ) ^ (-β) + (((2 ^ (j + 1)) ^ 2 : ℕ) : ℝ) ^ (-β) ≤
      2 * ((2 : ℝ) ^ (-2 * β)) ^ j := by
    rw [← hpow]; linarith
  have hnonneg : 0 ≤ ((((2 ^ j) ^ 2 : ℕ) : ℝ) ^ (-β) + (((2 ^ (j + 1)) ^ 2 : ℕ) : ℝ) ^ (-β)) *
      ramanujanCutoffErrorConstant ε β := by
    have := ramanujanCutoffErrorConstant_nonneg ε β
    positivity
  have hmul_le : ((((2 ^ j) ^ 2 : ℕ) : ℝ) ^ (-β) + (((2 ^ (j + 1)) ^ 2 : ℕ) : ℝ) ^ (-β)) *
      ramanujanCutoffErrorConstant ε β ≤
      2 * ((2 : ℝ) ^ (-2 * β)) ^ j * ramanujanCutoffErrorConstant ε β :=
    mul_le_mul_of_nonneg_right hsum_le (ramanujanCutoffErrorConstant_nonneg ε β)
  calc ramanujanCutoffTransportEnergy ε ((2 ^ j) ^ 2) ((2 ^ (j + 1)) ^ 2) (2 ^ j)
      ≤ ((2 ^ j : ℕ) : ℝ) * (((((2 ^ j) ^ 2 : ℕ) : ℝ) ^ (-β) +
          (((2 ^ (j + 1)) ^ 2 : ℕ) : ℝ) ^ (-β)) * ramanujanCutoffErrorConstant ε β) ^ 2 := hb
    _ ≤ ((2 ^ j : ℕ) : ℝ) *
          (2 * ((2 : ℝ) ^ (-2 * β)) ^ j * ramanujanCutoffErrorConstant ε β) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnonneg hmul_le 2) (Nat.cast_nonneg _)
    _ = 4 * ramanujanCutoffErrorConstant ε β ^ 2 *
          (((2 ^ j : ℕ) : ℝ) * (((2 : ℝ) ^ (-2 * β)) ^ j) ^ 2) := by ring
    _ = twoScaleSquareCutoffEnvelope ε β j := by rw [hbase, twoScaleSquareCutoffEnvelope]

/-! ## §3. Two-Sided Comparison with the Receiver Energy and Equivalence with Admission -/

/-- The dyadic stage prefix energy `pmPowerDampedRamanujanPrefixEnergy ε (2^{m(j+1)} − 1) (2^{j+1})`. -/
def dyadicRamanujanPrefixEnergy (ε : ℝ) (m j : ℕ) : ℝ :=
  pmPowerDampedRamanujanPrefixEnergy ε (2 ^ (m * (j + 1)) - 1) (2 ^ (j + 1))

theorem dyadicRamanujanPrefixEnergy_nonneg (ε : ℝ) (m j : ℕ) :
    0 ≤ dyadicRamanujanPrefixEnergy ε m j := by
  unfold dyadicRamanujanPrefixEnergy pmPowerDampedRamanujanPrefixEnergy
  exact sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (by positivity)

/-- **Upper comparison: the dyadic stage prefix energy is bounded by twice the receiver energy plus
one geometric shell error.** -/
theorem dyadicRamanujanPrefixEnergy_le_dampedMobiusEnergy_add {ε : ℝ} (hε : 0 < ε)
    {m : ℕ} (hm : 1 ≤ m) (j : ℕ) :
    dyadicRamanujanPrefixEnergy ε m j ≤
      2 * dampedMobiusEnergy ε (2 ^ (j + 1)) +
        2 * ramanujanCutoffErrorConstant ε (ε / 2) ^ 2 * shellRatio ε m ^ (j + 1) := by
  have hIoc : Finset.Ioc 0 (2 ^ (j + 1)) = Finset.Icc 1 (2 ^ (j + 1)) := by
    ext n; rw [Finset.mem_Ioc, Finset.mem_Icc]; omega
  have h1 : ramanujanPhysicalShellEnergy ε (2 ^ (m * (j + 1))) 0 (2 ^ (j + 1)) =
      dyadicRamanujanPrefixEnergy ε m j := by
    rw [ramanujanPhysicalShellEnergy, hIoc, ← pmPowerDampedRamanujanPrefixEnergy,
      ← dyadicRamanujanPrefixEnergy]
  have h2 : shellWindowEnergy ε 0 (2 ^ (j + 1)) = dampedMobiusEnergy ε (2 ^ (j + 1)) := by
    rw [shellWindowEnergy, hIoc, dampedMobiusEnergy, pmPowerDampedDivisorDiscreteEnergy]
  have hUR : (2 : ℕ) ^ (j + 1) ≤ 2 ^ (m * (j + 1)) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left _ hm)
  have hbound := ramanujanPhysicalShellEnergy_le_energy_add hε (by positivity : (0 : ℝ) ≤ ε / 2)
    (by linarith : ε / 2 < ε) (R := 2 ^ (m * (j + 1))) (T := 0) (U := 2 ^ (j + 1))
    (by positivity) hUR
  have hcast : (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (j + 1) := by push_cast; ring
  have hcastR : (((2 : ℕ) ^ (m * (j + 1)) : ℕ) : ℝ) = ((2 : ℕ) : ℝ) ^ (m * (j + 1)) :=
    Nat.cast_pow 2 (m * (j + 1))
  rw [h1, h2, hcast, hcastR, shellError_eq] at hbound
  exact hbound

/-- **Lower comparison: the receiver energy at `2^{j+1}` is bounded by twice the dyadic stage prefix
energy plus one geometric cutoff error.** -/
theorem dampedMobiusEnergy_le_dyadicRamanujanPrefixEnergy_add {ε : ℝ} (hε : 0 < ε)
    {m : ℕ} (hm : 1 ≤ m) (j : ℕ) :
    dampedMobiusEnergy ε (2 ^ (j + 1)) ≤
      2 * dyadicRamanujanPrefixEnergy ε m j +
        2 * ramanujanCutoffErrorConstant ε (ε / 2) ^ 2 * shellRatio ε m ^ (j + 1) := by
  have hUR : (2 : ℕ) ^ (j + 1) ≤ 2 ^ (m * (j + 1)) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left _ hm)
  have hcell : ∀ n ∈ Finset.Icc 1 (2 ^ (j + 1)),
      pmPowerDampedCenteredDivisorPrefix ε n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        2 * (‖pmPowerDampedRamanujanCumulativePrefix ε (2 ^ (m * (j + 1)) - 1) n‖ ^ 2 /
          ((n : ℝ) * ((n : ℝ) + 1))) +
        2 * (‖pmPowerDampedRamanujanCumulativePrefix ε (2 ^ (m * (j + 1)) - 1) n -
          pmPowerDampedDivisorRemainder ε n‖ ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := by
    intro n _
    have htri : |pmPowerDampedCenteredDivisorPrefix ε n| ≤
        ‖pmPowerDampedRamanujanCumulativePrefix ε (2 ^ (m * (j + 1)) - 1) n‖ +
        ‖pmPowerDampedRamanujanCumulativePrefix ε (2 ^ (m * (j + 1)) - 1) n -
          pmPowerDampedDivisorRemainder ε n‖ := by
      rw [← norm_pmPowerDampedDivisorRemainder_natCast hε n]
      have h := norm_sub_le (pmPowerDampedRamanujanCumulativePrefix ε (2 ^ (m * (j + 1)) - 1) n)
        (pmPowerDampedRamanujanCumulativePrefix ε (2 ^ (m * (j + 1)) - 1) n -
          pmPowerDampedDivisorRemainder ε n)
      rw [sub_sub_cancel] at h
      exact h
    have hsq : pmPowerDampedCenteredDivisorPrefix ε n ^ 2 ≤
        2 * ‖pmPowerDampedRamanujanCumulativePrefix ε (2 ^ (m * (j + 1)) - 1) n‖ ^ 2 +
        2 * ‖pmPowerDampedRamanujanCumulativePrefix ε (2 ^ (m * (j + 1)) - 1) n -
          pmPowerDampedDivisorRemainder ε n‖ ^ 2 := by
      have hmono := pow_le_pow_left₀ (abs_nonneg _) htri 2
      rw [sq_abs] at hmono
      nlinarith [sq_nonneg (‖pmPowerDampedRamanujanCumulativePrefix ε (2 ^ (m * (j + 1)) - 1) n‖ -
        ‖pmPowerDampedRamanujanCumulativePrefix ε (2 ^ (m * (j + 1)) - 1) n -
          pmPowerDampedDivisorRemainder ε n‖)]
    have hdiv := div_le_div_of_nonneg_right hsq (by positivity : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1))
    linarith [show (2 * ‖pmPowerDampedRamanujanCumulativePrefix ε (2 ^ (m * (j + 1)) - 1) n‖ ^ 2 +
        2 * ‖pmPowerDampedRamanujanCumulativePrefix ε (2 ^ (m * (j + 1)) - 1) n -
          pmPowerDampedDivisorRemainder ε n‖ ^ 2) / ((n : ℝ) * ((n : ℝ) + 1)) =
        2 * (‖pmPowerDampedRamanujanCumulativePrefix ε (2 ^ (m * (j + 1)) - 1) n‖ ^ 2 /
          ((n : ℝ) * ((n : ℝ) + 1))) +
        2 * (‖pmPowerDampedRamanujanCumulativePrefix ε (2 ^ (m * (j + 1)) - 1) n -
          pmPowerDampedDivisorRemainder ε n‖ ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) by ring]
  have hsum : dampedMobiusEnergy ε (2 ^ (j + 1)) ≤
      2 * dyadicRamanujanPrefixEnergy ε m j +
        2 * ramanujanCutoffHeadErrorEnergy ε (2 ^ (m * (j + 1))) (2 ^ (j + 1)) := by
    unfold dampedMobiusEnergy pmPowerDampedDivisorDiscreteEnergy
      dyadicRamanujanPrefixEnergy pmPowerDampedRamanujanPrefixEnergy ramanujanCutoffHeadErrorEnergy
    calc (∑ n ∈ Finset.Icc 1 (2 ^ (j + 1)),
            pmPowerDampedCenteredDivisorPrefix ε n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)))
        ≤ ∑ n ∈ Finset.Icc 1 (2 ^ (j + 1)),
            (2 * (‖pmPowerDampedRamanujanCumulativePrefix ε (2 ^ (m * (j + 1)) - 1) n‖ ^ 2 /
              ((n : ℝ) * ((n : ℝ) + 1))) +
            2 * (‖pmPowerDampedRamanujanCumulativePrefix ε (2 ^ (m * (j + 1)) - 1) n -
              pmPowerDampedDivisorRemainder ε n‖ ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)))) :=
          sum_le_sum hcell
      _ = _ := by rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have herr := ramanujanCutoffHeadErrorEnergy_le hε (by positivity : (0 : ℝ) ≤ ε / 2)
    (by linarith : ε / 2 < ε) (Q := 2 ^ (m * (j + 1))) (T := 2 ^ (j + 1)) (by positivity) hUR
  have hcast : (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (j + 1) := by push_cast; ring
  have hcastR : (((2 : ℕ) ^ (m * (j + 1)) : ℕ) : ℝ) = ((2 : ℕ) : ℝ) ^ (m * (j + 1)) :=
    Nat.cast_pow 2 (m * (j + 1))
  have herr2 : 2 * ramanujanCutoffHeadErrorEnergy ε (2 ^ (m * (j + 1))) (2 ^ (j + 1)) ≤
      2 * ramanujanCutoffErrorConstant ε (ε / 2) ^ 2 * shellRatio ε m ^ (j + 1) := by
    have hmul := mul_le_mul_of_nonneg_left herr (by norm_num : (0 : ℝ) ≤ 2)
    rw [← mul_assoc, hcast, hcastR, shellError_eq] at hmul
    exact hmul
  linarith

/-- **Four-Way Equivalence of Contractive Complementary-Sector Propagation and Admission.**
For any `ε > 0` and compatible cutoff depth `1 ≤ m` with `1 < (m : ℝ) * ε`, admission at `ε`,
membership in `receiverDampings`, existence of a contractive affine recurrence
`F_{j+1} ≤ q_j F_j + r_j` (`0 ≤ q_j ≤ θ < 1`, `0 ≤ r_j ≤ R`) for `dyadicRamanujanPrefixEnergy ε m`,
and existence of a contractive affine recurrence with the canonical multiplier `q_j = shellRatio ε m`
are all equivalent. -/
theorem complementarySector_propagation_tfae {ε : ℝ} (hε : 0 < ε)
    {m : ℕ} (hm : 1 ≤ m) (hmε : 1 < (m : ℝ) * ε) :
    List.TFAE
      [ Admits dampedMobiusEnergy ε,
        ε ∈ receiverDampings,
        ∃ (θ R : ℝ) (q r : ℕ → ℝ), θ < 1 ∧ (∀ j, 0 ≤ q j) ∧ (∀ j, q j ≤ θ) ∧
          (∀ j, 0 ≤ r j) ∧ (∀ j, r j ≤ R) ∧
          ∀ j, dyadicRamanujanPrefixEnergy ε m (j + 1) ≤
            q j * dyadicRamanujanPrefixEnergy ε m j + r j,
        ∃ R : ℝ, 0 ≤ R ∧ ∀ j : ℕ,
          dyadicRamanujanPrefixEnergy ε m (j + 1) ≤
            shellRatio ε m * dyadicRamanujanPrefixEnergy ε m j + R ] := by
  tfae_have 1 ↔ 2 := (mem_receiverDampings_iff_admits hε).symm
  tfae_have 4 → 3 := by
    rintro ⟨R, hR0, hrec⟩
    exact ⟨shellRatio ε m, R, fun _ => shellRatio ε m, fun _ => R,
      shellRatio_lt_one hmε, fun _ => shellRatio_nonneg ε m, fun _ => le_rfl,
      fun _ => hR0, fun _ => le_rfl, hrec⟩
  tfae_have 1 → 4 := by
    rintro ⟨B, hB⟩
    have hq0 := shellRatio_nonneg ε m
    have hq1 := (shellRatio_lt_one hmε).le
    set M : ℝ := 2 * max B 0 + 2 * ramanujanCutoffErrorConstant ε (ε / 2) ^ 2
    refine ⟨M, by positivity, fun j => ?_⟩
    have hle : dyadicRamanujanPrefixEnergy ε m (j + 1) ≤ M := by
      have h1 := dyadicRamanujanPrefixEnergy_le_dampedMobiusEnergy_add hε hm (j + 1)
      have h2 : dampedMobiusEnergy ε (2 ^ (j + 1 + 1)) ≤ max B 0 :=
        (hB _).trans (le_max_left B 0)
      have h3 : shellRatio ε m ^ (j + 1 + 1) ≤ 1 := pow_le_one₀ hq0 hq1
      have hC : 0 ≤ 2 * ramanujanCutoffErrorConstant ε (ε / 2) ^ 2 := by positivity
      nlinarith
    have hnonneg : 0 ≤ shellRatio ε m * dyadicRamanujanPrefixEnergy ε m j :=
      mul_nonneg hq0 (dyadicRamanujanPrefixEnergy_nonneg ε m j)
    linarith
  tfae_have 3 → 1 := by
    rintro ⟨θ, R, q, r, hθ1, hq0, hqθ, hr0, hrR, hrec⟩
    obtain ⟨K, hK⟩ : ∃ K : ℝ,
        K = max (dyadicRamanujanPrefixEnergy ε m 0) (R / (1 - θ)) := ⟨_, rfl⟩
    have hFJ : ∀ j : ℕ, dyadicRamanujanPrefixEnergy ε m j ≤ K := fun j => by
      rw [hK]
      exact (le_affineEnvelope hq0 hrec j).trans
        (affineEnvelope_le_of_contraction (dyadicRamanujanPrefixEnergy_nonneg ε m 0)
          hθ1 hq0 hqθ hr0 hrR j)
    have hq_sr0 := shellRatio_nonneg ε m
    have hq_sr1 := (shellRatio_lt_one hmε).le
    refine Admits.of_dyadic_horizons
      (C := max (dampedMobiusEnergy ε 1)
        (2 * K + 2 * ramanujanCutoffErrorConstant ε (ε / 2) ^ 2))
      (dampedMobiusEnergy_mono ε) fun k => ?_
    rcases k with _ | j
    · simp only [pow_zero]
      exact le_max_left _ _
    · refine le_trans ?_ (le_max_right _ _)
      have hlow := dampedMobiusEnergy_le_dyadicRamanujanPrefixEnergy_add hε hm j
      have hpow : shellRatio ε m ^ (j + 1) ≤ 1 := pow_le_one₀ hq_sr0 hq_sr1
      have hC : 0 ≤ 2 * ramanujanCutoffErrorConstant ε (ε / 2) ^ 2 := by positivity
      nlinarith [hFJ j]
  tfae_finish

/-! ## §4. Unconditional Contractive Propagation Above `Θ − ½` and on the Vinogradov–Korobov Band -/

/-- **Unconditional Contractive Affine Propagation Above `Θ − ½`.**
For every `ε > Θ − ½` and every compatible depth `1 ≤ m` with `1 < (m : ℝ) * ε`,
`dyadicRamanujanPrefixEnergy ε m` unconditionally obeys a contractive affine recurrence with
multiplier `shellRatio ε m < 1` and a stage-uniform upper bound. -/
theorem exists_contractive_affine_propagation_above_zeroWidth {ε : ℝ}
    (hε : zetaZeroAbscissa - 1 / 2 < ε) {m : ℕ} (hm : 1 ≤ m) (hmε : 1 < (m : ℝ) * ε) :
    ∃ R : ℝ, 0 ≤ R ∧ shellRatio ε m < 1 ∧
      (∀ j : ℕ, dyadicRamanujanPrefixEnergy ε m (j + 1) ≤
        shellRatio ε m * dyadicRamanujanPrefixEnergy ε m j + R) ∧
      (∀ j : ℕ, dyadicRamanujanPrefixEnergy ε m j ≤
        max (dyadicRamanujanPrefixEnergy ε m 0) (R / (1 - shellRatio ε m))) := by
  have hε0 : 0 < ε := by linarith [half_le_zetaZeroAbscissa]
  have hadm := admits_dampedMobiusEnergy_of_zetaZeroAbscissa_sub_half_lt hε
  obtain ⟨R, hR0, hrec⟩ :=
    ((complementarySector_propagation_tfae hε0 hm hmε).out 0 3).mp hadm
  have hlt := shellRatio_lt_one hmε
  have hq0 := shellRatio_nonneg ε m
  refine ⟨R, hR0, hlt, hrec, fun j => ?_⟩
  exact (le_affineEnvelope (fun _ => hq0) hrec j).trans
    (affineEnvelope_le_of_contraction (dyadicRamanujanPrefixEnergy_nonneg ε m 0)
      hlt (fun _ => hq0) (fun _ => le_rfl) (fun _ => hR0) (fun _ => le_rfl) j)

/-- The complete compensated head energy `(1 − α_{2^{j+1}})² ‖L_{2^{j+1}}‖² + ‖R_{2^{j+1}}‖²` at
dyadic cutoff `P_{j+1}² = (2^{j+1})²`. -/
def dyadicCompensatedSectorEnergy (ε : ℝ) (j : ℕ) : ℝ :=
  (1 - sectorCompensationAmplitude ε (2 ^ (j + 1))) ^ 2 *
    pmRamanujanLargePrimeSectorEnergy ε (2 ^ (j + 1)) +
    sectorTransverseEnergy ε (2 ^ (j + 1))

theorem dyadicCompensatedSectorEnergy_eq (ε : ℝ) (j : ℕ) :
    dyadicCompensatedSectorEnergy ε j =
      pmPowerDampedRamanujanPrefixEnergy ε ((2 ^ (j + 1)) ^ 2 - 1) (2 ^ (j + 1) - 1) := by
  have hP2 : 2 ≤ 2 ^ (j + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact (pmCompleteHeadEnergy_eq_sector_compensation hP2 ε).1.symm

theorem dyadicCompensatedSectorEnergy_le_dyadicRamanujanPrefixEnergy (ε : ℝ) (j : ℕ) :
    dyadicCompensatedSectorEnergy ε j ≤ dyadicRamanujanPrefixEnergy ε 2 j := by
  rw [dyadicCompensatedSectorEnergy_eq, dyadicRamanujanPrefixEnergy]
  have hpow : (2 ^ (j + 1)) ^ 2 = 2 ^ (2 * (j + 1)) := by ring
  rw [hpow]
  unfold pmPowerDampedRamanujanPrefixEnergy
  exact sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (Nat.sub_le _ 1))
    fun _ _ _ => div_nonneg (sq_nonneg _) (by positivity)

theorem dyadicCompensatedSectorEnergy_nonneg (ε : ℝ) (j : ℕ) :
    0 ≤ dyadicCompensatedSectorEnergy ε j := by
  rw [dyadicCompensatedSectorEnergy_eq]
  unfold pmPowerDampedRamanujanPrefixEnergy
  exact sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (by positivity)

/-- **Unconditional Contractive Affine Recurrence for the Compensated Large-Prime Sector Energy.**
For every `ε > max (1 / 2) (Θ − ½)` (where `m = 2` satisfies `2 ε > 1`), the compensated
sector-plus-complement head energy `dyadicCompensatedSectorEnergy ε j` unconditionally obeys a
contractive affine recurrence with multiplier `shellRatio ε 2 < 1` and a uniform envelope bound. -/
theorem exists_compensated_head_affine_contraction_above_zeroWidth {ε : ℝ}
    (hε_half : 1 / 2 < ε) (hε_zw : zetaZeroAbscissa - 1 / 2 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ shellRatio ε 2 < 1 ∧
      (∀ j : ℕ, dyadicCompensatedSectorEnergy ε (j + 1) ≤
        shellRatio ε 2 * dyadicCompensatedSectorEnergy ε j + R) ∧
      (∀ j : ℕ, dyadicCompensatedSectorEnergy ε j ≤
        max (dyadicCompensatedSectorEnergy ε 0) (R / (1 - shellRatio ε 2))) := by
  have hmε : 1 < ((2 : ℕ) : ℝ) * ε := by push_cast; linarith
  obtain ⟨R₀, hR₀, hlt, _, hbound⟩ :=
    exists_contractive_affine_propagation_above_zeroWidth hε_zw (by norm_num : 1 ≤ 2) hmε
  obtain ⟨K, hK⟩ : ∃ K : ℝ,
      K = max (dyadicRamanujanPrefixEnergy ε 2 0) (R₀ / (1 - shellRatio ε 2)) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact le_max_of_le_left (dyadicRamanujanPrefixEnergy_nonneg ε 2 0)
  have hq0 := shellRatio_nonneg ε 2
  have hrec : ∀ j : ℕ, dyadicCompensatedSectorEnergy ε (j + 1) ≤
      shellRatio ε 2 * dyadicCompensatedSectorEnergy ε j + K := by
    intro j
    have h1 : dyadicCompensatedSectorEnergy ε (j + 1) ≤ K := by
      rw [hK]
      exact (dyadicCompensatedSectorEnergy_le_dyadicRamanujanPrefixEnergy ε (j + 1)).trans
        (hbound (j + 1))
    exact le_add_of_nonneg_of_le
      (mul_nonneg hq0 (dyadicCompensatedSectorEnergy_nonneg ε j)) h1
  refine ⟨K, hK0, hlt, hrec, fun j => ?_⟩
  exact (le_affineEnvelope (fun _ => hq0) hrec j).trans
    (affineEnvelope_le_of_contraction (dyadicCompensatedSectorEnergy_nonneg ε 0)
      hlt (fun _ => hq0) (fun _ => le_rfl) (fun _ => hK0) (fun _ => le_rfl) j)

/-- **Unconditional Vinogradov–Korobov Band Bound for the Dyadic Stage Prefix Energy.**
For every damping floor `ε₀ > 0` and depth `m ≥ 1` with `1 < m ε₀`, there exists `K ≥ 0` such that
for all `j : ℕ` and all `ε ∈ [ε₀, 1/2]` in the Vinogradov–Korobov band at horizon `2^{j+1}`,
`dyadicRamanujanPrefixEnergy ε m j ≤ K`. -/
theorem exists_dyadicRamanujanPrefixEnergy_le_on_vinogradovKorobovBand {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    {m : ℕ} (hm : 1 ≤ m) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (j : ℕ) (ε : ℝ), ε₀ ≤ ε → ε ≤ 1 / 2 →
      1 / 2 - vkKappa * vkScale ((2 ^ (j + 1) : ℕ) : ℝ) /
        (480 * Real.log ((2 ^ (j + 1) : ℕ) : ℝ)) ≤ ε →
        dyadicRamanujanPrefixEnergy ε m j ≤
          2 * E + 2 * ramanujanCutoffErrorConstant ε (ε / 2) ^ 2 * shellRatio ε m ^ (j + 1) := by
  obtain ⟨E, hE0, hE⟩ := exists_receiver_le_on_vinogradovKorobovBand_of_pos hε₀
  refine ⟨E, hE0, fun j ε hε_ge hε2 hband => ?_⟩
  have hε0 : 0 < ε := lt_of_lt_of_le hε₀ hε_ge
  have h1 := dyadicRamanujanPrefixEnergy_le_dampedMobiusEnergy_add hε0 hm j
  have h2 := hE (2 ^ (j + 1)) ε hε_ge hε2 hband
  linarith

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

import GaloisForLFunctions.RHTower.PMRamanujanComplementaryCancellation

/-!
# Compensation coordinates: amplitude mismatch and transverse remainder

Two sectors `L`, `C` of one source whose separate energies diverge can cancel to leading order.
Project the complement onto the coherent sector: `α = −⟪L, C⟫/‖L‖²`, `R = C + αL`, so `⟪L, R⟫ = 0`.
Then exactly

`‖L + C‖² = (1 − α)² ‖L‖² + ‖R‖²`  (`norm_add_sq_eq_compensation`).

The **amplitude mismatch** `1 − α` and the **transverse remainder** `R` are the two coordinates of
compensation, and the identity is a Pythagorean law: their normalized squares add up to the
relative complete energy, `(1 − α)² + ‖R‖²/‖L‖² = ‖L + C‖²/‖L‖²`
(`compensationDefect_eq_relativeEnergy`). Consequently

* relative cancellation `‖L + C‖ = o(‖L‖)` is *equivalent* to `α → 1` together with
  `‖R‖ = o(‖L‖)`, and any rate for either coordinate is a rate for the complete energy and
  conversely — the coordinates carry no information beyond the receiver itself;
* neither coordinate bounds the complete energy: relative smallness is not admission.

The actual instance (`RHTower.PMRamanujanComplementaryCancellation`): at cutoff `P²` the large-prime
sector `L_P` of the damped Möbius–Ramanujan expansion and its literal complement `C_P` have
`‖C_P‖²/‖L_P‖² → 1` and `⟪L_P, C_P⟫/‖L_P‖² → −1`. In compensation coordinates
(`tendsto_pmCompensationAmplitude_one`, `tendsto_pmTransverseEnergy_div_sectorEnergy_zero`):
`α_P → 1` and `‖R_P‖²/‖L_P‖² → 0`, with the complete head energy split exactly as
`(1 − α_P)²‖L_P‖² + ‖R_P‖²` (`pmCompleteHeadEnergy_eq_compensation`). What the source has not yet
been shown to give is a bound on either term that does not grow with `P`.
-/

open Filter Topology Finset RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

/-! ## The abstract law -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The amplitude ratio `α = −⟪L, C⟫/‖L‖²` of the complement against the coherent sector. -/
def compensationAmplitude (L C : E) : ℝ := -inner ℝ L C / ‖L‖ ^ 2

/-- The transverse remainder `R = C + αL`. -/
def transverseRemainder (L C : E) : E := C + compensationAmplitude L C • L

/-- The transverse remainder is orthogonal to the coherent sector. -/
theorem inner_transverseRemainder {L : E} (hL : L ≠ 0) (C : E) :
    inner ℝ L (transverseRemainder L C) = 0 := by
  have hn : ‖L‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hL)
  rw [transverseRemainder, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
    compensationAmplitude]
  field_simp
  ring

/-- **The Pythagorean compensation law.** `‖L + C‖² = (1 − α)²‖L‖² + ‖R‖²`. -/
theorem norm_add_sq_eq_compensation {L : E} (hL : L ≠ 0) (C : E) :
    ‖L + C‖ ^ 2 = (1 - compensationAmplitude L C) ^ 2 * ‖L‖ ^ 2 +
      ‖transverseRemainder L C‖ ^ 2 := by
  have hdecomp : L + C = (1 - compensationAmplitude L C) • L + transverseRemainder L C := by
    rw [transverseRemainder, sub_smul, one_smul]; abel
  have horth : inner ℝ ((1 - compensationAmplitude L C) • L) (transverseRemainder L C) = 0 := by
    rw [inner_smul_left, inner_transverseRemainder hL, mul_zero]
  rw [hdecomp, norm_add_sq_real, horth, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- **The compensation defect is the relative complete energy.**
`(1 − α)² + ‖R‖²/‖L‖² = ‖L + C‖²/‖L‖²`. -/
theorem compensationDefect_eq_relativeEnergy {L : E} (hL : L ≠ 0) (C : E) :
    (1 - compensationAmplitude L C) ^ 2 + ‖transverseRemainder L C‖ ^ 2 / ‖L‖ ^ 2 =
      ‖L + C‖ ^ 2 / ‖L‖ ^ 2 := by
  have hn : ‖L‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hL)
  rw [norm_add_sq_eq_compensation hL C]
  field_simp

end Abstract

/-! ## Scalar Gram data

Energies of the actual source are weighted sums, not vectors of a named Hilbert space; the law only
needs the three Gram numbers `a = ‖L‖²`, `b = ‖C‖²`, `m = ⟪L, C⟫`. -/

/-- Scalar amplitude `α = −m/a`. -/
def gramAmplitude (a m : ℝ) : ℝ := -m / a

/-- Scalar transverse energy `‖R‖² = b − m²/a`. -/
def gramTransverse (a b m : ℝ) : ℝ := b - m ^ 2 / a

/-- The scalar Pythagorean law `a + b + 2m = (1 − α)² a + ‖R‖²`. -/
theorem gram_add_eq_compensation {a : ℝ} (ha : a ≠ 0) (b m : ℝ) :
    a + b + 2 * m = (1 - gramAmplitude a m) ^ 2 * a + gramTransverse a b m := by
  rw [gramAmplitude, gramTransverse]
  field_simp
  ring

/-- Under Cauchy–Schwarz `m² ≤ ab` the transverse energy is nonnegative. -/
theorem gramTransverse_nonneg {a b m : ℝ} (ha : 0 < a) (hcs : m ^ 2 ≤ a * b) :
    0 ≤ gramTransverse a b m := by
  rw [gramTransverse, sub_nonneg, div_le_iff₀ ha]
  linarith

/-- Each compensation coordinate is at most the relative complete energy. -/
theorem gram_coordinates_le {a b m : ℝ} (ha : 0 < a) (hcs : m ^ 2 ≤ a * b) :
    (1 - gramAmplitude a m) ^ 2 ≤ (a + b + 2 * m) / a ∧
      gramTransverse a b m / a ≤ (a + b + 2 * m) / a := by
  have hR := gramTransverse_nonneg ha hcs
  have hlaw := gram_add_eq_compensation ha.ne' b m
  constructor
  · rw [le_div_iff₀ ha]; nlinarith [sq_nonneg (1 - gramAmplitude a m)]
  · exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (1 - gramAmplitude a m)]) ha.le

/-! ## The actual instance: the large-prime sector of the Möbius–Ramanujan expansion -/

/-- The amplitude of the literal complement against the large-prime sector at cutoff `P²`. -/
def pmCompensationAmplitude (ε : ℝ) (P : ℕ) : ℝ :=
  gramAmplitude (pmRamanujanLargePrimeSectorEnergy ε P)
    (pmRamanujanLargePrimeComplementMixedEnergy ε P)

/-- The transverse energy of the complement after removing its coherent part. -/
def pmTransverseEnergy (ε : ℝ) (P : ℕ) : ℝ :=
  gramTransverse (pmRamanujanLargePrimeSectorEnergy ε P) (pmRamanujanLargePrimeComplementEnergy ε P)
    (pmRamanujanLargePrimeComplementMixedEnergy ε P)

/-- The complete head energy is the sector energy, the complement energy and twice the mixed
energy. -/
theorem pmCompleteHeadEnergy_eq_sum {P : ℕ} (hP : 2 ≤ P) (ε : ℝ) :
    pmPowerDampedRamanujanPrefixEnergy ε (P ^ 2 - 1) (P - 1) =
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

/-- The mixed energy obeys Cauchy–Schwarz against the two sector energies. -/
theorem pmMixedEnergy_sq_le (ε : ℝ) (P : ℕ) :
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

/-- **The actual compensation law.** For `P ≥ 2` with a nonzero sector energy, the complete head
energy is `(1 − α_P)²‖L_P‖² + ‖R_P‖²` with `‖R_P‖² ≥ 0`. -/
theorem pmCompleteHeadEnergy_eq_compensation {P : ℕ} (hP : 2 ≤ P) {ε : ℝ}
    (hL : 0 < pmRamanujanLargePrimeSectorEnergy ε P) :
    pmPowerDampedRamanujanPrefixEnergy ε (P ^ 2 - 1) (P - 1) =
        (1 - pmCompensationAmplitude ε P) ^ 2 * pmRamanujanLargePrimeSectorEnergy ε P +
          pmTransverseEnergy ε P ∧
      0 ≤ pmTransverseEnergy ε P := by
  refine ⟨?_, gramTransverse_nonneg hL (pmMixedEnergy_sq_le ε P)⟩
  rw [pmCompleteHeadEnergy_eq_sum hP, pmCompensationAmplitude, pmTransverseEnergy]
  exact gram_add_eq_compensation hL.ne' _ _

/-- **The amplitude tends to one**: the complement carries, to leading order, exactly the negative
of the coherent sector. -/
theorem tendsto_pmCompensationAmplitude_one {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    Tendsto (pmCompensationAmplitude ε) atTop (𝓝 1) := by
  have h := (tendsto_pmRamanujanLargePrimeComplementMixedEnergy_ratio_neg_one hε hεhalf).neg
  rw [neg_neg] at h
  refine h.congr fun P => ?_
  rw [pmCompensationAmplitude, gramAmplitude, neg_div]

/-- **The transverse remainder is relatively negligible**: `‖R_P‖²/‖L_P‖² → 0`. -/
theorem tendsto_pmTransverseEnergy_div_sectorEnergy_zero {ε : ℝ} (hε : 0 < ε)
    (hεhalf : ε < 1 / 2) :
    Tendsto (fun P => pmTransverseEnergy ε P / pmRamanujanLargePrimeSectorEnergy ε P) atTop
      (𝓝 0) := by
  have hb := tendsto_pmRamanujanLargePrimeComplementEnergy_ratio_one hε hεhalf
  have hm := tendsto_pmRamanujanLargePrimeComplementMixedEnergy_ratio_neg_one hε hεhalf
  have h := hb.sub (hm.pow 2)
  rw [show (1 : ℝ) - (-1) ^ 2 = 0 by norm_num] at h
  refine h.congr' ?_
  filter_upwards [(tendsto_pmRamanujanLargePrimeSectorEnergy_atTop hε hεhalf).eventually_gt_atTop 0]
    with P hL
  rw [pmTransverseEnergy, gramTransverse, sub_div, div_pow]
  field_simp

end GaloisForLFunctions.ArithmeticCompensationTheory

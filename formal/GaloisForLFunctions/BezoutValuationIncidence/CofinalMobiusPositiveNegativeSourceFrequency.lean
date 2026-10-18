import GaloisForLFunctions.BezoutValuationIncidence.CofinalMobiusOddMomentsAndQuotientProducts
import GaloisForLFunctions.BezoutValuationIncidence.CofinalLinearWindowMobiusEnergyAndDefectBounds

/-!
# Positive frequency of both Möbius-source signs

For each fixed natural B, put C=B+1 and observe the actual truncated
Möbius source up to M=(C+1)N. Both its positive-value count and its
negative-value count are eventually at least

`cofinalMobiusQuadraticProfile C * N / (4*C^2)`.

Since the profile is at least the squarefree density `6/pi^2`, this gives
an explicit positive lower bound for both sign frequencies on every
fixed integer horizon ratio at least two.

The proof uses the unconditional quadratic profile, first-moment
cancellation, and the pointwise band bound. The finite inequalities
`Q + C*S <= 2*C^2*positiveCount` and
`Q - C*S <= 2*C^2*negativeCount` transfer these arithmetic inputs to the
literal sign readouts. No MC/PM receiver hypothesis is assumed.

This does not assert equal sign counts, individual sign-density limits,
or a bound uniform in a growing horizon ratio. The factor four allows
an eventual margin and is not claimed sharp.
-/

open Finset Filter
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open RHTower RHTower.Sieve
open scoped BigOperators Topology

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The number of strictly positive values of the literal Möbius source in its finite prefix. -/
def moebiusSourcePositiveCount (N M : ℕ) : ℕ :=
  ((Finset.Icc 1 M).filter (fun k => 0 < sieveSeq N moebiusReal k)).card

/-- The number of strictly negative values of the literal Möbius source in its finite prefix. -/
def moebiusSourceNegativeCount (N M : ℕ) : ℕ :=
  ((Finset.Icc 1 M).filter (fun k => sieveSeq N moebiusReal k < 0)).card

private theorem square_add_mul_le_positive_indicator {x C : ℝ}
    (hC : 0 ≤ C) (hx : |x| ≤ C) :
    x ^ 2 + C * x ≤ 2 * C ^ 2 * (if 0 < x then 1 else 0) := by
  by_cases hpos : 0 < x
  · rw [if_pos hpos, mul_one]
    have hsq := pow_le_pow_left₀ (abs_nonneg x) hx 2
    rw [sq_abs] at hsq
    have hmul := mul_le_mul_of_nonneg_left (abs_le.mp hx).2 hC
    nlinarith
  · rw [if_neg hpos, mul_zero]
    have hmul := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hpos)
      (show 0 ≤ x + C by linarith [(abs_le.mp hx).1])
    nlinarith

private theorem square_sub_mul_le_negative_indicator {x C : ℝ}
    (hC : 0 ≤ C) (hx : |x| ≤ C) :
    x ^ 2 - C * x ≤ 2 * C ^ 2 * (if x < 0 then 1 else 0) := by
  have h := square_add_mul_le_positive_indicator hC (show |-x| ≤ C by simpa using hx)
  simpa only [neg_sq, mul_neg, sub_eq_add_neg, neg_pos] using h

/-- Finite quadratic energy plus the signed first moment is controlled by the positive-value count. -/
theorem moebiusSourcePositiveCount_quadratic_bound (B N : ℕ) :
    sieveL2PrefixEnergy N (((B + 1) + 1) * N) moebiusReal +
        ((B + 1 : ℕ) : ℝ) *
          (∑ k ∈ Finset.Icc 1 (((B + 1) + 1) * N), sieveSeq N moebiusReal k) ≤
      2 * ((B + 1 : ℕ) : ℝ) ^ 2 *
        (moebiusSourcePositiveCount N (((B + 1) + 1) * N) : ℝ) := by
  classical
  by_cases hN : N = 0
  · subst N
    simp [sieveL2PrefixEnergy, moebiusSourcePositiveCount]
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  have hcount :
      (∑ k ∈ Finset.Icc 1 (((B + 1) + 1) * N),
        if 0 < sieveSeq N moebiusReal k then (1 : ℝ) else 0) =
      (moebiusSourcePositiveCount N (((B + 1) + 1) * N) : ℝ) := by
    rw [← Finset.sum_filter]
    simp [moebiusSourcePositiveCount]
  calc
    _ = ∑ k ∈ Finset.Icc 1 (((B + 1) + 1) * N),
        ((sieveSeq N moebiusReal k) ^ 2 +
          ((B + 1 : ℕ) : ℝ) * sieveSeq N moebiusReal k) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rfl
    _ ≤ ∑ k ∈ Finset.Icc 1 (((B + 1) + 1) * N),
        2 * ((B + 1 : ℕ) : ℝ) ^ 2 *
          (if 0 < sieveSeq N moebiusReal k then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro k hk
      exact square_add_mul_le_positive_indicator (by positivity)
        (abs_sieveSeq_moebiusReal_le_band_width hN1 (by omega)
          (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2)
    _ = _ := by rw [← Finset.mul_sum, hcount]

/-- Finite quadratic energy minus the signed first moment is controlled by the negative-value count. -/
theorem moebiusSourceNegativeCount_quadratic_bound (B N : ℕ) :
    sieveL2PrefixEnergy N (((B + 1) + 1) * N) moebiusReal -
        ((B + 1 : ℕ) : ℝ) *
          (∑ k ∈ Finset.Icc 1 (((B + 1) + 1) * N), sieveSeq N moebiusReal k) ≤
      2 * ((B + 1 : ℕ) : ℝ) ^ 2 *
        (moebiusSourceNegativeCount N (((B + 1) + 1) * N) : ℝ) := by
  classical
  by_cases hN : N = 0
  · subst N
    simp [sieveL2PrefixEnergy, moebiusSourceNegativeCount]
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  have hcount :
      (∑ k ∈ Finset.Icc 1 (((B + 1) + 1) * N),
        if sieveSeq N moebiusReal k < 0 then (1 : ℝ) else 0) =
      (moebiusSourceNegativeCount N (((B + 1) + 1) * N) : ℝ) := by
    rw [← Finset.sum_filter]
    simp [moebiusSourceNegativeCount]
  calc
    _ = ∑ k ∈ Finset.Icc 1 (((B + 1) + 1) * N),
        ((sieveSeq N moebiusReal k) ^ 2 -
          ((B + 1 : ℕ) : ℝ) * sieveSeq N moebiusReal k) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      rfl
    _ ≤ ∑ k ∈ Finset.Icc 1 (((B + 1) + 1) * N),
        2 * ((B + 1 : ℕ) : ℝ) ^ 2 *
          (if sieveSeq N moebiusReal k < 0 then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro k hk
      exact square_sub_mul_le_negative_indicator (by positivity)
        (abs_sieveSeq_moebiusReal_le_band_width hN1 (by omega)
          (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2)
    _ = _ := by rw [← Finset.mul_sum, hcount]

/-- Both source signs occur linearly often at every fixed integer horizon ratio at least two. -/
theorem eventually_moebiusSource_sign_counts_profile_lower (B : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      cofinalMobiusQuadraticProfile (B + 1) / (4 * ((B + 1 : ℕ) : ℝ) ^ 2) * N ≤
          (moebiusSourcePositiveCount N (((B + 1) + 1) * N) : ℝ) ∧
      cofinalMobiusQuadraticProfile (B + 1) / (4 * ((B + 1 : ℕ) : ℝ) ^ 2) * N ≤
          (moebiusSourceNegativeCount N (((B + 1) + 1) * N) : ℝ) := by
  let C : ℝ := ((B + 1 : ℕ) : ℝ)
  let F : ℝ := cofinalMobiusQuadraticProfile (B + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hD : 0 < squarefreeDensity := by rw [squarefreeDensity_eq]; positivity
  have hF : 0 < F := hD.trans_le (squarefreeDensity_le_cofinalMobiusQuadraticProfile (by omega))
  have hfirst : Tendsto (fun N : ℕ =>
      (∑ k ∈ Finset.Icc 1 (((B + 1) + 1) * N), sieveSeq N moebiusReal k) / (N : ℝ))
      atTop (𝓝 0) := by
    simpa only [Nat.mul_zero, zero_add, pow_one] using
      tendsto_sieveSeq_odd_moment_linear_horizon (B + 1) 0
  have hplus : Tendsto (fun N : ℕ =>
      (sieveL2PrefixEnergy N (((B + 1) + 1) * N) moebiusReal +
        C * ∑ k ∈ Finset.Icc 1 (((B + 1) + 1) * N), sieveSeq N moebiusReal k) / (N : ℝ))
      atTop (𝓝 F) := by
    have h := (tendsto_sieveL2PrefixEnergy_moebiusReal_linear_horizon (B + 1)).add
      (hfirst.const_mul C)
    simpa only [mul_zero, add_zero, add_div, mul_div_assoc, F] using h
  have hminus : Tendsto (fun N : ℕ =>
      (sieveL2PrefixEnergy N (((B + 1) + 1) * N) moebiusReal -
        C * ∑ k ∈ Finset.Icc 1 (((B + 1) + 1) * N), sieveSeq N moebiusReal k) / (N : ℝ))
      atTop (𝓝 F) := by
    have h := (tendsto_sieveL2PrefixEnergy_moebiusReal_linear_horizon (B + 1)).sub
      (hfirst.const_mul C)
    simpa only [mul_zero, sub_zero, sub_div, mul_div_assoc, F] using h
  filter_upwards [hplus.eventually (eventually_gt_nhds (show F / 2 < F by linarith)),
    hminus.eventually (eventually_gt_nhds (show F / 2 < F by linarith)),
    eventually_ge_atTop 1] with N hp hm hN
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hp' := (lt_div_iff₀ hNr).mp hp
  have hm' := (lt_div_iff₀ hNr).mp hm
  have hcp := moebiusSourcePositiveCount_quadratic_bound B N
  have hcm := moebiusSourceNegativeCount_quadratic_bound B N
  change F / (4 * C ^ 2) * (N : ℝ) ≤ _ ∧ F / (4 * C ^ 2) * (N : ℝ) ≤ _
  change _ ≤ 2 * C ^ 2 * _ at hcp hcm
  constructor
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0 < 4 * C ^ 2 by positivity)).mpr
    nlinarith only [hp', hcp]
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0 < 4 * C ^ 2 by positivity)).mpr
    nlinarith only [hm', hcm]

/-- The squarefree density supplies an explicit unconditional lower bound for both source-sign counts. -/
theorem eventually_moebiusSource_sign_counts_squarefree_lower (B : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      squarefreeDensity / (4 * ((B + 1 : ℕ) : ℝ) ^ 2) * N ≤
          (moebiusSourcePositiveCount N (((B + 1) + 1) * N) : ℝ) ∧
      squarefreeDensity / (4 * ((B + 1 : ℕ) : ℝ) ^ 2) * N ≤
          (moebiusSourceNegativeCount N (((B + 1) + 1) * N) : ℝ) := by
  filter_upwards [eventually_moebiusSource_sign_counts_profile_lower B] with N hN
  have hcoef := div_le_div_of_nonneg_right
    (squarefreeDensity_le_cofinalMobiusQuadraticProfile (B := B + 1) (by omega))
    (show 0 ≤ 4 * ((B + 1 : ℕ) : ℝ) ^ 2 by positivity)
  have hbound := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ (N : ℝ) by positivity)
  exact ⟨hbound.trans hN.1, hbound.trans hN.2⟩

end
end GaloisForLFunctions.BezoutValuationIncidence

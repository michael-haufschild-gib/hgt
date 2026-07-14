import GaloisForLFunctions.RHTower.XiEndpointReciprocalTraceReflection
import GaloisForLFunctions.RHTower.PrimeArchCentralMomentGerm

/-!
# Dyadic value bridge from endpoint traces to central Xi moments

The raw endpoint reciprocal coordinate `z = 1/rho` and the centered reciprocal-square coordinate
are related by the exact rational substitution

`-1 / (rho - 1/2)^2 = -z^2 / (1 - z/2)^2`.

The endpoint disk bound makes the negative-binomial expansion of every power of this substitution
absolutely summable over both expansion order and the multiplicity-exact Xi divisor.  Consequently
the complete centered trace--Hankel moment sequence, and hence the fixed prime--Gamma source Taylor
moments, are reconstructed from the all-order raw endpoint traces by one explicit dyadic transform.
-/

open Complex

namespace RHTower

noncomputable section

/-- Exact rational substitution from the raw endpoint coordinate to the centered reciprocal-square
coordinate. -/
theorem xiZeroCopyReciprocalSquare_eq_rawDyadicMobius (q : XiZeroCopy) :
    xiZeroCopyReciprocalSquare q =
      -(xiRawReciprocalCoordinate q ^ 2) /
        (1 - xiRawReciprocalCoordinate q / 2) ^ 2 := by
  have hrho : (q.1 : ℂ) ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.zero_im] at him
    exact xi_divisor_support_im_ne_zero q.1 him
  have hhalf : (q.1 : ℂ) ≠ 1 / 2 := xi_divisor_support_ne_half q.1
  rw [xiZeroCopyReciprocalSquare_eq, xiCentralReciprocalSquare,
    xiRawReciprocalCoordinate]
  field_simp [hrho, hhalf]

/-- Pointwise negative-binomial reconstruction of every centered reciprocal-square power from the
raw endpoint coordinate. -/
theorem hasSum_xiZeroCopyReciprocalSquare_pow_rawDyadicTraces
    (q : XiZeroCopy) (m : ℕ) :
    HasSum (fun n : ℕ =>
      (-1 : ℂ) ^ (m + 1) *
        ((n + (2 * m + 1)).choose (2 * m + 1) : ℂ) *
          (2 : ℂ)⁻¹ ^ n *
            xiRawReciprocalCoordinate q ^ (n + (2 * m + 2)))
      (xiZeroCopyReciprocalSquare q ^ (m + 1)) := by
  let z : ℂ := xiRawReciprocalCoordinate q
  have hz : ‖z / 2‖ < 1 := by
    calc
      ‖z / 2‖ = ‖z‖ / 2 := by norm_num
      _ < 1 / 2 := by
        exact (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
          (xiRawReciprocalCoordinate_norm_lt_one q)
      _ < 1 := by norm_num
  have hseries :=
    hasSum_choose_mul_geometric_of_norm_lt_one (2 * m + 1) hz
  have hmul := hseries.mul_left
    ((-1 : ℂ) ^ (m + 1) * z ^ (2 * m + 2))
  rw [xiZeroCopyReciprocalSquare_eq_rawDyadicMobius]
  change HasSum (fun n : ℕ =>
      (-1 : ℂ) ^ (m + 1) *
        ((n + (2 * m + 1)).choose (2 * m + 1) : ℂ) *
          (2 : ℂ)⁻¹ ^ n * z ^ (n + (2 * m + 2)))
    ((-(z ^ 2) / (1 - z / 2) ^ 2) ^ (m + 1))
  convert hmul using 1
  · funext n
    rw [div_pow, pow_add, div_eq_mul_inv, ← inv_pow]
    ring
  · have hexp : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
    rw [hexp, div_pow, neg_pow, pow_mul, pow_mul]
    ring

set_option maxHeartbeats 800000 in
/-- Absolute summability of the complete dyadic transform over expansion order and exact Xi-divisor
copies. -/
theorem summable_xiCentralRawDyadicTrace_double (m : ℕ) :
    Summable (fun p : ℕ × XiZeroCopy =>
      (-1 : ℂ) ^ (m + 1) *
        ((p.1 + (2 * m + 1)).choose (2 * m + 1) : ℂ) *
          (2 : ℂ)⁻¹ ^ p.1 *
            xiRawReciprocalCoordinate p.2 ^ (p.1 + (2 * m + 2))) := by
  have hbase := summable_xiRawReciprocalTraceReflection_double
    (2 * m + 2) (by omega)
  refine Summable.of_norm_bounded hbase.norm ?_
  rintro ⟨n, q⟩
  change ‖(-1 : ℂ) ^ (m + 1) *
        ((n + (2 * m + 1)).choose (2 * m + 1) : ℂ) *
          (2 : ℂ)⁻¹ ^ n *
            xiRawReciprocalCoordinate q ^ (n + (2 * m + 2))‖ ≤
    ‖((n + ((2 * m + 2) - 1)).choose ((2 * m + 2) - 1) : ℂ) *
      xiRawReciprocalCoordinate q ^ ((2 * m + 2) + n)‖
  have hsub : (2 * m + 2) - 1 = 2 * m + 1 := by omega
  rw [hsub, show (2 * m + 2) + n = n + (2 * m + 2) by omega]
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hhalf : ‖(2 : ℂ)⁻¹‖ ^ n ≤ 1 := by
    apply pow_le_one₀ (norm_nonneg _)
    norm_num
  calc
    ‖((n + (2 * m + 1)).choose (2 * m + 1) : ℂ)‖ *
          ‖(2 : ℂ)⁻¹‖ ^ n *
            ‖xiRawReciprocalCoordinate q‖ ^ (n + (2 * m + 2)) ≤
      ‖((n + (2 * m + 1)).choose (2 * m + 1) : ℂ)‖ * 1 *
            ‖xiRawReciprocalCoordinate q‖ ^ (n + (2 * m + 2)) := by gcongr
    _ = ‖((n + (2 * m + 1)).choose (2 * m + 1) : ℂ)‖ *
            ‖xiRawReciprocalCoordinate q‖ ^ (n + (2 * m + 2)) := by ring

/-- **All-order endpoint-to-central value bridge.**  Every centered reciprocal-square Xi moment
is the explicit dyadic negative-binomial transform of the raw endpoint reciprocal traces. -/
theorem xiCentralReciprocalMoment_eq_rawDyadicTraces (m : ℕ) :
    xiCentralReciprocalMoment m =
      (-1 : ℂ) ^ (m + 1) *
        ∑' n : ℕ, ((n + (2 * m + 1)).choose (2 * m + 1) : ℂ) *
          (2 : ℂ)⁻¹ ^ n *
            xiRawReciprocalPowerTrace (n + (2 * m + 2)) := by
  let f : ℕ → XiZeroCopy → ℂ := fun n q =>
    (-1 : ℂ) ^ (m + 1) *
      ((n + (2 * m + 1)).choose (2 * m + 1) : ℂ) *
        (2 : ℂ)⁻¹ ^ n *
          xiRawReciprocalCoordinate q ^ (n + (2 * m + 2))
  have hf : Summable (Function.uncurry f) := summable_xiCentralRawDyadicTrace_double m
  have hpoint (q : XiZeroCopy) :
      ∑' n : ℕ, f n q = xiZeroCopyReciprocalSquare q ^ (m + 1) :=
    (hasSum_xiZeroCopyReciprocalSquare_pow_rawDyadicTraces q m).tsum_eq
  calc
    xiCentralReciprocalMoment m =
        ∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q ^ (m + 1) := by
      simpa using (tsum_xiZeroCopyReciprocalSquare_pow m).symm
    _ = ∑' q : XiZeroCopy, ∑' n : ℕ, f n q := by
      apply tsum_congr
      exact fun q => (hpoint q).symm
    _ = ∑' n : ℕ, ∑' q : XiZeroCopy, f n q := by
      rw [hf.tsum_comm]
    _ = (-1 : ℂ) ^ (m + 1) *
        ∑' n : ℕ, ((n + (2 * m + 1)).choose (2 * m + 1) : ℂ) *
          (2 : ℂ)⁻¹ ^ n *
            xiRawReciprocalPowerTrace (n + (2 * m + 2)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [xiRawReciprocalPowerTrace, ← tsum_mul_left]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro q
      simp [f]
      ring

/-- The same bridge read entirely from the fixed completed prime--Gamma source Taylor moments. -/
theorem primeArchSourceMoment_eq_rawDyadicTraces (m : ℕ) :
    ((analyticTraceMoments
        (normalizedTraceMomentGerm continuedPrimeArchSourceRelativeTrace) m : ℝ) : ℂ) =
      (-1 : ℂ) ^ (m + 1) *
        ∑' n : ℕ, ((n + (2 * m + 1)).choose (2 * m + 1) : ℂ) *
          (2 : ℂ)⁻¹ ^ n *
            xiRawReciprocalPowerTrace (n + (2 * m + 2)) := by
  rw [primeArchSourceMoment_eq_xiCentralReciprocalMoment,
    xiCentralReciprocalMoment_eq_rawDyadicTraces]

end

end RHTower

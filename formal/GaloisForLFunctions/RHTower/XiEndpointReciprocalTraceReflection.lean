import GaloisForLFunctions.RHTower.XiEndpointReflectionNeumannCarrier

/-!
# Functional-equation constraints on the endpoint reciprocal traces

The endpoint Neumann carrier expresses the completed Xi endpoint curvature through the raw
reciprocal-power traces

`T k = ∑_ρ ρ⁻ᵏ`.

This file adds the missing functional-equation constraint on that carrier.  Reflection
`ρ ↦ 1 - ρ` acts on the reciprocal coordinate by the exact Möbius map

`z ↦ -z / (1 - z)`.

The already proved uniform disk bound `|z| < 9/10` makes the associated negative-binomial
expansion absolutely summable after summing over all divisor copies.  Reindexing the Xi divisor
by reflection therefore gives, unconditionally and with multiplicity,

`T k = (-1)^k ∑_{n ≥ 0} choose (n+k-1) (k-1) T (k+n)` for every `k ≥ 2`.

This is a constraint among the actual Xi reciprocal traces, rather than an RH reformulation.
In degree two it removes the leading term and yields the exact Ward-type cancellation

`∑_{n ≥ 0} (n+2) T (n+3) = 0`.
-/

open Complex

namespace RHTower

noncomputable section

/-- Functional-equation reflection is the Möbius transform `z ↦ -z/(1-z)` on the raw
reciprocal coordinate. -/
theorem xiRawReciprocalCoordinate_reflect_eq_mobius (q : XiZeroCopy) :
    xiRawReciprocalCoordinate (xiZeroCopyReflectEquiv q) =
      -(xiRawReciprocalCoordinate q) / (1 - xiRawReciprocalCoordinate q) := by
  have hrho : (q.1 : ℂ) ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.zero_im] at him
    exact xi_divisor_support_im_ne_zero q.1 him
  have hrhoOne : (q.1 : ℂ) ≠ 1 := by
    intro hone
    have him := congrArg Complex.im hone
    simp only [Complex.one_im] at him
    exact xi_divisor_support_im_ne_zero q.1 him
  rw [xiRawReciprocalCoordinate, xiRawReciprocalCoordinate]
  change (1 - (q.1 : ℂ))⁻¹ = -((q.1 : ℂ)⁻¹) / (1 - (q.1 : ℂ)⁻¹)
  field_simp [hrho, hrhoOne]
  rw [show (q.1 : ℂ) - 1 = -(1 - (q.1 : ℂ)) by ring]
  rw [one_div, one_div, inv_neg, neg_neg]

/-- Pointwise negative-binomial reconstruction of a reflected reciprocal power. -/
theorem hasSum_xiRawReciprocalCoordinate_reflect_binomial
    (q : XiZeroCopy) (k : ℕ) (hk : 2 ≤ k) :
    HasSum (fun n : ℕ =>
      ((n + (k - 1)).choose (k - 1) : ℂ) *
        xiRawReciprocalCoordinate q ^ (k + n))
      (((-1 : ℂ) ^ k) *
        xiRawReciprocalCoordinate (xiZeroCopyReflectEquiv q) ^ k) := by
  let z : ℂ := xiRawReciprocalCoordinate q
  have hz : ‖z‖ < 1 := xiRawReciprocalCoordinate_norm_lt_one q
  have hseries := hasSum_choose_mul_geometric_of_norm_lt_one (k - 1) hz
  have hmul := hseries.mul_left (z ^ k)
  rw [xiRawReciprocalCoordinate_reflect_eq_mobius]
  change HasSum (fun n : ℕ =>
      ((n + (k - 1)).choose (k - 1) : ℂ) * z ^ (k + n))
    ((-1 : ℂ) ^ k * (-z / (1 - z)) ^ k)
  convert hmul using 1
  · funext n
    rw [pow_add]
    ring
  · have hk1 : k - 1 + 1 = k := by omega
    rw [hk1, div_pow, neg_pow]
    ring_nf
    have hsign : (-1 : ℂ) ^ (k * 2) = 1 := by
      rw [mul_comm, pow_mul]
      norm_num
    rw [hsign, mul_one]

set_option maxHeartbeats 800000 in
/-- The full binomially weighted trace carrier is absolutely summable over order and exact
Xi-divisor copies. -/
theorem summable_xiRawReciprocalTraceReflection_double (k : ℕ) (hk : 2 ≤ k) :
    Summable (fun p : ℕ × XiZeroCopy =>
      ((p.1 + (k - 1)).choose (k - 1) : ℂ) *
        xiRawReciprocalCoordinate p.2 ^ (k + p.1)) := by
  let ratio : ℝ := 9 / 10
  have hratio0 : 0 ≤ ratio := by norm_num [ratio]
  have hratio1 : ‖ratio‖ < 1 := by norm_num [ratio, Real.norm_eq_abs]
  have hcoeff : Summable (fun n : ℕ =>
      ((n + (k - 1)).choose (k - 1) : ℝ) * ratio ^ n) :=
    summable_choose_mul_geometric_of_norm_lt_one (k - 1) hratio1
  have hmajor : Summable (fun p : ℕ × XiZeroCopy =>
      ((p.1 + (k - 1)).choose (k - 1) : ℝ) * ratio ^ p.1 *
        ‖xiRawReciprocalCoordinate p.2‖ ^ 2) := by
    rw [summable_prod_of_nonneg]
    · constructor
      · intro n
        exact summable_norm_xiRawReciprocalCoordinate_sq.mul_left
          (((n + (k - 1)).choose (k - 1) : ℝ) * ratio ^ n)
      · convert hcoeff.mul_right xiRawReciprocalHermitianMass using 1
        funext n
        rw [xiRawReciprocalHermitianMass, ← tsum_mul_left]
    · rintro ⟨n, q⟩
      positivity
  apply Summable.of_norm_bounded hmajor
  rintro ⟨n, q⟩
  change ‖(((n + (k - 1)).choose (k - 1) : ℂ) *
      xiRawReciprocalCoordinate q ^ (k + n))‖ ≤
        ((n + (k - 1)).choose (k - 1) : ℝ) * ratio ^ n *
          ‖xiRawReciprocalCoordinate q‖ ^ 2
  rw [norm_mul, Complex.norm_natCast, norm_pow]
  have hq0 : 0 ≤ ‖xiRawReciprocalCoordinate q‖ := norm_nonneg _
  have hq1 : ‖xiRawReciprocalCoordinate q‖ ≤ 1 :=
    (xiRawReciprocalCoordinate_norm_lt_one q).le
  have hn : ‖xiRawReciprocalCoordinate q‖ ^ n ≤ ratio ^ n := by
    apply pow_le_pow_left₀ hq0
    simpa [ratio] using (xiRawReciprocalCoordinate_norm_lt_nine_tenths q).le
  have hkextra : ‖xiRawReciprocalCoordinate q‖ ^ (k - 2) ≤ 1 := by
    exact pow_le_one₀ hq0 hq1
  have hsplit : k + n = (k - 2) + n + 2 := by omega
  rw [hsplit, pow_add, pow_add]
  have hcoeff0 : 0 ≤ ((n + (k - 1)).choose (k - 1) : ℝ) := by positivity
  have hsq0 : 0 ≤ ‖xiRawReciprocalCoordinate q‖ ^ 2 := sq_nonneg _
  have hprod :
      ‖xiRawReciprocalCoordinate q‖ ^ (k - 2) *
          ‖xiRawReciprocalCoordinate q‖ ^ n ≤ ratio ^ n := by
    calc
      _ ≤ 1 * ‖xiRawReciprocalCoordinate q‖ ^ n := by
        gcongr
      _ ≤ 1 * ratio ^ n := by gcongr
      _ = ratio ^ n := one_mul _
  calc
    ((n + (k - 1)).choose (k - 1) : ℝ) *
          (‖xiRawReciprocalCoordinate q‖ ^ (k - 2) *
            ‖xiRawReciprocalCoordinate q‖ ^ n *
              ‖xiRawReciprocalCoordinate q‖ ^ 2) =
        ((n + (k - 1)).choose (k - 1) : ℝ) *
          ((‖xiRawReciprocalCoordinate q‖ ^ (k - 2) *
            ‖xiRawReciprocalCoordinate q‖ ^ n) *
              ‖xiRawReciprocalCoordinate q‖ ^ 2) := by ring
    _ ≤ ((n + (k - 1)).choose (k - 1) : ℝ) *
          (ratio ^ n * ‖xiRawReciprocalCoordinate q‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hprod hsq0) hcoeff0
    _ = ((n + (k - 1)).choose (k - 1) : ℝ) * ratio ^ n *
          ‖xiRawReciprocalCoordinate q‖ ^ 2 := by ring

/-- The binomially weighted sequence of all-order reciprocal traces is summable. -/
theorem summable_xiRawReciprocalPowerTrace_reflectionSeries (k : ℕ) (hk : 2 ≤ k) :
    Summable (fun n : ℕ =>
      ((n + (k - 1)).choose (k - 1) : ℂ) *
        xiRawReciprocalPowerTrace (k + n)) := by
  have hf := (summable_xiRawReciprocalTraceReflection_double k hk).prod
  convert hf using 1
  funext n
  rw [xiRawReciprocalPowerTrace, ← tsum_mul_left]

/-- **All-order Xi reciprocal-trace reflection law.**  Functional-equation reflection imposes
an unconditional negative-binomial relation among the actual reciprocal traces. -/
theorem xiRawReciprocalPowerTrace_reflection (k : ℕ) (hk : 2 ≤ k) :
    xiRawReciprocalPowerTrace k =
      (-1 : ℂ) ^ k * ∑' n : ℕ,
        ((n + (k - 1)).choose (k - 1) : ℂ) *
          xiRawReciprocalPowerTrace (k + n) := by
  let f : ℕ → XiZeroCopy → ℂ := fun n q =>
    ((n + (k - 1)).choose (k - 1) : ℂ) *
      xiRawReciprocalCoordinate q ^ (k + n)
  have hf : Summable (Function.uncurry f) :=
    summable_xiRawReciprocalTraceReflection_double k hk
  have hpoint (q : XiZeroCopy) :
      ∑' n : ℕ, f n q =
        (-1 : ℂ) ^ k *
          xiRawReciprocalCoordinate (xiZeroCopyReflectEquiv q) ^ k :=
    (hasSum_xiRawReciprocalCoordinate_reflect_binomial q k hk).tsum_eq
  have hreindex :
      ∑' q : XiZeroCopy,
          xiRawReciprocalCoordinate (xiZeroCopyReflectEquiv q) ^ k =
        xiRawReciprocalPowerTrace k := by
    rw [xiRawReciprocalPowerTrace]
    exact xiZeroCopyReflectEquiv.tsum_eq
      (fun q : XiZeroCopy => xiRawReciprocalCoordinate q ^ k)
  calc
    xiRawReciprocalPowerTrace k =
        ∑' q : XiZeroCopy,
          xiRawReciprocalCoordinate (xiZeroCopyReflectEquiv q) ^ k := hreindex.symm
    _ = (-1 : ℂ) ^ k *
        ∑' q : XiZeroCopy, ((-1 : ℂ) ^ k *
          xiRawReciprocalCoordinate (xiZeroCopyReflectEquiv q) ^ k) := by
      rw [← tsum_mul_left]
      have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
        rw [← mul_pow]
        norm_num
      apply tsum_congr
      intro q
      rw [← mul_assoc, hsign, one_mul]
    _ = (-1 : ℂ) ^ k * ∑' q : XiZeroCopy, ∑' n : ℕ, f n q := by
      congr 1
      apply tsum_congr
      exact fun q => (hpoint q).symm
    _ = (-1 : ℂ) ^ k * ∑' n : ℕ, ∑' q : XiZeroCopy, f n q := by
      rw [hf.tsum_comm]
    _ = (-1 : ℂ) ^ k * ∑' n : ℕ,
        ((n + (k - 1)).choose (k - 1) : ℂ) *
          xiRawReciprocalPowerTrace (k + n) := by
      congr 1
      apply tsum_congr
      intro n
      rw [xiRawReciprocalPowerTrace, ← tsum_mul_left]

/-- **Leading-term-free reciprocal-trace constraint.**  Removing the `n = 0` term from the
all-order reflection law gives a zero tail in every even degree and exactly `-2 T k` in every
odd degree. -/
theorem xiRawReciprocalPowerTrace_reflection_tail (k : ℕ) (hk : 2 ≤ k) :
    ∑' n : ℕ, ((n + k).choose (k - 1) : ℂ) *
        xiRawReciprocalPowerTrace (k + n + 1) =
      (((-1 : ℂ) ^ k) - 1) * xiRawReciprocalPowerTrace k := by
  let g : ℕ → ℂ := fun n =>
    ((n + (k - 1)).choose (k - 1) : ℂ) *
      xiRawReciprocalPowerTrace (k + n)
  have hg : Summable g := by
    simpa [g] using summable_xiRawReciprocalPowerTrace_reflectionSeries k hk
  have hreflection := xiRawReciprocalPowerTrace_reflection k hk
  have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  have hsum : ∑' n : ℕ, g n =
      (-1 : ℂ) ^ k * xiRawReciprocalPowerTrace k := by
    calc
      ∑' n : ℕ, g n = 1 * ∑' n : ℕ, g n := by rw [one_mul]
      _ = ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) * ∑' n : ℕ, g n := by
        rw [hsign]
      _ = (-1 : ℂ) ^ k *
          ((-1 : ℂ) ^ k * ∑' n : ℕ, g n) := by ring
      _ = (-1 : ℂ) ^ k * xiRawReciprocalPowerTrace k := by
        rw [← hreflection]
  have hsplit := hg.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hsplit
  have hg0 : g 0 = xiRawReciprocalPowerTrace k := by simp [g]
  rw [hsum, hg0] at hsplit
  have htail : ∑' n : ℕ, g (n + 1) =
      (((-1 : ℂ) ^ k) - 1) * xiRawReciprocalPowerTrace k := by
    calc
      ∑' n : ℕ, g (n + 1) =
          (xiRawReciprocalPowerTrace k + ∑' n : ℕ, g (n + 1)) -
            xiRawReciprocalPowerTrace k := by ring
      _ = (-1 : ℂ) ^ k * xiRawReciprocalPowerTrace k -
            xiRawReciprocalPowerTrace k := by rw [hsplit]
      _ = (((-1 : ℂ) ^ k) - 1) * xiRawReciprocalPowerTrace k := by ring
  rw [← htail]
  apply tsum_congr
  intro n
  simp only [g]
  have hidx : n + 1 + (k - 1) = n + k := by omega
  have hexp : k + (n + 1) = k + n + 1 := by omega
  rw [hidx, hexp]

/-- The first nontrivial even reflection constraint: after the `T 2` term cancels, the whole
binomially weighted higher-trace tail vanishes. -/
theorem xiRawReciprocalPowerTrace_reflection_tail_two :
    ∑' n : ℕ, ((n + 2 : ℕ) : ℂ) *
        xiRawReciprocalPowerTrace (n + 3) = 0 := by
  simpa [add_assoc, add_comm, add_left_comm] using
    xiRawReciprocalPowerTrace_reflection_tail 2 (by omega)

end

end RHTower

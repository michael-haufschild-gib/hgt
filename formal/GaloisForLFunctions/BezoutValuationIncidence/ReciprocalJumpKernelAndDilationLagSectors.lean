import GaloisForLFunctions.BezoutValuationIncidence.TruncatedPronicGramMatrixAndFiniteHorizonVonMangoldtApproximation
/-!
# Reciprocal jump kernels and integer dilation lag sectors

Finite reciprocal energy is reconstructed from its literal jump streams.
For integer dilations, multiplier pairs retain the Diophantine separation
`p*a-q*b`. Both the scale gcd and the multiplier gcd divide that separation.
All sums share one physical cutoff; no infinite jump-pair rearrangement is used.
-/

open scoped BigOperators
open Finset RHTower
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence

/-- Reciprocal overlap of two integer jumps up to a common physical cutoff. -/
def reciprocalJumpKernel (H i j : ℕ) : ℝ :=
  ∑ n ∈ Icc (max i j) H, 1 / ((n : ℝ) * ((n : ℝ) + 1))

private theorem sum_reciprocal_Icc {a H : ℕ} (ha : 0 < a) (haH : a ≤ H + 1) :
    (∑ n ∈ Icc a H, 1 / ((n : ℝ) * ((n : ℝ) + 1))) =
      1 / (a : ℝ) - 1 / ((H : ℝ) + 1) := by
  induction H with
  | zero =>
    have : a = 1 := by omega
    subst a
    simp
  | succ H ih =>
    by_cases h : a ≤ H + 1
    · rw [sum_Icc_succ_top h, ih h]
      push_cast
      have h1 : (H : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (H : ℝ) + 1 + 1 ≠ 0 := by positivity
      field_simp
      ring
    · have he : a = H + 2 := by omega
      subst a
      rw [Icc_eq_empty_of_lt (by omega)]
      simp
      ring

/-- The cutoff correction is part of the exact Green kernel. -/
theorem reciprocalJumpKernel_eq {H i j : ℕ} (hi : i ∈ Icc 1 H)
    (hj : j ∈ Icc 1 H) :
    reciprocalJumpKernel H i j =
      1 / ((max i j : ℕ) : ℝ) - 1 / ((H : ℝ) + 1) := by
  apply sum_reciprocal_Icc
  · have := (mem_Icc.mp hi).1
    omega
  · have := (mem_Icc.mp hi).2
    have := (mem_Icc.mp hj).2
    omega

/-- Finite reciprocal energy equals a double pairing of its literal jumps. -/
theorem finite_prefix_product_eq_jump_kernel (f g : ℕ → ℝ) (H : ℕ) :
    (∑ n ∈ Icc 1 H,
      (∑ i ∈ Icc 1 n, f i) * (∑ j ∈ Icc 1 n, g j) /
        ((n : ℝ) * ((n : ℝ) + 1))) =
      ∑ i ∈ Icc 1 H, ∑ j ∈ Icc 1 H,
        f i * g j * reciprocalJumpKernel H i j := by
  classical
  have hprefix (F : ℕ → ℝ) (n : ℕ) (hn : n ≤ H) :
      (∑ i ∈ Icc 1 H, if i ≤ n then F i else 0) = ∑ i ∈ Icc 1 n, F i := by
    rw [← sum_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_Icc]
    omega
  calc
    _ = ∑ n ∈ Icc 1 H, ∑ i ∈ Icc 1 H, ∑ j ∈ Icc 1 H,
        f i * g j * (if i ≤ n ∧ j ≤ n then
          1 / ((n : ℝ) * ((n : ℝ) + 1)) else 0) := by
      apply sum_congr rfl
      intro n hn
      rw [← hprefix f n (mem_Icc.mp hn).2, ← hprefix g n (mem_Icc.mp hn).2]
      rw [sum_mul_sum, sum_div]
      simp only [sum_div]
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      split_ifs <;> simp_all [div_eq_mul_inv, mul_inv_rev]
    _ = ∑ i ∈ Icc 1 H, ∑ j ∈ Icc 1 H, ∑ n ∈ Icc 1 H,
        f i * g j * (if i ≤ n ∧ j ≤ n then
          1 / ((n : ℝ) * ((n : ℝ) + 1)) else 0) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i hi
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      rw [← mul_sum]
      congr 1
      rw [← sum_filter]
      unfold reciprocalJumpKernel
      congr 1
      ext n
      have hi1 := (mem_Icc.mp hi).1
      simp only [mem_filter, mem_Icc]
      omega

/-- The jump of the dilated primitive at integer position n. -/
def ramanujanDilationJump (r p n : ℕ) : ℝ :=
  if p ∣ n then (d4BMRamanujanNaturalCoefficient (n / p) r).re else 0

theorem sum_ramanujanDilationJump {p : ℕ} (hp : 0 < p) (r H : ℕ) :
    (∑ n ∈ Icc 1 H, ramanujanDilationJump r p n) =
      (pmRamanujanPrimitive r (H / p)).re := by
  unfold ramanujanDilationJump
  rw [← sum_filter, sum_Icc_filter_dvd_reindex p H hp]
  simp only [Nat.mul_div_cancel_left _ hp, pmRamanujanPrimitive, Complex.re_sum]

/-- Pairing the two integer jump streams reconstructs the dilated primitive energy. -/
theorem ramanujan_dilation_finite_jump_kernel {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (r H : ℕ) :
    (∑ n ∈ Icc 1 H,
      (pmRamanujanPrimitive r (n / p)).re * (pmRamanujanPrimitive r (n / q)).re /
        ((n : ℝ) * ((n : ℝ) + 1))) =
      ∑ i ∈ Icc 1 H, ∑ j ∈ Icc 1 H,
        ramanujanDilationJump r p i * ramanujanDilationJump r q j *
          reciprocalJumpKernel H i j := by
  simpa only [sum_ramanujanDilationJump hp, sum_ramanujanDilationJump hq] using
    finite_prefix_product_eq_jump_kernel (ramanujanDilationJump r p)
      (ramanujanDilationJump r q) H

/-- Jump-pair coordinates before grouping by their signed integer separation. -/
def dilationJumpPairs (H p q : ℕ) : Finset (ℕ × ℕ) :=
  Icc 1 (H / p) ×ˢ Icc 1 (H / q)

/-- The additive separation of two jumps, in the original integer coordinate. -/
def dilationJumpGap (p q : ℕ) (ab : ℕ × ℕ) : ℤ :=
  (p : ℤ) * ab.1 - (q : ℤ) * ab.2

/-- The finite reciprocal pairing in multiplier coordinates. -/
def ramanujanJumpPairTerm (r p q H : ℕ) (ab : ℕ × ℕ) : ℝ :=
  (d4BMRamanujanNaturalCoefficient ab.1 r).re *
    (d4BMRamanujanNaturalCoefficient ab.2 r).re *
    reciprocalJumpKernel H (p * ab.1) (q * ab.2)

/-- The signed contribution from one additive separation. -/
def ramanujanDilationLagSector (r p q H : ℕ) (h : ℤ) : ℝ :=
  ∑ ab ∈ (dilationJumpPairs H p q).filter (fun ab => dilationJumpGap p q ab = h),
    ramanujanJumpPairTerm r p q H ab

/-- Integer jump coordinates retain the original multiplier coefficients. -/
theorem ramanujan_dilation_finite_pair_kernel {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (r H : ℕ) :
    (∑ n ∈ Icc 1 H,
      (pmRamanujanPrimitive r (n / p)).re * (pmRamanujanPrimitive r (n / q)).re /
        ((n : ℝ) * ((n : ℝ) + 1))) =
      ∑ ab ∈ dilationJumpPairs H p q, ramanujanJumpPairTerm r p q H ab := by
  rw [ramanujan_dilation_finite_jump_kernel hp hq]
  have hfilter :
      (∑ i ∈ Icc 1 H, ∑ j ∈ Icc 1 H,
        ramanujanDilationJump r p i * ramanujanDilationJump r q j *
          reciprocalJumpKernel H i j) =
        ∑ i ∈ (Icc 1 H).filter (fun i => p ∣ i),
          ∑ j ∈ (Icc 1 H).filter (fun j => q ∣ j),
            (d4BMRamanujanNaturalCoefficient (i / p) r).re *
              (d4BMRamanujanNaturalCoefficient (j / q) r).re *
                reciprocalJumpKernel H i j := by
    simp only [sum_filter]
    apply sum_congr rfl
    intro i hi
    by_cases hpi : p ∣ i
    · simp only [ramanujanDilationJump, if_pos hpi]
      apply sum_congr rfl
      intro j hj
      by_cases hqj : q ∣ j <;> simp [hqj]
    · simp [ramanujanDilationJump, hpi]
  rw [hfilter, sum_Icc_filter_dvd_reindex p H hp]
  unfold dilationJumpPairs
  rw [sum_product]
  apply sum_congr rfl
  intro a ha
  rw [sum_Icc_filter_dvd_reindex q H hq]
  simp only [ramanujanJumpPairTerm, Nat.mul_div_cancel_left _ hp,
    Nat.mul_div_cancel_left _ hq]

/-- The dilation pairing resolves exactly into its integer Diophantine lag sectors. -/
theorem ramanujan_dilation_finite_lag_sectors {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (r H : ℕ) :
    (∑ n ∈ Icc 1 H,
      (pmRamanujanPrimitive r (n / p)).re * (pmRamanujanPrimitive r (n / q)).re /
        ((n : ℝ) * ((n : ℝ) + 1))) =
      ∑ h ∈ (dilationJumpPairs H p q).image (dilationJumpGap p q),
        ramanujanDilationLagSector r p q H h := by
  rw [ramanujan_dilation_finite_pair_kernel hp hq]
  symm
  exact sum_fiberwise_of_maps_to (fun ab hab => mem_image_of_mem _ hab) _

/-- Both the scale gcd and the multiplier gcd divide every jump separation. -/
theorem gcd_dvd_dilationJumpGap (p q : ℕ) (ab : ℕ × ℕ) :
    (Nat.gcd p q : ℤ) ∣ dilationJumpGap p q ab ∧
      (Nat.gcd ab.1 ab.2 : ℤ) ∣ dilationJumpGap p q ab := by
  constructor
  · apply dvd_sub
    · exact_mod_cast dvd_mul_of_dvd_left (Nat.gcd_dvd_left p q) ab.1
    · exact_mod_cast dvd_mul_of_dvd_left (Nat.gcd_dvd_right p q) ab.2
  · apply dvd_sub
    · exact_mod_cast dvd_mul_of_dvd_right (Nat.gcd_dvd_left ab.1 ab.2) p
    · exact_mod_cast dvd_mul_of_dvd_right (Nat.gcd_dvd_right ab.1 ab.2) q

/-- Successor-separated jumps force coprimality in both coordinate systems. -/
theorem dilationJumpGap_one_coprime {p q : ℕ} {ab : ℕ × ℕ}
    (h : dilationJumpGap p q ab = 1) : Nat.Coprime p q ∧ Nat.Coprime ab.1 ab.2 := by
  have hd := gcd_dvd_dilationJumpGap p q ab
  rw [h] at hd
  have hpq : Nat.gcd p q ∣ 1 := by exact_mod_cast hd.1
  have hab : Nat.gcd ab.1 ab.2 ∣ 1 := by exact_mod_cast hd.2
  exact ⟨Nat.dvd_one.mp hpq, Nat.dvd_one.mp hab⟩

/-- A forbidden gcd lag is absent, at every cutoff and at arbitrary scale. -/
theorem ramanujanDilationLagSector_eq_zero_of_not_dvd (r p q H : ℕ) (h : ℤ)
    (hh : ¬ (Nat.gcd p q : ℤ) ∣ h) :
    ramanujanDilationLagSector r p q H h = 0 := by
  apply sum_eq_zero
  intro ab hab
  have he := (mem_filter.mp hab).2
  exact (hh (he ▸ (gcd_dvd_dilationJumpGap p q ab).1)).elim

/-- The successor sector keeps only coprime multiplier pairs, even at unbounded scale. -/
theorem ramanujanDilationLagSector_one_coprime_filter (r p q H : ℕ) :
    ramanujanDilationLagSector r p q H 1 =
      ∑ ab ∈ (dilationJumpPairs H p q).filter
        (fun ab => dilationJumpGap p q ab = 1 ∧ Nat.Coprime ab.1 ab.2),
        ramanujanJumpPairTerm r p q H ab := by
  unfold ramanujanDilationLagSector
  congr 1
  ext ab
  simp only [mem_filter]
  exact ⟨fun h => ⟨h.1, h.2, (dilationJumpGap_one_coprime h.2).2⟩,
    fun h => ⟨h.1, h.2.1⟩⟩

end GaloisForLFunctions.BezoutValuationIncidence

import GaloisForLFunctions.BezoutValuationIncidence.TheAbsoluteVaughanRemainderBudgetHasTheTrivialExponent
import GaloisForLFunctions.RHTower.Sieve.HeathBrownDyadicCoefficientBound
import GaloisForLFunctions.RHTower.Sieve.VaughanTypeIPieces

/-!
# Uniform floor means and moving Vaughan Grams

One summable divisor majorant controls the normalized floor errors of every Vaughan
cutoff. Cesàro averaging gives a uniform leading Gram matrix. When both cutoffs diverge,
its mean vector tends to the reciprocal zeta density times `(1,1,-1,0,-1)`.
This leading-order law leaves the smaller signed interior energy unresolved.
-/

open Finset Filter ArithmeticFunction RHTower
open GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- The normalized floor transform of a coefficient sequence. -/
def pmFloorAverage (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ d ∈ Icc 1 n, a d * (n / d : ℕ)) / n

private theorem pmFloorAverage_eq_tsum (a : ℕ → ℝ) (n : ℕ) :
    pmFloorAverage a n = ∑' d : ℕ, a d * ((n / d : ℕ) : ℝ) / n := by
  rw [tsum_eq_sum (s := Icc 1 n) (fun d hd => ?_)]
  · simp only [pmFloorAverage, sum_div]
  · by_cases hd0 : d = 0
    · simp [hd0]
    · have hnd : n < d := by simp only [mem_Icc] at hd; omega
      simp [Nat.div_eq_of_lt hnd]

private theorem nat_floor_ratio_le (n d : ℕ) :
    ((n / d : ℕ) : ℝ) / n ≤ 1 / (d : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfloor : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d := Nat.cast_div_le
  calc
    _ ≤ ((n : ℝ) / d) / n := div_le_div_of_nonneg_right hfloor hnR.le
    _ = _ := by rw [div_right_comm, div_self hnR.ne']

private theorem summable_floor_average {a b : ℕ → ℝ}
    (hb : Summable (fun d => b d / (d : ℝ))) (hab : ∀ d, |a d| ≤ b d) (n : ℕ) :
    Summable (fun d : ℕ => a d * ((n / d : ℕ) : ℝ) / n) := by
  apply hb.of_norm_bounded
  intro d
  rw [Real.norm_eq_abs, abs_div, abs_mul,
    show |((n / d : ℕ) : ℝ)| = (n / d : ℕ) from abs_of_nonneg (Nat.cast_nonneg _),
    show |(n : ℝ)| = n from abs_of_nonneg (Nat.cast_nonneg _), mul_div_assoc]
  calc
    _ ≤ b d * (((n / d : ℕ) : ℝ) / n) :=
      mul_le_mul_of_nonneg_right (hab d) (by positivity)
    _ ≤ b d * (1 / (d : ℝ)) :=
      mul_le_mul_of_nonneg_left (nat_floor_ratio_le n d) ((abs_nonneg _).trans (hab d))
    _ = _ := by ring

private theorem summable_density_of_abs_le {a b : ℕ → ℝ}
    (hb : Summable (fun d => b d / (d : ℝ))) (hab : ∀ d, |a d| ≤ b d) :
    Summable (fun d => a d / (d : ℝ)) := by
  apply hb.of_norm_bounded
  intro d
  rw [Real.norm_eq_abs, abs_div,
    show |(d : ℝ)| = d from abs_of_nonneg (Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (hab d) (Nat.cast_nonneg d)

/-- A single nonnegative majorant bounds every dominated floor-mean error. -/
def pmFloorMeanDefect (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑' d : ℕ, b d / d) - pmFloorAverage b n

theorem abs_pmFloorAverage_sub_density_le {a b : ℕ → ℝ}
    (hb : Summable (fun d => b d / (d : ℝ))) (hab : ∀ d, |a d| ≤ b d) (n : ℕ) :
    |pmFloorAverage a n - ∑' d : ℕ, a d / d| ≤ pmFloorMeanDefect b n := by
  have hb0 (d : ℕ) : 0 ≤ b d := (abs_nonneg _).trans (hab d)
  have hbb (d : ℕ) : |b d| ≤ b d := (abs_of_nonneg (hb0 d)).le
  have hA := (summable_density_of_abs_le hb hab).hasSum.sub
    (summable_floor_average hb hab n).hasSum
  have hB := hb.hasSum.sub (summable_floor_average hb hbb n).hasSum
  rw [← pmFloorAverage_eq_tsum a n] at hA
  rw [← pmFloorAverage_eq_tsum b n] at hB
  have hbound (d : ℕ) : ‖a d / (d : ℝ) - a d * ((n / d : ℕ) : ℝ) / n‖ ≤
      b d / (d : ℝ) - b d * ((n / d : ℕ) : ℝ) / n := by
    have hq : 0 ≤ 1 / (d : ℝ) - ((n / d : ℕ) : ℝ) / n :=
      sub_nonneg.mpr (nat_floor_ratio_le n d)
    rw [show a d / (d : ℝ) - a d * ((n / d : ℕ) : ℝ) / n =
      a d * (1 / (d : ℝ) - ((n / d : ℕ) : ℝ) / n) by ring,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg hq]
    calc
      _ ≤ b d * (1 / (d : ℝ) - ((n / d : ℕ) : ℝ) / n) :=
        mul_le_mul_of_nonneg_right (hab d) hq
      _ = _ := by ring
  have h := hA.norm_le_of_bounded hB hbound
  simpa only [Real.norm_eq_abs, abs_sub_comm, pmFloorMeanDefect] using h

theorem pmFloorMeanDefect_nonneg {b : ℕ → ℝ}
    (hb0 : ∀ d, 0 ≤ b d) (hb : Summable (fun d => b d / (d : ℝ))) (n : ℕ) :
    0 ≤ pmFloorMeanDefect b n :=
  (abs_nonneg _).trans (abs_pmFloorAverage_sub_density_le hb
    (fun d => (abs_of_nonneg (hb0 d)).le) n)

/-- The floor transform has the absolutely convergent reciprocal density. -/
theorem tendsto_pmFloorAverage {b : ℕ → ℝ}
    (hb : Summable (fun d => b d / (d : ℝ))) :
    Tendsto (pmFloorAverage b) atTop (𝓝 (∑' d : ℕ, b d / d)) := by
  change Tendsto (fun n : ℕ => (∑ d ∈ Icc 1 n, b d * (n / d : ℕ)) / n)
    atTop (𝓝 (∑' d : ℕ, b d / d))
  have heq (n : ℕ) :
      (∑ k ∈ Icc 1 n, ∑ d ∈ k.divisors, b d) =
        ∑ d ∈ Icc 1 n, b d * (n / d : ℕ) := by
    have h := congrArg Complex.re (pm_divisor_floor_sum_nat (fun d => (b d : ℂ)) n)
    simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero] using h.symm
  have h := (pm_tendsto_divisor_average hb).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def, Nat.floor_natCast, heq] using h

/-- Absolute reciprocal summability pays the common floor-mean defect. -/
theorem tendsto_pmFloorMeanDefect_zero {b : ℕ → ℝ}
    (hb : Summable (fun d => b d / (d : ℝ))) :
    Tendsto (pmFloorMeanDefect b) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => (∑' d : ℕ, b d / d) - pmFloorAverage b n) atTop (𝓝 0)
  simpa only [sub_self] using
    (tendsto_const_nhds (x := ∑' d : ℕ, b d / d)).sub (tendsto_pmFloorAverage hb)

private theorem weighted_convolution_rectangle
    (f g : ArithmeticFunction ℝ) (w : ℕ → ℝ) (X : ℕ) :
    (∑ n ∈ Icc 1 X, (f * g) n * w n) =
      ∑ a ∈ Icc 1 X, f a * ∑ b ∈ Icc 1 (X / a), g b * w (a * b) := by
  have he : (∑ n ∈ Icc 1 X, (f * g) n * w n) =
      ∑ n ∈ Icc 1 X, ∑ x ∈ n.divisorsAntidiagonal,
        f x.1 * g x.2 * w (x.1 * x.2) := by
    apply sum_congr rfl
    intro n _
    rw [ArithmeticFunction.mul_apply, sum_mul]
    apply sum_congr rfl
    intro x hx
    rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
  rw [he, Sieve.sum_Icc_divisorsAntidiagonal_swap
    (fun a b => f a * g b * w (a * b)) X]
  simp only [mul_sum, mul_assoc]

private theorem weighted_zeta_convolution_rectangle
    (f g : ArithmeticFunction ℝ) (w : ℕ → ℝ) (X : ℕ) :
    (∑ n ∈ Icc 1 X, (f * (g * (zeta : ArithmeticFunction ℝ))) n * w n) =
      ∑ a ∈ Icc 1 X, f a * ∑ b ∈ Icc 1 X,
        g b * ∑ k ∈ Icc 1 (X / (a * b)), w (a * b * k) := by
  rw [weighted_convolution_rectangle]
  apply sum_congr rfl
  intro a ha
  congr 1
  rw [weighted_convolution_rectangle]
  have he : (∑ b ∈ Icc 1 (X / a), g b *
      ∑ k ∈ Icc 1 (X / a / b), (zeta : ArithmeticFunction ℝ) k * w (a * (b * k))) =
      ∑ b ∈ Icc 1 (X / a), g b * ∑ k ∈ Icc 1 (X / (a * b)), w (a * b * k) := by
    apply sum_congr rfl
    intro b _
    congr 1
    rw [Nat.div_div_eq_div_mul]
    apply sum_congr rfl
    intro k hk
    rw [Sieve.zeta_real_apply_of_ne_zero (by have := (mem_Icc.mp hk).1; omega),
      one_mul, Nat.mul_assoc]
  rw [he]
  apply sum_subset
  · exact Icc_subset_Icc_right (Nat.div_le_self X a)
  · intro b hb hnot
    have ha0 : 0 < a := (mem_Icc.mp ha).1
    have hbcut : X / a < b := by
      have := (mem_Icc.mp hb).1
      simp only [mem_Icc] at hnot
      omega
    have hprod : X < a * b := by
      by_contra h
      have hle : b ≤ X / a := (Nat.le_div_iff_mul_le ha0).mpr
        (by simpa only [Nat.mul_comm] using le_of_not_gt h)
      omega
    simp [Nat.div_eq_of_lt hprod]

private theorem truncatedMoebius_weighted_sum (U X : ℕ) (w : ℕ → ℝ) :
    (∑ d ∈ Icc 1 X, Sieve.truncatedMoebius U d * w d) =
      ∑ d ∈ Icc 1 (min U X), (moebius d : ℝ) * w d := by
  calc
    _ = ∑ d ∈ Icc 1 (min U X), Sieve.truncatedMoebius U d * w d := by
      symm
      apply sum_subset (Icc_subset_Icc_right (min_le_right U X))
      intro d hd hnot
      have hdU : ¬ d ≤ U := by
        intro h
        exact hnot (mem_Icc.mpr ⟨(mem_Icc.mp hd).1, le_min h (mem_Icc.mp hd).2⟩)
      simp [hdU]
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      simp [((mem_Icc.mp hd).2.trans (min_le_left U X))]

/-- The undamped coefficient of the small-small floor piece. -/
def pmPronicVaughanSmallSmallCoeff (U V n : ℕ) : ℝ :=
  (Sieve.truncatedMoebius U *
    (Sieve.truncatedMoebius V * (zeta : ArithmeticFunction ℝ))) n

/-- The rectangular small-small formula is exactly one damped floor transform. -/
theorem pmPronicVaughanPiece_smallSmall_eq_floorAverage (ε : ℝ) (U V n : ℕ) :
    pmPronicVaughanPiece ε U V n 2 / n =
      -pmFloorAverage (fun d => pmPronicVaughanSmallSmallCoeff U V d * (d : ℝ) ^ (-ε)) n := by
  have h := weighted_zeta_convolution_rectangle
    (Sieve.truncatedMoebius U) (Sieve.truncatedMoebius V) (pmPronicFloorWeight ε n) n
  rw [truncatedMoebius_weighted_sum] at h
  simp_rw [truncatedMoebius_weighted_sum] at h
  change -(∑ a ∈ Icc 1 (min U n), (moebius a : ℝ) *
    ∑ b ∈ Icc 1 (min V n), (moebius b : ℝ) *
      ∑ k ∈ Icc 1 (n / (a * b)), pmPronicFloorWeight ε n (a * b * k)) / n = _
  rw [← h]
  simp only [pmFloorAverage, pmPronicVaughanSmallSmallCoeff, pmPronicFloorWeight,
    mul_assoc, neg_div]

/-- The first small leg is the floor transform of the truncated damped Möbius sequence. -/
theorem pmPronicVaughanPiece_small_eq_floorAverage (ε : ℝ) (U V n : ℕ) :
    pmPronicVaughanPiece ε U V n 0 / n =
      pmFloorAverage (fun d => Sieve.truncatedMoebius U d * (d : ℝ) ^ (-ε)) n := by
  have h := truncatedMoebius_weighted_sum U n (pmPronicFloorWeight ε n)
  change (∑ d ∈ Icc 1 (min U n), (moebius d : ℝ) * pmPronicFloorWeight ε n d) / n = _
  rw [← h]
  simp only [pmFloorAverage, pmPronicFloorWeight, mul_assoc]

/-- Three unit-bounded convolution factors give one cutoff-independent divisor majorant. -/
theorem abs_pmPronicVaughanSmallSmallCoeff_le (U V n : ℕ) :
    |pmPronicVaughanSmallSmallCoeff U V n| ≤ (n.divisors.card : ℝ) ^ 2 := by
  have hU : ∀ d, ‖Sieve.truncatedMoebius U d‖ ≤ (d.divisors.card : ℝ) ^ 0 := by
    intro d
    simpa only [pow_zero] using Sieve.norm_truncatedMoebius_le_one U d
  have hV : ∀ d, ‖Sieve.truncatedMoebius V d‖ ≤ (d.divisors.card : ℝ) ^ 0 := by
    intro d
    simpa only [pow_zero] using Sieve.norm_truncatedMoebius_le_one V d
  have hZ : ∀ d, ‖(zeta : ArithmeticFunction ℝ) d‖ ≤ (d.divisors.card : ℝ) ^ 0 := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · rw [Sieve.zeta_real_apply_of_ne_zero hd.ne']
      simp
  have hVZ : ∀ d,
      ‖(Sieve.truncatedMoebius V * (zeta : ArithmeticFunction ℝ)) d‖ ≤
        (d.divisors.card : ℝ) ^ 1 :=
    fun d => Sieve.norm_mul_apply_le_divisors_pow_add_succ hV hZ d
  simpa only [pmPronicVaughanSmallSmallCoeff, Real.norm_eq_abs] using
    Sieve.norm_mul_apply_le_divisors_pow_add_succ hU hVZ n

/-- One majorant controls the first three damped Vaughan coefficients at every cutoff. -/
def pmVaughanFloorMajorant (ε : ℝ) (d : ℕ) : ℝ :=
  (d.divisors.card : ℝ) ^ 2 * (d : ℝ) ^ (-ε)

theorem pmVaughanFloorMajorant_nonneg (ε : ℝ) (d : ℕ) :
    0 ≤ pmVaughanFloorMajorant ε d := by
  unfold pmVaughanFloorMajorant
  positivity

/-- The square-divisor majorant has finite reciprocal mass at every positive damping. -/
theorem summable_pmVaughanFloorMajorant_div {ε : ℝ} (hε : 0 < ε) :
    Summable (fun d : ℕ => pmVaughanFloorMajorant ε d / d) := by
  unfold pmVaughanFloorMajorant
  have h := summable_divisor_sq_rpow (σ := (1 + ε) / 2) (by linarith)
  apply h.congr
  intro d
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    rw [mul_div_assoc, ← Real.rpow_sub_one hdR.ne']
    congr 2
    ring

private theorem abs_small_floor_coefficient_le (ε : ℝ) (U d : ℕ) :
    |Sieve.truncatedMoebius U d * (d : ℝ) ^ (-ε)| ≤ pmVaughanFloorMajorant ε d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [pmVaughanFloorMajorant]
  have hc : (1 : ℝ) ≤ d.divisors.card := by
    exact_mod_cast (one_le_card.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd d, hd.ne'⟩⟩)
  have hc2 : (1 : ℝ) ≤ (d.divisors.card : ℝ) ^ 2 := by nlinarith only [hc]
  have hμ : |Sieve.truncatedMoebius U d| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using Sieve.norm_truncatedMoebius_le_one U d
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  exact mul_le_mul_of_nonneg_right (hμ.trans hc2) (Real.rpow_nonneg (Nat.cast_nonneg d) _)

private theorem abs_smallSmall_floor_coefficient_le (ε : ℝ) (U V d : ℕ) :
    |-(pmPronicVaughanSmallSmallCoeff U V d * (d : ℝ) ^ (-ε))| ≤
      pmVaughanFloorMajorant ε d := by
  rw [abs_neg, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  exact mul_le_mul_of_nonneg_right (abs_pmPronicVaughanSmallSmallCoeff_le U V d)
    (Real.rpow_nonneg (Nat.cast_nonneg d) _)

private theorem floor_mean_calibration {a b f : ℕ → ℝ} {c : ℝ}
    (hb : Summable (fun d => b d / (d : ℝ))) (hab : ∀ d, |a d| ≤ b d)
    (hf : ∀ n, f n / n = pmFloorAverage a n)
    (hc : Tendsto (fun n : ℕ => f n / n) atTop (𝓝 c)) :
    |c| ≤ (∑' d : ℕ, b d / d) ∧
      ∀ n, |f n / n - c| ≤ pmFloorMeanDefect b n := by
  have ha := summable_density_of_abs_le hb hab
  have hlim : Tendsto (pmFloorAverage a) atTop (𝓝 c) := by
    simpa only [hf] using hc
  have heq : (∑' d : ℕ, a d / d) = c :=
    tendsto_nhds_unique (tendsto_pmFloorAverage ha) hlim
  constructor
  · rw [← heq]
    have h := tsum_of_norm_bounded (f := fun d : ℕ => a d / (d : ℝ))
      hb.hasSum (fun d => ?_)
    · simpa only [Real.norm_eq_abs] using h
    · rw [Real.norm_eq_abs, abs_div,
        show |(d : ℝ)| = d from abs_of_nonneg (Nat.cast_nonneg _)]
      exact div_le_div_of_nonneg_right (hab d) (Nat.cast_nonneg d)
  · intro n
    rw [hf, ← heq]
    exact abs_pmFloorAverage_sub_density_le hb hab n

/-- The first three means and their errors share a bound independent of both cutoffs. -/
theorem pmPronicVaughan_small_floor_calibration {ε : ℝ} (hε : 0 < ε)
    (U V : ℕ) (i : Fin 5) (hi : i.val < 3) :
    |pmPronicVaughanMean ε U V i| ≤
        (∑' d : ℕ, pmVaughanFloorMajorant ε d / d) ∧
      ∀ n, |pmPronicVaughanPiece ε U V n i / n - pmPronicVaughanMean ε U V i| ≤
        pmFloorMeanDefect (pmVaughanFloorMajorant ε) n := by
  have hb := summable_pmVaughanFloorMajorant_div hε
  fin_cases i
  · exact floor_mean_calibration hb (abs_small_floor_coefficient_le ε U)
      (pmPronicVaughanPiece_small_eq_floorAverage ε U V)
      (tendsto_pmPronicVaughanPiece_div_nat hε U V 0)
  · apply floor_mean_calibration hb (abs_small_floor_coefficient_le ε V)
      (fun n => ?_) (tendsto_pmPronicVaughanPiece_div_nat hε U V 1)
    exact pmPronicVaughanPiece_small_eq_floorAverage ε V U n
  · apply floor_mean_calibration hb (abs_smallSmall_floor_coefficient_le ε U V)
      (fun n => ?_) (tendsto_pmPronicVaughanPiece_div_nat hε U V 2)
    rw [pmPronicVaughanPiece_smallSmall_eq_floorAverage]
    simp only [pmFloorAverage, neg_mul, sum_neg_distrib, neg_div]
  · change 3 < 3 at hi
    omega
  · change 4 < 3 at hi
    omega

/-- The reciprocal mass used to dominate the floor pieces. -/
def pmVaughanFloorMass (ε : ℝ) : ℝ :=
  ∑' d : ℕ, pmVaughanFloorMajorant ε d / d

theorem pmVaughanFloorMass_nonneg (ε : ℝ) : 0 ≤ pmVaughanFloorMass ε :=
  tsum_nonneg fun d => div_nonneg (pmVaughanFloorMajorant_nonneg ε d) (Nat.cast_nonneg d)

/-- A cutoff-independent bound for all five linear means. -/
def pmVaughanMeanBound (ε : ℝ) : ℝ :=
  (pmPowerDampedDivisorDensity ε).re + 3 * pmVaughanFloorMass ε

theorem abs_pmPronicVaughanMean_le {ε : ℝ} (hε : 0 < ε)
    (U V : ℕ) (i : Fin 5) :
    |pmPronicVaughanMean ε U V i| ≤ pmVaughanMeanBound ε := by
  have hρ := pmPowerDampedDivisorDensity_re_pos hε
  have hM := pmVaughanFloorMass_nonneg ε
  have h0 := (pmPronicVaughan_small_floor_calibration hε U V 0 (by decide)).1
  have h1 := (pmPronicVaughan_small_floor_calibration hε U V 1 (by decide)).1
  have h2 := (pmPronicVaughan_small_floor_calibration hε U V 2 (by decide)).1
  change |pmPronicVaughanMean ε U V 0| ≤ pmVaughanFloorMass ε at h0
  change |pmPronicVaughanMean ε U V 1| ≤ pmVaughanFloorMass ε at h1
  change |pmPronicVaughanMean ε U V 2| ≤ pmVaughanFloorMass ε at h2
  unfold pmVaughanMeanBound
  fin_cases i
  · change |pmPronicVaughanMean ε U V 0| ≤ _
    linarith only [h0, hM, hρ]
  · change |pmPronicVaughanMean ε U V 1| ≤ _
    linarith only [h1, hM, hρ]
  · change |pmPronicVaughanMean ε U V 2| ≤ _
    linarith only [h2, hM, hρ]
  · change |pmPronicVaughanMean ε U V 3| ≤ _
    have heq : pmPronicVaughanMean ε U V 3 =
        (pmPowerDampedDivisorDensity ε).re - pmPronicVaughanMean ε U V 0 -
          pmPronicVaughanMean ε U V 1 - pmPronicVaughanMean ε U V 2 := by
      change (pmPowerDampedDivisorDensity ε).re - pmPronicVaughanSmallDensity ε U -
        pmPronicVaughanSmallDensity ε V + pmPronicPowerDensity ε *
          pmPronicVaughanSmallDensity ε U * pmPronicVaughanSmallDensity ε V =
        (pmPowerDampedDivisorDensity ε).re - pmPronicVaughanSmallDensity ε U -
          pmPronicVaughanSmallDensity ε V - (-pmPronicPowerDensity ε *
            pmPronicVaughanSmallDensity ε U * pmPronicVaughanSmallDensity ε V)
      ring
    rw [heq]
    have ha := abs_sub ((pmPowerDampedDivisorDensity ε).re - pmPronicVaughanMean ε U V 0 -
      pmPronicVaughanMean ε U V 1) (pmPronicVaughanMean ε U V 2)
    have hb := abs_sub ((pmPowerDampedDivisorDensity ε).re - pmPronicVaughanMean ε U V 0)
      (pmPronicVaughanMean ε U V 1)
    have hc := abs_sub (pmPowerDampedDivisorDensity ε).re (pmPronicVaughanMean ε U V 0)
    rw [abs_of_pos hρ] at hc
    linarith only [ha, hb, hc, h0, h1, h2]
  · change |-(pmPowerDampedDivisorDensity ε).re| ≤ _
    rw [abs_neg, abs_of_pos hρ]
    linarith only [hM]

private theorem pole_floor_error_le {ε : ℝ} (hε : 0 ≤ ε) (U V : ℕ)
    {n : ℕ} (hn : 1 ≤ n) :
    |pmPronicVaughanPiece ε U V n 4 / n - pmPronicVaughanMean ε U V 4| ≤
      (1 / 2 : ℝ) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have heq : pmPronicVaughanPiece ε U V n 4 / n - pmPronicVaughanMean ε U V 4 =
      -(addDiff (pmActiveSawtoothComponent ε) n) / n := by
    change (-(pmPowerDampedDivisorDensity ε).re * n -
      addDiff (pmActiveSawtoothComponent ε) n) / n - (-(pmPowerDampedDivisorDensity ε).re) = _
    field_simp [hnR.ne']
    ring
  rw [heq, abs_div, abs_neg, abs_of_pos hnR]
  exact div_le_div_of_nonneg_right
    (abs_addDiff_pmActiveSawtoothComponent_le_half hε n) hnR.le

/-- One scalar sequence controls every component's normalized mean error. -/
def pmVaughanMeanError (ε : ℝ) (n : ℕ) : ℝ :=
  |pmBezoutInteriorPrefix ε n / n| +
    3 * pmFloorMeanDefect (pmVaughanFloorMajorant ε) n + (1 / 2 : ℝ) / n

theorem pmVaughanMeanError_nonneg {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    0 ≤ pmVaughanMeanError ε n := by
  have hD := pmFloorMeanDefect_nonneg (pmVaughanFloorMajorant_nonneg ε)
    (summable_pmVaughanFloorMajorant_div hε) n
  unfold pmVaughanMeanError
  positivity

theorem tendsto_pmVaughanMeanError_zero {ε : ℝ} (hε : 0 < ε) :
    Tendsto (pmVaughanMeanError ε) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => |pmBezoutInteriorPrefix ε n / n| +
    3 * pmFloorMeanDefect (pmVaughanFloorMajorant ε) n + (1 / 2 : ℝ) / n) atTop (𝓝 0)
  have hI := (tendsto_pmBezoutInteriorPrefix_div_nat hε).abs
  have hD := (tendsto_pmFloorMeanDefect_zero
    (summable_pmVaughanFloorMajorant_div hε)).const_mul 3
  have hA := tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ)
  simpa only [abs_zero, mul_zero, add_zero] using (hI.add hD).add hA

/-- The leading means approximate every piece uniformly over both Vaughan cutoffs. -/
theorem abs_pmPronicVaughanPiece_div_sub_mean_le {ε : ℝ} (hε : 0 < ε)
    (U V : ℕ) (i : Fin 5) {n : ℕ} (hn : 1 ≤ n) :
    |pmPronicVaughanPiece ε U V n i / n - pmPronicVaughanMean ε U V i| ≤
      pmVaughanMeanError ε n := by
  have hD := pmFloorMeanDefect_nonneg (pmVaughanFloorMajorant_nonneg ε)
    (summable_pmVaughanFloorMajorant_div hε) n
  have hI := abs_nonneg (pmBezoutInteriorPrefix ε n / n)
  have hA : (0 : ℝ) ≤ (1 / 2 : ℝ) / n := by positivity
  have h0 := (pmPronicVaughan_small_floor_calibration hε U V 0 (by decide)).2 n
  have h1 := (pmPronicVaughan_small_floor_calibration hε U V 1 (by decide)).2 n
  have h2 := (pmPronicVaughan_small_floor_calibration hε U V 2 (by decide)).2 n
  have h4 := pole_floor_error_le hε.le U V hn
  unfold pmVaughanMeanError
  fin_cases i
  · change |pmPronicVaughanPiece ε U V n 0 / n - pmPronicVaughanMean ε U V 0| ≤ _
    linarith only [h0, hD, hI, hA]
  · change |pmPronicVaughanPiece ε U V n 1 / n - pmPronicVaughanMean ε U V 1| ≤ _
    linarith only [h1, hD, hI, hA]
  · change |pmPronicVaughanPiece ε U V n 2 / n - pmPronicVaughanMean ε U V 2| ≤ _
    linarith only [h2, hD, hI, hA]
  · let e : Fin 5 → ℝ := fun j =>
      pmPronicVaughanPiece ε U V n j / n - pmPronicVaughanMean ε U V j
    have hs : (∑ j : Fin 5, e j) = pmBezoutInteriorPrefix ε n / n := by
      simp only [e, sum_sub_distrib, ← sum_div, sum_pmPronicVaughanPiece,
        sum_pmPronicVaughanMean, sub_zero]
    have heq : e 3 = pmBezoutInteriorPrefix ε n / n - e 0 - e 1 - e 2 - e 4 := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
      change e 0 + (e 1 + (e 2 + (e 3 + e 4))) = pmBezoutInteriorPrefix ε n / n at hs
      linarith only [hs]
    change |e 3| ≤ _
    rw [heq]
    have ha := abs_sub (pmBezoutInteriorPrefix ε n / n - e 0 - e 1 - e 2) (e 4)
    have hb := abs_sub (pmBezoutInteriorPrefix ε n / n - e 0 - e 1) (e 2)
    have hc := abs_sub (pmBezoutInteriorPrefix ε n / n - e 0) (e 1)
    have hd := abs_sub (pmBezoutInteriorPrefix ε n / n) (e 0)
    change |e 0| ≤ _ at h0
    change |e 1| ≤ _ at h1
    change |e 2| ≤ _ at h2
    change |e 4| ≤ _ at h4
    linarith only [ha, hb, hc, hd, h0, h1, h2, h4]
  · change |pmPronicVaughanPiece ε U V n 4 / n - pmPronicVaughanMean ε U V 4| ≤ _
    linarith only [h4, hD, hI]

private theorem abs_product_sub_of_errors {x y a b E B : ℝ}
    (hE : 0 ≤ E) (hB : 0 ≤ B) (hx : |x - a| ≤ E) (hy : |y - b| ≤ E)
    (ha : |a| ≤ B) (hb : |b| ≤ B) :
    |x * y - a * b| ≤ E * (2 * B + E) := by
  calc
    _ = |(x - a) * (y - b) + a * (y - b) + b * (x - a)| := by congr 1; ring
    _ ≤ |(x - a) * (y - b)| + |a * (y - b)| + |b * (x - a)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |x - a| * |y - b| + |a| * |y - b| + |b| * |x - a| := by
      rw [abs_mul, abs_mul, abs_mul]
    _ ≤ E * E + B * E + B * E :=
      add_le_add
        (add_le_add (mul_le_mul hx hy (abs_nonneg _) hE)
          (mul_le_mul ha hy (abs_nonneg _) hB))
        (mul_le_mul hb hx (abs_nonneg _) hB)
    _ = _ := by ring

private theorem abs_pronic_product_sub_of_errors {f g a b E B : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hf : |f / n - a| ≤ E) (hg : |g / n - b| ≤ E)
    (ha : |a| ≤ B) (hb : |b| ≤ B) :
    |f * g / (pronicSeq n : ℝ) - a * b| ≤
      E * (2 * B + E) + B ^ 2 / ((n : ℝ) + 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hs0 : 0 ≤ (n : ℝ) / ((n : ℝ) + 1) := by positivity
  have hs1 : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
    (div_le_one hn1).mpr (by linarith)
  have heq : f * g / (pronicSeq n : ℝ) - a * b =
      (n : ℝ) / ((n : ℝ) + 1) * ((f / n) * (g / n) - a * b) -
        (a * b) / ((n : ℝ) + 1) := by
    simp only [pronicSeq, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp [hnR.ne', hn1.ne']
    ring
  have hprod := abs_product_sub_of_errors hE hB hf hg ha hb
  have hab : |a * b| ≤ B ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul ha hb (abs_nonneg _) hB
  rw [heq]
  calc
    _ ≤ |(n : ℝ) / ((n : ℝ) + 1) * ((f / n) * (g / n) - a * b)| +
        |(a * b) / ((n : ℝ) + 1)| := abs_sub _ _
    _ = (n : ℝ) / ((n : ℝ) + 1) * |(f / n) * (g / n) - a * b| +
        |a * b| / ((n : ℝ) + 1) := by
      rw [abs_mul, abs_of_nonneg hs0, abs_div, abs_of_pos hn1]
    _ ≤ 1 * (E * (2 * B + E)) + B ^ 2 / ((n : ℝ) + 1) :=
      add_le_add (mul_le_mul hs1 hprod (abs_nonneg _) zero_le_one)
        (div_le_div_of_nonneg_right hab hn1.le)
    _ = _ := by rw [one_mul]

/-- Cesàro averaging the common component error controls the entire Gram. -/
def pmVaughanGramError (ε : ℝ) (T : ℕ) : ℝ :=
  (∑ n ∈ Icc 1 T,
    (pmVaughanMeanError ε n * (2 * pmVaughanMeanBound ε + pmVaughanMeanError ε n) +
      pmVaughanMeanBound ε ^ 2 / ((n : ℝ) + 1))) / T

theorem tendsto_pmVaughanGramError_zero {ε : ℝ} (hε : 0 < ε) :
    Tendsto (pmVaughanGramError ε) atTop (𝓝 0) := by
  let h : ℕ → ℝ := fun n =>
    pmVaughanMeanError ε n * (2 * pmVaughanMeanBound ε + pmVaughanMeanError ε n) +
      pmVaughanMeanBound ε ^ 2 / ((n : ℝ) + 1)
  have hmain := (tendsto_pmVaughanMeanError_zero hε).mul
    ((tendsto_const_nhds (x := 2 * pmVaughanMeanBound ε)).add
      (tendsto_pmVaughanMeanError_zero hε))
  have htail := (tendsto_const_div_atTop_nhds_zero_nat
    (pmVaughanMeanBound ε ^ 2)).comp (tendsto_add_atTop_nat 1)
  have hlim : Tendsto h atTop (𝓝 0) := by
    simpa only [h, Function.comp_def, Nat.cast_add, Nat.cast_one, zero_mul, add_zero] using
      hmain.add htail
  have hc := (hlim.comp (tendsto_add_atTop_nat 1)).cesaro
  simp only [Function.comp_def] at hc
  convert hc using 1
  ext T
  rw [Finset.range_eq_Ico, Finset.sum_Ico_add' h 0 T 1]
  simp only [zero_add, Finset.Ico_add_one_right_eq_Icc, div_eq_mul_inv, mul_comm,
    pmVaughanGramError, h]

/-- The normalized Vaughan Gram approaches its mean outer product uniformly in the cutoffs. -/
theorem abs_pmPronicVaughanGram_div_sub_means_le {ε : ℝ} (hε : 0 < ε)
    (U V : ℕ) (i j : Fin 5) {T : ℕ} (hT : 1 ≤ T) :
    |pmPronicVaughanGram ε U V T i j / T -
        pmPronicVaughanMean ε U V i * pmPronicVaughanMean ε U V j| ≤
      pmVaughanGramError ε T := by
  have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast (by omega : T ≠ 0)
  have hB : 0 ≤ pmVaughanMeanBound ε :=
    (abs_nonneg _).trans (abs_pmPronicVaughanMean_le hε U V i)
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 T) :
      |pmPronicVaughanPiece ε U V n i * pmPronicVaughanPiece ε U V n j /
          (pronicSeq n : ℝ) - pmPronicVaughanMean ε U V i * pmPronicVaughanMean ε U V j| ≤
        pmVaughanMeanError ε n * (2 * pmVaughanMeanBound ε + pmVaughanMeanError ε n) +
          pmVaughanMeanBound ε ^ 2 / ((n : ℝ) + 1) :=
    abs_pronic_product_sub_of_errors (mem_Icc.mp hn).1
      (pmVaughanMeanError_nonneg hε n) hB
      (abs_pmPronicVaughanPiece_div_sub_mean_le hε U V i (mem_Icc.mp hn).1)
      (abs_pmPronicVaughanPiece_div_sub_mean_le hε U V j (mem_Icc.mp hn).1)
      (abs_pmPronicVaughanMean_le hε U V i) (abs_pmPronicVaughanMean_le hε U V j)
  have heq : pmPronicVaughanGram ε U V T i j / T -
      pmPronicVaughanMean ε U V i * pmPronicVaughanMean ε U V j =
      (∑ n ∈ Icc 1 T,
        (pmPronicVaughanPiece ε U V n i * pmPronicVaughanPiece ε U V n j /
          (pronicSeq n : ℝ) - pmPronicVaughanMean ε U V i * pmPronicVaughanMean ε U V j)) / T := by
    rw [sum_sub_distrib]
    simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
      pmPronicVaughanGram]
    field_simp [hT0]
  rw [heq, abs_div, show |(T : ℝ)| = T from abs_of_nonneg (Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right
    ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hpoint)) (Nat.cast_nonneg T)

/-- Every cutoff schedule obeys the uniform leading-matrix law. -/
theorem tendsto_pmPronicVaughanGram_div_sub_moving_means {ε : ℝ} (hε : 0 < ε)
    (U V : ℕ → ℕ) (i j : Fin 5) :
    Tendsto (fun T : ℕ => pmPronicVaughanGram ε (U T) (V T) T i j / T -
      pmPronicVaughanMean ε (U T) (V T) i * pmPronicVaughanMean ε (U T) (V T) j)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ (tendsto_pmVaughanGramError_zero hε)
  filter_upwards [eventually_ge_atTop 1] with T hT
  simpa only [Real.norm_eq_abs] using
    abs_pmPronicVaughanGram_div_sub_means_le hε (U T) (V T) i j hT

theorem pmPronicPowerDensity_nonneg (ε : ℝ) : 0 ≤ pmPronicPowerDensity ε :=
  tsum_nonneg fun n => div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (Nat.cast_nonneg n)

/-- The both-large linear mean is the product of the two omitted reciprocal tails. -/
theorem pmPronicVaughanMean_large_factorization {ε : ℝ} (hε : 0 < ε) (U V : ℕ) :
    pmPronicVaughanMean ε U V 3 =
      pmPronicPowerDensity ε *
        ((pmPowerDampedDivisorDensity ε).re - pmPronicVaughanSmallDensity ε U) *
        ((pmPowerDampedDivisorDensity ε).re - pmPronicVaughanSmallDensity ε V) := by
  change (pmPowerDampedDivisorDensity ε).re - pmPronicVaughanSmallDensity ε U -
    pmPronicVaughanSmallDensity ε V +
      pmPronicPowerDensity ε * pmPronicVaughanSmallDensity ε U *
        pmPronicVaughanSmallDensity ε V = _
  have hz : pmPronicPowerDensity ε * (pmPowerDampedDivisorDensity ε).re = 1 := by
    rw [pmPronicPowerDensity_eq_inv_density hε]
    field_simp [(pmPowerDampedDivisorDensity_re_pos hε).ne']
  linear_combination
    (pmPronicVaughanSmallDensity ε U + pmPronicVaughanSmallDensity ε V -
      (pmPowerDampedDivisorDensity ε).re) * hz

/-- Equal cutoffs give a nonnegative both-large mean, although the finite piece is signed. -/
theorem pmPronicVaughanMean_large_self_nonneg {ε : ℝ} (hε : 0 < ε) (U : ℕ) :
    0 ≤ pmPronicVaughanMean ε U U 3 := by
  rw [pmPronicVaughanMean_large_factorization hε, mul_assoc, ← sq]
  exact mul_nonneg (pmPronicPowerDensity_nonneg ε) (sq_nonneg _)

/-- Growing finite Möbius means recover the reciprocal zeta density. -/
theorem tendsto_pmPronicVaughanSmallDensity {ε : ℝ} (hε : 0 < ε) :
    Tendsto (pmPronicVaughanSmallDensity ε) atTop (𝓝 (pmPowerDampedDivisorDensity ε).re) := by
  let a : ℕ → ℝ := fun d => (moebius d : ℝ) * (d : ℝ) ^ (-ε)
  have ha : Summable (fun d => a d / (d : ℝ)) := by
    apply summable_density_of_abs_le (summable_pmVaughanFloorMajorant_div hε)
    intro d
    simpa only [a, Sieve.truncatedMoebius_apply, if_pos (le_refl d)] using
      abs_small_floor_coefficient_le ε d d
  have hdensity : (∑' d : ℕ, a d / d) = (pmPowerDampedDivisorDensity ε).re := by
    apply tendsto_nhds_unique (pm_tendsto_divisor_average ha)
    simpa only [a, pmPowerDampedDivisorSum, pmPowerDampedDivisorCoeff] using
      tendsto_pmPowerDampedDivisorSum_div_real hε
  have heq (N : ℕ) : (∑ d ∈ range (N + 1), a d / d) = pmPronicVaughanSmallDensity ε N := by
    change _ = ∑ d ∈ Icc 1 N, (moebius d : ℝ) * ((d : ℝ) ^ (-ε) / d)
    simp only [← mul_div_assoc]
    symm
    apply sum_subset
    · intro d hd
      have := (mem_Icc.mp hd).2
      simp only [mem_range]
      omega
    · intro d hd hnot
      have hd0 : d = 0 := by simp only [mem_range] at hd; simp only [mem_Icc] at hnot; omega
      simp [hd0]
  have h := ha.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, heq, hdensity] using h

/-- The limiting signs of the five Vaughan means when both cutoffs diverge. -/
def pmPronicVaughanLimitSigns : Fin 5 → ℝ := ![1, 1, -1, 0, -1]

theorem tendsto_pmPronicVaughanMean_moving {ε : ℝ} (hε : 0 < ε)
    {U V : ℕ → ℕ} (hU : Tendsto U atTop atTop) (hV : Tendsto V atTop atTop) (i : Fin 5) :
    Tendsto (fun N => pmPronicVaughanMean ε (U N) (V N) i) atTop
      (𝓝 ((pmPowerDampedDivisorDensity ε).re * pmPronicVaughanLimitSigns i)) := by
  have hA := (tendsto_pmPronicVaughanSmallDensity hε).comp hU
  have hB := (tendsto_pmPronicVaughanSmallDensity hε).comp hV
  have hρ := (pmPowerDampedDivisorDensity_re_pos hε).ne'
  fin_cases i
  · change Tendsto (fun N => pmPronicVaughanSmallDensity ε (U N)) atTop
      (𝓝 ((pmPowerDampedDivisorDensity ε).re * 1))
    simpa only [Function.comp_def, mul_one] using hA
  · change Tendsto (fun N => pmPronicVaughanSmallDensity ε (V N)) atTop
      (𝓝 ((pmPowerDampedDivisorDensity ε).re * 1))
    simpa only [Function.comp_def, mul_one] using hB
  · change Tendsto (fun N => -pmPronicPowerDensity ε *
      pmPronicVaughanSmallDensity ε (U N) * pmPronicVaughanSmallDensity ε (V N)) atTop
      (𝓝 ((pmPowerDampedDivisorDensity ε).re * (-1)))
    have h := (hA.const_mul (-pmPronicPowerDensity ε)).mul hB
    have hv : -pmPronicPowerDensity ε * (pmPowerDampedDivisorDensity ε).re *
        (pmPowerDampedDivisorDensity ε).re = -(pmPowerDampedDivisorDensity ε).re := by
      rw [pmPronicPowerDensity_eq_inv_density hε]
      field_simp [hρ]
    rw [hv] at h
    simpa only [Function.comp_def, mul_neg_one] using h
  · change Tendsto (fun N => pmPronicVaughanMean ε (U N) (V N) 3) atTop
      (𝓝 ((pmPowerDampedDivisorDensity ε).re * 0))
    have hconst : Tendsto (fun _ : ℕ => (pmPowerDampedDivisorDensity ε).re) atTop
        (𝓝 (pmPowerDampedDivisorDensity ε).re) := tendsto_const_nhds
    have h := ((hconst.sub hA).const_mul (pmPronicPowerDensity ε)).mul (hconst.sub hB)
    simpa only [Function.comp_def, pmPronicVaughanMean_large_factorization hε,
      sub_self, mul_zero] using h
  · change Tendsto (fun _ : ℕ => -(pmPowerDampedDivisorDensity ε).re) atTop
      (𝓝 ((pmPowerDampedDivisorDensity ε).re * (-1)))
    simpa only [mul_neg_one] using
      (tendsto_const_nhds (x := -(pmPowerDampedDivisorDensity ε).re) :
        Tendsto (fun _ : ℕ => -(pmPowerDampedDivisorDensity ε).re) atTop _)

/-- Any divergent horizon and cutoff schedules have the same limiting rank-one Gram. -/
theorem tendsto_pmPronicVaughanGram_div_moving {ε : ℝ} (hε : 0 < ε)
    {H U V : ℕ → ℕ} (hH : Tendsto H atTop atTop)
    (hU : Tendsto U atTop atTop) (hV : Tendsto V atTop atTop) (i j : Fin 5) :
    Tendsto (fun N => pmPronicVaughanGram ε (U N) (V N) (H N) i j / (H N)) atTop
      (𝓝 ((pmPowerDampedDivisorDensity ε).re ^ 2 *
        pmPronicVaughanLimitSigns i * pmPronicVaughanLimitSigns j)) := by
  have herr : Tendsto (fun N => pmPronicVaughanGram ε (U N) (V N) (H N) i j / (H N) -
      pmPronicVaughanMean ε (U N) (V N) i * pmPronicVaughanMean ε (U N) (V N) j)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ ((tendsto_pmVaughanGramError_zero hε).comp hH)
    filter_upwards [hH.eventually (eventually_ge_atTop 1)] with N hN
    simpa only [Real.norm_eq_abs, Function.comp_def] using
      abs_pmPronicVaughanGram_div_sub_means_le hε (U N) (V N) i j hN
  have hmain := (tendsto_pmPronicVaughanMean_moving hε hU hV i).mul
    (tendsto_pmPronicVaughanMean_moving hε hU hV j)
  have h := herr.add hmain
  have hv : ((pmPowerDampedDivisorDensity ε).re * pmPronicVaughanLimitSigns i) *
      ((pmPowerDampedDivisorDensity ε).re * pmPronicVaughanLimitSigns j) =
        (pmPowerDampedDivisorDensity ε).re ^ 2 * pmPronicVaughanLimitSigns i *
          pmPronicVaughanLimitSigns j := by ring
  simpa only [sub_add_cancel, zero_add, hv] using h

theorem tendsto_pmPronicVaughanDiagonal_div_moving {ε : ℝ} (hε : 0 < ε)
    {H U V : ℕ → ℕ} (hH : Tendsto H atTop atTop)
    (hU : Tendsto U atTop atTop) (hV : Tendsto V atTop atTop) :
    Tendsto (fun N => pmPronicVaughanDiagonal ε (U N) (V N) (H N) / (H N)) atTop
      (𝓝 (4 * (pmPowerDampedDivisorDensity ε).re ^ 2)) := by
  have h := tendsto_finsetSum univ (fun i _ => tendsto_pmPronicVaughanGram_div_moving hε hH hU hV i i)
  have hv : (∑ i : Fin 5, (pmPowerDampedDivisorDensity ε).re ^ 2 *
      pmPronicVaughanLimitSigns i * pmPronicVaughanLimitSigns i) =
        4 * (pmPowerDampedDivisorDensity ε).re ^ 2 := by
    simp [pmPronicVaughanLimitSigns, Fin.sum_univ_succ]
    ring
  rw [hv] at h
  simpa only [pmPronicVaughanDiagonal, sum_div] using h

private theorem tendsto_nat_square_atTop : Tendsto (fun N : ℕ => N ^ 2) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b, eventually_ge_atTop 1] with N hNb hN
  nlinarith only [hNb, hN]

/-- The leading matrix at the literal square-root Vaughan cutoffs. -/
theorem tendsto_pmPronicVaughanGram_square {ε : ℝ} (hε : 0 < ε) (i j : Fin 5) :
    Tendsto (fun N : ℕ => pmPronicVaughanGram ε N N (N ^ 2) i j / (N ^ 2 : ℕ)) atTop
      (𝓝 ((pmPowerDampedDivisorDensity ε).re ^ 2 *
        pmPronicVaughanLimitSigns i * pmPronicVaughanLimitSigns j)) :=
  tendsto_pmPronicVaughanGram_div_moving hε tendsto_nat_square_atTop tendsto_id tendsto_id i j

theorem tendsto_pmPronicVaughanDiagonal_square {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => pmPronicVaughanDiagonal ε N N (N ^ 2) / (N ^ 2 : ℕ)) atTop
      (𝓝 (4 * (pmPowerDampedDivisorDensity ε).re ^ 2)) :=
  tendsto_pmPronicVaughanDiagonal_div_moving hε tendsto_nat_square_atTop tendsto_id tendsto_id

end GaloisForLFunctions.BezoutValuationIncidence


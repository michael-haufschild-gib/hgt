import Mathlib
import GaloisForLFunctions.RHTower.CentralReciprocalMoments
import GaloisForLFunctions.RHTower.PrimeArchCentralMomentGerm
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor

/-!
# The height ratio gate for centered divisor moments

The absolute centered reciprocal moments of the xi divisor,

`absMoment n = ∑_ρ mult(ρ) * ‖ρ - 1/2‖⁻¹ ^ (2(n+1))`,

satisfy a purely geometric damping law: a lower bound `c` on the centered heights of the divisor
points forces `absMoment (n+1) ≤ absMoment n / c ^ 2`, and hence geometric decay in `n` with ratio
`c⁻²`.  A positive lower bound always exists, because the divisor is locally finite, so the decay
law holds unconditionally with *some* ratio; the arithmetic input is only the size of `c`.

Consequently the ratio gate `absMoment 2 < absMoment 1 / 81` follows from the single height
statement `9 < c`.  No estimate on individual moments is used: the whole gate is one bounded
multiplier applied under the sum.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric Function Filter MeromorphicOn _root_.RHTower

noncomputable section

/-- A finite set of positive reals has a positive lower bound. -/
theorem exists_pos_lowerBound_of_finite_pos {T : Set ℝ} (hT : T.Finite)
    (hpos : ∀ x ∈ T, 0 < x) : ∃ c > 0, ∀ x ∈ T, c ≤ x := by
  classical
  obtain ⟨F, hF⟩ := hT.exists_finset_coe
  rcases F.eq_empty_or_nonempty with hE | hE
  · refine ⟨1, one_pos, fun x hx => ?_⟩
    rw [← hF, hE] at hx
    simp at hx
  · refine ⟨F.min' hE, hpos _ ?_, fun x hx => F.min'_le x ?_⟩
    · rw [← hF]
      exact_mod_cast F.min'_mem hE
    · rw [← hF] at hx
      exact_mod_cast hx

/-- The absolute centered reciprocal moments of the xi divisor. -/
def xiCentralAbsMoment (n : ℕ) : ℝ :=
  ∑' ρ : ↥(MeromorphicOn.divisor xi Set.univ).support,
    ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * ‖(ρ : ℂ) - 1 / 2‖⁻¹ ^ (2 * (n + 1))

/-- Every absolute centered reciprocal moment converges. -/
theorem xiCentralAbsMoment_summable (n : ℕ) :
    Summable (fun ρ : ↥(MeromorphicOn.divisor xi Set.univ).support =>
      ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) *
        ‖(ρ : ℂ) - 1 / 2‖⁻¹ ^ (2 * (n + 1))) := by
  refine (xi_central_reciprocal_moment_summable n).norm.congr (fun ρ => ?_)
  have hd : (0 : ℝ) ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
    exact_mod_cast xi_divisor_nonneg Set.univ (ρ : ℂ)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd, norm_pow,
    xiCentralReciprocalSquare, norm_neg, norm_pow, norm_inv, ← pow_mul]

/-- Each moment summand is nonnegative. -/
theorem xiCentralAbsMoment_term_nonneg (n : ℕ)
    (ρ : ↥(MeromorphicOn.divisor xi Set.univ).support) :
    0 ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) *
      ‖(ρ : ℂ) - 1 / 2‖⁻¹ ^ (2 * (n + 1)) := by
  have hd : (0 : ℝ) ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
    exact_mod_cast xi_divisor_nonneg Set.univ (ρ : ℂ)
  positivity

/-- The absolute moments dominate the signed centered reciprocal moments. -/
theorem norm_xiCentralReciprocalMoment_le (n : ℕ) :
    ‖xiCentralReciprocalMoment n‖ ≤ xiCentralAbsMoment n := by
  rw [xiCentralReciprocalMoment, xiCentralAbsMoment]
  refine le_trans (norm_tsum_le_tsum_norm (xi_central_reciprocal_moment_summable n).norm)
    (le_of_eq (tsum_congr (fun ρ => ?_)))
  have hd : (0 : ℝ) ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
    exact_mod_cast xi_divisor_nonneg Set.univ (ρ : ℂ)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd, norm_pow,
    xiCentralReciprocalSquare, norm_neg, norm_pow, norm_inv, ← pow_mul]

/-- Passing from one moment to the next multiplies each summand by the squared inverse height. -/
theorem xiCentralAbsMoment_term_succ (n : ℕ)
    (ρ : ↥(MeromorphicOn.divisor xi Set.univ).support) :
    ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) *
        ‖(ρ : ℂ) - 1 / 2‖⁻¹ ^ (2 * (n + 1 + 1)) =
      ‖(ρ : ℂ) - 1 / 2‖⁻¹ ^ 2 *
        (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) *
          ‖(ρ : ℂ) - 1 / 2‖⁻¹ ^ (2 * (n + 1))) := by
  rw [show 2 * (n + 1 + 1) = 2 + 2 * (n + 1) by ring, pow_add]
  ring

/-- A bounded multiplier passes through an absolutely convergent sum of nonnegative terms. -/
theorem tsum_mul_le_const_mul_tsum {ι : Type*} {t f : ι → ℝ} (hf : Summable f)
    (htf : Summable fun i => t i * f i) {K : ℝ} (hf0 : ∀ i, 0 ≤ f i) (htK : ∀ i, t i ≤ K) :
    ∑' i, t i * f i ≤ K * ∑' i, f i := by
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun i => mul_le_mul_of_nonneg_right (htK i) (hf0 i)) htf
    (hf.mul_left K)

/-- **Height damping.**  A positive lower bound on the centered heights of the divisor points
damps successive absolute moments by the square of that bound. -/
theorem xiCentralAbsMoment_succ_le_div {c : ℝ} (hc : 0 < c)
    (hheight : ∀ ρ : ℂ, (MeromorphicOn.divisor xi Set.univ) ρ ≠ 0 → ρ ≠ 1 / 2 →
      c ≤ ‖ρ - 1 / 2‖) (n : ℕ) :
    xiCentralAbsMoment (n + 1) ≤ xiCentralAbsMoment n / c ^ 2 := by
  have hmul : ∀ ρ : ↥(MeromorphicOn.divisor xi Set.univ).support,
      ‖(ρ : ℂ) - 1 / 2‖⁻¹ ^ 2 ≤ (c ^ 2)⁻¹ := by
    intro ρ
    by_cases hhalf : (ρ : ℂ) = 1 / 2
    · rw [hhalf]
      simp
      positivity
    · have hle : c ≤ ‖(ρ : ℂ) - 1 / 2‖ :=
        hheight (ρ : ℂ) (Function.mem_support.mp ρ.2) hhalf
      rw [← inv_pow]
      exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hc hle) 2
  have hsum := xiCentralAbsMoment_summable n
  have hsum2 := (xiCentralAbsMoment_summable (n + 1)).congr
    (fun ρ => xiCentralAbsMoment_term_succ n ρ)
  have key := tsum_mul_le_const_mul_tsum hsum hsum2 (xiCentralAbsMoment_term_nonneg n) hmul
  have hrewrite : xiCentralAbsMoment (n + 1) =
      ∑' ρ : ↥(MeromorphicOn.divisor xi Set.univ).support,
        ‖(ρ : ℂ) - 1 / 2‖⁻¹ ^ 2 *
          (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) *
            ‖(ρ : ℂ) - 1 / 2‖⁻¹ ^ (2 * (n + 1))) :=
    tsum_congr (fun ρ => xiCentralAbsMoment_term_succ n ρ)
  have hdiv : xiCentralAbsMoment n / c ^ 2 = (c ^ 2)⁻¹ * xiCentralAbsMoment n := by ring
  rw [hrewrite, hdiv]
  exact key

/-- The divisor of xi has a positive centered height floor away from the fixed point. -/
theorem exists_pos_xiCentralHeightFloor :
    ∃ c > 0, ∀ ρ : ℂ, (MeromorphicOn.divisor xi Set.univ) ρ ≠ 0 → ρ ≠ 1 / 2 →
      c ≤ ‖ρ - 1 / 2‖ := by
  classical
  have hLF : LocallyFiniteSupport (MeromorphicOn.divisor xi Set.univ).toFun :=
    Function.locallyFinsupp.locallyFiniteSupport _
  have hfin := hLF.finite_inter_support_of_isCompact (isCompact_closedBall (1 / 2 : ℂ) 1)
  set T : Set ℝ := (fun z : ℂ => ‖z - 1 / 2‖) ''
    (closedBall (1 / 2 : ℂ) 1 ∩ Function.support (MeromorphicOn.divisor xi Set.univ).toFun) \ {0}
    with hT
  have hTfin : T.Finite := (hfin.image _).sdiff
  have hTpos : ∀ x ∈ T, 0 < x := by
    rintro x ⟨⟨z, _, rfl⟩, hx0⟩
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm (by simpa using hx0))
  obtain ⟨c, hc, hcle⟩ := exists_pos_lowerBound_of_finite_pos hTfin hTpos
  refine ⟨min c 1, lt_min hc one_pos, fun ρ hρ hhalf => ?_⟩
  rcases le_or_gt ‖ρ - 1 / 2‖ 1 with hsmall | hbig
  · refine le_trans (min_le_left _ _) (hcle _ ⟨⟨ρ, ⟨?_, hρ⟩, rfl⟩, ?_⟩)
    · simpa [mem_closedBall, dist_eq_norm] using hsmall
    · simp only [Set.mem_singleton_iff]
      exact fun h => hhalf (by rwa [norm_eq_zero, sub_eq_zero] at h)
  · exact le_trans (min_le_right _ _) hbig.le

/-- **Unconditional geometric decay.**  Some fixed ratio damps every step of the absolute
centered moment sequence. -/
theorem exists_pos_xiCentralAbsMoment_ratio :
    ∃ c > 0, ∀ n : ℕ, xiCentralAbsMoment (n + 1) ≤ xiCentralAbsMoment n / c ^ 2 := by
  obtain ⟨c, hc, hcle⟩ := exists_pos_xiCentralHeightFloor
  exact ⟨c, hc, fun n => xiCentralAbsMoment_succ_le_div hc hcle n⟩

/-- Iterating the damping law gives geometric decay of the absolute moments. -/
theorem xiCentralAbsMoment_add_le_div {c : ℝ} (hc : 0 < c)
    (hheight : ∀ ρ : ℂ, (MeromorphicOn.divisor xi Set.univ) ρ ≠ 0 → ρ ≠ 1 / 2 →
      c ≤ ‖ρ - 1 / 2‖) (n k : ℕ) :
    xiCentralAbsMoment (n + k) ≤ xiCentralAbsMoment n / c ^ (2 * k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := xiCentralAbsMoment_succ_le_div hc hheight (n + k)
      have hpow : (0 : ℝ) < c ^ (2 * k) := by positivity
      calc xiCentralAbsMoment (n + (k + 1))
          = xiCentralAbsMoment ((n + k) + 1) := by ring_nf
        _ ≤ xiCentralAbsMoment (n + k) / c ^ 2 := hstep
        _ ≤ (xiCentralAbsMoment n / c ^ (2 * k)) / c ^ 2 := by
            gcongr
        _ = xiCentralAbsMoment n / c ^ (2 * (k + 1)) := by
            rw [div_div, ← pow_add]
            ring_nf

/-- **The ratio gate.**  A centered height floor above `9` forces the second absolute moment
below the eighty-first part of the first.  This is the whole content of the gate: one bounded
multiplier under the sum, with no estimate on either moment. -/
theorem xiCentralAbsMoment_two_lt_div_of_height {c : ℝ} (hc : 9 < c)
    (hheight : ∀ ρ : ℂ, (MeromorphicOn.divisor xi Set.univ) ρ ≠ 0 → ρ ≠ 1 / 2 →
      c ≤ ‖ρ - 1 / 2‖) (hpos : 0 < xiCentralAbsMoment 1) :
    xiCentralAbsMoment 2 < xiCentralAbsMoment 1 / 81 := by
  have hc0 : (0 : ℝ) < c := lt_trans (by norm_num) hc
  have hsq : (81 : ℝ) < c ^ 2 := by nlinarith
  calc xiCentralAbsMoment 2 ≤ xiCentralAbsMoment 1 / c ^ 2 :=
        xiCentralAbsMoment_succ_le_div hc0 hheight 1
    _ < xiCentralAbsMoment 1 / 81 := by
        exact div_lt_div_of_pos_left hpos (by norm_num) hsq

/-- The source moments of the continued prime-archimedean relative trace are bounded in absolute
value by the absolute centered divisor moments. -/
theorem abs_normalizedPrimeArchMoment_le (n : ℕ) :
    |normalizedPrimeArchMoment n| ≤ xiCentralAbsMoment n := by
  have h : ((normalizedPrimeArchMoment n : ℝ) : ℂ) = xiCentralReciprocalMoment n :=
    primeArchSourceMoment_eq_xiCentralReciprocalMoment n
  have hnorm : |normalizedPrimeArchMoment n| = ‖xiCentralReciprocalMoment n‖ := by
    rw [← h, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  exact norm_xiCentralReciprocalMoment_le n

/-- **The gate in source vocabulary.**  A centered height floor above `9` places the second
source moment below the eighty-first part of the first absolute moment. -/
theorem normalizedPrimeArchMoment_two_lt_of_height {c : ℝ} (hc : 9 < c)
    (hheight : ∀ ρ : ℂ, (MeromorphicOn.divisor xi Set.univ) ρ ≠ 0 → ρ ≠ 1 / 2 →
      c ≤ ‖ρ - 1 / 2‖) (hpos : 0 < xiCentralAbsMoment 1) :
    normalizedPrimeArchMoment 2 < xiCentralAbsMoment 1 / 81 :=
  lt_of_le_of_lt (le_trans (le_abs_self _) (abs_normalizedPrimeArchMoment_le 2))
    (xiCentralAbsMoment_two_lt_div_of_height hc hheight hpos)

end

end GaloisForLFunctions.HTGeometry

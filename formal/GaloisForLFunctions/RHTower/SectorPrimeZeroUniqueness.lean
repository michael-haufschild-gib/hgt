import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Prime-log zero density in a sector

This file supplies the arithmetic half of the sectorial zero-uniqueness
argument used by actual-source Euler-unit completeness.  It deliberately uses
only Euler's divergence of the prime reciprocal sum: no prime number theorem
is required.

The next analytic layer is the disk/half-plane Blaschke consequence for a
bounded analytic function.  The final theorem below already proves that the
prime-log Cayley defects violate that consequence after every real translation.
-/

noncomputable section

namespace RHTower

open Filter Function MeromorphicOn Metric Real Set
open Complex
open scoped Topology

private def primeSubtypeEmbedding : Nat.Primes ↪ ℕ :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- Prime values escape every real bound along the cofinite filter on the
prime subtype. -/
theorem tendsto_prime_coe_real_cofinite_atTop :
    Tendsto (fun p : Nat.Primes ↦ (p : ℝ)) cofinite atTop := by
  apply Filter.tendsto_atTop.mpr
  intro b
  rw [eventually_cofinite]
  apply (Set.Finite.preimage_embedding primeSubtypeEmbedding
    (Set.finite_lt_nat ⌈b⌉₊)).subset
  intro p hp
  change (p : ℕ) < ⌈b⌉₊
  rw [Nat.lt_ceil]
  exact lt_of_not_ge hp

/-- For every integral power, the reciprocal prime-log series diverges.

The proof is strictly weaker than PNT: eventually `(log p)^n ≤ p`, so
summability would contradict Euler's divergence of `Σ_p 1/p`. -/
theorem prime_log_pow_not_summable (n : ℕ) :
    ¬ Summable (fun p : Nat.Primes ↦
      (1 / (Real.log (p : ℝ)) ^ n : ℝ)) := by
  intro hlog
  have hgrowth : ∀ᶠ x : ℝ in atTop,
      ‖Real.log x ^ n‖ ≤ 1 * ‖x‖ :=
    Real.isLittleO_pow_log_id_atTop.bound one_pos
  have hprime := tendsto_prime_coe_real_cofinite_atTop.eventually hgrowth
  have hrecip : Summable (fun p : Nat.Primes ↦ (1 / (p : ℝ) : ℝ)) := by
    apply Summable.of_norm_bounded_eventually hlog
    filter_upwards [hprime] with p hp
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    have hp0 : 0 < (p : ℝ) := hp1.trans' zero_lt_one
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
    have hpowp : 0 < Real.log (p : ℝ) ^ n := pow_pos hlogp _
    have hle : Real.log (p : ℝ) ^ n ≤ (p : ℝ) := by
      simpa [Real.norm_of_nonneg (pow_nonneg hlogp.le n),
        Real.norm_of_nonneg hp0.le] using hp
    rw [Real.norm_of_nonneg (one_div_nonneg.mpr hp0.le)]
    exact one_div_le_one_div_of_le hpowp hle
  exact Nat.Primes.not_summable_one_div hrecip

/-- Translation of the sector vertex does not repair the divergent prime-log
Blaschke defect.  Equivalently, for every `R ≥ 0` the positive tail

`1 / ((log p - R)^n + 1)`

is not summable over the primes.  These are, up to a factor `2`, exactly the
radial defects of the Cayley images
`((log p - R)^n - 1) / ((log p - R)^n + 1)`. -/
theorem prime_shifted_log_power_recip_not_summable
    (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ¬ Summable (fun p : Nat.Primes ↦
      (1 / ((Real.log (p : ℝ) - R) ^ n + 1) : ℝ)) := by
  intro hshift
  have hlogtop : Tendsto (fun p : Nat.Primes ↦ Real.log (p : ℝ))
      cofinite atTop := by
    simpa only [Function.comp_apply] using
      Real.tendsto_log_atTop.comp tendsto_prime_coe_real_cofinite_atTop
  have hlarge := Filter.tendsto_atTop.mp hlogtop (max R 1)
  have hmajor : Summable (fun p : Nat.Primes ↦
      2 * |(1 / ((Real.log (p : ℝ) - R) ^ n + 1) : ℝ)|) :=
    hshift.abs.mul_left 2
  have hlogsum : Summable (fun p : Nat.Primes ↦
      (1 / (Real.log (p : ℝ)) ^ n : ℝ)) := by
    apply Summable.of_norm_bounded_eventually hmajor
    filter_upwards [hlarge] with p hp
    let L : ℝ := Real.log (p : ℝ)
    have hRL : R ≤ L := le_trans (le_max_left R 1) hp
    have hL1 : 1 ≤ L := le_trans (le_max_right R 1) hp
    have hL0 : 0 < L := zero_lt_one.trans_le hL1
    have hy0 : 0 ≤ L - R := sub_nonneg.mpr hRL
    have hyL : L - R ≤ L := by linarith
    have hpowle : (L - R) ^ n ≤ L ^ n := by gcongr
    have hLpow1 : 1 ≤ L ^ n := one_le_pow₀ hL1
    have hdenpos : 0 < (L - R) ^ n + 1 := by positivity
    have hdenle : (L - R) ^ n + 1 ≤ 2 * L ^ n := by nlinarith
    have hrec : 1 / (2 * L ^ n) ≤ 1 / ((L - R) ^ n + 1) :=
      one_div_le_one_div_of_le hdenpos hdenle
    have hLpow0 : 0 < L ^ n := pow_pos hL0 _
    change ‖(1 / L ^ n : ℝ)‖ ≤ 2 * |(1 / ((L - R) ^ n + 1) : ℝ)|
    rw [Real.norm_of_nonneg (one_div_nonneg.mpr hLpow0.le),
      abs_of_pos (one_div_pos.mpr hdenpos)]
    calc
      1 / L ^ n = 2 * (1 / (2 * L ^ n)) := by field_simp
      _ ≤ 2 * (1 / ((L - R) ^ n + 1)) := by gcongr
  exact prime_log_pow_not_summable n hlogsum

private theorem jensen_weighted_divisor_le
    {f : ℂ → ℂ} {M : ℝ}
    (hM : 1 ≤ M)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 |(1 : ℝ)|))
    (hf0 : f 0 ≠ 0)
    (f_bound : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ ≤ M) :
    ∑ᶠ u, divisor f (closedBall 0 |(1 : ℝ)|) u *
      Real.log (1 * ‖(0 : ℂ) - u‖⁻¹) ≤ Real.log (M / ‖f 0‖) := by
  have hj := hf.circleAverage_log_norm one_ne_zero hf0
  have havg : circleAverage (fun x ↦ Real.log ‖f x‖) 0 1 ≤ Real.log M := by
    apply circleAverage_mono_on_of_le_circle
    · exact (hf.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
    · intro z hz
      have hzbound := f_bound z (by simpa using hz)
      by_cases hzero : f z = 0
      · simpa [hzero] using log_nonneg hM
      · exact Real.log_le_log (norm_pos_iff.mpr hzero) hzbound
  rw [hj] at havg
  have havg' :
      ∑ᶠ u, divisor f (closedBall 0 |(1 : ℝ)|) u *
          Real.log (1 * ‖(0 : ℂ) - u‖⁻¹) + Real.log ‖f 0‖ ≤ Real.log M := by
    simpa using havg
  rw [Real.log_div (by positivity) (norm_ne_zero_iff.mpr hf0)]
  linarith

private theorem divisor_ge_one_of_zero
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (closedBall 0 |(1 : ℝ)|))
    (hf0 : f 0 ≠ 0) {x : ℂ} (hx : x ∈ closedBall 0 |(1 : ℝ)|)
    (hz : f x = 0) :
    (1 : ℤ) ≤ divisor f (closedBall 0 |(1 : ℝ)|) x := by
  have hnonneg : (0 : ℤ) ≤ divisor f (closedBall 0 |(1 : ℝ)|) x :=
    hf.divisor_nonneg x
  suffices divisor f (closedBall 0 |(1 : ℝ)|) x ≠ 0 by omega
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn hx]
  simp only [ne_eq, WithTop.untop₀_eq_zero, not_or]
  constructor
  · exact (hf x hx).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.not.mpr
      (not_ne_iff.mpr hz)
  · apply hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall 0 |(1 : ℝ)|).isPreconnected
      (show (0 : ℂ) ∈ closedBall 0 |(1 : ℝ)| by simp) hx
    rw [(hf 0 (by simp)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hf0]
    simp

private theorem divisor_log_weight_nonneg
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (closedBall 0 |(1 : ℝ)|))
    (x : ℂ) :
    0 ≤ (divisor f (closedBall 0 |(1 : ℝ)|) x : ℝ) *
      Real.log (1 * ‖(0 : ℂ) - x‖⁻¹) := by
  by_cases hx : x ∈ closedBall (0 : ℂ) |(1 : ℝ)|
  · apply mul_nonneg
    · exact_mod_cast hf.divisor_nonneg x
    · by_cases hx0 : x = 0
      · simp [hx0]
      · apply Real.log_nonneg
        rw [one_mul, one_le_inv₀ (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hx0)))]
        simpa [mem_closedBall, dist_zero_right] using hx
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hx]
    simp

/-- A finite injective family of zeros in the unit disk is bounded by the
Jensen divisor mass, with each zero counted at least once. -/
theorem finite_zero_log_weight_le_divisor
    {ι : Type*} [DecidableEq ι]
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (closedBall 0 |(1 : ℝ)|))
    (hf0 : f 0 ≠ 0) (u : ι → ℂ) (s : Finset ι)
    (hinj : Set.InjOn u s) (hu_mem : ∀ i ∈ s, ‖u i‖ < 1)
    (hu_zero : ∀ i ∈ s, f (u i) = 0) :
    ∑ i ∈ s, Real.log (‖u i‖⁻¹) ≤
      ∑ᶠ x, (divisor f (closedBall 0 |(1 : ℝ)|) x : ℝ) *
        Real.log (1 * ‖(0 : ℂ) - x‖⁻¹) := by
  classical
  let t : Finset ℂ := s.image u
  let lhs : ℂ → ℝ := fun x ↦ if x ∈ t then Real.log (‖x‖⁻¹) else 0
  have hlhsSupport : Function.HasFiniteSupport lhs := by
    apply (t.finite_toSet.subset)
    intro x hx
    by_contra hxt
    apply hx
    change (if x ∈ t then Real.log (‖x‖⁻¹) else 0) = 0
    exact if_neg hxt
  have hrightSupport : Function.HasFiniteSupport (fun x : ℂ ↦
      (divisor f (closedBall 0 |(1 : ℝ)|) x : ℝ) *
        Real.log (1 * ‖(0 : ℂ) - x‖⁻¹)) := by
    apply (divisor f (closedBall 0 |(1 : ℝ)|)).finiteSupport
      (isCompact_closedBall (0 : ℂ) |(1 : ℝ)|) |>.subset
    intro x hx
    simp only [Function.mem_support, ne_eq, mul_ne_zero_iff] at hx ⊢
    exact_mod_cast hx.1
  have hpoint : ∀ x, lhs x ≤
      (divisor f (closedBall 0 |(1 : ℝ)|) x : ℝ) *
        Real.log (1 * ‖(0 : ℂ) - x‖⁻¹) := by
    intro x
    by_cases hxt : x ∈ t
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxt
      have hnorm : ‖u i‖ < 1 := hu_mem i hi
      have hu0 : u i ≠ 0 := by
        intro h
        apply hf0
        simpa [h] using hu_zero i hi
      have hlog0 : 0 ≤ Real.log (‖u i‖⁻¹) := by
        apply Real.log_nonneg
        exact one_le_inv₀ (norm_pos_iff.mpr hu0) |>.mpr hnorm.le
      have hmem : u i ∈ closedBall (0 : ℂ) |(1 : ℝ)| := by
        simpa [mem_closedBall, dist_zero_right] using hnorm.le
      have hdiv := divisor_ge_one_of_zero hf hf0 hmem (hu_zero i hi)
      simp only [lhs, hxt, ↓reduceIte, one_mul, zero_sub, norm_neg]
      calc
        Real.log (‖u i‖⁻¹) = 1 * Real.log (‖u i‖⁻¹) := by simp
        _ ≤ (divisor f (closedBall 0 |(1 : ℝ)|) (u i) : ℝ) *
            Real.log (‖u i‖⁻¹) := by
              gcongr
              exact_mod_cast hdiv
    · simp only [lhs, hxt, ↓reduceIte]
      exact divisor_log_weight_nonneg hf x
  have hfinsum := finsum_le_finsum' hlhsSupport hrightSupport hpoint
  calc
    ∑ i ∈ s, Real.log (‖u i‖⁻¹) = ∑ x ∈ t, Real.log (‖x‖⁻¹) := by
      rw [show t = s.image u by rfl]
      simpa only using (Finset.sum_image
        (f := fun x : ℂ ↦ Real.log (‖x‖⁻¹)) hinj).symm
    _ = ∑ᶠ x, lhs x := by
      rw [finsum_eq_sum_of_support_subset lhs (s := t)]
      · apply Finset.sum_congr rfl
        intro x hx
        simp [lhs, hx]
      · intro x hx
        by_contra hxt
        apply hx
        change (if x ∈ t then Real.log (‖x‖⁻¹) else 0) = 0
        exact if_neg hxt
    _ ≤ _ := hfinsum

/-- **Disk Blaschke condition from Jensen's formula.**  An injective family
of zeros of a bounded nonzero analytic function in the unit disk has summable
radial defects `1 - ‖u i‖`. -/
theorem summable_one_sub_norm_of_bounded_analytic_zeros
    {ι : Type*} {f : ℂ → ℂ} {M : ℝ}
    (hM : 1 ≤ M)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 |(1 : ℝ)|))
    (hf0 : f 0 ≠ 0)
    (f_bound : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ ≤ M)
    (u : ι → ℂ) (hinj : Function.Injective u)
    (hu_mem : ∀ i, ‖u i‖ < 1) (hu_zero : ∀ i, f (u i) = 0) :
    Summable (fun i ↦ 1 - ‖u i‖) := by
  classical
  apply summable_of_sum_le (c := Real.log (M / ‖f 0‖))
  · intro i
    exact sub_nonneg.mpr (hu_mem i).le
  · intro s
    calc
      ∑ i ∈ s, (1 - ‖u i‖) ≤ ∑ i ∈ s, Real.log (‖u i‖⁻¹) := by
        gcongr with i hi
        have hu0 : u i ≠ 0 := by
          intro h
          apply hf0
          simpa [h] using hu_zero i
        rw [Real.log_inv]
        have hlog := Real.log_le_sub_one_of_pos (norm_pos_iff.mpr hu0)
        linarith
      _ ≤ ∑ᶠ x, (divisor f (closedBall 0 |(1 : ℝ)|) x : ℝ) *
          Real.log (1 * ‖(0 : ℂ) - x‖⁻¹) :=
        finite_zero_log_weight_le_divisor hf hf0 u s
          hinj.injOn (fun i _ ↦ hu_mem i) (fun i _ ↦ hu_zero i)
      _ ≤ Real.log (M / ‖f 0‖) :=
        jensen_weighted_divisor_le hM hf hf0 f_bound

end RHTower
namespace RHTower

/-- The finite set of primes whose logarithm has not passed the translated
sector vertex by one unit. -/
def smallPrimeLogs (R : ℝ) : Set Nat.Primes :=
  {p | ¬ R + 1 < Real.log (p : ℝ)}

/-- Cofinite prime tail on which `log p - R > 1`. -/
abbrev PrimeLogBeyond (R : ℝ) := (smallPrimeLogs R)ᶜ

theorem smallPrimeLogs_finite (R : ℝ) : (smallPrimeLogs R).Finite := by
  have hlogtop : Filter.Tendsto (fun p : Nat.Primes ↦ Real.log (p : ℝ))
      Filter.cofinite Filter.atTop := by
    simpa only [Function.comp_apply] using
      Real.tendsto_log_atTop.comp tendsto_prime_coe_real_cofinite_atTop
  have hlarge := Filter.tendsto_atTop.mp hlogtop (R + 2)
  rw [Filter.eventually_cofinite] at hlarge
  apply hlarge.subset
  intro p hp
  simp only [smallPrimeLogs, Set.mem_setOf_eq] at hp ⊢
  linarith

theorem prime_shifted_log_power_recip_beyond_not_summable
    (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ¬ Summable (fun p : PrimeLogBeyond R ↦
      (1 / ((Real.log ((p : Nat.Primes) : ℝ) - R) ^ n + 1) : ℝ)) := by
  intro htail
  apply prime_shifted_log_power_recip_not_summable n R hR
  exact (smallPrimeLogs_finite R).summable_compl_iff.mp htail

/-- Cayley image of the positive power `(log p - R)^n`. -/
def primeLogCayley (n : ℕ) (R : ℝ) (p : PrimeLogBeyond R) : ℂ :=
  (((Real.log ((p : Nat.Primes) : ℝ) - R) ^ n - 1) /
    ((Real.log ((p : Nat.Primes) : ℝ) - R) ^ n + 1) : ℝ)

private theorem primeLogBeyond_base_gt_one (R : ℝ) (p : PrimeLogBeyond R) :
    1 < Real.log ((p : Nat.Primes) : ℝ) - R := by
  have hpnot : (p : Nat.Primes) ∉ smallPrimeLogs R := p.prop
  have hp : R + 1 < Real.log ((p : Nat.Primes) : ℝ) := by
    simpa only [smallPrimeLogs, Set.mem_setOf_eq, Classical.not_not] using hpnot
  linarith

private theorem primeLogCayley_real_pos_lt_one
    {n : ℕ} (hn : n ≠ 0) (R : ℝ) (p : PrimeLogBeyond R) :
    0 < (((Real.log ((p : Nat.Primes) : ℝ) - R) ^ n - 1) /
      ((Real.log ((p : Nat.Primes) : ℝ) - R) ^ n + 1) : ℝ) ∧
    (((Real.log ((p : Nat.Primes) : ℝ) - R) ^ n - 1) /
      ((Real.log ((p : Nat.Primes) : ℝ) - R) ^ n + 1) : ℝ) < 1 := by
  let y : ℝ := Real.log ((p : Nat.Primes) : ℝ) - R
  have hy : 1 < y := primeLogBeyond_base_gt_one R p
  have hyn : 1 < y ^ n := by
    simpa using pow_lt_pow_left₀ hy zero_le_one hn
  change 0 < (y ^ n - 1) / (y ^ n + 1) ∧
    (y ^ n - 1) / (y ^ n + 1) < 1
  constructor
  · exact div_pos (sub_pos.mpr hyn) (by linarith)
  · rw [div_lt_one (by linarith)]
    linarith

@[simp] theorem norm_primeLogCayley
    {n : ℕ} (hn : n ≠ 0) (R : ℝ) (p : PrimeLogBeyond R) :
    ‖primeLogCayley n R p‖ =
      ((Real.log ((p : Nat.Primes) : ℝ) - R) ^ n - 1) /
        ((Real.log ((p : Nat.Primes) : ℝ) - R) ^ n + 1) := by
  rw [primeLogCayley, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (primeLogCayley_real_pos_lt_one hn R p).1]

@[simp] theorem one_sub_norm_primeLogCayley
    {n : ℕ} (hn : n ≠ 0) (R : ℝ) (p : PrimeLogBeyond R) :
    1 - ‖primeLogCayley n R p‖ =
      2 / ((Real.log ((p : Nat.Primes) : ℝ) - R) ^ n + 1) := by
  rw [norm_primeLogCayley hn]
  have hbase : 0 < Real.log ((p : Nat.Primes) : ℝ) - R :=
    (primeLogBeyond_base_gt_one R p).trans' zero_lt_one
  have hy : 0 < (Real.log ((p : Nat.Primes) : ℝ) - R) ^ n + 1 := by
    positivity
  field_simp
  ring

end RHTower

namespace RHTower

open Filter Function MeromorphicOn Metric Real Set
open Complex

theorem primeLogCayley_injective
    {n : ℕ} (hn : n ≠ 0) (R : ℝ) : Function.Injective (primeLogCayley n R) := by
  intro p q hpq
  have hpqR :
      (((Real.log ((p : Nat.Primes) : ℝ) - R) ^ n - 1) /
        ((Real.log ((p : Nat.Primes) : ℝ) - R) ^ n + 1) : ℝ) =
      (((Real.log ((q : Nat.Primes) : ℝ) - R) ^ n - 1) /
        ((Real.log ((q : Nat.Primes) : ℝ) - R) ^ n + 1) : ℝ) := by
    rw [primeLogCayley] at hpq
    exact Complex.ofReal_injective hpq
  let a : ℝ := Real.log ((p : Nat.Primes) : ℝ) - R
  let b : ℝ := Real.log ((q : Nat.Primes) : ℝ) - R
  have ha : 0 ≤ a := (primeLogBeyond_base_gt_one R p).le.trans' zero_le_one
  have hb : 0 ≤ b := (primeLogBeyond_base_gt_one R q).le.trans' zero_le_one
  have hda : a ^ n + 1 ≠ 0 := by positivity
  have hdb : b ^ n + 1 ≠ 0 := by positivity
  have hpow : a ^ n = b ^ n := by
    change (a ^ n - 1) / (a ^ n + 1) =
      (b ^ n - 1) / (b ^ n + 1) at hpqR
    field_simp [hda, hdb] at hpqR
    nlinarith
  have hab : a = b := (pow_left_inj₀ ha hb hn).mp hpow
  have hlog : Real.log ((p : Nat.Primes) : ℝ) =
      Real.log ((q : Nat.Primes) : ℝ) := by
    dsimp [a, b] at hab
    linarith
  have hp0 : 0 < ((p : Nat.Primes) : ℝ) := by
    exact_mod_cast (p : Nat.Primes).prop.pos
  have hq0 : 0 < ((q : Nat.Primes) : ℝ) := by
    exact_mod_cast (q : Nat.Primes).prop.pos
  have hcast : (((p : Nat.Primes) : ℝ)) = (((q : Nat.Primes) : ℝ)) := by
    calc
      ((p : Nat.Primes) : ℝ) = Real.exp (Real.log ((p : Nat.Primes) : ℝ)) :=
        (Real.exp_log hp0).symm
      _ = Real.exp (Real.log ((q : Nat.Primes) : ℝ)) := by rw [hlog]
      _ = ((q : Nat.Primes) : ℝ) := Real.exp_log hq0
  apply Subtype.ext
  apply Subtype.ext
  exact_mod_cast hcast

theorem primeLogCayley_defect_not_summable
    {n : ℕ} (hn : n ≠ 0) (R : ℝ) (hR : 0 ≤ R) :
    ¬ Summable (fun p : PrimeLogBeyond R ↦ 1 - ‖primeLogCayley n R p‖) := by
  intro h
  have htwo : Summable (fun p : PrimeLogBeyond R ↦
      2 * (1 / ((Real.log ((p : Nat.Primes) : ℝ) - R) ^ n + 1) : ℝ)) := by
    apply h.congr
    intro p
    simpa [div_eq_mul_inv] using one_sub_norm_primeLogCayley hn R p
  have hone : Summable (fun p : PrimeLogBeyond R ↦
      (1 / ((Real.log ((p : Nat.Primes) : ℝ) - R) ^ n + 1) : ℝ)) := by
    have := htwo.mul_left (1 / 2 : ℝ)
    convert this using 1
    funext p
    ring
  exact prime_shifted_log_power_recip_beyond_not_summable n R hR hone

/-- A bounded analytic function on the unit disk, nonzero at the origin,
cannot vanish on all translated prime-log Cayley points.  This is the exact
Blaschke contradiction consumed by the sector uniqueness theorem. -/
theorem not_bounded_analytic_zero_on_all_primeLogCayley_closedDisk
    {n : ℕ} (hn : n ≠ 0) (R : ℝ) (hR : 0 ≤ R)
    {f : ℂ → ℂ} {M : ℝ} (hM : 1 ≤ M)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 |(1 : ℝ)|))
    (hf0 : f 0 ≠ 0)
    (f_bound : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ ≤ M)
    (hzero : ∀ p : PrimeLogBeyond R, f (primeLogCayley n R p) = 0) : False := by
  apply primeLogCayley_defect_not_summable hn R hR
  apply summable_one_sub_norm_of_bounded_analytic_zeros hM hf hf0 f_bound
    (primeLogCayley n R) (primeLogCayley_injective hn R)
  · intro p
    rw [norm_primeLogCayley hn]
    exact (primeLogCayley_real_pos_lt_one hn R p).2
  · exact hzero

end RHTower
namespace RHTower

open Filter Function MeromorphicOn Metric Real Set
open Complex

/-- Disk Blaschke condition in its usable form: the function need only be
analytic and bounded on the open unit disk. -/
theorem summable_one_sub_norm_of_bounded_analytic_zeros_openDisk
    {ι : Type*} {f : ℂ → ℂ} {M : ℝ}
    (hM : 1 ≤ M)
    (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hf0 : f 0 ≠ 0)
    (f_bound : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ M)
    (u : ι → ℂ) (hinj : Function.Injective u)
    (hu_mem : ∀ i, ‖u i‖ < 1) (hu_zero : ∀ i, f (u i) = 0) :
    Summable (fun i ↦ 1 - ‖u i‖) := by
  classical
  apply summable_of_sum_le (c := Real.log (M / ‖f 0‖) + 1)
  · intro i
    exact sub_nonneg.mpr (hu_mem i).le
  · intro s
    by_cases hs : s.Nonempty
    · let ns : Finset ℝ := s.image (fun i ↦ ‖u i‖)
      have hns : ns.Nonempty := Finset.image_nonempty.mpr hs
      let q : ℝ := ns.max' hns
      have hq0 : 0 ≤ q := by
        obtain ⟨i, hi, hqi⟩ := Finset.mem_image.mp (Finset.max'_mem ns hns)
        change 0 ≤ ns.max' hns
        rw [← hqi]
        exact norm_nonneg (u i)
      have hq1 : q < 1 := by
        rw [Finset.max'_lt_iff ns hns]
        intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        exact hu_mem i
      let k : ℝ := s.card
      have hk0 : 0 < k := by
        change (0 : ℝ) < (s.card : ℝ)
        exact_mod_cast Finset.card_pos.mpr hs
      let R : ℝ := max ((q + 1) / 2) (1 - 1 / k)
      have hqR : q < R := by
        apply lt_of_lt_of_le (b := (q + 1) / 2)
        · linarith
        · exact le_max_left _ _
      have hR0 : 0 < R := hq0.trans_lt hqR
      have hR1 : R < 1 := by
        rw [max_lt_iff]
        constructor
        · linarith
        · have : 0 < 1 / k := one_div_pos.mpr hk0
          linarith
      have herror : k * (1 - R) ≤ 1 := by
        have hRB : 1 - 1 / k ≤ R := le_max_right _ _
        have hk : k ≠ 0 := ne_of_gt hk0
        have : 1 - R ≤ 1 / k := by linarith
        calc
          k * (1 - R) ≤ k * (1 / k) := by gcongr
          _ = 1 := by field_simp
      let g : ℂ → ℂ := fun z ↦ f ((R : ℂ) * z)
      have hg : AnalyticOnNhd ℂ g (closedBall 0 |(1 : ℝ)|) := by
        intro z hz
        have hzle : ‖z‖ ≤ 1 := by
          simpa [mem_closedBall, dist_zero_right] using hz
        have hmap : ‖(R : ℂ) * z‖ < 1 := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR0.le]
          calc
            R * ‖z‖ ≤ R * 1 := by gcongr
            _ < 1 := by simpa using hR1
        have hfa := hf ((R : ℂ) * z) (by simpa [mem_ball, dist_zero_right] using hmap)
        have hlin : AnalyticAt ℂ (fun w : ℂ ↦ (R : ℂ) * w) z :=
          analyticAt_const.mul analyticAt_id
        simpa only [g, Function.comp_apply] using hfa.comp hlin
      have hg0 : g 0 ≠ 0 := by simpa [g] using hf0
      have hgbound : ∀ z ∈ sphere (0 : ℂ) 1, ‖g z‖ ≤ M := by
        intro z hz
        have hznorm : ‖z‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hz
        apply f_bound
        simp only [mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg hR0.le, hznorm, mul_one]
        exact hR1
      let v : ι → ℂ := fun i ↦ u i / (R : ℂ)
      have hvnorm (i : ι) : ‖v i‖ = ‖u i‖ / R := by
        simp [v, Complex.norm_real, Real.norm_of_nonneg hR0.le]
      have hvinj : Function.Injective v := by
        intro i j hij
        apply hinj
        have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hR0
        dsimp [v] at hij
        exact (div_left_inj' hRC).mp hij
      have hvmem (i : ι) (hi : i ∈ s) : ‖v i‖ < 1 := by
        rw [hvnorm]
        apply (div_lt_one hR0).mpr
        exact (Finset.le_max' ns ‖u i‖ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)).trans_lt hqR
      have hvzero (i : ι) : g (v i) = 0 := by
        have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hR0
        change f ((R : ℂ) * (u i / (R : ℂ))) = 0
        rw [show (R : ℂ) * (u i / (R : ℂ)) = u i by field_simp]
        exact hu_zero i
      have hlogsum : ∑ i ∈ s, Real.log (‖v i‖⁻¹) ≤ Real.log (M / ‖g 0‖) :=
        (finite_zero_log_weight_le_divisor hg hg0 v s hvinj.injOn hvmem
          (fun i _ ↦ hvzero i)).trans (jensen_weighted_divisor_le hM hg hg0 hgbound)
      calc
        ∑ i ∈ s, (1 - ‖u i‖) ≤
            ∑ i ∈ s, (Real.log (‖v i‖⁻¹) + (1 - R)) := by
          gcongr with i hi
          have hv0 : 0 < ‖v i‖ := by
            rw [hvnorm]
            exact div_pos (norm_pos_iff.mpr (by
              intro hui
              apply hf0
              simpa [hui] using hu_zero i)) hR0
          have hv1 : ‖v i‖ < 1 := hvmem i hi
          have hmul : R * (1 - ‖v i‖) ≤ 1 - ‖v i‖ := by
            apply mul_le_of_le_one_left (sub_nonneg.mpr hv1.le) hR1.le
          have hrel : R * ‖v i‖ = ‖u i‖ := by
            rw [hvnorm]
            field_simp
          rw [Real.log_inv]
          have hlog := Real.log_le_sub_one_of_pos hv0
          nlinarith
        _ = (∑ i ∈ s, Real.log (‖v i‖⁻¹)) + k * (1 - R) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, k]
        _ ≤ Real.log (M / ‖g 0‖) + 1 := add_le_add hlogsum herror
        _ = Real.log (M / ‖f 0‖) + 1 := by simp [g]
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.sum_empty]
      have hf0pos : 0 < ‖f 0‖ := norm_pos_iff.mpr hf0
      have hf0le : ‖f 0‖ ≤ M := f_bound 0 (by simp)
      have hratio : 1 ≤ M / ‖f 0‖ := (le_div_iff₀ hf0pos).mpr (by simpa using hf0le)
      exact add_nonneg (Real.log_nonneg hratio) zero_le_one

end RHTower

namespace RHTower

open Metric

/-- A bounded analytic function on the open unit disk, nonzero at the origin,
cannot vanish on all translated prime-log Cayley points. This is the usable
Blaschke contradiction for sectorial prime-log uniqueness. -/
theorem not_bounded_analytic_zero_on_all_primeLogCayley
    {n : ℕ} (hn : n ≠ 0) (R : ℝ) (hR : 0 ≤ R)
    {f : ℂ → ℂ} {M : ℝ} (hM : 1 ≤ M)
    (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hf0 : f 0 ≠ 0)
    (f_bound : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ M)
    (hzero : ∀ p : PrimeLogBeyond R, f (primeLogCayley n R p) = 0) : False := by
  apply primeLogCayley_defect_not_summable hn R hR
  apply summable_one_sub_norm_of_bounded_analytic_zeros_openDisk hM hf hf0 f_bound
    (primeLogCayley n R) (primeLogCayley_injective hn R)
  · intro p
    rw [norm_primeLogCayley hn]
    exact (primeLogCayley_real_pos_lt_one hn R p).2
  · exact hzero

end RHTower
namespace RHTower

open Metric Set
open Complex

def diskToRight (z : ℂ) : ℂ := (1 + z) / (1 - z)

lemma one_sub_ne_zero_of_mem_unitBall {z : ℂ} (hz : z ∈ ball 0 1) : 1 - z ≠ 0 := by
  intro h
  have : z = 1 := by linear_combination -h
  subst z
  simp at hz

lemma diskToRight_re_pos {z : ℂ} (hz : z ∈ ball 0 1) : 0 < (diskToRight z).re := by
  have hden : 1 - z ≠ 0 := one_sub_ne_zero_of_mem_unitBall hz
  have hnorm : ‖z‖ < 1 := by simpa [mem_ball, dist_zero_right] using hz
  rw [diskToRight, Complex.div_re]
  have hsq : z.re ^ 2 + z.im ^ 2 < 1 := by
    calc
      z.re ^ 2 + z.im ^ 2 = Complex.normSq z := by
        rw [Complex.normSq_apply]
        ring
      _ = ‖z‖ ^ 2 := (Complex.sq_norm z).symm
      _ < 1 := by
        simpa using (pow_lt_pow_left₀ hnorm (norm_nonneg z) two_ne_zero)
  have hnormsq : 0 < Complex.normSq (1 - z) := Complex.normSq_pos.mpr hden
  simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im,
    Complex.one_im, zero_add, Complex.sub_im, zero_sub]
  rw [← add_div]
  apply div_pos
  · nlinarith
  · exact hnormsq

lemma diskToRight_mem_slitPlane {z : ℂ} (hz : z ∈ ball 0 1) :
    diskToRight z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  exact Or.inl (diskToRight_re_pos hz)

lemma diskToRight_analyticAt {z : ℂ} (hz : z ∈ ball 0 1) :
    AnalyticAt ℂ diskToRight z := by
  unfold diskToRight
  exact (analyticAt_const.add analyticAt_id).div
    (analyticAt_const.sub analyticAt_id) (one_sub_ne_zero_of_mem_unitBall hz)

def sectorRootMap (n : ℕ) (R : ℝ) (z : ℂ) : ℂ :=
  (R : ℂ) + diskToRight z ^ ((n : ℂ)⁻¹)

lemma sectorRootMap_analyticOnNhd (n : ℕ) (R : ℝ) :
    AnalyticOnNhd ℂ (sectorRootMap n R) (ball 0 1) := by
  intro z hz
  unfold sectorRootMap
  exact analyticAt_const.add ((diskToRight_analyticAt hz).cpow analyticAt_const
    (diskToRight_mem_slitPlane hz))

lemma diskToRight_primeLogCayley
    (n : ℕ) (R : ℝ) (p : PrimeLogBeyond R) :
    diskToRight (primeLogCayley n R p) =
      ((Real.log ((p : Nat.Primes) : ℝ) - R : ℝ) ^ n : ℂ) := by
  let y : ℝ := Real.log ((p : Nat.Primes) : ℝ) - R
  have hy : 0 < y := (primeLogBeyond_base_gt_one R p).trans' zero_lt_one
  have hden : y ^ n + 1 ≠ 0 := by positivity
  unfold diskToRight primeLogCayley
  norm_cast
  change (1 + ((y ^ n - 1) / (y ^ n + 1))) /
    (1 - ((y ^ n - 1) / (y ^ n + 1))) = y ^ n
  field_simp [hden]
  ring

lemma sectorRootMap_primeLogCayley
    {n : ℕ} (hn : n ≠ 0) (R : ℝ) (p : PrimeLogBeyond R) :
    sectorRootMap n R (primeLogCayley n R p) =
      Real.log ((p : Nat.Primes) : ℝ) := by
  let y : ℝ := Real.log ((p : Nat.Primes) : ℝ) - R
  have hy : 0 < y := (primeLogBeyond_base_gt_one R p).trans' zero_lt_one
  rw [sectorRootMap, diskToRight_primeLogCayley n]
  have hroot : (((y : ℂ) ^ n) ^ ((n : ℂ)⁻¹)) = (y : ℂ) := by
    apply Complex.pow_cpow_nat_inv hn
    · rw [Complex.arg_ofReal_of_nonneg hy.le]
      have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hdivpos : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnpos
      linarith
    · rw [Complex.arg_ofReal_of_nonneg hy.le]
      have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      exact (div_pos Real.pi_pos hnpos).le
  change (R : ℂ) + (((y : ℂ) ^ n) ^ ((n : ℂ)⁻¹)) =
    (Real.log ((p : Nat.Primes) : ℝ) : ℂ)
  rw [hroot]
  exact_mod_cast (show R + y = Real.log ((p : Nat.Primes) : ℝ) by
    dsimp [y]
    ring)

end RHTower

namespace RHTower

open Metric Set

@[simp] lemma sectorRootMap_zero (n : ℕ) (R : ℝ) :
    sectorRootMap n R 0 = (R + 1 : ℝ) := by
  simp [sectorRootMap, diskToRight]

/-- Prime-log zeros force vanishing at the vertex-plus-one point whenever the
translated sector pullback is bounded and analytic on the unit disk. -/
theorem primeLog_zero_forces_sectorRootMap_zero
    {n : ℕ} (hn : n ≠ 0) (R : ℝ) (hR : 0 ≤ R)
    {H : ℂ → ℂ} {M : ℝ} (hM : 1 ≤ M)
    (hcomp : AnalyticOnNhd ℂ (fun z ↦ H (sectorRootMap n R z)) (ball 0 1))
    (hbound : ∀ z ∈ ball (0 : ℂ) 1, ‖H (sectorRootMap n R z)‖ ≤ M)
    (hzero : ∀ p : PrimeLogBeyond R,
      H (Real.log ((p : Nat.Primes) : ℝ)) = 0) :
    H (R + 1) = 0 := by
  by_contra hne
  apply not_bounded_analytic_zero_on_all_primeLogCayley hn R hR hM hcomp
  · simpa using hne
  · exact hbound
  · intro p
    rw [sectorRootMap_primeLogCayley hn]
    exact hzero p

/-- Ray form of sectorial prime-log uniqueness.  No PNT is used. -/
theorem primeLog_zero_uniqueness_on_ray
    {n : ℕ} (hn : n ≠ 0) (R₀ : ℝ) (hR₀ : 0 ≤ R₀)
    {H : ℂ → ℂ}
    (hcomp : ∀ R ≥ R₀,
      AnalyticOnNhd ℂ (fun z ↦ H (sectorRootMap n R z)) (ball 0 1))
    (hbound : ∀ R ≥ R₀, ∃ M : ℝ, 1 ≤ M ∧
      ∀ z ∈ ball (0 : ℂ) 1, ‖H (sectorRootMap n R z)‖ ≤ M)
    (hzero : ∀ p : Nat.Primes, R₀ + 1 < Real.log (p : ℝ) →
      H (Real.log (p : ℝ)) = 0) :
    ∀ x : ℝ, R₀ + 1 ≤ x → H x = 0 := by
  intro x hx
  let R : ℝ := x - 1
  have hRR₀ : R₀ ≤ R := by dsimp [R]; linarith
  have hR0 : 0 ≤ R := hR₀.trans hRR₀
  obtain ⟨M, hM, hMb⟩ := hbound R hRR₀
  have htail : ∀ p : PrimeLogBeyond R,
      H (Real.log ((p : Nat.Primes) : ℝ)) = 0 := by
    intro p
    apply hzero (p : Nat.Primes)
    have hp := primeLogBeyond_base_gt_one R p
    dsimp [R] at hp
    linarith
  have hv := primeLog_zero_forces_sectorRootMap_zero hn R hR0 hM
    (hcomp R hRR₀) hMb htail
  simpa [R] using hv

end RHTower

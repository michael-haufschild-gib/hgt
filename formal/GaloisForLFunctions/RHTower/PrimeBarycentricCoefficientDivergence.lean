import GaloisForLFunctions.RHTower.WindowBudget
import GaloisForLFunctions.RHTower.FEPairedPrimeJetBarycentricRigidity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Divergence of canonical prime barycentric coefficients

For a finite reflected prime-log support, the unique coefficient at a fixed prime `p₀` is a
barycentric product.  This file asks whether recomputing all coefficients along the canonical
exhaustion by primes `p ≤ x` can nevertheless converge coefficientwise.

It cannot.  The factors contributed by primes above `p₀` are

`(log p)^2 / ((log p)^2-(log p₀)^2) > 1 + (log p₀)^2/(log p)^2`.

The existing Chebyshev lower bound implies, without the prime number theorem,

`∑_{p≤x} 1/(log p)^2 → +∞`.

Consequently the positive tail product, and hence the magnitude of the exact barycentric
coefficient at every fixed prime, tends to infinity.  Thus even support-dependent recomputation
does not turn finite exact packets into a coefficientwise limiting Euler source.  A surviving
all-prime object must be fixed non-finitely and renormalized from the start.
-/

namespace RHTower

open Filter Finset Set Topology
open scoped BigOperators Topology

noncomputable section

def chebyshevPrimeLower (x : ℝ) : ℝ :=
  (x - 1) * Real.log 2 - Real.log (x + 2) - 2 * Real.sqrt x * Real.log x

theorem tendsto_chebyshevPrimeLower_div_id :
    Tendsto (fun x : ℝ => chebyshevPrimeLower x / x) atTop
      (𝓝 (Real.log 2)) := by
  have hmain : Tendsto (fun x : ℝ => (x - 1) * Real.log 2 / x) atTop
      (𝓝 (Real.log 2)) := by
    have hratio : Tendsto (fun x : ℝ => (x - 1) / x) atTop (𝓝 1) := by
      have h : Tendsto (fun x : ℝ => 1 - x⁻¹) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub tendsto_inv_atTop_zero
      have h' : Tendsto (fun x : ℝ => 1 - x⁻¹) atTop (𝓝 1) := by simpa using h
      apply h'.congr'
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
      field_simp
    have h := hratio.mul_const (Real.log 2)
    simpa only [one_mul] using h.congr' (by
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
      field_simp)
  have hshift : Tendsto (fun x : ℝ => x + 2) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_id
  have hlogshift : Tendsto (fun x : ℝ => Real.log (x + 2) / x) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero).comp hshift
    apply h.congr'
    filter_upwards with x
    simp only [Function.comp_apply, pow_one, one_mul]
    congr 2
    all_goals ring
  have hlogsqrt : Tendsto (fun x : ℝ => Real.log x / x ^ ((1 : ℝ) / 2)) atTop
      (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hsqrtlog : Tendsto (fun x : ℝ => 2 * Real.sqrt x * Real.log x / x) atTop
      (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => 2 * (Real.log x / x ^ ((1 : ℝ) / 2))) atTop
        (𝓝 0) := by simpa using hlogsqrt.const_mul 2
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.sqrt_eq_rpow]
    have hpow : x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2) = x := by
      rw [← Real.rpow_add hx]
      norm_num
    let s : ℝ := x ^ ((1 : ℝ) / 2)
    have hs : s ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx _)
    change 2 * (Real.log x / s) = 2 * s * Real.log x / x
    calc
      2 * (Real.log x / s) = 2 * s * Real.log x / (s * s) := by
        field_simp [hs]
      _ = 2 * s * Real.log x / x := by rw [show s * s = x by exact hpow]
  have h := hmain.sub hlogshift |>.sub hsqrtlog
  have h' : Tendsto
      (fun x : ℝ => (x - 1) * Real.log 2 / x - Real.log (x + 2) / x -
        2 * Real.sqrt x * Real.log x / x) atTop (𝓝 (Real.log 2)) := by
    simpa using h
  apply h'.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
  simp only [chebyshevPrimeLower]
  field_simp

theorem tendsto_id_div_log_cube_atTop :
    Tendsto (fun x : ℝ => x / Real.log x ^ 3) atTop atTop := by
  have hzero : Tendsto (fun x : ℝ => Real.log x ^ 3 / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 3 one_ne_zero
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < Real.log x ^ 3 / x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (pow_pos (Real.log_pos hx) 3) (lt_trans zero_lt_one hx)
  have hwithin : Tendsto (fun x : ℝ => Real.log x ^ 3 / x) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  have hinv := hwithin.inv_tendsto_nhdsGT_zero
  apply hinv.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hlog0 : Real.log x ^ 3 ≠ 0 := pow_ne_zero 3 (Real.log_pos hx).ne'
  change (Real.log x ^ 3 / x)⁻¹ = x / Real.log x ^ 3
  field_simp

theorem tendsto_chebyshevPrimeLower_div_log_cube_atTop :
    Tendsto (fun x : ℝ => chebyshevPrimeLower x / Real.log x ^ 3) atTop atTop := by
  have hprod := tendsto_chebyshevPrimeLower_div_id.pos_mul_atTop
    (Real.log_pos (by norm_num)) tendsto_id_div_log_cube_atTop
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hlog0 : Real.log x ^ 3 ≠ 0 := pow_ne_zero 3 (Real.log_pos hx).ne'
  field_simp

/-- Reciprocal squared-log mass of all primes in `(1,x]`. -/
def primeReciprocalLogSqSum (x : ℝ) : ℝ :=
  ∑ p ∈ windowPrimes 1 x, 1 / Real.log p ^ 2

theorem chebyshevPrimeLower_div_log_cube_le_primeReciprocalLogSqSum
    {x : ℝ} (hx : 2 ≤ x) :
    chebyshevPrimeLower x / Real.log x ^ 3 ≤ primeReciprocalLogSqSum x := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (lt_of_lt_of_le (by norm_num) hx)
  have htheta : chebyshevPrimeLower x ≤ Chebyshev.theta x := by
    simpa [chebyshevPrimeLower] using Chebyshev.theta_ge' hx1
  have hsumlog : ∑ p ∈ windowPrimes 1 x, Real.log p = Chebyshev.theta x := by
    have h := sum_log_windowPrimes (x := (1 : ℝ)) (y := x) hx1
    have htheta1 : Chebyshev.theta 1 = 0 := by
      rw [Chebyshev.theta]
      simp only [Nat.floor_one]
      have hfilter : (Finset.Ioc 0 1).filter Nat.Prime = ∅ := by
        ext n
        constructor
        · rintro ⟨⟨hn0, hn1⟩, hnprime⟩
        · intro hnempty
          simp at hnempty
      rw [hfilter]
      simp
    rw [htheta1, sub_zero] at h
    exact h
  calc
    chebyshevPrimeLower x / Real.log x ^ 3 ≤
        Chebyshev.theta x / Real.log x ^ 3 :=
      div_le_div_of_nonneg_right htheta (pow_nonneg hlogx.le 3)
    _ = ∑ p ∈ windowPrimes 1 x, Real.log p / Real.log x ^ 3 := by
      rw [← hsumlog, Finset.sum_div]
    _ ≤ ∑ p ∈ windowPrimes 1 x, 1 / Real.log p ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hprime, hp1, hpx⟩ :=
        (mem_windowPrimes (by norm_num : (0 : ℝ) ≤ 1) (by linarith)).mp hp
      have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp1)
      have hlogle : Real.log p ≤ Real.log x :=
        Real.log_le_log (by exact_mod_cast hprime.pos) hpx
      rw [div_le_div_iff₀ (pow_pos hlogx 3) (pow_pos hlogp 2)]
      have hcub := pow_le_pow_left₀ hlogp.le hlogle 3
      nlinarith
    _ = primeReciprocalLogSqSum x := rfl

/-- **Unconditional reciprocal-log-square prime divergence.** Chebyshev density alone forces the
prime mass `sum_{p≤x} 1/(log p)^2` to tend to infinity. -/
theorem tendsto_primeReciprocalLogSqSum_atTop :
    Tendsto primeReciprocalLogSqSum atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_
    tendsto_chebyshevPrimeLower_div_log_cube_atTop
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  exact chebyshevPrimeLower_div_log_cube_le_primeReciprocalLogSqSum hx

/-- Reciprocal squared-log mass of primes in `(p₀,x]`. -/
def primeReciprocalLogSqTailSum (p₀ : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ windowPrimes p₀ x, 1 / Real.log p ^ 2

theorem windowPrimes_one_union_tail (p₀ : ℕ) {x : ℝ} (hp₀ : 1 ≤ p₀)
    (hx : (p₀ : ℝ) ≤ x) :
    windowPrimes 1 x = windowPrimes 1 p₀ ∪ windowPrimes p₀ x := by
  ext p
  rw [Finset.mem_union]
  simp only [mem_windowPrimes (by norm_num : (0 : ℝ) ≤ 1)
      (by exact_mod_cast Nat.zero_le p₀ : (0 : ℝ) ≤ (p₀ : ℝ)),
    mem_windowPrimes (by norm_num : (0 : ℝ) ≤ 1) (by linarith),
    mem_windowPrimes
      (by exact_mod_cast Nat.zero_le p₀ : (0 : ℝ) ≤ (p₀ : ℝ)) (by linarith)]
  constructor
  · rintro ⟨hprime, hp1, hpx⟩
    by_cases hpp₀ : (p : ℝ) ≤ p₀
    · exact Or.inl ⟨hprime, hp1, hpp₀⟩
    · exact Or.inr ⟨hprime, lt_of_not_ge hpp₀, hpx⟩
  · rintro (⟨hprime, hp1, hpp₀⟩ | ⟨hprime, hp₀p, hpx⟩)
    · exact ⟨hprime, hp1, le_trans hpp₀ hx⟩
    · exact ⟨hprime, lt_of_le_of_lt (by exact_mod_cast hp₀) hp₀p, hpx⟩

theorem windowPrimes_one_disjoint_tail (p₀ : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Disjoint (windowPrimes 1 p₀) (windowPrimes p₀ x) := by
  apply Finset.disjoint_left.mpr
  intro p hphead hptail
  have hphead' := (mem_windowPrimes (by norm_num : (0 : ℝ) ≤ 1)
    (by exact_mod_cast Nat.zero_le p₀ : (0 : ℝ) ≤ (p₀ : ℝ))).mp hphead
  have hptail' := (mem_windowPrimes
    (by exact_mod_cast Nat.zero_le p₀ : (0 : ℝ) ≤ (p₀ : ℝ))
    hx).mp hptail
  linarith

theorem primeReciprocalLogSqSum_eq_head_add_tail (p₀ : ℕ) (hp₀ : 1 ≤ p₀)
    {x : ℝ} (hx : (p₀ : ℝ) ≤ x) :
    primeReciprocalLogSqSum x =
    primeReciprocalLogSqSum p₀ + primeReciprocalLogSqTailSum p₀ x := by
  have hx0 : 0 ≤ x := le_trans (by exact_mod_cast Nat.zero_le p₀) hx
  rw [primeReciprocalLogSqSum, primeReciprocalLogSqSum,
    primeReciprocalLogSqTailSum, windowPrimes_one_union_tail p₀ hp₀ hx,
    Finset.sum_union (windowPrimes_one_disjoint_tail p₀ hx0)]

theorem tendsto_primeReciprocalLogSqTailSum_atTop (p₀ : ℕ) (hp₀ : 1 ≤ p₀) :
    Tendsto (primeReciprocalLogSqTailSum p₀) atTop atTop := by
  have hdiff := tendsto_atTop_add_const_right atTop
    (-primeReciprocalLogSqSum p₀) tendsto_primeReciprocalLogSqSum_atTop
  apply hdiff.congr'
  filter_upwards [eventually_ge_atTop (p₀ : ℝ)] with x hx
  rw [primeReciprocalLogSqSum_eq_head_add_tail p₀ hp₀ hx]
  ring

/-- First-order terms in a finite product of nonnegative factors already dominate their sum. -/
theorem one_add_sum_le_prod_one_add {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u : ι → ℝ) (hu : ∀ i ∈ s, 0 ≤ u i) :
    1 + ∑ i ∈ s, u i ≤ ∏ i ∈ s, (1 + u i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hua : 0 ≤ u a := hu a (Finset.mem_insert_self a s)
      have hus : ∀ i ∈ s, 0 ≤ u i := fun i hi => hu i (Finset.mem_insert_of_mem hi)
      have hsum : 0 ≤ ∑ i ∈ s, u i := Finset.sum_nonneg hus
      have hih := ih hus
      calc
        1 + (u a + ∑ i ∈ s, u i) ≤
            (1 + u a) * (1 + ∑ i ∈ s, u i) := by nlinarith
        _ ≤ (1 + u a) * ∏ i ∈ s, (1 + u i) :=
          mul_le_mul_of_nonneg_left hih (by linarith)

/-- Positive tail product appearing in the magnitude of the barycentric coefficient at `p₀`. -/
def primeBarycentricTailGrowth (p₀ : ℕ) (x : ℝ) : ℝ :=
  ∏ q ∈ windowPrimes p₀ x,
    Real.log q ^ 2 / (Real.log q ^ 2 - Real.log p₀ ^ 2)

theorem one_add_logSq_mul_tailSum_le_primeBarycentricTailGrowth
    (p₀ : ℕ) (hp₀ : 1 < p₀) {x : ℝ} (hx : (p₀ : ℝ) ≤ x) :
    1 + Real.log p₀ ^ 2 * primeReciprocalLogSqTailSum p₀ x ≤
      primeBarycentricTailGrowth p₀ x := by
  have hp₀log : 0 < Real.log p₀ := Real.log_pos (by exact_mod_cast hp₀)
  let u : ℕ → ℝ := fun q => Real.log p₀ ^ 2 / Real.log q ^ 2
  have hu : ∀ q ∈ windowPrimes p₀ x, 0 ≤ u q := by
    intro q hq
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hfirst := one_add_sum_le_prod_one_add (windowPrimes p₀ x) u hu
  calc
    1 + Real.log p₀ ^ 2 * primeReciprocalLogSqTailSum p₀ x =
        1 + ∑ q ∈ windowPrimes p₀ x, u q := by
      rw [primeReciprocalLogSqTailSum, Finset.mul_sum]
      simp [u, div_eq_mul_inv]
    _ ≤ ∏ q ∈ windowPrimes p₀ x, (1 + u q) := hfirst
    _ ≤ ∏ q ∈ windowPrimes p₀ x,
        Real.log q ^ 2 / (Real.log q ^ 2 - Real.log p₀ ^ 2) := by
      apply Finset.prod_le_prod
      · intro q hq
        linarith [hu q hq]
      · intro q hq
        obtain ⟨hprime, hp₀q, hqx⟩ :=
          (mem_windowPrimes (by exact_mod_cast Nat.zero_le p₀ :
              (0 : ℝ) ≤ (p₀ : ℝ)) (by linarith)).mp hq
        have hq1 : (1 : ℝ) < q := lt_trans (by exact_mod_cast hp₀) hp₀q
        have hqlog : 0 < Real.log q := Real.log_pos hq1
        have hloglt : Real.log p₀ < Real.log q :=
          Real.strictMonoOn_log
            (by change (0 : ℝ) < p₀
                exact_mod_cast Nat.zero_lt_one.trans hp₀)
            (by change (0 : ℝ) < q
                exact_mod_cast hprime.pos)
            hp₀q
        have hsq : Real.log p₀ ^ 2 < Real.log q ^ 2 := by nlinarith
        have hden : 0 < Real.log q ^ 2 - Real.log p₀ ^ 2 := sub_pos.mpr hsq
        have hcomp : u q ≤
            Real.log p₀ ^ 2 / (Real.log q ^ 2 - Real.log p₀ ^ 2) := by
          dsimp [u]
          rw [div_le_div_iff₀ (sq_pos_of_pos hqlog) hden]
          nlinarith [sq_nonneg (Real.log p₀)]
        have hfactor : Real.log q ^ 2 /
              (Real.log q ^ 2 - Real.log p₀ ^ 2) =
            1 + Real.log p₀ ^ 2 /
              (Real.log q ^ 2 - Real.log p₀ ^ 2) := by
          field_simp [hden.ne']
          ring
        rw [hfactor]
        linarith
    _ = primeBarycentricTailGrowth p₀ x := rfl

/-- **The barycentric prime tail product diverges.** -/
theorem tendsto_primeBarycentricTailGrowth_atTop (p₀ : ℕ) (hp₀ : 1 < p₀) :
    Tendsto (primeBarycentricTailGrowth p₀) atTop atTop := by
  have hc : 0 < Real.log p₀ ^ 2 := sq_pos_of_pos (Real.log_pos (by exact_mod_cast hp₀))
  have hmul := tendsto_const_nhds.pos_mul_atTop hc
    (tendsto_primeReciprocalLogSqTailSum_atTop p₀ (Nat.one_le_iff_ne_zero.mpr
      (by omega)))
  have hadd := tendsto_atTop_add_const_left atTop (1 : ℝ) hmul
  refine tendsto_atTop_mono' atTop ?_ hadd
  filter_upwards [eventually_ge_atTop (p₀ : ℝ)] with x hx
  exact one_add_logSq_mul_tailSum_le_primeBarycentricTailGrowth p₀ hp₀ hx

/-- Magnitude of the canonical barycentric coefficient at `p₀` on the prime support `(1,x]`. -/
def primeBarycentricCoefficientMagnitude (p₀ : ℕ) (x : ℝ) : ℝ :=
  (1 / (2 * Real.log p₀)) *
    ∏ q ∈ (windowPrimes 1 x).erase p₀,
      Real.log q ^ 2 / |Real.log p₀ ^ 2 - Real.log q ^ 2|

theorem primeBarycentricCoefficientMagnitude_head_pos (p₀ : ℕ) (hp₀ : p₀.Prime) :
    0 < primeBarycentricCoefficientMagnitude p₀ p₀ := by
  have hp₀log : 0 < Real.log p₀ := Real.log_pos (by exact_mod_cast hp₀.one_lt)
  apply mul_pos (div_pos one_pos (mul_pos (by norm_num) hp₀log))
  apply Finset.prod_pos
  intro q hq
  have hqmem := Finset.mem_of_mem_erase hq
  have hqne : q ≠ p₀ := Finset.ne_of_mem_erase hq
  obtain ⟨hqprime, hq1, hqp₀⟩ :=
    (mem_windowPrimes (by norm_num : (0 : ℝ) ≤ 1)
      (by exact_mod_cast Nat.zero_le p₀ : (0 : ℝ) ≤ (p₀ : ℝ))).mp hqmem
  have hqlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq1)
  have hlogne : Real.log p₀ ^ 2 ≠ Real.log q ^ 2 := by
    intro h
    have hlogs : Real.log p₀ = Real.log q := by nlinarith
    have hpq : p₀ = q := by
      exact_mod_cast Real.log_injOn_pos
        (by exact_mod_cast hp₀.pos : (0 : ℝ) < p₀)
        (by exact_mod_cast hqprime.pos : (0 : ℝ) < q) hlogs
    exact hqne hpq.symm
  exact div_pos (sq_pos_of_pos hqlog) (abs_pos.mpr (sub_ne_zero.mpr hlogne))

theorem primeBarycentricCoefficientMagnitude_eq_head_mul_tail
    (p₀ : ℕ) (hp₀ : p₀.Prime) {x : ℝ} (hx : (p₀ : ℝ) ≤ x) :
    primeBarycentricCoefficientMagnitude p₀ x =
      primeBarycentricCoefficientMagnitude p₀ p₀ *
        primeBarycentricTailGrowth p₀ x := by
  have hx0 : 0 ≤ x := le_trans (by exact_mod_cast Nat.zero_le p₀) hx
  have hp₀notTail : p₀ ∉ windowPrimes p₀ x := by
    intro hmem
    have h := (mem_windowPrimes
      (by exact_mod_cast Nat.zero_le p₀ : (0 : ℝ) ≤ (p₀ : ℝ)) hx0).mp hmem
    exact (lt_irrefl (p₀ : ℝ)) h.2.1
  have herase : (windowPrimes 1 x).erase p₀ =
      (windowPrimes 1 p₀).erase p₀ ∪ windowPrimes p₀ x := by
    rw [windowPrimes_one_union_tail p₀ hp₀.one_le hx,
      Finset.erase_union_distrib, Finset.erase_eq_of_notMem hp₀notTail]
  have hdisj : Disjoint ((windowPrimes 1 p₀).erase p₀) (windowPrimes p₀ x) :=
    (windowPrimes_one_disjoint_tail p₀ hx0).mono_left (Finset.erase_subset _ _)
  rw [primeBarycentricCoefficientMagnitude, primeBarycentricCoefficientMagnitude,
    primeBarycentricTailGrowth, herase, Finset.prod_union hdisj]
  have htail :
      (∏ q ∈ windowPrimes p₀ x,
          Real.log q ^ 2 / |Real.log p₀ ^ 2 - Real.log q ^ 2|) =
        ∏ q ∈ windowPrimes p₀ x,
          Real.log q ^ 2 / (Real.log q ^ 2 - Real.log p₀ ^ 2) := by
    apply Finset.prod_congr rfl
    intro q hq
    obtain ⟨hqprime, hp₀q, hqx⟩ :=
      (mem_windowPrimes
        (by exact_mod_cast Nat.zero_le p₀ : (0 : ℝ) ≤ (p₀ : ℝ)) hx0).mp hq
    have hp₀log : 0 < Real.log p₀ := Real.log_pos (by exact_mod_cast hp₀.one_lt)
    have hqlog : 0 < Real.log q :=
      Real.log_pos (lt_trans (by exact_mod_cast hp₀.one_lt) hp₀q)
    have hloglt : Real.log p₀ < Real.log q :=
      Real.strictMonoOn_log
        (by change (0 : ℝ) < p₀
            exact_mod_cast hp₀.pos)
        (by change (0 : ℝ) < q
            exact_mod_cast hqprime.pos)
        hp₀q
    have hneg : Real.log p₀ ^ 2 - Real.log q ^ 2 < 0 := by nlinarith
    rw [abs_of_neg hneg]
    ring_nf
  rw [htail]
  ring

/-- **Canonical coefficient divergence.** For every fixed prime `p₀`, the exact barycentric
coefficient magnitude on all prime supports `(1,x]` tends to infinity. -/
theorem tendsto_primeBarycentricCoefficientMagnitude_atTop
    (p₀ : ℕ) (hp₀ : p₀.Prime) :
    Tendsto (primeBarycentricCoefficientMagnitude p₀) atTop atTop := by
  have hhead := primeBarycentricCoefficientMagnitude_head_pos p₀ hp₀
  have hprod := tendsto_const_nhds.pos_mul_atTop hhead
    (tendsto_primeBarycentricTailGrowth_atTop p₀ hp₀.one_lt)
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop (p₀ : ℝ)] with x hx
  exact (primeBarycentricCoefficientMagnitude_eq_head_mul_tail p₀ hp₀ hx).symm

end

end RHTower


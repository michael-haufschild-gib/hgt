import GaloisForLFunctions.HTGeometry.PrimeSieveRegularDeterminant

/-!
# The source transition size of a commuting prime sieve

The transition from a finite sieve to its one-prime enlargement has two
channels: the singular density loss `a_P / p` and the regular determinant
increment, whose size on a closed subdisk is the supremum of the decimated
logarithm.  Their sum is the source transition size.

Along every enumeration of the primes the transition sizes are summable: the
singular losses telescope to one, and the regular increments are bounded by a
constant times the inverse cube of the adjoined prime.

The same estimates show that the naive independent one-prime reporter is not a
replacement.  Its regular channel converges to the unsieved logarithm, which is
strictly negative on the positive part of the disk, so the independent defects do
not tend to the identity and their sum diverges; its singular channel is the
divergent sum of prime reciprocals.  Only the nested sieve has summable
transitions.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

section Bound

/-- The universal regular transition constant on the closed subdisk of radius
`r`. -/
noncomputable def sieveRegularConstant (r : ℝ) : ℝ :=
  2 * sieveTraceBound / (1 - r ^ (2 : ℕ)) * r ^ (3 : ℕ)

theorem sieveRegularConstant_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    0 ≤ sieveRegularConstant r := by
  have hden : (0 : ℝ) < 1 - r ^ (2 : ℕ) := by nlinarith
  rw [sieveRegularConstant]
  have : (0 : ℝ) ≤ 2 * sieveTraceBound / (1 - r ^ (2 : ℕ)) :=
    div_nonneg (by linarith [sieveTraceBound_nonneg]) hden.le
  positivity

/-- The decimated logarithm is bounded by the regular transition constant over
the cube of the prime. -/
theorem abs_sieveLogPhi_div_le (P : Finset Nat.Primes) {r t : ℝ} (hr0 : 0 ≤ r)
    (hr : r < 1) (ht : |t| ≤ r) (p : Nat.Primes) :
    |sieveLogPhi P (t / ((p : ℕ) : ℝ))|
      ≤ sieveRegularConstant r / ((p : ℕ) : ℝ) ^ (3 : ℕ) := by
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  have htp : |t / ((p : ℕ) : ℝ)| ≤ r := by
    rw [abs_div, abs_of_nonneg hppos.le, div_le_iff₀ hppos]
    nlinarith [abs_nonneg t]
  refine (abs_sieveLogPhi_le P hr0 hr htp).trans ?_
  have hcube : |t / ((p : ℕ) : ℝ)| ^ (3 : ℕ) ≤ r ^ (3 : ℕ) / ((p : ℕ) : ℝ) ^ (3 : ℕ) := by
    rw [abs_div, abs_of_nonneg hppos.le, div_pow]
    gcongr
  have hden : (0 : ℝ) < 1 - r ^ (2 : ℕ) := by nlinarith
  have hcoef : (0 : ℝ) ≤ 2 * sieveTraceBound / (1 - r ^ (2 : ℕ)) :=
    div_nonneg (by linarith [sieveTraceBound_nonneg]) hden.le
  calc 2 * sieveTraceBound / (1 - r ^ (2 : ℕ)) * |t / ((p : ℕ) : ℝ)| ^ (3 : ℕ)
      ≤ 2 * sieveTraceBound / (1 - r ^ (2 : ℕ)) * (r ^ (3 : ℕ) / ((p : ℕ) : ℝ) ^ (3 : ℕ)) :=
        mul_le_mul_of_nonneg_left hcube hcoef
    _ = sieveRegularConstant r / ((p : ℕ) : ℝ) ^ (3 : ℕ) := by
        rw [sieveRegularConstant]; ring

end Bound

section TransitionSize

/-- **The source transition size.**  The singular density loss plus the regular
determinant increment on the closed subdisk of radius `r`. -/
noncomputable def sieveTransitionSize (r : ℝ) (P : Finset Nat.Primes)
    (p : Nat.Primes) : ℝ :=
  sieveDensity P / ((p : ℕ) : ℝ)
    + sSup ((fun t : ℝ => |sieveLogPhi P (t / ((p : ℕ) : ℝ))|) '' Set.Icc (-r) r)

theorem sSup_abs_sieveLogPhi_nonneg (r : ℝ) (P : Finset Nat.Primes)
    (p : Nat.Primes) :
    0 ≤ sSup ((fun t : ℝ => |sieveLogPhi P (t / ((p : ℕ) : ℝ))|) '' Set.Icc (-r) r) := by
  refine Real.sSup_nonneg ?_
  rintro x ⟨t, -, rfl⟩
  exact abs_nonneg _

theorem sSup_abs_sieveLogPhi_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (P : Finset Nat.Primes) (p : Nat.Primes) :
    sSup ((fun t : ℝ => |sieveLogPhi P (t / ((p : ℕ) : ℝ))|) '' Set.Icc (-r) r)
      ≤ sieveRegularConstant r / ((p : ℕ) : ℝ) ^ (3 : ℕ) := by
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  refine Real.sSup_le ?_ (by
    have := sieveRegularConstant_nonneg hr0 hr
    positivity)
  rintro x ⟨t, ht, rfl⟩
  rw [Set.mem_Icc] at ht
  exact abs_sieveLogPhi_div_le P hr0 hr (abs_le.mpr ⟨ht.1, ht.2⟩) p

theorem sieveTransitionSize_nonneg (r : ℝ) (P : Finset Nat.Primes)
    (p : Nat.Primes) : 0 ≤ sieveTransitionSize r P p := by
  have h1 : 0 ≤ sieveDensity P / ((p : ℕ) : ℝ) := by
    have := (sieveDensity_pos P).le
    have hp : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := by positivity
    positivity
  exact add_nonneg h1 (sSup_abs_sieveLogPhi_nonneg r P p)

theorem sieveTransitionSize_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (P : Finset Nat.Primes) (p : Nat.Primes) :
    sieveTransitionSize r P p
      ≤ sieveDensity P / ((p : ℕ) : ℝ)
        + sieveRegularConstant r / ((p : ℕ) : ℝ) ^ (3 : ℕ) := by
  rw [sieveTransitionSize]
  linarith [sSup_abs_sieveLogPhi_le hr0 hr P p]

end TransitionSize

section Summability

variable (e : ℕ ≃ Nat.Primes)

theorem injective_primeIndex : Function.Injective fun n : ℕ => ((e n : ℕ)) := by
  intro a b hab
  exact e.injective (Subtype.ext hab)

/-- The prime indices of an enumeration are cofinal. -/
theorem tendsto_primeIndex_atTop :
    Tendsto (fun n : ℕ => ((e n : ℕ))) atTop atTop := by
  have h := (injective_primeIndex e).tendsto_cofinite
  rwa [Nat.cofinite_eq_atTop] at h

/-- The inverse cubes of the primes are summable. -/
theorem summable_primeIndex_cube_inv :
    Summable fun n : ℕ => (((e n : ℕ) : ℝ) ^ (3 : ℕ))⁻¹ := by
  have hbase : Summable fun m : ℕ => (((m : ℕ) : ℝ) ^ (3 : ℕ))⁻¹ :=
    summable_natPow_inv (by norm_num)
  exact hbase.comp_injective (injective_primeIndex e)

/-- **Summable source transitions.**  Along every enumeration of the primes the
source transition sizes of the nested sieve are summable. -/
theorem summable_sieveTransitionSize {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable fun n : ℕ => sieveTransitionSize r (sievePrefix e n) (e n) := by
  have hsing : Summable fun n : ℕ =>
      sieveDensity (sievePrefix e n) / ((e n : ℕ) : ℝ) :=
    (hasSum_sieveDensity_div_prime e).summable
  have hreg : Summable fun n : ℕ =>
      sieveRegularConstant r / (((e n : ℕ) : ℝ)) ^ (3 : ℕ) := by
    refine ((summable_primeIndex_cube_inv e).mul_left (sieveRegularConstant r)).congr
      fun n => ?_
    rw [div_eq_mul_inv]
  refine Summable.of_nonneg_of_le (fun n => sieveTransitionSize_nonneg r _ _)
    (fun n => sieveTransitionSize_le hr0 hr _ _) (hsing.add hreg)

end Summability

section NaiveNoGo

theorem sieveTrace_empty_pos {k : ℕ} (hk : 1 < k) : 0 < sieveTrace ∅ k := by
  rw [sieveTrace_eq_mul_prod hk, Finset.prod_empty, mul_one]
  refine Summable.tsum_pos (summable_natPow_inv hk) (fun n => by positivity) 1 ?_
  norm_num

/-- The unsieved logarithm is strictly negative on the positive part of the
disk. -/
theorem sieveLogPhi_empty_neg {t : ℝ} (ht0 : 0 < t) (ht : t < 1) :
    sieveLogPhi ∅ t < 0 := by
  have habs : |t| < 1 := by rw [abs_of_pos ht0]; exact ht
  have hpos : 0 < ∑' j : ℕ,
      t ^ (2 * j + 3) / ((2 * j + 3 : ℕ) : ℝ) * sieveTrace ∅ (2 * j + 3) := by
    refine Summable.tsum_pos (summable_sieveLogPhi_term ∅ habs) (fun j => ?_) 0 ?_
    · have := (sieveTrace_nonneg ∅ (2 * j + 3))
      positivity
    · have h3 : 0 < sieveTrace ∅ (2 * 0 + 3) := sieveTrace_empty_pos (by omega)
      have : (0 : ℝ) < t ^ (2 * 0 + 3) / ((2 * 0 + 3 : ℕ) : ℝ) := by positivity
      exact mul_pos this h3
  rw [sieveLogPhi]
  linarith

/-- The independent one-prime regular defect converges to the unsieved
logarithm, not to the identity. -/
theorem tendsto_naiveRegularDefect (e : ℕ ≃ Nat.Primes) {r t : ℝ} (hr0 : 0 ≤ r)
    (hr : r < 1) (ht : |t| ≤ r) :
    Tendsto (fun n : ℕ =>
        sieveLogPhi ∅ t - sieveLogPhi ∅ (t / ((e n : ℕ) : ℝ))) atTop
      (𝓝 (sieveLogPhi ∅ t)) := by
  have hcube : Tendsto (fun n : ℕ =>
      sieveRegularConstant r / (((e n : ℕ) : ℝ)) ^ (3 : ℕ)) atTop (𝓝 0) := by
    have h := (summable_primeIndex_cube_inv e).tendsto_atTop_zero
    have h2 := h.const_mul (sieveRegularConstant r)
    rw [mul_zero] at h2
    exact h2.congr fun n => by rw [div_eq_mul_inv]
  have hzero : Tendsto (fun n : ℕ => sieveLogPhi ∅ (t / ((e n : ℕ) : ℝ))) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hcube
    rw [Real.norm_eq_abs]
    exact abs_sieveLogPhi_div_le ∅ hr0 hr ht (e n)
  simpa using (tendsto_const_nhds (x := sieveLogPhi ∅ t) (f := atTop (α := ℕ))).sub hzero

/-- **The naive independent one-prime regular channel diverges.**  Its defects do
not tend to the identity, so their sum cannot converge. -/
theorem not_summable_naiveRegularDefect (e : ℕ ≃ Nat.Primes) {r t : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1) (ht : |t| ≤ r) (ht0 : 0 < t) (ht1 : t < 1) :
    ¬ Summable fun n : ℕ =>
        sieveLogPhi ∅ t - sieveLogPhi ∅ (t / ((e n : ℕ) : ℝ)) := by
  intro hsum
  have hzero := hsum.tendsto_atTop_zero
  have hlim := tendsto_naiveRegularDefect e hr0 hr ht
  have := tendsto_nhds_unique hzero hlim
  exact absurd this.symm (sieveLogPhi_empty_neg ht0 ht1).ne

/-- **The naive independent one-prime singular channel diverges.**  The
independent singular defects are the prime reciprocals, which are not
summable. -/
theorem not_summable_naiveSingularDefect (e : ℕ ≃ Nat.Primes) :
    ¬ Summable fun n : ℕ => 1 - (1 - (((e n : ℕ) : ℝ))⁻¹) := by
  intro hsum
  refine Nat.Primes.not_summable_one_div ?_
  have hre := (e.summable_iff (f := fun p : Nat.Primes => ((p : ℕ) : ℝ)⁻¹)).mp
    (hsum.congr fun n => by simp)
  simpa [one_div] using hre

end NaiveNoGo

end GaloisForLFunctions.HTGeometry

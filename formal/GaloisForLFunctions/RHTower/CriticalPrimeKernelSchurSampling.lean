import GaloisForLFunctions.RHTower.CriticalPrimeKernelSamplingCompact
import GaloisForLFunctions.RHTower.Sieve.AlmostOrthogonality

open scoped InnerProductSpace

namespace RHTower

noncomputable section

open ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Uniform finite Gram-row bounds make an arbitrary Hilbert family Bessel. -/
theorem summable_norm_inner_sq_of_forall_finset_gram_row_le
    (φ : ι → H) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hrow : ∀ (r : ι) (T : Finset ι),
      ∑ t ∈ T, ‖inner ℂ (φ r) (φ t)‖ ≤ Δ)
    (x : H) :
    Summable fun r => ‖inner ℂ (φ r) x‖ ^ 2 := by
  refine summable_of_sum_le (c := Δ * ‖x‖ ^ 2) (fun r => by positivity) fun T => ?_
  exact Sieve.sum_norm_inner_sq_le_of_schur T φ hΔ
    (fun r _ => hrow r T) x

/-- Infinite Bessel bound obtained from the same finite Gram-row certificate. -/
theorem tsum_norm_inner_sq_le_of_forall_finset_gram_row_le
    (φ : ι → H) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hrow : ∀ (r : ι) (T : Finset ι),
      ∑ t ∈ T, ‖inner ℂ (φ r) (φ t)‖ ≤ Δ)
    (x : H) :
    ∑' r, ‖inner ℂ (φ r) x‖ ^ 2 ≤ Δ * ‖x‖ ^ 2 := by
  have hsum := summable_norm_inner_sq_of_forall_finset_gram_row_le φ hΔ hrow x
  exact le_of_tendsto hsum.hasSum (Filter.Eventually.of_forall fun T =>
    Sieve.sum_norm_inner_sq_le_of_schur T φ hΔ (fun r _ => hrow r T) x)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Weighted normalized kernel vector whose analysis coefficient is the critical-prime
restriction. -/
def criticalPrimeWeightedKernel (k : Nat.Primes → H) (p : Nat.Primes) : H :=
  (Real.sqrt (criticalPrimeSamplingWeight p) : ℂ) • k p

theorem inner_criticalPrimeWeightedKernel
    (k : Nat.Primes → H) (p : Nat.Primes) (x : H) :
    inner ℂ (criticalPrimeWeightedKernel k p) x =
      criticalPrimeKernelRestriction k p x := by
  rw [criticalPrimeWeightedKernel, criticalPrimeKernelRestriction_apply, inner_smul_left]
  simp

/-- A finite Gram-row estimate constructs pointwise square-summability of the literal normalized
critical-prime restriction family. -/
theorem criticalPrimeKernelSampling_summable_of_gram_row_le
    (k : Nat.Primes → H) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hrow : ∀ (p : Nat.Primes) (T : Finset Nat.Primes),
      ∑ q ∈ T,
        ‖inner ℂ (criticalPrimeWeightedKernel k p)
          (criticalPrimeWeightedKernel k q)‖ ≤ Δ)
    (x : H) :
    Summable fun p => ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ) := by
  simpa [inner_criticalPrimeWeightedKernel] using
    (summable_norm_inner_sq_of_forall_finset_gram_row_le
      (criticalPrimeWeightedKernel k) hΔ hrow x)

/-- The literal normalized prime sampler has Bessel constant `sqrt Δ` under a finite Gram-row
certificate. -/
theorem criticalPrimeKernelSampling_tsum_le_of_gram_row_le
    (k : Nat.Primes → H) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hrow : ∀ (p : Nat.Primes) (T : Finset Nat.Primes),
      ∑ q ∈ T,
        ‖inner ℂ (criticalPrimeWeightedKernel k p)
          (criticalPrimeWeightedKernel k q)‖ ≤ Δ)
    (x : H) :
    ∑' p, ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ) ≤
      (Real.sqrt Δ * ‖x‖) ^ (2 : ℝ) := by
  have h := tsum_norm_inner_sq_le_of_forall_finset_gram_row_le
    (criticalPrimeWeightedKernel k) hΔ hrow x
  have hrhs : (Real.sqrt Δ * ‖x‖) ^ (2 : ℝ) =
      (Real.sqrt Δ * ‖x‖) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  rw [hrhs, mul_pow, Real.sq_sqrt hΔ]
  simpa [inner_criticalPrimeWeightedKernel] using h

/-- Deleting a finite prime head turns a tail Gram-row certificate into the corresponding tail
Bessel estimate. -/
theorem criticalPrimeKernelSampling_tail_tsum_le_of_gram_row_le
    (k : Nat.Primes → H) (P : Finset Nat.Primes) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hrow : ∀ p : Nat.Primes, p ∉ P → ∀ T : Finset Nat.Primes,
      ∑ q ∈ T.filter (· ∉ P),
        ‖inner ℂ (criticalPrimeWeightedKernel k p)
          (criticalPrimeWeightedKernel k q)‖ ≤ Δ)
    (x : H) :
    ∑' p, ‖if p ∈ P then 0 else criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ) ≤
      (Real.sqrt Δ * ‖x‖) ^ (2 : ℝ) := by
  let φ : Nat.Primes → H := fun p => if p ∈ P then 0 else criticalPrimeWeightedKernel k p
  have hφrow : ∀ (p : Nat.Primes) (T : Finset Nat.Primes),
      ∑ q ∈ T, ‖inner ℂ (φ p) (φ q)‖ ≤ Δ := by
    intro p T
    by_cases hp : p ∈ P
    · simpa [φ, hp] using hΔ
    · have h := hrow p hp T
      rw [Finset.sum_filter] at h
      simpa [φ, hp, apply_ite, ite_apply] using h
  have h := tsum_norm_inner_sq_le_of_forall_finset_gram_row_le φ hΔ hφrow x
  have hrhs : (Real.sqrt Δ * ‖x‖) ^ (2 : ℝ) =
      (Real.sqrt Δ * ‖x‖) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  rw [hrhs, mul_pow, Real.sq_sqrt hΔ]
  have hleft :
      (∑' p, ‖if p ∈ P then 0 else criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ)) =
        ∑' p, ‖inner ℂ (φ p) x‖ ^ 2 := by
    apply tsum_congr
    intro p
    by_cases hp : p ∈ P <;> simp [φ, hp, inner_criticalPrimeWeightedKernel]
  rw [hleft]
  exact h

/-- Literal normalized critical-prime sampling operator constructed solely from a finite Gram-row
bound. -/
def criticalPrimeKernelSchurSamplingOperator
    (k : Nat.Primes → H) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hrow : ∀ (p : Nat.Primes) (T : Finset Nat.Primes),
      ∑ q ∈ T,
        ‖inner ℂ (criticalPrimeWeightedKernel k p)
          (criticalPrimeWeightedKernel k q)‖ ≤ Δ) :
    H →L[ℂ] CriticalPrimeEllTwo :=
  criticalPrimeKernelSamplingOperator k
    (criticalPrimeKernelSampling_summable_of_gram_row_le k hΔ hrow)
    (Real.sqrt_nonneg Δ)
    (criticalPrimeKernelSampling_tsum_le_of_gram_row_le k hΔ hrow)

@[simp] theorem criticalPrimeKernelSchurSamplingOperator_apply
    (k : Nat.Primes → H) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hrow : ∀ (p : Nat.Primes) (T : Finset Nat.Primes),
      ∑ q ∈ T,
        ‖inner ℂ (criticalPrimeWeightedKernel k p)
          (criticalPrimeWeightedKernel k q)‖ ≤ Δ)
    (x : H) (p : Nat.Primes) :
    criticalPrimeKernelSchurSamplingOperator k hΔ hrow x p =
      criticalPrimeKernelRestriction k p x := rfl

/-- Vanishing finite-tail Gram rows make the Schur-constructed normalized sampler compact. -/
theorem criticalPrimeKernelSchurSamplingOperator_isCompactOperator_of_tail_gram_row
    (k : Nat.Primes → H) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hrow : ∀ (p : Nat.Primes) (T : Finset Nat.Primes),
      ∑ q ∈ T,
        ‖inner ℂ (criticalPrimeWeightedKernel k p)
          (criticalPrimeWeightedKernel k q)‖ ≤ Δ)
    (P : ℕ → Finset Nat.Primes) (δ : ℕ → ℝ)
    (hδ : ∀ n, 0 ≤ δ n) (hδ0 : Filter.Tendsto δ Filter.atTop (nhds 0))
    (htailRow : ∀ n (p : Nat.Primes), p ∉ P n → ∀ T : Finset Nat.Primes,
      ∑ q ∈ T.filter (· ∉ P n),
        ‖inner ℂ (criticalPrimeWeightedKernel k p)
          (criticalPrimeWeightedKernel k q)‖ ≤ δ n) :
    IsCompactOperator (criticalPrimeKernelSchurSamplingOperator k hΔ hrow) := by
  unfold criticalPrimeKernelSchurSamplingOperator
  apply criticalPrimeKernelSamplingOperator_isCompactOperator_of_tailBessel
    k (criticalPrimeKernelSampling_summable_of_gram_row_le k hΔ hrow)
    (Real.sqrt_nonneg Δ)
    (criticalPrimeKernelSampling_tsum_le_of_gram_row_le k hΔ hrow)
    P (fun n => Real.sqrt (δ n))
  · exact fun n => Real.sqrt_nonneg _
  · simpa [Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hδ0
  · intro n x
    exact criticalPrimeKernelSampling_tail_tsum_le_of_gram_row_le
      k (P n) (hδ n) (htailRow n) x

variable [CompleteSpace H]

/-- Unit normalized kernels force the Schur-constructed sampler outside Hilbert--Schmidt class. -/
theorem criticalPrimeKernelSchurSamplingOperator_not_isHilbertSchmidt
    (k : Nat.Primes → H) (hk : ∀ p, ‖k p‖ = 1)
    {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hrow : ∀ (p : Nat.Primes) (T : Finset Nat.Primes),
      ∑ q ∈ T,
        ‖inner ℂ (criticalPrimeWeightedKernel k p)
          (criticalPrimeWeightedKernel k q)‖ ≤ Δ) :
    ¬ (criticalPrimeKernelSchurSamplingOperator k hΔ hrow).IsHilbertSchmidt := by
  unfold criticalPrimeKernelSchurSamplingOperator
  exact criticalPrimeKernelSamplingOperator_not_isHilbertSchmidt k hk
    (criticalPrimeKernelSampling_summable_of_gram_row_le k hΔ hrow)
    (Real.sqrt_nonneg Δ)
    (criticalPrimeKernelSampling_tsum_le_of_gram_row_le k hΔ hrow)

/-- Positive Gram incidence of the Schur-constructed sampler is never trace class. -/
theorem criticalPrimeKernelSchurSamplingIncidence_not_memSchattenClass_one
    (k : Nat.Primes → H) (hk : ∀ p, ‖k p‖ = 1)
    {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hrow : ∀ (p : Nat.Primes) (T : Finset Nat.Primes),
      ∑ q ∈ T,
        ‖inner ℂ (criticalPrimeWeightedKernel k p)
          (criticalPrimeWeightedKernel k q)‖ ≤ Δ) :
    ¬ MemSchattenClass 1 (criticalPrimeSamplingIncidence
      (criticalPrimeKernelSchurSamplingOperator k hΔ hrow)) := by
  unfold criticalPrimeKernelSchurSamplingOperator
  exact criticalPrimeKernelSamplingIncidence_not_memSchattenClass_one k hk
    (criticalPrimeKernelSampling_summable_of_gram_row_le k hΔ hrow)
    (Real.sqrt_nonneg Δ)
    (criticalPrimeKernelSampling_tsum_le_of_gram_row_le k hΔ hrow)

end

end RHTower

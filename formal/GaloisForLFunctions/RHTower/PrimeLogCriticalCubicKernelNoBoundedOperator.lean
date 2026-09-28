import GaloisForLFunctions.RHTower.PrimeLogCriticalCubicKernelUnboundedness
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# No bounded operator on `ℓ²(Primes)` carries the critical cubic prime kernel

`PrimeLogCriticalCubicKernelUnboundedness` proves the Rayleigh growth
`∑_{p,q ∈ S_n} h(p) h(q) c(p,q)³ ≥ M_n² / 8` with `M_n → ∞`.  This module turns it into the
operator statement of (PLCCKU): no bounded operator on `ℓ²(Primes)` has matrix coefficients

`K(p, q) = √(h(p) h(q)) · c(p, q)³`,   `h(p) = log p / p`,
`c(p, q) = 2 √(log p log q) / (log p + log q)`.
-/

open scoped InnerProductSpace

namespace RHTower

noncomputable section

open Finset

/-- Critical first-clock weight `h(p) = log p / p`. -/
def primeLogCriticalWeight (p : ℕ) : ℝ := Real.log (p : ℝ) / (p : ℝ)

theorem primeLogCriticalWeight_nonneg (p : ℕ) : 0 ≤ primeLogCriticalWeight p :=
  div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

/-- **(PLCCKU.1)** The raw critical cubic prime kernel. -/
def primeLogCriticalCubicKernel (p q : Nat.Primes) : ℝ :=
  Real.sqrt (primeLogCriticalWeight p * primeLogCriticalWeight q) *
    primeLogCriticalCubicCorrelation p q

/-- The critical block `S_n` as a finite set of primes. -/
def primeLogCriticalPrimeBlock (n : ℕ) : Finset Nat.Primes :=
  (primeLogCriticalBlock n).subtype Nat.Prime

theorem prime_of_mem_primeLogCriticalBlock {n p : ℕ} (hp : p ∈ primeLogCriticalBlock n) :
    p.Prime := by
  unfold primeLogCriticalBlock at hp
  exact (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2

theorem sum_primeLogCriticalPrimeBlock {n : ℕ} (f : ℕ → ℝ) :
    ∑ p ∈ primeLogCriticalPrimeBlock n, f p = ∑ p ∈ primeLogCriticalBlock n, f p :=
  Finset.sum_subtype_of_mem f fun _ hp => prime_of_mem_primeLogCriticalBlock hp

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The test vector `∑_{p ∈ S_n} √h(p) e_p`. -/
def primeLogCriticalTestVector (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) : lp (fun _ : Nat.Primes => 𝕜) 2 :=
  ∑ p ∈ primeLogCriticalPrimeBlock n,
    lp.single 2 p ((Real.sqrt (primeLogCriticalWeight p) : ℝ) : 𝕜)

/-- Bilinear expansion of a quadratic form on the test vector. -/
theorem inner_primeLogCriticalTestVector_apply
    (T : lp (fun _ : Nat.Primes => 𝕜) 2 →L[𝕜] lp (fun _ : Nat.Primes => 𝕜) 2) (n : ℕ) :
    ⟪primeLogCriticalTestVector 𝕜 n, T (primeLogCriticalTestVector 𝕜 n)⟫_𝕜 =
      ∑ p ∈ primeLogCriticalPrimeBlock n, ∑ q ∈ primeLogCriticalPrimeBlock n,
        ((Real.sqrt (primeLogCriticalWeight p) * Real.sqrt (primeLogCriticalWeight q) : ℝ) : 𝕜) *
          T (lp.single 2 q 1) p := by
  unfold primeLogCriticalTestVector
  rw [sum_inner]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [lp.inner_single_left, map_sum, lp.coeFn_sum, Finset.sum_apply, RCLike.inner_apply,
    RCLike.conj_ofReal, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hq : (lp.single 2 q ((Real.sqrt (primeLogCriticalWeight q) : ℝ) : 𝕜) :
        lp (fun _ : Nat.Primes => 𝕜) 2) =
      ((Real.sqrt (primeLogCriticalWeight q) : ℝ) : 𝕜) •
        (lp.single 2 q (1 : 𝕜) : lp (fun _ : Nat.Primes => 𝕜) 2) := by
    rw [← lp.single_smul, smul_eq_mul, mul_one]
  rw [hq, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- `‖∑_{p ∈ S_n} √h(p) e_p‖² = M_n`. -/
theorem norm_sq_primeLogCriticalTestVector (n : ℕ) :
    ‖primeLogCriticalTestVector 𝕜 n‖ ^ 2 = primeLogCriticalBlockMass n := by
  have h := inner_primeLogCriticalTestVector_apply (ContinuousLinearMap.id 𝕜 _) n
  simp only [ContinuousLinearMap.id_apply] at h
  have hsum : ∑ p ∈ primeLogCriticalPrimeBlock n, ∑ q ∈ primeLogCriticalPrimeBlock n,
        ((Real.sqrt (primeLogCriticalWeight p) * Real.sqrt (primeLogCriticalWeight q) : ℝ) : 𝕜) *
          (lp.single 2 q (1 : 𝕜) : lp (fun _ : Nat.Primes => 𝕜) 2) p =
      ((primeLogCriticalBlockMass n : ℝ) : 𝕜) := by
    rw [primeLogCriticalBlockMass, ← sum_primeLogCriticalPrimeBlock, RCLike.ofReal_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.sum_eq_single p]
    · simp only [lp.single_apply, Pi.single_eq_same, mul_one]
      rw [Real.mul_self_sqrt (primeLogCriticalWeight_nonneg p)]
      rfl
    · intro q _ hqp
      simp [lp.single_apply, Ne.symm hqp]
    · intro hp'; exact absurd hp hp'
  rw [hsum, inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

/-- **(PLCCKU)** No bounded operator on `ℓ²(Primes)` (real or complex) has matrix coefficients
`K(p, q)`. -/
theorem not_exists_bounded_operator_primeLogCriticalCubicKernel :
    ¬ ∃ T : lp (fun _ : Nat.Primes => 𝕜) 2 →L[𝕜] lp (fun _ : Nat.Primes => 𝕜) 2,
      ∀ p q : Nat.Primes, T (lp.single 2 q 1) p = (primeLogCriticalCubicKernel p q : 𝕜) := by
  rintro ⟨T, hT⟩
  apply not_exists_primeLogCriticalCubicRayleigh_bound
  refine ⟨‖T‖, fun n => ?_⟩
  have hform : ⟪primeLogCriticalTestVector 𝕜 n, T (primeLogCriticalTestVector 𝕜 n)⟫_𝕜 =
      ((primeLogCriticalCubicRayleighNumerator n : ℝ) : 𝕜) := by
    rw [inner_primeLogCriticalTestVector_apply, primeLogCriticalCubicRayleighNumerator,
      ← sum_primeLogCriticalPrimeBlock, RCLike.ofReal_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← sum_primeLogCriticalPrimeBlock
      (fun q => Real.log (p : ℝ) / (p : ℝ) * (Real.log (q : ℝ) / (q : ℝ)) *
        primeLogCriticalCubicCorrelation p q), RCLike.ofReal_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hT, primeLogCriticalCubicKernel, ← RCLike.ofReal_mul]
    congr 1
    have hp := primeLogCriticalWeight_nonneg p
    have hq := primeLogCriticalWeight_nonneg q
    rw [Real.sqrt_mul hp, ← mul_assoc, mul_mul_mul_comm, Real.mul_self_sqrt hp,
      Real.mul_self_sqrt hq]
    rfl
  have hre : primeLogCriticalCubicRayleighNumerator n =
      RCLike.re ⟪primeLogCriticalTestVector 𝕜 n, T (primeLogCriticalTestVector 𝕜 n)⟫_𝕜 := by
    rw [hform, RCLike.ofReal_re]
  calc primeLogCriticalCubicRayleighNumerator n
      = RCLike.re ⟪primeLogCriticalTestVector 𝕜 n, T (primeLogCriticalTestVector 𝕜 n)⟫_𝕜 := hre
    _ ≤ ‖⟪primeLogCriticalTestVector 𝕜 n, T (primeLogCriticalTestVector 𝕜 n)⟫_𝕜‖ :=
      RCLike.re_le_norm _
    _ ≤ ‖primeLogCriticalTestVector 𝕜 n‖ * ‖T (primeLogCriticalTestVector 𝕜 n)‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖primeLogCriticalTestVector 𝕜 n‖ * (‖T‖ * ‖primeLogCriticalTestVector 𝕜 n‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
    _ = ‖T‖ * ‖primeLogCriticalTestVector 𝕜 n‖ ^ 2 := by ring
    _ = ‖T‖ * primeLogCriticalBlockMass n := by rw [norm_sq_primeLogCriticalTestVector]

end

end RHTower

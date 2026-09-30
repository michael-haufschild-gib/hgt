import GaloisForLFunctions.RHTower.SteinhausWeightedSummatoryAbel
import GaloisForLFunctions.RHTower.SteinhausPrefixResampling
import GaloisForLFunctions.RHTower.SteinhausLargestPrimeDecomposition

open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace RHTower
open SteinhausModel

/-- Averaging the exterior phases keeps exactly those characters supported on the retained primes. -/
theorem integral_frozenPrefix_character (S : Finset ℕ) (ω : Omega) (n : ℕ) :
    (∫ η, X n (freezeSteinhausPrefix S ω η) ∂steinhausMeasure) =
      if n.primeFactors ⊆ S then X n ω else 0 := by
  classical
  have hext : steinhausExteriorFactorization S n = steinhausExteriorFactorization S 1 ↔
      n.primeFactors ⊆ S := by
    rw [steinhausExteriorFactorization_eq_iff]
    simp only [Nat.factorization_one, Finsupp.zero_apply]
    constructor
    · intro h p hp
      by_contra hpS
      have hp' : n.factorization p ≠ 0 := by
        exact Finsupp.mem_support_iff.mp (by simpa only [Nat.support_factorization] using hp)
      exact hp' (h p hpS)
    · intro h p hpS
      by_contra hp
      exact hpS (h (by simpa only [Nat.support_factorization] using
        (Finsupp.mem_support_iff.mpr hp : p ∈ n.factorization.support)))
  have h := integral_frozenPrefix_character_pair S ω n 1
  simp only [X_one, map_one, mul_one, hext] at h
  rw [h]
  split_ifs with hn
  · apply X_congr_of_eqOn_primeFactors
    intro p hp
    simp only [freezeSteinhausPrefix, if_pos (hn hp)]
  · rfl

/-- The literal S-smooth coefficient sum is exactly the mean after resampling exterior phases. -/
theorem integral_frozenPrefix_carrier_eq_smooth (a : ℕ → ℂ) (N : ℕ) (S : Finset ℕ)
    (ω : Omega) :
    (∫ η, ∑ n ∈ Finset.Icc 1 N, a n * X n (freezeSteinhausPrefix S ω η)
      ∂steinhausMeasure) =
      ∑ n ∈ Sieve.smoothUpTo S N, a n * X n ω := by
  classical
  have hi (n : ℕ) : Integrable (fun η => a n * X n (freezeSteinhausPrefix S ω η))
      steinhausMeasure := by
    have h := integrable_frozenPrefix_character_pair S ω n 1
    simp only [X_one, map_one, mul_one] at h
    exact h.const_mul _
  rw [integral_finsetSum _ (fun n _ => hi n)]
  simp_rw [integral_const_mul, integral_frozenPrefix_character]
  rw [Sieve.smoothUpTo, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> simp

/-- Smooth projection contracts the original absolute first mean for every finite retained prime set. -/
theorem integral_norm_smoothUpTo_carrier_le (a : ℕ → ℂ) (N : ℕ) (S : Finset ℕ) :
    (∫ ω, ‖∑ n ∈ Sieve.smoothUpTo S N, a n * X n ω‖ ∂steinhausMeasure) ≤
      ∫ ω, ‖∑ n ∈ Finset.Icc 1 N, a n * X n ω‖ ∂steinhausMeasure := by
  have hm : Measurable (fun ω => ∑ n ∈ Finset.Icc 1 N, a n * X n ω) :=
    Finset.measurable_sum _ (fun n _ => measurable_const.mul (measurable_X n))
  have hj : Measurable (fun z : Omega × Omega =>
      ‖∑ n ∈ Finset.Icc 1 N, a n * X n (freezeSteinhausPrefix S z.1 z.2)‖) := by
    simpa only [Function.comp_def] using hm.norm.comp (measurable_freezeSteinhausPrefix_joint S)
  have hi : Integrable (fun z : Omega × Omega =>
      ‖∑ n ∈ Finset.Icc 1 N, a n * X n (freezeSteinhausPrefix S z.1 z.2)‖)
      (steinhausMeasure.prod steinhausMeasure) := by
    refine Integrable.mono' (integrable_const (∑ n ∈ Finset.Icc 1 N, ‖a n‖))
      hj.aestronglyMeasurable ?_
    filter_upwards with z
    rw [norm_norm]
    simpa only [norm_mul, norm_X, mul_one] using norm_sum_le (Finset.Icc 1 N)
      (fun n => a n * X n (freezeSteinhausPrefix S z.1 z.2))
  have hmap := integral_map_of_stronglyMeasurable
    (μ := steinhausMeasure.prod steinhausMeasure)
    (measurable_freezeSteinhausPrefix_joint S) hm.norm.stronglyMeasurable
  rw [map_freezeSteinhausPrefix] at hmap
  calc
    _ ≤ ∫ ω, ∫ η, ‖∑ n ∈ Finset.Icc 1 N, a n * X n (freezeSteinhausPrefix S ω η)‖
        ∂steinhausMeasure ∂steinhausMeasure := by
      apply integral_mono (integrable_norm_steinhausFiniteSum a (Sieve.smoothUpTo S N))
        hi.integral_prod_left
      intro ω
      dsimp only
      rw [← integral_frozenPrefix_carrier_eq_smooth a N S ω]
      exact norm_integral_le_integral_norm _
    _ = ∫ z : Omega × Omega,
        ‖∑ n ∈ Finset.Icc 1 N, a n * X n (freezeSteinhausPrefix S z.1 z.2)‖
          ∂steinhausMeasure.prod steinhausMeasure := integral_integral hi
    _ = _ := hmap.symm

/-- The actual small-prime background contracts first mean, uniformly over its cutoff. -/
theorem integral_norm_steinhausSmoothCarrier_le (a : ℕ → ℂ) (N Y : ℕ) :
    (∫ ω, ‖steinhausSmoothCarrier a N Y ω‖ ∂steinhausMeasure) ≤
      ∫ ω, ‖∑ n ∈ Finset.Icc 1 N, a n * X n ω‖ ∂steinhausMeasure :=
  integral_norm_smoothUpTo_carrier_le a N (Nat.primesLE Y)

end RHTower

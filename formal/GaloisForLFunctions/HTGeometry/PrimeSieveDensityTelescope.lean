import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The singular sieve density and its telescoping total variation

The density of the integers coprime to a finite set of primes is the Euler
product of that set.  Adjoining one prime multiplies the density by `1 - 1/p`, so
the loss is exactly the density divided by that prime.  Along any enumeration of
all primes the losses telescope, and because the reciprocals of the primes are
not summable the density tends to zero, so the total loss is exactly one.

This is the singular layer of the prime-sieve relative character: the singular
first-trace density has finite total cofinal variation, equal to one, even though
the independent one-prime densities `1 - 1/p` are not summable.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- The sieve density of a finite set of primes: the density of the integers
coprime to all of them. -/
noncomputable def sieveDensity (P : Finset Nat.Primes) : ℝ :=
  ∏ p ∈ P, (1 - ((p : ℕ) : ℝ)⁻¹)

@[simp] theorem sieveDensity_empty : sieveDensity ∅ = 1 := by
  simp [sieveDensity]

theorem one_lt_prime_cast (p : Nat.Primes) : (1 : ℝ) < ((p : ℕ) : ℝ) := by
  exact_mod_cast p.2.one_lt

theorem sieveDensity_pos (P : Finset Nat.Primes) : 0 < sieveDensity P := by
  refine Finset.prod_pos fun p _ => ?_
  have h := one_lt_prime_cast p
  have hpos : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  rw [sub_pos, inv_lt_one_iff₀]
  right
  exact h

theorem sieveDensity_le_one (P : Finset Nat.Primes) : sieveDensity P ≤ 1 := by
  refine Finset.prod_le_one (fun p _ => ?_) fun p _ => ?_
  · have h := one_lt_prime_cast p
    have hpos : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
    rw [sub_nonneg]
    exact le_of_lt ((inv_lt_one_iff₀).mpr (Or.inr h))
  · have h := one_lt_prime_cast p
    have hpos : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
    have : (0 : ℝ) < ((p : ℕ) : ℝ)⁻¹ := by positivity
    linarith

/-- **Prime-enlargement of the sieve density.** -/
theorem sieveDensity_insert {p : Nat.Primes} {P : Finset Nat.Primes} (hp : p ∉ P) :
    sieveDensity (insert p P) = sieveDensity P * (1 - ((p : ℕ) : ℝ)⁻¹) := by
  rw [sieveDensity, Finset.prod_insert hp, sieveDensity, mul_comm]

/-- **Exact singular loss.**  Adjoining a prime loses exactly the density divided
by that prime. -/
theorem sieveDensity_sub_insert {p : Nat.Primes} {P : Finset Nat.Primes}
    (hp : p ∉ P) :
    sieveDensity P - sieveDensity (insert p P)
      = sieveDensity P / ((p : ℕ) : ℝ) := by
  rw [sieveDensity_insert hp]
  field_simp
  ring

section Enumeration

variable (e : ℕ ≃ Nat.Primes)

/-- The first `n` primes of an enumeration. -/
def sievePrefix (n : ℕ) : Finset Nat.Primes := (Finset.range n).image e

theorem sievePrefix_zero : sievePrefix e 0 = ∅ := by
  simp [sievePrefix]

theorem notMem_sievePrefix (n : ℕ) : e n ∉ sievePrefix e n := by
  simp only [sievePrefix, Finset.mem_image, Finset.mem_range, not_exists]
  rintro k ⟨hk, hke⟩
  exact absurd (e.injective hke) (Nat.ne_of_lt hk)

theorem sievePrefix_succ (n : ℕ) :
    sievePrefix e (n + 1) = insert (e n) (sievePrefix e n) := by
  rw [sievePrefix, sievePrefix, Finset.range_add_one, Finset.image_insert]

/-- The telescoping identity for the partial losses. -/
theorem sum_sieveDensity_div_prime (N : ℕ) :
    ∑ n ∈ Finset.range N, sieveDensity (sievePrefix e n) / ((e n : ℕ) : ℝ)
      = 1 - sieveDensity (sievePrefix e N) := by
  induction N with
  | zero => simp [sievePrefix_zero]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, sievePrefix_succ,
        ← sieveDensity_sub_insert (notMem_sievePrefix e N)]
      ring

/-- The sieve density along an enumeration tends to zero: the reciprocals of the
primes are not summable. -/
theorem tendsto_sieveDensity_sievePrefix :
    Tendsto (fun n => sieveDensity (sievePrefix e n)) atTop (𝓝 0) := by
  have hnonneg : ∀ n : ℕ, (0 : ℝ) ≤ ((e n : ℕ) : ℝ)⁻¹ := fun n => by positivity
  have hnotsummable : ¬ Summable fun n : ℕ => ((e n : ℕ) : ℝ)⁻¹ := by
    intro hsum
    refine Nat.Primes.not_summable_one_div ?_
    have hre := (e.summable_iff (f := fun p : Nat.Primes => ((p : ℕ) : ℝ)⁻¹)).mp hsum
    simpa [one_div] using hre
  have hdiv : Tendsto
      (fun N => ∑ n ∈ Finset.range N, ((e n : ℕ) : ℝ)⁻¹) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hnonneg).mp hnotsummable
  have hexp : Tendsto
      (fun N => Real.exp (-∑ n ∈ Finset.range N, ((e n : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hdiv
  refine squeeze_zero (fun N => le_of_lt (sieveDensity_pos _)) (fun N => ?_) hexp
  have hprod : sieveDensity (sievePrefix e N)
      = ∏ n ∈ Finset.range N, (1 - ((e n : ℕ) : ℝ)⁻¹) := by
    rw [sieveDensity, sievePrefix,
      Finset.prod_image (fun a _ b _ hab => e.injective hab)]
  rw [hprod, ← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_le_prod (fun n _ => ?_) (fun n _ => ?_)
  · have h := one_lt_prime_cast (e n)
    have hpos : (0 : ℝ) < ((e n : ℕ) : ℝ) := by linarith
    have hle : ((e n : ℕ) : ℝ)⁻¹ ≤ 1 := le_of_lt ((inv_lt_one_iff₀).mpr (Or.inr h))
    linarith
  · linarith [Real.add_one_le_exp (-((e n : ℕ) : ℝ)⁻¹)]

/-- **Total cofinal variation of the singular density.**  Along any enumeration
of the primes, the losses sum to exactly one. -/
theorem hasSum_sieveDensity_div_prime :
    HasSum (fun n : ℕ => sieveDensity (sievePrefix e n) / ((e n : ℕ) : ℝ)) 1 := by
  have hnonneg : ∀ n : ℕ,
      0 ≤ sieveDensity (sievePrefix e n) / ((e n : ℕ) : ℝ) := by
    intro n
    have h := one_lt_prime_cast (e n)
    have := sieveDensity_pos (sievePrefix e n)
    positivity
  have hbound : ∀ N : ℕ,
      ∑ n ∈ Finset.range N, sieveDensity (sievePrefix e n) / ((e n : ℕ) : ℝ) ≤ 1 := by
    intro N
    rw [sum_sieveDensity_div_prime e N]
    have := sieveDensity_pos (sievePrefix e N)
    linarith
  have hsummable : Summable
      fun n : ℕ => sieveDensity (sievePrefix e n) / ((e n : ℕ) : ℝ) :=
    summable_of_sum_range_le hnonneg hbound
  refine (hsummable.hasSum_iff_tendsto_nat).mpr ?_
  refine Tendsto.congr (fun N => (sum_sieveDensity_div_prime e N).symm) ?_
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_sieveDensity_sievePrefix e)

/-- The boxed form of the total-variation law. -/
theorem tsum_sieveDensity_div_prime :
    ∑' n : ℕ, sieveDensity (sievePrefix e n) / ((e n : ℕ) : ℝ) = 1 :=
  (hasSum_sieveDensity_div_prime e).tsum_eq

end Enumeration

end GaloisForLFunctions.HTGeometry

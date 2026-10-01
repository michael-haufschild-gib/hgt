import GaloisForLFunctions.RHTower.SteinhausFrozenCarrierLocalTarget
import GaloisForLFunctions.RHTower.Sieve.EulerExpansion

open Complex Finset
noncomputable section
namespace RHTower
open SteinhausModel

/-- The actual coefficient at one subset of the local degree-one factors. -/
def steinhausSpectralSubsetCoefficient (P : Finset ℕ) (a b : ℕ → ℂ) (T : Finset ℕ) : ℂ :=
  (∏ p ∈ T, b p) * ∏ p ∈ P \ T, a p

private theorem character_prod_primes (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (ω : Omega) :
    X (∏ p ∈ P, p) ω = ∏ p ∈ P, charFactor 1 (ω p) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [X_one]
  | @insert p P hp ih =>
    have hprime : p.Prime := hP p (mem_insert_self _ _)
    have hrest : ∀ q ∈ P, q.Prime := fun q hq => hP q (mem_insert_of_mem hq)
    rw [prod_insert hp, X_mul hprime.ne_zero
      (prod_ne_zero_iff.mpr (fun q hq => (hrest q hq).ne_zero)),
      steinhausCharacter_prime_eq_charFactor hprime, ih hrest, prod_insert hp]

/-- The phase product is literally a Dirichlet character polynomial on the
squarefree prime products; the existing arithmetic injectivity excludes collisions. -/
theorem steinhausSpectralProduct_eq_character_sum
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a b : ℕ → ℂ) (ω : Omega) :
    (∏ p ∈ P, (a p + b p * charFactor 1 (ω p))) =
      ∑ T ∈ P.powerset, steinhausSpectralSubsetCoefficient P a b T * X (∏ p ∈ T, p) ω := by
  rw [show (∏ p ∈ P, (a p + b p * charFactor 1 (ω p))) =
    ∏ p ∈ P, (b p * charFactor 1 (ω p) + a p) by simp only [add_comm], prod_add]
  apply sum_congr rfl
  intro T hT
  rw [character_prod_primes T (fun p hp => hP p ((mem_powerset.mp hT) hp)) ω,
    prod_mul_distrib]
  unfold steinhausSpectralSubsetCoefficient
  ring

/-- Exact frequency-weighted squared coefficient mass, before any mean-value
error estimate. No maximum-support or absolute off-diagonal surrogate is used. -/
theorem steinhausSpectralProduct_frequencyWeightedCost (P : Finset ℕ) (a b : ℕ → ℂ) :
    (∑ T ∈ P.powerset, ((∏ p ∈ T, p : ℕ) : ℝ) *
      ‖steinhausSpectralSubsetCoefficient P a b T‖ ^ 2) =
      ∏ p ∈ P, (‖a p‖ ^ 2 + (p : ℝ) * ‖b p‖ ^ 2) := by
  rw [show (∏ p ∈ P, (‖a p‖ ^ 2 + (p : ℝ) * ‖b p‖ ^ 2)) =
    ∏ p ∈ P, ((p : ℝ) * ‖b p‖ ^ 2 + ‖a p‖ ^ 2) by simp only [add_comm], prod_add]
  apply sum_congr rfl
  intro T _
  simp only [steinhausSpectralSubsetCoefficient, norm_mul, norm_prod, mul_pow,
    ← prod_pow, Nat.cast_prod, prod_mul_distrib]
  ring

/-- The same cost on literal distinct integer frequencies, with coefficients
read from their prime-factor sets. -/
theorem steinhausSpectralProduct_integerFrequencyCost
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a b : ℕ → ℂ) :
    (∑ n ∈ P.powerset.image (fun T => ∏ p ∈ T, p), (n : ℝ) *
      ‖steinhausSpectralSubsetCoefficient P a b n.primeFactors‖ ^ 2) =
      ∏ p ∈ P, (‖a p‖ ^ 2 + (p : ℝ) * ‖b p‖ ^ 2) := by
  classical
  calc
    _ = ∑ T ∈ P.powerset, ((∏ p ∈ T, p : ℕ) : ℝ) *
        ‖steinhausSpectralSubsetCoefficient P a b T‖ ^ 2 := by
      rw [sum_image]
      · apply sum_congr rfl
        intro T hT
        rw [Sieve.primeFactors_prod_of_subset hP (mem_powerset.mp hT)]
      · exact Sieve.prod_injOn_powerset hP
    _ = _ := steinhausSpectralProduct_frequencyWeightedCost P a b

/-- The literal integer-frequency polynomial is exactly the original phase product. -/
theorem steinhausSpectralProduct_eq_integerCharacter_sum
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a b : ℕ → ℂ) (ω : Omega) :
    (∏ p ∈ P, (a p + b p * charFactor 1 (ω p))) =
      ∑ n ∈ P.powerset.image (fun T => ∏ p ∈ T, p),
        steinhausSpectralSubsetCoefficient P a b n.primeFactors * X n ω := by
  rw [steinhausSpectralProduct_eq_character_sum P hP a b ω, sum_image]
  · apply sum_congr rfl
    intro T hT
    rw [Sieve.primeFactors_prod_of_subset hP (mem_powerset.mp hT)]
  · exact Sieve.prod_injOn_powerset hP

private theorem one_add_sum_le_product (P : Finset ℕ) (u : ℕ → ℝ)
    (hu : ∀ p ∈ P, 0 ≤ u p) : 1 + ∑ p ∈ P, u p ≤ ∏ p ∈ P, (1 + u p) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    have hp0 := hu p (mem_insert_self _ _)
    have hr : ∀ q ∈ P, 0 ≤ u q := fun q hq => hu q (mem_insert_of_mem hq)
    have hsum : 0 ≤ ∑ q ∈ P, u q := sum_nonneg hr
    have h := mul_le_mul_of_nonneg_left (ih hr) (by linarith : 0 ≤ 1 + u p)
    rw [sum_insert hp, prod_insert hp]
    nlinarith

/-- Normalized local factors retain the full arithmetic cost of every bias. -/
theorem steinhausSpectralProduct_frequencyWeightedCost_lower
    (P : Finset ℕ) (hP : ∀ p ∈ P, 1 ≤ p) (a b m : ℕ → ℂ)
    (hnorm : ∀ p ∈ P, ‖a p‖ ^ 2 + ‖b p‖ ^ 2 = 1)
    (hbias : ∀ p ∈ P, ‖m p‖ ^ 2 ≤ ‖b p‖ ^ 2) :
    1 + ∑ p ∈ P, ((p : ℝ) - 1) * ‖m p‖ ^ 2 ≤
      ∑ T ∈ P.powerset, ((∏ p ∈ T, p : ℕ) : ℝ) *
        ‖steinhausSpectralSubsetCoefficient P a b T‖ ^ 2 := by
  rw [steinhausSpectralProduct_frequencyWeightedCost]
  have hp0 (p : ℕ) (hp : p ∈ P) : 0 ≤ (p : ℝ) - 1 := by
    have hh : (1 : ℝ) ≤ p := by exact_mod_cast hP p hp
    linarith
  calc
    _ ≤ 1 + ∑ p ∈ P, ((p : ℝ) - 1) * ‖b p‖ ^ 2 := by
      apply add_le_add le_rfl
      apply sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (hbias p hp) (hp0 p hp)
    _ ≤ ∏ p ∈ P, (1 + ((p : ℝ) - 1) * ‖b p‖ ^ 2) :=
      one_add_sum_le_product P _ (fun p hp => mul_nonneg (hp0 p hp) (sq_nonneg _))
    _ = _ := by
      apply prod_congr rfl
      intro p hp
      nlinarith [hnorm p hp]

end RHTower

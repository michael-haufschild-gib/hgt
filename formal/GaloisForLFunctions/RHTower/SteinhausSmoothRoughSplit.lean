import GaloisForLFunctions.RHTower.Sieve.SmoothRough
import GaloisForLFunctions.RHTower.SteinhausFrozenPrefixSecondMoment
import Mathlib.NumberTheory.SmoothNumbers

namespace RHTower

private theorem prime_le_pred_iff {p y : ℕ} (hp : p.Prime) : p ≤ y - 1 ↔ p < y := by
  have := hp.two_le
  omega

private theorem factorization_filteredPrimeProduct (n : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    ((n.factorization.filter Q).prod (fun p k => p ^ k)).factorization =
      n.factorization.filter Q := by
  apply Nat.prod_pow_factorization_eq_self
  intro p hp
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

/-- The existing sieve smooth part has exactly the prefix-prime factorization. -/
theorem factorization_sieveSmoothPart (y n : ℕ) :
    (Sieve.smoothPart (y - 1) n).factorization =
      n.factorization.filter (fun p => p ∈ Nat.primesBelow y) := by
  classical
  unfold Sieve.smoothPart
  change (∏ p ∈ {p ∈ n.factorization.support | p ≤ y - 1}, p ^ n.factorization p).factorization = _
  have h := factorization_filteredPrimeProduct n (fun p => p ≤ y - 1)
  rw [Finsupp.prod_filter_index, Finsupp.support_filter] at h
  rw [h]
  ext p
  by_cases hp : p.Prime
  · simp only [Finsupp.filter_apply, Nat.mem_primesBelow, hp, and_true, prime_le_pred_iff hp]
  · simp [Finsupp.filter_apply, Nat.factorization_eq_zero_of_not_prime n hp]

/-- The existing sieve rough part realizes the literal exterior index in frozen-prefix moments. -/
theorem factorization_sieveRoughPart (y n : ℕ) :
    (Sieve.roughPart (y - 1) n).factorization =
      steinhausExteriorFactorization (Nat.primesBelow y) n := by
  classical
  unfold Sieve.roughPart steinhausExteriorFactorization
  change (∏ p ∈ {p ∈ n.factorization.support | ¬p ≤ y - 1}, p ^ n.factorization p).factorization = _
  have h := factorization_filteredPrimeProduct n (fun p => ¬p ≤ y - 1)
  rw [Finsupp.prod_filter_index, Finsupp.support_filter] at h
  rw [h]
  ext p
  by_cases hp : p.Prime
  · simp only [Finsupp.filter_apply, Nat.mem_primesBelow, hp, and_true, prime_le_pred_iff hp]
  · simp [Finsupp.filter_apply, Nat.factorization_eq_zero_of_not_prime n hp]

/-- The sieve smooth part is a member of the actual smooth-number summation type. -/
theorem sieveSmoothPart_mem_smoothNumbers (y n : ℕ) :
    Sieve.smoothPart (y - 1) n ∈ Nat.smoothNumbers y := by
  classical
  apply Nat.mem_smoothNumbers_iff_primeFactors_subset.mpr
  refine ⟨(Sieve.smoothPart_pos _ _).ne', ?_⟩
  rw [← Nat.support_factorization, factorization_sieveSmoothPart, Finsupp.support_filter]
  exact fun p hp => (Finset.mem_filter.mp hp).2

/-- No prefix prime divides the actual sieve rough part. -/
theorem not_dvd_sieveRoughPart (y n : ℕ) {p : ℕ} (hp : p ∈ Nat.primesBelow y) :
    ¬p ∣ Sieve.roughPart (y - 1) n := by
  intro hd
  have hpos := (Nat.mem_primesBelow.mp hp).2.factorization_pos_of_dvd
    (Sieve.roughPart_pos _ _).ne' hd
  rw [factorization_sieveRoughPart] at hpos
  simp [steinhausExteriorFactorization, hp] at hpos

/-- Equality of exterior factorization indices is exactly equality of rough factors. -/
theorem steinhausExteriorFactorization_eq_iff_sieveRoughPart_eq (y n m : ℕ) :
    steinhausExteriorFactorization (Nat.primesBelow y) n =
        steinhausExteriorFactorization (Nat.primesBelow y) m ↔
      Sieve.roughPart (y - 1) n = Sieve.roughPart (y - 1) m := by
  rw [← factorization_sieveRoughPart, ← factorization_sieveRoughPart]
  exact ⟨Nat.factorization_inj (Sieve.roughPart_pos _ _).ne'
    (Sieve.roughPart_pos _ _).ne', congrArg Nat.factorization⟩

private theorem smooth_factorization_zero_outside {y a : ℕ} (ha : a ∈ Nat.smoothNumbers y)
    {p : ℕ} (hp : p ∉ Nat.primesBelow y) : a.factorization p = 0 := by
  apply Finsupp.notMem_support_iff.mp
  intro hmem
  exact hp ((Nat.mem_smoothNumbers_iff_primeFactors_subset.mp ha).2 hmem)

/-- Multiplication by a prefix-rough integer leaves exactly the prescribed smooth part. -/
theorem sieveSmoothPart_mul_of_smooth_rough {y a b : ℕ} (ha : a ∈ Nat.smoothNumbers y)
    (hb : b ≠ 0) (hr : ∀ p ∈ Nat.primesBelow y, ¬p ∣ b) :
    Sieve.smoothPart (y - 1) (a * b) = a := by
  apply Nat.factorization_inj (Sieve.smoothPart_pos _ _).ne'
    (Nat.ne_zero_of_mem_smoothNumbers ha)
  rw [factorization_sieveSmoothPart,
    Nat.factorization_mul (Nat.ne_zero_of_mem_smoothNumbers ha) hb]
  ext p
  by_cases hp : p ∈ Nat.primesBelow y
  · simp [hp, Nat.factorization_eq_zero_of_not_dvd (hr p hp)]
  · simp [hp, smooth_factorization_zero_outside ha hp]

/-- Multiplication by a smooth integer leaves exactly the prescribed rough part. -/
theorem sieveRoughPart_mul_of_smooth_rough {y a b : ℕ} (ha : a ∈ Nat.smoothNumbers y)
    (hb : b ≠ 0) (hr : ∀ p ∈ Nat.primesBelow y, ¬p ∣ b) :
    Sieve.roughPart (y - 1) (a * b) = b := by
  apply Nat.factorization_inj (Sieve.roughPart_pos _ _).ne' hb
  rw [factorization_sieveRoughPart]
  unfold steinhausExteriorFactorization
  rw [Nat.factorization_mul (Nat.ne_zero_of_mem_smoothNumbers ha) hb]
  ext p
  by_cases hp : p ∈ Nat.primesBelow y
  · simp [hp, Nat.factorization_eq_zero_of_not_dvd (hr p hp)]
  · simp [hp, smooth_factorization_zero_outside ha hp]

/-- Smooth/rough products are injectively parametrized by the actual two arithmetic factors. -/
theorem smooth_rough_pair_unique {y a b c d : ℕ}
    (ha : a ∈ Nat.smoothNumbers y) (hb : b ≠ 0)
    (hbr : ∀ p ∈ Nat.primesBelow y, ¬p ∣ b)
    (hc : c ∈ Nat.smoothNumbers y) (hd : d ≠ 0)
    (hdr : ∀ p ∈ Nat.primesBelow y, ¬p ∣ d) (heq : a * b = c * d) :
    a = c ∧ b = d := by
  constructor
  · have h := congrArg (Sieve.smoothPart (y - 1)) heq
    simpa only [sieveSmoothPart_mul_of_smooth_rough ha hb hbr,
      sieveSmoothPart_mul_of_smooth_rough hc hd hdr] using h
  · have h := congrArg (Sieve.roughPart (y - 1)) heq
    simpa only [sieveRoughPart_mul_of_smooth_rough ha hb hbr,
      sieveRoughPart_mul_of_smooth_rough hc hd hdr] using h

end RHTower

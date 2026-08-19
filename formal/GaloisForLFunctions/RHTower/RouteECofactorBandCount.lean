import GaloisForLFunctions.RHTower.RouteECofactorParityWeights
import GaloisForLFunctions.RHTower.RouteECofactorSquarefreeHarmonic

/-!
# The odd band-avoiding squarefree source, counted

The cofactor card's `(7)` and `(9)` are lower bounds for a *parity class* of band-avoiding
cofactors.  The pairing of `RouteECofactorParityBalance` reduces them to the same weighted sum over
the odd band-avoiding squarefree integers, and that sum is bounded below by the squarefree count
minus one multiple-count per excluded prime — the classical union bound, with the excluded set
being `2` together with the band.
-/

namespace RHTower

namespace CofactorParity

open Finset ArithmeticFunction

/-- The primes excluded from a cofactor: the prime `2` and the whole band below `Y`. -/
def excludedPrimes (Band : ℕ → Prop) [DecidablePred Band] (Y : ℕ) : Finset ℕ :=
  insert 2 ((Finset.Icc 1 Y).filter (fun p => p.Prime ∧ Band p))

theorem one_le_of_mem_excludedPrimes {Band : ℕ → Prop} [DecidablePred Band] {Y p : ℕ}
    (hp : p ∈ excludedPrimes Band Y) : 1 ≤ p := by
  rw [excludedPrimes, Finset.mem_insert] at hp
  rcases hp with rfl | hp
  · norm_num
  · exact (Finset.mem_Icc.1 (Finset.mem_filter.1 hp).1).1

/-- **The odd band-avoiding squarefree cofactors, counted from below.** -/
theorem card_oddBase_ge {Band : ℕ → Prop} [DecidablePred Band] {T R : ℕ} (hR : 1 ≤ R)
    (hRY : T / 2 ≤ R ^ 2) :
    ((T / 2 : ℕ) : ℝ) * Sieve.squarefreeDensity
        - ((R : ℝ) + ((T / 2 : ℕ) : ℝ) / (R : ℝ))
        - ∑ p ∈ excludedPrimes Band (T / 2), ((T / 2 : ℕ) : ℝ) / (p : ℝ)
      ≤ (((oddBase Band T).card : ℕ) : ℝ) := by
  classical
  refine Sieve.card_squarefree_avoid_ge_of_subset _
    (fun p hp => one_le_of_mem_excludedPrimes hp) hR hRY (oddBase Band T) ?_
  intro n hn hsq hall
  rw [oddBase, Finset.mem_filter]
  refine ⟨hn, hsq, hall 2 (Finset.mem_insert_self _ _), fun p hp hbp => ?_⟩
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
  have hnle : n ≤ T / 2 := (Finset.mem_Icc.1 hn).2
  have hple : p ≤ T / 2 := le_trans (Nat.le_of_dvd (by omega) hdvd) hnle
  refine hall p ?_ hdvd
  rw [excludedPrimes, Finset.mem_insert]
  exact Or.inr (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hpp.one_lt.le, hple⟩, hpp, hbp⟩)

/-- **The card's `(7)` source sum, from below.**  Every weight `s^{-1/2}` with `s ≤ T/2` is at
least `(T/2)^{-1/2}`, so the source sum dominates the count divided by `√(T/2)`. -/
theorem sum_sqrtInv_oddBase_ge {Band : ℕ → Prop} [DecidablePred Band] {T R : ℕ} (hR : 1 ≤ R)
    (hRY : T / 2 ≤ R ^ 2) :
    (((T / 2 : ℕ) : ℝ) * Sieve.squarefreeDensity
        - ((R : ℝ) + ((T / 2 : ℕ) : ℝ) / (R : ℝ))
        - ∑ p ∈ excludedPrimes Band (T / 2), ((T / 2 : ℕ) : ℝ) / (p : ℝ))
        / Real.sqrt ((T / 2 : ℕ) : ℝ)
      ≤ ∑ s ∈ oddBase Band T, (Real.sqrt s)⁻¹ := by
  classical
  rcases Nat.eq_zero_or_pos (T / 2) with h0 | hpos
  · have hempty : oddBase Band T = ∅ := by
      rw [oddBase]
      refine Finset.filter_eq_empty_iff.2 fun s hs => ?_
      rw [Finset.mem_Icc, h0] at hs
      omega
    rw [hempty, h0]
    simp
  have hY0 : (0 : ℝ) < ((T / 2 : ℕ) : ℝ) := by exact_mod_cast hpos
  have hsY : (0 : ℝ) < Real.sqrt ((T / 2 : ℕ) : ℝ) := Real.sqrt_pos.2 hY0
  have hcard := card_oddBase_ge (Band := Band) (T := T) hR hRY
  have hterm : ∀ s ∈ oddBase Band T,
      (Real.sqrt ((T / 2 : ℕ) : ℝ))⁻¹ ≤ (Real.sqrt s)⁻¹ := by
    intro s hs
    rw [oddBase, Finset.mem_filter, Finset.mem_Icc] at hs
    have hs1 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs.1.1
    have hsle : (s : ℝ) ≤ ((T / 2 : ℕ) : ℝ) := by exact_mod_cast hs.1.2
    exact inv_anti₀ (Real.sqrt_pos.2 hs1) (Real.sqrt_le_sqrt hsle)
  have hsum : (((oddBase Band T).card : ℕ) : ℝ) * (Real.sqrt ((T / 2 : ℕ) : ℝ))⁻¹
      ≤ ∑ s ∈ oddBase Band T, (Real.sqrt s)⁻¹ := by
    have h := Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul] at h
    exact h
  refine le_trans ?_ hsum
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hcard (by positivity)

/-! ## The card's `(7)`, both sides -/

/-- **The card's `(7)`, from below.**  Each parity class of band-avoiding cofactors carries at
least half the source sum, and the source sum is the odd band-avoiding squarefree count divided by
`√(T/2)`.  At `R ≍ √T` and a band whose reciprocal mass is small the right side is `≍ √T`. -/
theorem sum_sqrtInv_parityClass_ge {Band : ℕ → Prop} [DecidablePred Band] (hband : ¬ Band 2)
    {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {T R : ℕ} (hR : 1 ≤ R) (hRY : T / 2 ≤ R ^ 2) :
    (1 / 2 : ℝ) * ((((T / 2 : ℕ) : ℝ) * Sieve.squarefreeDensity
          - ((R : ℝ) + ((T / 2 : ℕ) : ℝ) / (R : ℝ))
          - ∑ p ∈ excludedPrimes Band (T / 2), ((T / 2 : ℕ) : ℝ) / (p : ℝ))
        / Real.sqrt ((T / 2 : ℕ) : ℝ))
      ≤ ∑ t ∈ parityClass Band σ T, (Real.sqrt t)⁻¹ := by
  refine le_trans ?_ (half_sum_oddBase_le_sum_parityClass_sqrt hband hσ T)
  exact mul_le_mul_of_nonneg_left (sum_sqrtInv_oddBase_ge hR hRY) (by norm_num)

/-- **The card's `(7)`, from above.** -/
theorem sum_sqrtInv_parityClass_le {Band : ℕ → Prop} [DecidablePred Band] {σ : ℤ} (T : ℕ) :
    ∑ t ∈ parityClass Band σ T, (Real.sqrt t)⁻¹ ≤ 2 * Real.sqrt T := by
  classical
  refine le_trans ?_ (Sieve.sum_sqrtInv_le T)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => by positivity
  rw [parityClass]
  exact Finset.filter_subset _ _

end CofactorParity

end RHTower

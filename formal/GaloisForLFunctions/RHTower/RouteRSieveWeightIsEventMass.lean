import GaloisForLFunctions.RHTower.RouteRCofinalSieveIsUnitProfile
import GaloisForLFunctions.HTGeometry.PrimeValuationSector

/-!
# The restarted sieve weights are event masses of the prime-valuation sector

The restarted Euler sieve assigns to the `n`-th prime of the tail beginning at `N` the weight

`w_{N,n} = D_{N,n} / p_{N+n}`,

where `D_{N,n}` is the density surviving the first `n` tail primes.  In the prime-valuation product
sector this is the mass of an explicit event: *the first `n` tail primes have valuation zero and the
next one divides*.  Since `μ_p({0}) = 1 - 1/p` and `μ_p({0}ᶜ) = 1/p`, the product formula for
cylinders returns exactly `w_{N,n}`.

So the sieve's telescoping unit mass is the statement that the index of the first dividing tail prime
is almost surely defined, and the sieve profile is a genuine probability distribution on that index.
-/

open MeasureTheory Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The first `n + 1` primes of the tail starting at `N`. -/
def sieveTailIndex (e : ℕ ≃ Nat.Primes) (N n : ℕ) : Finset Nat.Primes :=
  (Finset.range (n + 1)).image fun k => e (N + k)

/-- Valuation zero at each of the first `n` tail primes, and a positive valuation
at the next one. -/
def firstDivisorTarget (e : ℕ ≃ Nat.Primes) (N n : ℕ) : Nat.Primes → Set ℕ :=
  fun p => if p = e (N + n) then {0}ᶜ else {0}

/-- The event that the `n`-th tail prime is the first one that divides. -/
def firstDivisorEvent (e : ℕ ≃ Nat.Primes) (N n : ℕ) :
    Set (∀ _ : Nat.Primes, ℕ) :=
  Set.pi (↑(sieveTailIndex e N n)) (firstDivisorTarget e N n)

theorem measurableSet_firstDivisorTarget (e : ℕ ≃ Nat.Primes) (N n : ℕ)
    (p : Nat.Primes) : MeasurableSet (firstDivisorTarget e N n p) := by
  rw [firstDivisorTarget]
  split_ifs
  · exact (measurableSet_singleton 0).compl
  · exact measurableSet_singleton 0

/-- **The sieve weight is the mass of the first-divisor event.** -/
theorem primeValuationMeasure_firstDivisorEvent (e : ℕ ≃ Nat.Primes) (N n : ℕ) :
    primeValuationMeasure (firstDivisorEvent e N n) =
      ENNReal.ofReal (routeRCofinalSieveWeight e N n) := by
  have hinj : ∀ x ∈ Finset.range (n + 1), ∀ y ∈ Finset.range (n + 1),
      e (N + x) = e (N + y) → x = y := by
    intro x _ y _ h
    have h' := e.injective h
    omega
  have hpi := Measure.infinitePi_pi (μ := primeValuationLaw)
    (s := sieveTailIndex e N n) (t := firstDivisorTarget e N n)
    (fun p _ => measurableSet_firstDivisorTarget e N n p)
  rw [primeValuationMeasure, firstDivisorEvent, hpi, sieveTailIndex,
    Finset.prod_image hinj, Finset.prod_range_succ]
  -- the last factor
  have hlast : primeValuationLaw (e (N + n))
      (firstDivisorTarget e N n (e (N + n))) =
        ENNReal.ofReal ((((e (N + n) : ℕ) : ℝ))⁻¹) := by
    rw [firstDivisorTarget, if_pos rfl, primeValuationLaw_compl_zero]
  -- the earlier factors
  have hearly : ∀ k ∈ Finset.range n,
      primeValuationLaw (e (N + k)) (firstDivisorTarget e N n (e (N + k))) =
        ENNReal.ofReal (1 - (((e (N + k) : ℕ) : ℝ))⁻¹) := by
    intro k hk
    have hne : e (N + k) ≠ e (N + n) := by
      intro h
      have := e.injective h
      have : k = n := by omega
      exact absurd this (Finset.mem_range.mp hk).ne
    rw [firstDivisorTarget, if_neg hne, primeValuationLaw_zero]
  rw [hlast, Finset.prod_congr rfl hearly, ← ENNReal.ofReal_prod_of_nonneg,
    ← ENNReal.ofReal_mul, routeRCofinalSieveWeight, routeRCofinalSieveDensity,
    div_eq_mul_inv]
  · exact Finset.prod_nonneg fun k _ => by
      have h1 : (((e (N + k) : ℕ) : ℝ))⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]
        exact Or.inr (one_lt_prime_cast (e (N + k))).le
      linarith
  · intro k _
    have h1 : (((e (N + k) : ℕ) : ℝ))⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      exact Or.inr (one_lt_prime_cast (e (N + k))).le
    linarith

theorem toReal_primeValuationMeasure_firstDivisorEvent (e : ℕ ≃ Nat.Primes)
    (N n : ℕ) :
    (primeValuationMeasure (firstDivisorEvent e N n)).toReal =
      routeRCofinalSieveWeight e N n := by
  rw [primeValuationMeasure_firstDivisorEvent,
    ENNReal.toReal_ofReal (routeRCofinalSieveWeight_pos e N n).le]

/-- **The first dividing tail prime is almost surely defined.**  The masses of the
first-divisor events sum to one, which is exactly the corpus's telescoping
identity for the restarted sieve weights read probabilistically. -/
theorem hasSum_toReal_primeValuationMeasure_firstDivisorEvent
    (e : ℕ ≃ Nat.Primes) (N : ℕ) :
    HasSum (fun n => (primeValuationMeasure (firstDivisorEvent e N n)).toReal) 1 :=
  (hasSum_routeRCofinalSieveWeight e N).congr_fun fun n =>
    toReal_primeValuationMeasure_firstDivisorEvent e N n

/-! ## The first-divisor events partition the sector -/

theorem mem_sieveTailIndex (e : ℕ ≃ Nat.Primes) (N n k : ℕ) (hk : k ≤ n) :
    e (N + k) ∈ sieveTailIndex e N n := by
  simp only [sieveTailIndex, Finset.mem_image, Finset.mem_range]
  exact ⟨k, by omega, rfl⟩

theorem measurableSet_firstDivisorEvent (e : ℕ ≃ Nat.Primes) (N n : ℕ) :
    MeasurableSet (firstDivisorEvent e N n) :=
  MeasurableSet.pi (sieveTailIndex e N n).countable_toSet
    fun p _ => measurableSet_firstDivisorTarget e N n p

/-- Distinct first-divisor events are disjoint: they disagree about the valuation
at the earlier of the two distinguished primes. -/
theorem pairwise_disjoint_firstDivisorEvent (e : ℕ ≃ Nat.Primes) (N : ℕ) :
    Pairwise (Function.onFun Disjoint (firstDivisorEvent e N)) := by
  have key : ∀ m n : ℕ, m < n →
      Disjoint (firstDivisorEvent e N m) (firstDivisorEvent e N n) := by
    intro m n hmn
    rw [Set.disjoint_left]
    intro k hkm hkn
    have hne : e (N + m) ≠ e (N + n) := by
      intro h
      have := e.injective h
      omega
    have hm := hkm (e (N + m))
      (mem_sieveTailIndex e N m m (le_refl m))
    have hn := hkn (e (N + m))
      (mem_sieveTailIndex e N n m (le_of_lt hmn))
    rw [firstDivisorTarget, if_pos rfl] at hm
    rw [firstDivisorTarget, if_neg hne] at hn
    exact hm hn
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with h | h
  · exact key m n h
  · exact (key n m h).symm

/-- **The first-divisor events partition the sector.**  Their union has full
measure: almost surely some tail prime divides, and the sieve profile is the law
of which one does so first. -/
theorem primeValuationMeasure_iUnion_firstDivisorEvent (e : ℕ ≃ Nat.Primes)
    (N : ℕ) :
    primeValuationMeasure (⋃ n, firstDivisorEvent e N n) = 1 := by
  have hunion := measure_iUnion (pairwise_disjoint_firstDivisorEvent e N)
    (measurableSet_firstDivisorEvent e N)
  have hfin : primeValuationMeasure (⋃ n, firstDivisorEvent e N n) ≠ ⊤ :=
    measure_ne_top _ _
  have htoReal := congrArg ENNReal.toReal hunion
  rw [ENNReal.tsum_toReal_eq (fun n => measure_ne_top _ _),
    (hasSum_toReal_primeValuationMeasure_firstDivisorEvent e N).tsum_eq]
    at htoReal
  rw [← ENNReal.ofReal_toReal hfin, htoReal, ENNReal.ofReal_one]

end

end RHTower

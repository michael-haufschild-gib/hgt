import GaloisForLFunctions.HTGeometry.PrimeSieveDensityTelescope
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.NumberTheory.Divisors

/-!
# The sieved Euler trace of a commuting prime sieve

The integers coprime to a finite set of primes split, at each further prime, into
those coprime to it and those divisible by it; the second class is the whole
class scaled by that prime.  For a completely multiplicative summable weight this
gives the exact prime-enlargement law of the sieved sum, and by induction the
finite Euler product.

Applied to `n ↦ n^{-k}` this is the trace of the `k`-th power of the sieved
diagonal operator: `Tr(Q_P^k) = ζ(k) ∏_{p ∈ P} (1 - p^{-k})`.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- The primorial of a finite set of primes. -/
def sievePrimorial (P : Finset Nat.Primes) : ℕ := ∏ p ∈ P, (p : ℕ)

@[simp] theorem sievePrimorial_empty : sievePrimorial ∅ = 1 := by
  simp [sievePrimorial]

theorem sievePrimorial_insert {p : Nat.Primes} {P : Finset Nat.Primes} (hp : p ∉ P) :
    sievePrimorial (insert p P) = (p : ℕ) * sievePrimorial P := by
  rw [sievePrimorial, Finset.prod_insert hp, sievePrimorial]

/-- A prime outside a finite set is coprime to its primorial. -/
theorem coprime_sievePrimorial {p : Nat.Primes} {P : Finset Nat.Primes} (hp : p ∉ P) :
    Nat.Coprime (p : ℕ) (sievePrimorial P) := by
  refine Nat.Coprime.prod_right fun q hq => ?_
  refine (Nat.coprime_primes p.2 q.2).mpr ?_
  intro h
  exact hp (by rwa [Subtype.ext h])

/-- The coprimality class of the enlarged sieve. -/
theorem coprime_sievePrimorial_insert_iff {p : Nat.Primes} {P : Finset Nat.Primes}
    (hp : p ∉ P) (n : ℕ) :
    Nat.Coprime n (sievePrimorial (insert p P))
      ↔ Nat.Coprime n (sievePrimorial P) ∧ ¬ ((p : ℕ) ∣ n) := by
  rw [sievePrimorial_insert hp, Nat.coprime_mul_iff_right]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, (Nat.Prime.coprime_iff_not_dvd p.2).mp (Nat.coprime_comm.mp h1)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd p.2).mpr h2), h1⟩

/-- The sieved sum of a weight over the integers coprime to a prime set. -/
noncomputable def sievedSum (f : ℕ → ℝ) (P : Finset Nat.Primes) : ℝ :=
  ∑' n : ℕ, {n : ℕ | Nat.Coprime n (sievePrimorial P)}.indicator f n

theorem summable_sieved_indicator {f : ℕ → ℝ} (hf : Summable f)
    (P : Finset Nat.Primes) :
    Summable ({n : ℕ | Nat.Coprime n (sievePrimorial P)}.indicator f) :=
  hf.indicator _

/-- **Prime enlargement of the sieved sum.**  Adjoining a prime multiplies the
sieved sum by `1 - f p`. -/
theorem sievedSum_insert {f : ℕ → ℝ} (hf : Summable f)
    (hmul : ∀ m n : ℕ, f (m * n) = f m * f n)
    {p : Nat.Primes} {P : Finset Nat.Primes} (hp : p ∉ P) :
    sievedSum f (insert p P) = sievedSum f P * (1 - f (p : ℕ)) := by
  classical
  set A : Set ℕ := {n : ℕ | Nat.Coprime n (sievePrimorial P)} with hA
  set B : Set ℕ := {n : ℕ | Nat.Coprime n (sievePrimorial (insert p P))} with hB
  set C : Set ℕ := {n : ℕ | Nat.Coprime n (sievePrimorial P) ∧ (p : ℕ) ∣ n} with hC
  have hcopP : Nat.Coprime (p : ℕ) (sievePrimorial P) := coprime_sievePrimorial hp
  -- pointwise splitting of the sieved class
  have hpoint : ∀ n : ℕ, A.indicator f n = B.indicator f n + C.indicator f n := by
    intro n
    by_cases hcop : Nat.Coprime n (sievePrimorial P)
    · by_cases hdvd : (p : ℕ) ∣ n
      · rw [Set.indicator_of_mem (by rw [hA]; exact hcop),
          Set.indicator_of_notMem (by
            rw [hB, Set.mem_setOf_eq, coprime_sievePrimorial_insert_iff hp]
            exact fun h => h.2 hdvd),
          Set.indicator_of_mem (by rw [hC]; exact ⟨hcop, hdvd⟩), zero_add]
      · rw [Set.indicator_of_mem (by rw [hA]; exact hcop),
          Set.indicator_of_mem (by
            rw [hB, Set.mem_setOf_eq, coprime_sievePrimorial_insert_iff hp]
            exact ⟨hcop, hdvd⟩),
          Set.indicator_of_notMem (by rw [hC]; exact fun h => hdvd h.2), add_zero]
    · rw [Set.indicator_of_notMem (by rw [hA]; exact hcop),
        Set.indicator_of_notMem (by
          rw [hB, Set.mem_setOf_eq, coprime_sievePrimorial_insert_iff hp]
          exact fun h => hcop h.1),
        Set.indicator_of_notMem (by rw [hC]; exact fun h => hcop h.1), add_zero]
  have hAs : Summable (A.indicator f) := hf.indicator _
  have hBs : Summable (B.indicator f) := hf.indicator _
  have hCs : Summable (C.indicator f) := hf.indicator _
  -- the multiples of `p` inside the sieved class carry the scaled sum
  have hmulpart : (∑' n : ℕ, C.indicator f n)
      = f (p : ℕ) * ∑' n : ℕ, A.indicator f n := by
    have hinj : Function.Injective fun m : ℕ => (p : ℕ) * m :=
      fun a b hab => Nat.eq_of_mul_eq_mul_left p.2.pos hab
    have hsupp : Function.support (C.indicator f) ⊆ Set.range fun m : ℕ => (p : ℕ) * m := by
      intro n hn
      have hmem : n ∈ C := by
        by_contra hcon
        exact hn (Set.indicator_of_notMem hcon f)
      obtain ⟨m, hm⟩ := hmem.2
      exact ⟨m, hm.symm⟩
    rw [← hinj.tsum_eq hsupp]
    have hterm : ∀ m : ℕ, C.indicator f ((p : ℕ) * m) = f (p : ℕ) * A.indicator f m := by
      intro m
      by_cases hcop : Nat.Coprime m (sievePrimorial P)
      · have hcopm : Nat.Coprime ((p : ℕ) * m) (sievePrimorial P) :=
          Nat.coprime_mul_iff_left.mpr ⟨hcopP, hcop⟩
        rw [Set.indicator_of_mem (by rw [hC]; exact ⟨hcopm, Dvd.intro m rfl⟩),
          Set.indicator_of_mem (by rw [hA]; exact hcop), hmul]
      · rw [Set.indicator_of_notMem (by
          rw [hC]
          exact fun h => hcop (Nat.coprime_mul_iff_left.mp h.1).2),
          Set.indicator_of_notMem (by rw [hA]; exact hcop), mul_zero]
    rw [tsum_congr hterm, tsum_mul_left]
  have hsum : (∑' n : ℕ, A.indicator f n)
      = (∑' n : ℕ, B.indicator f n) + f (p : ℕ) * ∑' n : ℕ, A.indicator f n :=
    calc (∑' n : ℕ, A.indicator f n)
        = (∑' n : ℕ, B.indicator f n) + (∑' n : ℕ, C.indicator f n) := by
          rw [← Summable.tsum_add hBs hCs]
          exact tsum_congr hpoint
      _ = (∑' n : ℕ, B.indicator f n) + f (p : ℕ) * ∑' n : ℕ, A.indicator f n := by
          rw [hmulpart]
  have hring : (∑' n : ℕ, A.indicator f n) * (1 - f (p : ℕ))
      = (∑' n : ℕ, A.indicator f n) - f (p : ℕ) * ∑' n : ℕ, A.indicator f n := by
    ring
  rw [sievedSum, sievedSum, ← hA, ← hB, hring]
  linarith [hsum]

/-- **Sieved Euler product.**  The sieved sum of a completely multiplicative
summable weight is the total sum times the finite Euler product. -/
theorem sievedSum_eq_mul_prod {f : ℕ → ℝ} (hf : Summable f)
    (hmul : ∀ m n : ℕ, f (m * n) = f m * f n) (P : Finset Nat.Primes) :
    sievedSum f P = (∑' n : ℕ, f n) * ∏ p ∈ P, (1 - f (p : ℕ)) := by
  classical
  induction P using Finset.induction with
  | empty =>
      simp only [sievePrimorial_empty, Finset.prod_empty, mul_one, sievedSum]
      refine tsum_congr fun n => ?_
      rw [Set.indicator_of_mem (by simp)]
  | insert p P hp ih =>
      rw [sievedSum_insert hf hmul hp, ih, Finset.prod_insert hp]
      ring

section ZetaTrace

/-- The diagonal trace weight `n ↦ n^{-k}` is completely multiplicative. -/
theorem multiplicative_rpow_inv {k : ℝ} (m n : ℕ) :
    ((((m * n : ℕ) : ℝ)) ^ k)⁻¹ = (((m : ℕ) : ℝ) ^ k)⁻¹ * (((n : ℕ) : ℝ) ^ k)⁻¹ := by
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity), mul_inv]

/-- The diagonal trace weight is summable above the abscissa one. -/
theorem summable_rpow_inv {k : ℝ} (hk : 1 < k) :
    Summable fun n : ℕ => (((n : ℕ) : ℝ) ^ k)⁻¹ := by
  simpa [one_div] using (Real.summable_one_div_nat_rpow).mpr hk

/-- **Sieved zeta trace.**  The trace of the `k`-th power of the sieved diagonal
operator is the zeta value times the finite Euler product of the sieve. -/
theorem sievedSum_rpow_inv {k : ℝ} (hk : 1 < k) (P : Finset Nat.Primes) :
    sievedSum (fun n : ℕ => (((n : ℕ) : ℝ) ^ k)⁻¹) P
      = (∑' n : ℕ, (((n : ℕ) : ℝ) ^ k)⁻¹)
        * ∏ p ∈ P, (1 - ((((p : ℕ) : ℝ)) ^ k)⁻¹) :=
  sievedSum_eq_mul_prod (summable_rpow_inv hk) (fun m n => multiplicative_rpow_inv m n) P

end ZetaTrace

end GaloisForLFunctions.HTGeometry

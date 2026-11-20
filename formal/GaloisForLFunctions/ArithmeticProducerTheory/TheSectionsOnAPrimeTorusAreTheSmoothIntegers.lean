import GaloisForLFunctions.ArithmeticProducerTheory.TheRiemannRochCountOnAFinitePrimeTorus
import GaloisForLFunctions.RHTower.Sieve.SmoothSum

/-!
# The sections on a prime torus are the smooth integers

For distinct primes `p_1, …, p_k` the exponent vectors of degree `≤ log X` are in bijection with
the integers `≤ X` composed of these primes (`card_smoothUpTo_eq_card_simplexPoints`). The
Riemann–Roch count on the torus is therefore a two-sided count of smooth integers.

* `card_smoothUpTo_finset_bounds`: for a finite set `S` of primes and `X ≥ 1`,
  `(log X)^k ≤ k! · Π_{p ∈ S} log p · Ψ(X; S) ≤ (log X + Σ_{p ∈ S} log p)^k`, `k = |S|`.
  This is the number of unknowns in a Siegel lemma on `S`-smooth integers.
* `card_smoothUpTo_of_full`: when `S` contains every prime `≤ N`, the count is `N`.
* `card_smoothUpTo_mul_le`: when `S` contains every prime `≤ XY`, the product of the counts at
  `X` and `Y` is at most the count at `XY`. The comparison of a product of two dimensions with the
  dimension at the sum of the degrees, which produces the auxiliary section on a curve, is
  marginal on the full prime torus; on few primes it holds from a degree of the order of
  `Σ_{p ∈ S} log p` on.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticProducerTheory

open RHTower.Sieve

section Monomials

variable {k : ℕ} {p : Fin k → ℕ}

/-- The exponent of `p_j` in a monomial of distinct primes. -/
theorem factorization_prod_pow (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (α : Fin k → ℕ) (j : Fin k) : (∏ i, p i ^ α i).factorization (p j) = α j := by
  rw [Nat.factorization_prod fun i _ => pow_ne_zero _ (hp i).ne_zero, Finsupp.finsetSum_apply,
    Finset.sum_eq_single j]
  · rw [(hp j).factorization_pow, Finsupp.single_apply, if_pos rfl]
  · intro i _ hij
    rw [(hp i).factorization_pow, Finsupp.single_apply, if_neg fun h => hij (hinj h)]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem primeFactors_prod_pow_subset (hp : ∀ i, (p i).Prime) (α : Fin k → ℕ) :
    (∏ i, p i ^ α i).primeFactors ⊆ Finset.univ.image p := by
  intro q hq
  have hqp := Nat.prime_of_mem_primeFactors hq
  obtain ⟨i, -, hi⟩ :=
    (Prime.dvd_finsetProd_iff hqp.prime _).mp (Nat.dvd_of_mem_primeFactors hq)
  have h1 : q ∣ p i := hqp.dvd_of_dvd_pow hi
  exact Finset.mem_image.mpr
    ⟨i, Finset.mem_univ i, ((Nat.prime_dvd_prime_iff_eq hqp (hp i)).mp h1).symm⟩

/-- An integer composed of the primes `p_i` is the monomial of its exponents. -/
theorem prod_pow_factorization (hinj : Function.Injective p) {n : ℕ} (hn : n ≠ 0)
    (hsub : n.primeFactors ⊆ Finset.univ.image p) : ∏ i, p i ^ n.factorization (p i) = n := by
  have h3 := Nat.prod_factorization_pow_eq_self hn
  rw [Finsupp.prod, Nat.support_factorization] at h3
  have h2 : ∏ q ∈ n.primeFactors, q ^ n.factorization q =
      ∏ q ∈ Finset.univ.image p, q ^ n.factorization q := by
    refine Finset.prod_subset hsub fun q _ hq => ?_
    have h0 : n.factorization q = 0 :=
      Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
    rw [h0, pow_zero]
  rw [Finset.prod_image fun i _ j _ h => hinj h] at h2
  exact h2.symm.trans h3

end Monomials

/-- The sections of degree `≤ log X` on the torus of the primes `p_i` are in bijection with the
integers `≤ X` composed of these primes. -/
theorem card_smoothUpTo_eq_card_simplexPoints {k : ℕ} {p : Fin k → ℕ} (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) {X : ℝ} (hX : 0 < X) :
    (smoothUpTo (Finset.univ.image p) ⌊X⌋₊).card =
      (simplexPoints k (fun i => Real.log (p i)) (Real.log X)).card := by
  have hp2 : ∀ i, 2 ≤ p i := fun i => (hp i).two_le
  symm
  refine Finset.card_bij (fun α _ => ∏ i, p i ^ α i) ?_ ?_ ?_
  · intro α hα
    have h1 := (mem_simplexPoints_log hp2 hX).mp hα
    refine mem_smoothUpTo.mpr ⟨⟨?_, Nat.le_floor h1⟩, primeFactors_prod_pow_subset hp α⟩
    exact Nat.pos_of_ne_zero
      (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hp i).ne_zero)
  · intro α _ β _ h
    have h' : ∏ i, p i ^ α i = ∏ i, p i ^ β i := h
    funext j
    rw [← factorization_prod_pow hp hinj α j, h', factorization_prod_pow hp hinj β j]
  · intro n hn
    obtain ⟨⟨hn1, hnX⟩, hsub⟩ := mem_smoothUpTo.mp hn
    have hprod := prod_pow_factorization hinj (by omega : n ≠ 0) hsub
    have hle : ((∏ i, p i ^ n.factorization (p i) : ℕ) : ℝ) ≤ X := by
      rw [hprod]
      exact (Nat.cast_le.mpr hnX).trans (Nat.floor_le hX.le)
    exact ⟨fun i => n.factorization (p i), (mem_simplexPoints_log hp2 hX).mpr hle, hprod⟩

/-- **The count of smooth integers lies between two simplex volumes.** -/
theorem card_smoothUpTo_bounds {k : ℕ} {p : Fin k → ℕ} (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) {X : ℝ} (hX : 1 ≤ X) :
    Real.log X ^ k ≤ (k.factorial : ℝ) * (∏ i, Real.log (p i)) *
        (smoothUpTo (Finset.univ.image p) ⌊X⌋₊).card ∧
      (k.factorial : ℝ) * (∏ i, Real.log (p i)) *
          (smoothUpTo (Finset.univ.image p) ⌊X⌋₊).card ≤
        (Real.log X + ∑ i, Real.log (p i)) ^ k := by
  have hw : ∀ i, 0 < Real.log (p i) := fun i =>
    Real.log_pos (by exact_mod_cast (hp i).one_lt)
  rw [card_smoothUpTo_eq_card_simplexPoints hp hinj (by linarith)]
  exact card_simplexPoints_bounds k _ hw _ (Real.log_nonneg hX)

/-- **Riemann–Roch for the integers composed of a finite set `S` of primes.** With `k = |S|`,
`(log X)^k ≤ k! · Π_{p ∈ S} log p · Ψ(X; S) ≤ (log X + Σ_{p ∈ S} log p)^k`. -/
theorem card_smoothUpTo_finset_bounds {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) {X : ℝ}
    (hX : 1 ≤ X) :
    Real.log X ^ S.card ≤ (S.card.factorial : ℝ) * (∏ q ∈ S, Real.log q) *
        (smoothUpTo S ⌊X⌋₊).card ∧
      (S.card.factorial : ℝ) * (∏ q ∈ S, Real.log q) * (smoothUpTo S ⌊X⌋₊).card ≤
        (Real.log X + ∑ q ∈ S, Real.log q) ^ S.card := by
  obtain ⟨p, hpdef⟩ : ∃ p : Fin S.card → ℕ, p = fun i => S.orderEmbOfFin rfl i := ⟨_, rfl⟩
  have hinj : Function.Injective p := by
    rw [hpdef]
    exact (S.orderEmbOfFin rfl).injective
  have himg : Finset.univ.image p = S := by
    rw [hpdef]
    exact Finset.image_orderEmbOfFin_univ S rfl
  have hp : ∀ i, (p i).Prime := fun i => hS _ (by
    rw [hpdef]
    exact Finset.orderEmbOfFin_mem S rfl i)
  have hprod := Finset.prod_image (s := Finset.univ) (g := p)
    (f := fun q : ℕ => Real.log q) fun i _ j _ h => hinj h
  have hsum := Finset.sum_image (s := Finset.univ) (g := p)
    (f := fun q : ℕ => Real.log q) fun i _ j _ h => hinj h
  rw [himg] at hprod hsum
  have h := card_smoothUpTo_bounds hp hinj hX
  rw [himg, ← hprod, ← hsum] at h
  exact h

/-- On a set of primes containing every prime `≤ N`, every integer in `[1, N]` is a section. -/
theorem smoothUpTo_eq_Icc {S : Finset ℕ} {N : ℕ} (hS : ∀ q : ℕ, q.Prime → q ≤ N → q ∈ S) :
    smoothUpTo S N = Finset.Icc 1 N := by
  ext s
  rw [mem_smoothUpTo, Finset.mem_Icc]
  refine ⟨fun h => h.1, fun h => ⟨h, fun q hq => ?_⟩⟩
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hle : q ≤ s := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hq)
  exact hS q hqp (hle.trans h.2)

theorem card_smoothUpTo_of_full {S : Finset ℕ} {N : ℕ}
    (hS : ∀ q : ℕ, q.Prime → q ≤ N → q ∈ S) : (smoothUpTo S N).card = N := by
  rw [smoothUpTo_eq_Icc hS, Nat.card_Icc, Nat.add_sub_cancel]

theorem card_smoothUpTo_le (S : Finset ℕ) (N : ℕ) : (smoothUpTo S N).card ≤ N := by
  have h := Finset.card_le_card
    (fun s hs => Finset.mem_Icc.mpr (mem_smoothUpTo.mp hs).1 : smoothUpTo S N ⊆ Finset.Icc 1 N)
  rwa [Nat.card_Icc, Nat.add_sub_cancel] at h

/-- **On all primes the product of two counts never exceeds the count at the sum of the
degrees.** -/
theorem card_smoothUpTo_mul_le {S : Finset ℕ} {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hS : ∀ q : ℕ, q.Prime → q ≤ ⌊X * Y⌋₊ → q ∈ S) :
    (smoothUpTo S ⌊X⌋₊).card * (smoothUpTo S ⌊Y⌋₊).card ≤ (smoothUpTo S ⌊X * Y⌋₊).card := by
  rw [card_smoothUpTo_of_full hS]
  have h3 : ⌊X⌋₊ * ⌊Y⌋₊ ≤ ⌊X * Y⌋₊ := by
    apply Nat.le_floor
    push_cast
    exact mul_le_mul (Nat.floor_le hX) (Nat.floor_le hY) (Nat.cast_nonneg _) hX
  exact (Nat.mul_le_mul (card_smoothUpTo_le S _) (card_smoothUpTo_le S _)).trans h3

end GaloisForLFunctions.ArithmeticProducerTheory

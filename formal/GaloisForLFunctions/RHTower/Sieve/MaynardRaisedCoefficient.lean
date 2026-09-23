import GaloisForLFunctions.RHTower.Sieve.PrimePowerSupport
import GaloisForLFunctions.RHTower.DivisorBound

/-!
# Divisor-controlled energy of a raised Dirichlet factor

Maynard's all-short case raises one grouped Dirichlet factor to a bounded power.  The resulting
coefficient vector is `convPow`.  A tuple in one coefficient fibre maps injectively to the tuple
of its entries, and every entry divides the anchored product.  Hence an `ℓ`-fold fibre has at most
`d(n)^ℓ` points.  The divisor bound then gives an arbitrarily small power loss, uniformly in the
original coefficients.

The final theorem is the coefficient-energy input needed by the Huxley large-values row:

`∑ |convPow a|² ≤ C (N^ℓ)^ε (∑ |a|²)^ℓ`.
-/

namespace RHTower.Sieve

open Finset

/-- **Every power fibre injects into a tuple of divisors of its anchored product.** -/
theorem powFibreOn_card_le_divisors_pow (N ℓ : ℕ) (S : Finset (Fin N))
    (j : Fin (N ^ ℓ)) :
    (powFibreOn N ℓ S j).card ≤ (Nat.divisors ((j : ℕ) + 1)).card ^ ℓ := by
  classical
  set F : (Fin ℓ → Fin N) → (Fin ℓ → ℕ) := fun p i => (p i : ℕ) + 1 with hF
  have hprod : ∀ p ∈ powFibreOn N ℓ S j,
      ∏ i : Fin ℓ, ((p i : ℕ) + 1) = (j : ℕ) + 1 := by
    intro p hp
    simp only [powFibreOn, Finset.mem_filter] at hp
    rw [← powIdx_val_add_one p, hp.1.2]
  have hmaps : ∀ p ∈ powFibreOn N ℓ S j,
      F p ∈ Fintype.piFinset (fun _ : Fin ℓ => Nat.divisors ((j : ℕ) + 1)) := by
    intro p hp
    rw [Fintype.mem_piFinset]
    intro i
    refine Nat.mem_divisors.2 ⟨?_, by omega⟩
    rw [← hprod p hp, hF]
    exact Finset.dvd_prod_of_mem (fun k : Fin ℓ => ((p k : ℕ) + 1)) (Finset.mem_univ i)
  have hinj : Set.InjOn F (powFibreOn N ℓ S j) := by
    intro p _ q _ hpq
    funext i
    apply Fin.ext
    have hi := congrFun hpq i
    simpa [hF] using hi
  have hcard := Finset.card_le_card_of_injOn F hmaps hinj
  simpa [Fintype.card_piFinset] using hcard

/-- **A bounded-fold product fibre costs only an arbitrarily small power.** -/
theorem exists_powFibreOn_card_le_rpow (ℓ : ℕ) (hℓ : 0 < ℓ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (S : Finset (Fin N))
      (j : Fin (N ^ ℓ)),
      ((powFibreOn N ℓ S j).card : ℝ) ≤ C * ((N ^ ℓ : ℕ) : ℝ) ^ ε := by
  obtain ⟨C₀, hC₀, hdiv⟩ :=
    RHTower.card_divisors_le_const_mul_rpow (ε := ε / (ℓ : ℝ)) (by positivity)
  refine ⟨C₀ ^ ℓ, by positivity, ?_⟩
  intro N hN S j
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
  have hnpos : (0 : ℝ) < (((j : ℕ) + 1 : ℕ) : ℝ) := by positivity
  have hd := hdiv ((j : ℕ) + 1) (by omega)
  have hcard : ((powFibreOn N ℓ S j).card : ℝ)
      ≤ (((Nat.divisors ((j : ℕ) + 1)).card : ℝ)) ^ ℓ := by
    exact_mod_cast powFibreOn_card_le_divisors_pow N ℓ S j
  have hd0 : (0 : ℝ) ≤ ((Nat.divisors ((j : ℕ) + 1)).card : ℝ) := Nat.cast_nonneg _
  have hpow := pow_le_pow_left₀ hd0 hd ℓ
  have hexp : (((((j : ℕ) + 1 : ℕ) : ℝ) ^ (ε / (ℓ : ℝ))) ^ ℓ)
      = ((((j : ℕ) + 1 : ℕ) : ℝ) ^ ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
    congr 1
    field_simp
  have hfactor : (C₀ * ((((j : ℕ) + 1 : ℕ) : ℝ) ^ (ε / (ℓ : ℝ)))) ^ ℓ
      = C₀ ^ ℓ * ((((j : ℕ) + 1 : ℕ) : ℝ) ^ ε) := by
    rw [mul_pow, hexp]
  rw [hfactor] at hpow
  have hjle : ((j : ℕ) + 1) ≤ N ^ ℓ := j.isLt
  have hjcast : ((((j : ℕ) + 1 : ℕ) : ℝ)) ≤ (((N ^ ℓ : ℕ) : ℝ)) := by
    exact_mod_cast hjle
  have hmono : ((((j : ℕ) + 1 : ℕ) : ℝ) ^ ε)
      ≤ (((N ^ ℓ : ℕ) : ℝ)) ^ ε :=
    Real.rpow_le_rpow hnpos.le hjcast hε.le
  calc
    ((powFibreOn N ℓ S j).card : ℝ)
        ≤ (((Nat.divisors ((j : ℕ) + 1)).card : ℝ)) ^ ℓ := hcard
    _ ≤ C₀ ^ ℓ * ((((j : ℕ) + 1 : ℕ) : ℝ) ^ ε) := hpow
    _ ≤ C₀ ^ ℓ * (((N ^ ℓ : ℕ) : ℝ)) ^ ε :=
      mul_le_mul_of_nonneg_left hmono (by positivity)

/-- **Raised-factor energy theorem.**  For every fixed positive raising exponent, the complete
coefficient energy loses only an arbitrarily small power of the raised length. -/
theorem exists_sum_normSq_convPow_le_rpow (ℓ : ℕ) (hℓ : 0 < ℓ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ a : Fin N → ℂ,
      ∑ j : Fin (N ^ ℓ), ‖convPow N ℓ a j‖ ^ 2
        ≤ C * ((N ^ ℓ : ℕ) : ℝ) ^ ε * (∑ n : Fin N, ‖a n‖ ^ 2) ^ ℓ := by
  obtain ⟨C, hC, hfibre⟩ := exists_powFibreOn_card_le_rpow ℓ hℓ hε
  refine ⟨C, hC, ?_⟩
  intro N hN a
  have hD0 : 0 ≤ C * ((N ^ ℓ : ℕ) : ℝ) ^ ε := by positivity
  exact sum_normSq_convPow_le_of_support_primePowerSupport N ℓ a Finset.univ
    (fun n _ => Finset.mem_univ n) (fun j => hfibre N hN Finset.univ j) hD0

/-- **Multiplicative support survives raising.**  If the original factor is supported in the
closed dyadic interval `[A,2A]`, its `ℓ`-th power is supported in `[A^ℓ,(2A)^ℓ]`.  The closed upper
endpoint is deliberate: it permits direct use for sharply truncated dyadic factors and costs at
most one final dyadic block. -/
theorem convPow_support_dyadic {N A ℓ : ℕ} (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 → A ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A)
    (j : Fin (N ^ ℓ)) (hj : convPow N ℓ a j ≠ 0) :
    A ^ ℓ ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ (2 * A) ^ ℓ := by
  classical
  have hex : ∃ p ∈ (Finset.univ : Finset (Fin ℓ → Fin N)).filter (fun p => powIdx p = j),
      ∏ i : Fin ℓ, a (p i) ≠ 0 := by
    by_contra h
    push Not at h
    apply hj
    rw [convPow]
    exact Finset.sum_eq_zero h
  obtain ⟨p, hp, hpne⟩ := hex
  have hcoord : ∀ i : Fin ℓ, a (p i) ≠ 0 := by
    intro i
    exact (Finset.prod_ne_zero_iff.mp hpne) i (Finset.mem_univ i)
  have hlo : A ^ ℓ ≤ ∏ i : Fin ℓ, ((p i : ℕ) + 1) := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (Finset.prod_le_prod' (s := (Finset.univ : Finset (Fin ℓ)))
        (fun i _ => (hsupp (p i) (hcoord i)).1))
  have hhi : (∏ i : Fin ℓ, ((p i : ℕ) + 1)) ≤ (2 * A) ^ ℓ := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (Finset.prod_le_prod' (s := (Finset.univ : Finset (Fin ℓ)))
        (fun i _ => (hsupp (p i) (hcoord i)).2))
  have hindex : ∏ i : Fin ℓ, ((p i : ℕ) + 1) = (j : ℕ) + 1 := by
    rw [← powIdx_val_add_one p]
    have := congrArg Fin.val (Finset.mem_filter.mp hp).2
    omega
  rw [hindex] at hlo hhi
  exact ⟨hlo, hhi⟩

/-- **General fixed-width multiplicative support.**  A factor supported in
`[A,A*2^w]` has its `ℓ`-th power supported in `[A^ℓ,(A*2^w)^ℓ]`.  This is the form needed for a
grouped product of several Heath--Brown dyadic factors: `w` is the number of factors in the group
and remains bounded independently of height. -/
theorem convPow_support_fixedWidth {N A w ℓ : ℕ} (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 →
      A ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ A * 2 ^ w)
    (j : Fin (N ^ ℓ)) (hj : convPow N ℓ a j ≠ 0) :
    A ^ ℓ ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ (A * 2 ^ w) ^ ℓ := by
  classical
  have hex : ∃ p ∈ (Finset.univ : Finset (Fin ℓ → Fin N)).filter (fun p => powIdx p = j),
      ∏ i : Fin ℓ, a (p i) ≠ 0 := by
    by_contra h
    push Not at h
    apply hj
    rw [convPow]
    exact Finset.sum_eq_zero h
  obtain ⟨p, hp, hpne⟩ := hex
  have hcoord : ∀ i : Fin ℓ, a (p i) ≠ 0 := by
    intro i
    exact (Finset.prod_ne_zero_iff.mp hpne) i (Finset.mem_univ i)
  have hlo : A ^ ℓ ≤ ∏ i : Fin ℓ, ((p i : ℕ) + 1) := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (Finset.prod_le_prod' (s := (Finset.univ : Finset (Fin ℓ)))
        (fun i _ => (hsupp (p i) (hcoord i)).1))
  have hhi : (∏ i : Fin ℓ, ((p i : ℕ) + 1)) ≤ (A * 2 ^ w) ^ ℓ := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (Finset.prod_le_prod' (s := (Finset.univ : Finset (Fin ℓ)))
        (fun i _ => (hsupp (p i) (hcoord i)).2))
  have hindex : ∏ i : Fin ℓ, ((p i : ℕ) + 1) = (j : ℕ) + 1 := by
    rw [← powIdx_val_add_one p]
    have := congrArg Fin.val (Finset.mem_filter.mp hp).2
    omega
  rw [hindex] at hlo hhi
  exact ⟨hlo, hhi⟩

end RHTower.Sieve

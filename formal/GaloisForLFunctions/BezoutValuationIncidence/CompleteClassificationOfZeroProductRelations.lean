import GaloisForLFunctions.BezoutValuationIncidence.ValuationLawForZeroProductRelationsAndVisibilityDegree

/-!
# Complete classification of zero-product relations and of sign visibility

An order tuple `(q_1, …, q_m)` is **layer admissible** if for every prime `p` and every `a ≥ 1`
with no `q_i` divisible by `p^{a+1}`, the number of `q_i` divisible by `p^a` is not one, and is
even when `p = 2`. The layer law says that the orders of a zero-product relation are layer
admissible. Conversely:

**Theorem.** Every layer-admissible tuple of positive orders is realized: there are primitive
`q_i`-th roots of unity `ζ_i` with `Π ζ_i = 1`.

The construction is prime by prime. At `p`, with top exponent `A` attained `n ≥ 2` times, take
`ω` primitive of order `p^A` and `η_i = ω^{p^{A - e_i} w_i}`, where `e_i = v_p(q_i)`, `w_i = 1`
except at two top indices: one carries the residue that closes the relation modulo `p^A`, the
other carries `2` when `p ∣ n - 1`. That residue is prime to `p` because the top layer contributes
`n - 1` or `n` modulo `p`. Primitive roots of coprime prime-power orders multiply to a primitive
root of the product order.

Combined with the sign visibility law this classifies visibility completely: **a degree-`m`
translated moment distinguishes `Y` from `εY` iff some layer-admissible `m`-tuple of active orders
has `Π ε ≠ 1`.** Which sign patterns are seen at which degree is a statement about valuations alone.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- Layer admissibility of an order tuple. -/
def IsLayerAdmissible {m : ℕ} (q : Fin m → ℕ) : Prop :=
  ∀ p a, p.Prime → 1 ≤ a → (∀ i, ¬ p ^ (a + 1) ∣ q i) →
    layerCount q p a ≠ 1 ∧ (p = 2 → Even (layerCount q p a))

/-! ## The construction at one prime -/

/-- **Relations at one prime.** If the top exponent of `e` is attained not exactly once (an even
number of times when `p = 2`), there are primitive `p^{e_i}`-th roots of unity multiplying to one. -/
theorem exists_primePower_relation {m p : ℕ} (hp : p.Prime) (e : Fin m → ℕ)
    (hadm : ∀ A, 1 ≤ A → (∀ i, e i ≤ A) →
      (univ.filter fun i => A ≤ e i).card ≠ 1 ∧
        (p = 2 → Even (univ.filter fun i => A ≤ e i).card)) :
    ∃ η : Fin m → ℂ, (∀ i, IsPrimitiveRoot (η i) (p ^ e i)) ∧ ∏ i, η i = 1 := by
  classical
  set A := univ.sup e
  have hle : ∀ i, e i ≤ A := fun i => le_sup (mem_univ i)
  rcases Nat.eq_zero_or_pos A with hA | hA
  · refine ⟨fun _ => 1, fun i => ?_, by simp⟩
    rw [show e i = 0 by have := hle i; omega, pow_zero]
    exact IsPrimitiveRoot.one
  set T := univ.filter fun i => A ≤ e i
  obtain ⟨hT1, hT2⟩ := hadm A hA hle
  obtain ⟨j0, hj0⟩ : ∃ j, e j = A := by
    by_contra h
    push Not at h
    have hlt : univ.sup e < A := (Finset.sup_lt_iff (s := univ) (f := e)
      (show (⊥ : ℕ) < A from hA)).mpr fun i _ => lt_of_le_of_ne (hle i) (h i)
    exact lt_irrefl _ hlt
  have hj0T : j0 ∈ T := mem_filter.mpr ⟨mem_univ _, hj0.ge⟩
  have hTcard : 1 < T.card := by
    have h0 := card_pos.mpr ⟨j0, hj0T⟩
    have h1 : T.card ≠ 1 := hT1
    omega
  obtain ⟨j1, hj1T, hj10⟩ := exists_mem_ne hTcard j0
  set n := T.card
  -- the bump at `j1` keeps the closing residue prime to `p`
  set w : Fin m → ℕ := fun i => if i = j1 ∧ p ∣ n - 1 then 2 else 1
  set S' := ∑ i ∈ univ.erase j0, p ^ (A - e i) * w i
  set W := p ^ A * (S' + 1) - S'
  set wt : Fin m → ℕ := fun i => if i = j0 then W else w i
  have hpA : 0 < p ^ A := pow_pos hp.pos A
  have hSW : W + S' = p ^ A * (S' + 1) := by
    have : S' ≤ p ^ A * (S' + 1) := le_trans (Nat.le_succ S') (Nat.le_mul_of_pos_left _ hpA)
    omega
  -- `S'` is prime to `p`
  have hS' : ¬ p ∣ S' := by
    have hsplit := sum_filter_add_sum_filter_not (univ.erase j0) (fun i => A ≤ e i)
      (fun i => p ^ (A - e i) * w i)
    have htop : (univ.erase j0).filter (fun i => A ≤ e i) = T.erase j0 := by
      ext i
      simp only [mem_filter, mem_erase, mem_univ, T]
      tauto
    have htopsum : ∑ i ∈ T.erase j0, p ^ (A - e i) * w i = (n - 1) + if p ∣ n - 1 then 1 else 0 := by
      have hterm : ∀ i ∈ T.erase j0, p ^ (A - e i) * w i =
          1 + if i = j1 then (if p ∣ n - 1 then 1 else 0) else 0 := by
        intro i hi
        have hei : e i = A := le_antisymm (hle i) (mem_filter.mp (mem_of_mem_erase hi)).2
        simp only [hei, Nat.sub_self, pow_zero, one_mul, w]
        by_cases h1 : i = j1 <;> by_cases h2 : p ∣ n - 1 <;> simp [h1, h2]
      rw [sum_congr rfl hterm, sum_add_distrib, sum_const, smul_eq_mul, mul_one,
        card_erase_of_mem hj0T, sum_ite_eq' (T.erase j0) j1,
        if_pos (mem_erase.mpr ⟨hj10, hj1T⟩)]
    have hlow : p ∣ ∑ i ∈ (univ.erase j0).filter (fun i => ¬ A ≤ e i), p ^ (A - e i) * w i :=
      dvd_sum fun i hi => by
        have hlt : e i < A := lt_of_not_ge (mem_filter.mp hi).2
        exact dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
    intro hdvd
    change p ∣ ∑ i ∈ univ.erase j0, p ^ (A - e i) * w i at hdvd
    rw [← hsplit, htop, htopsum] at hdvd
    have hY := (Nat.dvd_add_left hlow).mp hdvd
    by_cases hc : p ∣ n - 1
    · rw [if_pos hc, show n - 1 + 1 = n by omega] at hY
      have h1 : p ∣ n - (n - 1) := Nat.dvd_sub hY hc
      rw [show n - (n - 1) = 1 by omega] at h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
    · rw [if_neg hc, add_zero] at hY
      exact hc hY
  have hW : ¬ p ∣ W := by
    intro h
    have h1 : p ∣ W + S' := by rw [hSW]; exact dvd_mul_of_dvd_left (dvd_pow_self p hA.ne') _
    exact hS' ((Nat.dvd_add_right h).mp h1)
  have hcopw : ∀ i, Nat.Coprime (wt i) p := by
    intro i
    simp only [wt, w]
    split_ifs with h0 h1
    · exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hW).symm
    · have hp2 : p ≠ 2 := by
        rintro rfl
        obtain ⟨t, ht⟩ := hT2 rfl
        exact absurd h1.2 (by rw [Nat.two_dvd_ne_zero]; omega)
      exact (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
    · exact Nat.coprime_one_left p
  have hω := Complex.isPrimitiveRoot_exp (p ^ A) hpA.ne'
  set ω := Complex.exp (2 * ↑Real.pi * Complex.I / ↑(p ^ A))
  refine ⟨fun i => ω ^ (p ^ (A - e i) * wt i), fun i => ?_, ?_⟩
  · have h1 := hω.pow_of_dvd (pow_ne_zero (A - e i) hp.ne_zero) (pow_dvd_pow p (Nat.sub_le A (e i)))
    rw [Nat.pow_div (Nat.sub_le A (e i)) hp.pos, Nat.sub_sub_self (hle i)] at h1
    show IsPrimitiveRoot (ω ^ (p ^ (A - e i) * wt i)) (p ^ e i)
    rw [pow_mul]
    exact h1.pow_of_coprime _ (Nat.Coprime.pow_right _ (hcopw i))
  · rw [prod_pow_eq_pow_sum, ← add_sum_erase _ _ (mem_univ j0)]
    have hrest : ∑ i ∈ univ.erase j0, p ^ (A - e i) * wt i = S' :=
      sum_congr rfl fun i hi => by simp only [wt, if_neg (ne_of_mem_erase hi)]
    rw [hrest, hj0, Nat.sub_self, pow_zero, one_mul]
    simp only [wt, if_pos rfl]
    rw [hSW, pow_mul, hω.pow_eq_one, one_pow]

/-! ## Gluing the primes -/

/-- Primitive roots of pairwise coprime prime-power orders multiply to a primitive root of the
product order. -/
theorem isPrimitiveRoot_prod_primePowers {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (k : ℕ → ℕ)
    (x : ℕ → ℂ) (hx : ∀ p ∈ P, IsPrimitiveRoot (x p) (p ^ k p)) :
    IsPrimitiveRoot (∏ p ∈ P, x p) (∏ p ∈ P, p ^ k p) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | insert a P ha ih =>
    rw [prod_insert ha, prod_insert ha]
    have h1 := hx a (mem_insert_self a P)
    have h2 := ih (fun p hp => hP p (mem_insert_of_mem hp)) fun p hp => hx p (mem_insert_of_mem hp)
    have hcop : Nat.Coprime (a ^ k a) (∏ p ∈ P, p ^ k p) :=
      Nat.Coprime.prod_right fun p hp => Nat.Coprime.pow _ _
        ((Nat.coprime_primes (hP a (mem_insert_self a P)) (hP p (mem_insert_of_mem hp))).mpr
          fun h => ha (h ▸ hp))
    have hord := (Commute.all (x a) (∏ p ∈ P, x p)).orderOf_mul_eq_mul_orderOf_of_coprime
      (by rwa [← h1.eq_orderOf, ← h2.eq_orderOf])
    rw [h1.eq_orderOf, h2.eq_orderOf, ← hord]
    exact IsPrimitiveRoot.orderOf _

theorem prod_pow_factorization_of_subset {n : ℕ} (hn : n ≠ 0) {P : Finset ℕ}
    (hP : n.primeFactors ⊆ P) : ∏ p ∈ P, p ^ n.factorization p = n := by
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization]
  exact (prod_subset hP fun p _ hp => by
    rw [Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization]), pow_zero]).symm

/-! ## The classification -/

/-- **Every layer-admissible tuple is the order tuple of a zero-product relation.** -/
theorem exists_zeroProduct_of_isLayerAdmissible {m : ℕ} (q : Fin m → ℕ) (hq : ∀ i, 0 < q i)
    (hadm : IsLayerAdmissible q) :
    ∃ ζ : Fin m → ℂ, (∀ i, IsPrimitiveRoot (ζ i) (q i)) ∧ ∏ i, ζ i = 1 := by
  classical
  set P := (∏ i, q i).primeFactors
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hprod0 : (∏ i, q i) ≠ 0 := prod_ne_zero_iff.mpr fun i _ => (hq i).ne'
  have hsub : ∀ i, (q i).primeFactors ⊆ P := fun i =>
    Nat.primeFactors_mono (dvd_prod_of_mem _ (mem_univ i)) hprod0
  have hlocal : ∀ p ∈ P, ∃ η : Fin m → ℂ,
      (∀ i, IsPrimitiveRoot (η i) (p ^ (q i).factorization p)) ∧ ∏ i, η i = 1 := by
    intro p hpP
    have hp := hPprime p hpP
    refine exists_primePower_relation hp (fun i => (q i).factorization p) fun A hA hleA => ?_
    have hfac : ∀ i, p ^ A ∣ q i ↔ A ≤ (q i).factorization p := fun i =>
      hp.pow_dvd_iff_le_factorization (hq i).ne'
    have htop : ∀ i, ¬ p ^ (A + 1) ∣ q i := fun i h =>
      absurd ((hp.pow_dvd_iff_le_factorization (hq i).ne').mp h) (by have := hleA i; omega)
    have hcount : layerCount q p A = (univ.filter fun i => A ≤ (q i).factorization p).card := by
      unfold layerCount
      congr 1
      exact filter_congr fun i _ => hfac i
    rw [← hcount]
    exact hadm p A hp hA htop
  choose! η hη hηprod using hlocal
  refine ⟨fun i => ∏ p ∈ P, η p i, fun i => ?_, ?_⟩
  · have h := isPrimitiveRoot_prod_primePowers hPprime (fun p => (q i).factorization p)
      (fun p => η p i) fun p hp => hη p hp i
    rwa [prod_pow_factorization_of_subset (hq i).ne' (hsub i)] at h
  · rw [prod_comm]
    exact prod_eq_one fun p hp => hηprod p hp

/-- **Classification of zero-product relations.** A tuple of positive orders carries primitive
roots of unity with product one iff it is layer admissible. -/
theorem exists_zeroProduct_iff_isLayerAdmissible {m : ℕ} (q : Fin m → ℕ) (hq : ∀ i, 0 < q i) :
    (∃ ζ : Fin m → ℂ, (∀ i, IsPrimitiveRoot (ζ i) (q i)) ∧ ∏ i, ζ i = 1) ↔
      IsLayerAdmissible q := by
  constructor
  · rintro ⟨ζ, hζ, hprod⟩ p a hp ha htop
    have hord : (fun i => orderOf (ζ i)) = q := funext fun i => (hζ i).eq_orderOf.symm
    have h := layer_law (fun i => by rw [← (hζ i).eq_orderOf]; exact hq i) hprod hp ha
      (by simpa only [← hord] using htop)
    rwa [hord] at h
  · exact exists_zeroProduct_of_isLayerAdmissible q hq

/-- **Complete visibility law.** Some degree-`m` translated moment distinguishes the rows with
Selberg coordinates `Y` and `εY` iff some layer-admissible `m`-tuple of active orders has
`Π ε ≠ 1`. -/
theorem exists_translatedMoment_ne_iff (N : ℕ) (c ε : ℕ → ℝ) (m : ℕ) :
    (∃ v : Fin m → ℕ, SieveMoments.translatedMoment N (scaledSelbergRow N c ε) v ≠
        SieveMoments.translatedMoment N c v) ↔
      ∃ q : Fin m → ℕ, (∀ i, q i ∈ Icc 1 N ∧ selbergMultiplesCoord N c (q i) ≠ 0) ∧
        ∏ i, ε (q i) ≠ 1 ∧ IsLayerAdmissible q := by
  constructor
  · intro h
    exact exists_layer_admissible_of_translatedMoment_ne N c ε h
  · rintro ⟨q, hq, hε, hadm⟩
    obtain ⟨ζ, hζ, hprod⟩ := exists_zeroProduct_of_isLayerAdmissible q
      (fun i => (mem_Icc.mp (hq i).1).1) hadm
    by_contra hall
    push Not at hall
    have hmem : ζ ∈ Fintype.piFinset (fun _ : Fin m => responseRoots N) :=
      Fintype.mem_piFinset.mpr fun i => primitiveRoot_mem_responseRoots (hq i).1 (hζ i)
    have h := (translatedMoment_scaled_eq_iff N c ε m).mp hall ζ hmem hprod
    have hord : ∀ i, orderOf (ζ i) = q i := fun i => (hζ i).eq_orderOf.symm
    simp only [hord] at h
    rcases mul_eq_zero.mp h with h | h
    · obtain ⟨i, -, hi⟩ := prod_eq_zero_iff.mp h
      exact (hq i).2 hi
    · exact hε (sub_eq_zero.mp h).symm

end

end GaloisForLFunctions.BezoutValuationIncidence

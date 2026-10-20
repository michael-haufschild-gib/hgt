import GaloisForLFunctions.BezoutValuationIncidence.MomentSignVisibilityAndZeroProductRelations

/-!
# The valuation law for zero-product relations and the degree of sign visibility

A degree-`m` translated moment sees a sign pattern `ε` exactly when some zero-product `m`-tuple of
active frequencies has odd `ε`-weight. Which order tuples carry zero-product relations is governed
by valuations alone.

**Layer law.** Let `ζ_1, …, ζ_m` be roots of unity with `Π ζ_i = 1`, let `p` be prime and `a ≥ 1`
with no order divisible by `p^{a+1}`. Then the number of orders on the top layer `p^a ∣ ord ζ_i` is
not one, and is even if `p = 2`.

Raising the relation to the power `p^{a-1} R`, `R` the product of the prime-to-`p` parts of the
orders, kills every frequency off the layer and sends each frequency on it to a nontrivial `p`-th
root of unity; for `p = 2` these are all `-1`.

Consequences:

* the signs of all modes on the top dyadic layer are invisible to moments of every degree;
* if two modes share their top dyadic layer and each has a private odd prime layer, their
  relative sign is invisible to all moments of degree at most five: on the private layers each
  mode occurs at least twice, hence, with odd weight, three times, and the shared dyadic layer
  forces even total length;
* for modes `2p, 2r` with distinct odd primes `p, r` the relative sign is seen at degree six,
  through `ζ ζ ζ^{p-2} ξ ξ ξ^{r-2} = 1`. The visibility degree of `{2p, 2r}` is exactly six.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

theorem eq_neg_one_of_sq_eq_one {x : ℂ} (h : x ^ 2 = 1) (hx : x ≠ 1) : x = -1 := by
  have h0 : (x - 1) * (x + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hx
  · exact eq_neg_of_add_eq_zero_left h1

/-- The number of entries of an order tuple on the layer `p^a`. -/
def layerCount {m : ℕ} (q : Fin m → ℕ) (p a : ℕ) : ℕ :=
  (univ.filter fun i => p ^ a ∣ q i).card

/-- **The layer law.** -/
theorem layer_law {m : ℕ} {ζ : Fin m → ℂ} (hζ : ∀ i, 0 < orderOf (ζ i)) (hprod : ∏ i, ζ i = 1)
    {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (htop : ∀ i, ¬ p ^ (a + 1) ∣ orderOf (ζ i)) :
    layerCount (fun i => orderOf (ζ i)) p a ≠ 1 ∧
      (p = 2 → Even (layerCount (fun i => orderOf (ζ i)) p a)) := by
  classical
  set R := ∏ i, ordCompl[p] (orderOf (ζ i))
  set e := p ^ (a - 1) * R
  set S := univ.filter fun i => p ^ a ∣ orderOf (ζ i)
  have hRcop : Nat.Coprime p R :=
    Nat.Coprime.prod_right fun i _ => Nat.coprime_ordCompl hp (hζ i).ne'
  have hfac : ∀ i, p ^ a ∣ orderOf (ζ i) ↔ a ≤ (orderOf (ζ i)).factorization p := fun i =>
    hp.pow_dvd_iff_le_factorization (hζ i).ne'
  have hsucc : ∀ i, ¬ a + 1 ≤ (orderOf (ζ i)).factorization p := fun i h =>
    htop i ((hp.pow_dvd_iff_le_factorization (hζ i).ne').mpr h)
  have hsplit : ∀ i, p ^ (orderOf (ζ i)).factorization p * ordCompl[p] (orderOf (ζ i)) =
      orderOf (ζ i) := fun i => Nat.ordProj_mul_ordCompl_eq_self _ p
  -- off the layer the power is trivial
  have hoff : ∀ i, ¬ p ^ a ∣ orderOf (ζ i) → ζ i ^ e = 1 := by
    intro i hi
    have hv : (orderOf (ζ i)).factorization p ≤ a - 1 := by
      have := mt (hfac i).mpr hi
      omega
    apply orderOf_dvd_iff_pow_eq_one.mp
    have h := mul_dvd_mul (pow_dvd_pow p hv)
      (dvd_prod_of_mem (fun j => ordCompl[p] (orderOf (ζ j))) (mem_univ i))
    rwa [hsplit i] at h
  -- on the layer the power is a nontrivial `p`-th root of unity
  have hon : ∀ i ∈ S, (ζ i ^ e) ^ p = 1 ∧ ζ i ^ e ≠ 1 := by
    intro i hi
    have hdiv := (mem_filter.mp hi).2
    have hv : (orderOf (ζ i)).factorization p = a := by
      have h1 := (hfac i).mp hdiv
      have h2 := hsucc i
      omega
    constructor
    · rw [← pow_mul]
      apply orderOf_dvd_iff_pow_eq_one.mp
      have he : e * p = p ^ a * R := by
        simp only [e]
        rw [mul_comm (p ^ (a - 1)) R, mul_assoc, ← pow_succ, Nat.sub_add_cancel ha, mul_comm]
      rw [he]
      have h := mul_dvd_mul (pow_dvd_pow p hv.le)
        (dvd_prod_of_mem (fun j => ordCompl[p] (orderOf (ζ j))) (mem_univ i))
      rwa [hsplit i] at h
    · intro h1
      have hpa : p ^ a ∣ p ^ (a - 1) * R := hdiv.trans (orderOf_dvd_of_pow_eq_one h1)
      have hle := Nat.le_of_dvd (pow_pos hp.pos _)
        ((Nat.Coprime.pow_left a hRcop).dvd_of_dvd_mul_right hpa)
      have hlt : p ^ (a - 1) < p ^ a := Nat.pow_lt_pow_right hp.one_lt (by omega)
      omega
  -- the layer powers multiply to one
  have hlayer : ∏ i ∈ S, ζ i ^ e = 1 := by
    have h := congrArg (· ^ e) hprod
    simp only [one_pow, ← Finset.prod_pow] at h
    rw [← prod_filter_mul_prod_filter_not univ (fun i => p ^ a ∣ orderOf (ζ i))] at h
    rwa [prod_eq_one (fun i hi => hoff i (mem_filter.mp hi).2), mul_one] at h
  constructor
  · intro h1
    obtain ⟨i, hi⟩ := card_eq_one.mp h1
    have hiS : i ∈ S := by
      change i ∈ univ.filter fun i => p ^ a ∣ orderOf (ζ i)
      rw [hi]
      exact mem_singleton_self i
    change ∏ i ∈ univ.filter (fun i => p ^ a ∣ orderOf (ζ i)), ζ i ^ e = 1 at hlayer
    rw [hi, prod_singleton] at hlayer
    exact (hon i hiS).2 hlayer
  · intro hp2
    have hneg : ∀ i ∈ S, ζ i ^ e = -1 := fun i hi => by
      obtain ⟨h1, h2⟩ := hon i hi
      rw [hp2] at h1
      exact eq_neg_one_of_sq_eq_one h1 h2
    rw [prod_congr rfl hneg, prod_const] at hlayer
    exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp hlayer

/-- **Valuation obstruction to sign visibility.** If some degree-`m` translated moment sees `ε`,
some `m`-tuple of active orders with `Π ε ≠ 1` obeys the layer law at every prime. -/
theorem exists_layer_admissible_of_translatedMoment_ne (N : ℕ) (c ε : ℕ → ℝ) {m : ℕ}
    (hvis : ∃ v : Fin m → ℕ, SieveMoments.translatedMoment N (scaledSelbergRow N c ε) v ≠
      SieveMoments.translatedMoment N c v) :
    ∃ q : Fin m → ℕ, (∀ i, q i ∈ Icc 1 N ∧ selbergMultiplesCoord N c (q i) ≠ 0) ∧
      ∏ i, ε (q i) ≠ 1 ∧
      ∀ p a, p.Prime → 1 ≤ a → (∀ i, ¬ p ^ (a + 1) ∣ q i) →
        layerCount q p a ≠ 1 ∧ (p = 2 → Even (layerCount q p a)) := by
  have hnot : ¬ ∀ v : Fin m → ℕ, SieveMoments.translatedMoment N (scaledSelbergRow N c ε) v =
      SieveMoments.translatedMoment N c v := fun h => by
    obtain ⟨v, hv⟩ := hvis
    exact hv (h v)
  rw [translatedMoment_scaled_eq_iff] at hnot
  push Not at hnot
  obtain ⟨ζ, hζ, hprod, hne⟩ := hnot
  have hmem := Fintype.mem_piFinset.mp hζ
  have hord := fun i => orderOf_mem_Icc_of_mem_responseRoots (hmem i)
  refine ⟨fun i => orderOf (ζ i), fun i => ⟨hord i, fun h0 => hne ?_⟩, fun h1 => hne ?_, ?_⟩
  · rw [prod_eq_zero (mem_univ i) h0, zero_mul]
  · rw [h1, sub_self, mul_zero]
  · intro p a hp ha htop
    exact layer_law (fun i => (mem_Icc.mp (hord i)).1) hprod hp ha htop

theorem prod_sign_eq_neg_one_pow {m : ℕ} (P : Fin m → Prop) [DecidablePred P] :
    ∏ i, (if P i then (-1 : ℝ) else 1) = (-1) ^ (univ.filter P).card := by
  rw [prod_ite, prod_const_one, mul_one, prod_const]

/-! ## The top dyadic layer -/

/-- **The top dyadic layer is invisible.** Flipping the signs of all modes divisible by `2^a`,
when no active mode is divisible by `2^{a+1}`, leaves every translated moment unchanged. -/
theorem translatedMoment_topDyadicFlip_eq (N : ℕ) (c : ℕ → ℝ) {a : ℕ} (ha : 1 ≤ a)
    (htop : ∀ q ∈ Icc 1 N, selbergMultiplesCoord N c q ≠ 0 → ¬ 2 ^ (a + 1) ∣ q) {m : ℕ}
    (v : Fin m → ℕ) :
    SieveMoments.translatedMoment N
        (scaledSelbergRow N c fun q => if 2 ^ a ∣ q then -1 else 1) v =
      SieveMoments.translatedMoment N c v := by
  by_contra hne
  obtain ⟨q, hq, hε, hlaw⟩ := exists_layer_admissible_of_translatedMoment_ne N c _ ⟨v, hne⟩
  have heven := (hlaw 2 a Nat.prime_two ha fun i => htop _ (hq i).1 (hq i).2).2 rfl
  apply hε
  rw [prod_sign_eq_neg_one_pow]
  exact heven.neg_one_pow

/-! ## Relative signs of two modes -/

/-- **Blindness through degree five.** Two modes sharing their top dyadic layer, each with a
private odd prime layer: their relative sign is invisible to all moments of degree at most five. -/
theorem translatedMoment_relativeFlip_eq_of_le_five (N : ℕ) (c : ℕ → ℝ) {q₁ q₂ p r α β γ : ℕ}
    (hsupp : ∀ q ∈ Icc 1 N, selbergMultiplesCoord N c q ≠ 0 → q = q₁ ∨ q = q₂)
    (hp : p.Prime) (hα : 1 ≤ α) (hp1 : p ^ α ∣ q₁) (hp1' : ¬ p ^ (α + 1) ∣ q₁)
    (hp2 : ¬ p ^ α ∣ q₂)
    (hr : r.Prime) (hβ : 1 ≤ β) (hr2 : r ^ β ∣ q₂) (hr2' : ¬ r ^ (β + 1) ∣ q₂)
    (hr1 : ¬ r ^ β ∣ q₁)
    (hγ : 1 ≤ γ) (h21 : 2 ^ γ ∣ q₁) (h22 : 2 ^ γ ∣ q₂) (h21' : ¬ 2 ^ (γ + 1) ∣ q₁)
    (h22' : ¬ 2 ^ (γ + 1) ∣ q₂) {m : ℕ} (hm : m ≤ 5) (v : Fin m → ℕ) :
    SieveMoments.translatedMoment N (scaledSelbergRow N c fun q => if q = q₂ then -1 else 1) v =
      SieveMoments.translatedMoment N c v := by
  classical
  by_contra hne
  obtain ⟨q, hq, hε, hlaw⟩ := exists_layer_admissible_of_translatedMoment_ne N c _ ⟨v, hne⟩
  have hval : ∀ i, q i = q₁ ∨ q i = q₂ := fun i => hsupp _ (hq i).1 (hq i).2
  have hne12 : q₁ ≠ q₂ := fun h => hp2 (h ▸ hp1)
  -- the three layer counts
  have hk : layerCount q p α = (univ.filter fun i => q i = q₁).card := by
    unfold layerCount
    congr 1
    refine filter_congr fun i _ => ?_
    rcases hval i with h | h <;> simp [h, hp1, hp2, Ne.symm hne12]
  have hl : layerCount q r β = (univ.filter fun i => q i = q₂).card := by
    unfold layerCount
    congr 1
    refine filter_congr fun i _ => ?_
    rcases hval i with h | h <;> simp [h, hr1, hr2, hne12]
  have h2 : layerCount q 2 γ = m := by
    unfold layerCount
    rw [filter_true_of_mem fun i _ => by rcases hval i with h | h <;> rw [h] <;> assumption,
      card_univ, Fintype.card_fin]
  have hsum : (univ.filter fun i => q i = q₁).card + (univ.filter fun i => q i = q₂).card = m := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin m))) (fun i => q i = q₂)
    rw [card_univ, Fintype.card_fin] at h
    have hf : (univ.filter fun i => ¬ q i = q₂) = univ.filter fun i => q i = q₁ :=
      filter_congr fun i _ => by rcases hval i with h | h <;> simp [h, hne12, Ne.symm hne12]
    rw [hf] at h
    omega
  have hP := (hlaw p α hp hα fun i => by
    rcases hval i with h | h <;> rw [h]
    · exact hp1'
    · exact fun h' => hp2 ((pow_dvd_pow p (Nat.le_succ α)).trans h')).1
  have hR := (hlaw r β hr hβ fun i => by
    rcases hval i with h | h <;> rw [h]
    · exact fun h' => hr1 ((pow_dvd_pow r (Nat.le_succ β)).trans h')
    · exact hr2').1
  have hT := (hlaw 2 γ Nat.prime_two hγ fun i => by
    rcases hval i with h | h <;> rw [h]
    · exact h21'
    · exact h22').2 rfl
  rw [hk] at hP
  rw [hl] at hR
  rw [h2] at hT
  have hodd : ¬ Even (univ.filter fun i => q i = q₂).card := fun h => by
    apply hε
    rw [prod_sign_eq_neg_one_pow]
    exact h.neg_one_pow
  rw [Nat.not_even_iff_odd, Nat.odd_iff] at hodd
  rw [Nat.even_iff] at hT
  omega

/-- **Visibility at degree six.** For distinct odd primes `p, r` with active modes `2p, 2r`, some
sixth translated moment sees their relative sign. -/
theorem exists_translatedMoment_six_ne_relativeFlip (N : ℕ) (c : ℕ → ℝ) {p r : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hp2 : p ≠ 2) (hr2 : r ≠ 2) (hpr : p ≠ r)
    (hpN : 2 * p ≤ N) (hrN : 2 * r ≤ N) (hYp : selbergMultiplesCoord N c (2 * p) ≠ 0)
    (hYr : selbergMultiplesCoord N c (2 * r) ≠ 0) :
    ∃ v : Fin 6 → ℕ, SieveMoments.translatedMoment N
        (scaledSelbergRow N c fun q => if q = 2 * r then -1 else 1) v ≠
      SieveMoments.translatedMoment N c v := by
  by_contra hall
  push Not at hall
  -- `ζ ζ ζ^{p-2} = -1` for a primitive `2p`-th root `ζ`, `p` odd
  have hcube : ∀ {s : ℕ}, s.Prime → s ≠ 2 → ∃ ζ : ℂ, IsPrimitiveRoot ζ (2 * s) ∧
      IsPrimitiveRoot (ζ ^ (s - 2)) (2 * s) ∧ ζ * ζ * ζ ^ (s - 2) = -1 := by
    intro s hs hs2
    have hs3 : 3 ≤ s := by have := hs.two_le; omega
    have hsodd : Odd s := hs.odd_of_ne_two hs2
    have hζ := Complex.isPrimitiveRoot_exp (2 * s) (by omega)
    refine ⟨_, hζ, hζ.pow_of_coprime _ ?_, ?_⟩
    · have hodd2 : Odd (s - 2) := by
        obtain ⟨t, ht⟩ := hsodd
        exact ⟨t - 1, by omega⟩
      refine Nat.Coprime.mul_right (Nat.coprime_two_right.mpr hodd2) ?_
      exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hs).mpr
        (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)))
    · rw [← pow_two, ← pow_add, show 2 + (s - 2) = s by omega]
      apply eq_neg_one_of_sq_eq_one
      · rw [← pow_mul, show s * 2 = 2 * s by ring, hζ.pow_eq_one]
      · exact hζ.pow_ne_one_of_pos_of_lt (by omega) (by omega)
  obtain ⟨ζ, hζ, hζ', hζ3⟩ := hcube hp hp2
  obtain ⟨ξ, hξ, hξ', hξ3⟩ := hcube hr hr2
  have hpI : 2 * p ∈ Icc 1 N := mem_Icc.mpr ⟨by have := hp.two_le; omega, hpN⟩
  have hrI : 2 * r ∈ Icc 1 N := mem_Icc.mpr ⟨by have := hr.two_le; omega, hrN⟩
  set τ : Fin 6 → ℂ := ![ζ, ζ, ζ ^ (p - 2), ξ, ξ, ξ ^ (r - 2)]
  have hτ : τ ∈ Fintype.piFinset (fun _ : Fin 6 => responseRoots N) := by
    refine Fintype.mem_piFinset.mpr fun i => ?_
    fin_cases i
    · exact primitiveRoot_mem_responseRoots hpI hζ
    · exact primitiveRoot_mem_responseRoots hpI hζ
    · exact primitiveRoot_mem_responseRoots hpI hζ'
    · exact primitiveRoot_mem_responseRoots hrI hξ
    · exact primitiveRoot_mem_responseRoots hrI hξ
    · exact primitiveRoot_mem_responseRoots hrI hξ'
  have hprod : ∏ i, τ i = 1 := by
    rw [Fin.prod_univ_six]
    simp only [τ, Matrix.cons_val]
    linear_combination (ξ * ξ * ξ ^ (r - 2)) * hζ3 - hξ3
  have h := (translatedMoment_scaled_eq_iff N c _ 6).mp hall τ hτ hprod
  have hord : ∀ i, orderOf (τ i) = if (i : ℕ) < 3 then 2 * p else 2 * r := by
    intro i
    fin_cases i
    · exact hζ.eq_orderOf.symm
    · exact hζ.eq_orderOf.symm
    · exact hζ'.eq_orderOf.symm
    · exact hξ.eq_orderOf.symm
    · exact hξ.eq_orderOf.symm
    · exact hξ'.eq_orderOf.symm
  have hpr2 : 2 * p ≠ 2 * r := by omega
  simp only [hord, Fin.prod_univ_six] at h
  norm_num [hpr2] at h
  rcases h with h | h
  · exact hYp h
  · exact hYr h

/-- **The visibility degree of `{2p, 2r}` is six.** For distinct odd primes `p, r` and a row whose
active modes are exactly `2p` and `2r`, every moment of degree at most five is blind to the relative
sign and some sixth moment sees it. -/
theorem relativeSign_visibility_degree_six (N : ℕ) (c : ℕ → ℝ) {p r : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hp2 : p ≠ 2) (hr2 : r ≠ 2) (hpr : p ≠ r)
    (hpN : 2 * p ≤ N) (hrN : 2 * r ≤ N)
    (hsupp : ∀ q ∈ Icc 1 N, selbergMultiplesCoord N c q ≠ 0 → q = 2 * p ∨ q = 2 * r)
    (hYp : selbergMultiplesCoord N c (2 * p) ≠ 0) (hYr : selbergMultiplesCoord N c (2 * r) ≠ 0) :
    (∀ m ≤ 5, ∀ v : Fin m → ℕ, SieveMoments.translatedMoment N
        (scaledSelbergRow N c fun q => if q = 2 * r then -1 else 1) v =
      SieveMoments.translatedMoment N c v) ∧
    ∃ v : Fin 6 → ℕ, SieveMoments.translatedMoment N
        (scaledSelbergRow N c fun q => if q = 2 * r then -1 else 1) v ≠
      SieveMoments.translatedMoment N c v := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  -- `s ∣ 2t` for odd primes forces `s = t`
  have hdiv : ∀ {s t : ℕ}, s.Prime → s ≠ 2 → t.Prime → s ∣ 2 * t → s = t := by
    intro s t hs hs2 ht h
    rcases (Nat.Prime.dvd_mul hs).mp h with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp h) hs2
    · exact (Nat.prime_dvd_prime_iff_eq hs ht).mp h
  have hsq : ∀ {s : ℕ}, s.Prime → s ≠ 2 → ¬ s ^ 2 ∣ 2 * s := by
    intro s hs hs2 h
    rw [pow_two, mul_comm 2 s] at h
    have := Nat.dvd_of_mul_dvd_mul_left hs.pos h
    exact hs2 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp this)
  have hfour : ∀ {s : ℕ}, s.Prime → s ≠ 2 → ¬ 2 ^ 2 ∣ 2 * s := by
    intro s hs hs2 h
    rw [pow_two] at h
    have h' : 2 ∣ s := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) h
    exact hs2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hs).mp h').symm
  refine ⟨fun m hm v => ?_, exists_translatedMoment_six_ne_relativeFlip N c hp hr hp2 hr2 hpr hpN
    hrN hYp hYr⟩
  refine translatedMoment_relativeFlip_eq_of_le_five N c hsupp (p := p) (r := r) (α := 1) (β := 1)
    (γ := 1) hp le_rfl ?_ ?_ ?_ hr le_rfl ?_ ?_ ?_ le_rfl ?_ ?_ ?_ ?_ hm v
  · simp
  · simpa using hsq hp hp2
  · simpa using fun h => hpr (hdiv hp hp2 hr h)
  · simp
  · simpa using hsq hr hr2
  · simpa using fun h => hpr (hdiv hr hr2 hp h).symm
  · simp
  · simp
  · exact hfour hp hp2
  · exact hfour hr hr2

end

end GaloisForLFunctions.BezoutValuationIncidence

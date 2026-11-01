import GaloisForLFunctions.RHTower.BakerProof.BakerIteration

/-!
# Rigidity of positive algebraic prime frequencies

Baker independence balances algebraic weights separately at each prime. Positivity
then identifies prime supports. A frequency on `D` distinct primes has no representation
by fewer terms; every representation with at most `D` terms permutes its prime–weight pairs.
-/

open Finset
open scoped Classical
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlgebraicPrimeFrequency
noncomputable section

private theorem algebraic_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, IsAlgebraic ℤ (a i)) : IsAlgebraic ℤ (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isAlgebraic_zero : IsAlgebraic ℤ (0 : ℝ))
  | @insert i s hi ih =>
    rw [sum_insert hi]
    exact (ha i (mem_insert_self _ _)).add
      (ih (fun j hj => ha j (mem_insert_of_mem hj)))

/-- Baker independence with an arbitrary finite index type. -/
theorem primeLog_relation {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (hp : Function.Injective p) (hprime : ∀ i, (p i).Prime)
    (c : ι → ℝ) (hc : ∀ i, IsAlgebraic ℤ (c i))
    (h : ∑ i, c i * Real.log (p i) = 0) : ∀ i, c i = 0 := by
  classical
  let e := Fintype.equivFin ι
  have hf : ∑ j, c (e.symm j) * Real.log (p (e.symm j)) = 0 := by
    rw [← h]
    exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  have hz := RHTower.primeLog_algIndep (fun j => p (e.symm j))
    (hp.comp e.symm.injective) (fun j => hprime (e.symm j))
    (fun j => c (e.symm j)) (fun j => hc (e.symm j)) hf
  intro i
  simpa only [Equiv.symm_apply_apply] using hz (e i)

/-- A prime-log relation with algebraic weights balances separately at every prime. -/
theorem primeLog_grouped_eq_zero {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (hprime : ∀ i, (p i).Prime) (a : ι → ℝ) (ha : ∀ i, IsAlgebraic ℤ (a i))
    (h : ∑ i, a i * Real.log (p i) = 0) (q : ℕ) :
    (∑ i, if p i = q then a i else 0) = 0 := by
  classical
  let S : Finset ℕ := univ.image p
  let c : S → ℝ := fun q => ∑ i, if p i = (q : ℕ) then a i else 0
  have hS : ∀ i, p i ∈ S := fun i => mem_image_of_mem p (mem_univ i)
  have hc : ∀ q : S, IsAlgebraic ℤ (c q) := by
    intro q
    apply algebraic_sum
    intro i _
    split_ifs
    · exact ha i
    · exact isAlgebraic_zero
  have hsum : ∑ q : S, c q * Real.log (q : ℕ) = ∑ i, a i * Real.log (p i) := by
    simp only [c, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [sum_eq_single (⟨p i, hS i⟩ : S)]
    · simp only [ite_true]
    · intro q _ hqi
      have hne : p i ≠ (q : ℕ) := fun he => hqi (Subtype.ext he.symm)
      rw [if_neg hne, zero_mul]
    · simp
  have hz := primeLog_relation (fun q : S => (q : ℕ)) Subtype.val_injective
    (fun q => by
      obtain ⟨i, _, he⟩ := mem_image.mp q.property
      rw [← he]
      exact hprime i) c hc (hsum.trans h)
  by_cases hq : q ∈ S
  · exact hz ⟨q,hq⟩
  · apply sum_eq_zero
    intro i _
    exact if_neg (fun he : p i = q => hq (he ▸ hS i))

/-- Equal algebraic prime frequencies have equal total weight at each prime. -/
theorem primeLog_weight_balance {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℕ) (q : κ → ℕ) (hp : ∀ i, (p i).Prime) (hq : ∀ j, (q j).Prime)
    (a : ι → ℝ) (b : κ → ℝ)
    (ha : ∀ i, IsAlgebraic ℤ (a i)) (hb : ∀ j, IsAlgebraic ℤ (b j))
    (h : ∑ i, a i * Real.log (p i) = ∑ j, b j * Real.log (q j)) (ell : ℕ) :
    (∑ i, if p i = ell then a i else 0) = ∑ j, if q j = ell then b j else 0 := by
  classical
  let pq : ι ⊕ κ → ℕ := Sum.elim p q
  let ab : ι ⊕ κ → ℝ := Sum.elim a (fun j => -b j)
  have hpq : ∀ i, (pq i).Prime := Sum.rec hp hq
  have hab : ∀ i, IsAlgebraic ℤ (ab i) := Sum.rec ha (fun j => (hb j).neg)
  have hz : ∑ i, ab i * Real.log (pq i) = 0 := by
    rw [Fintype.sum_sum_type]
    simp only [ab, pq, Sum.elim_inl, Sum.elim_inr, neg_mul, sum_neg_distrib]
    simpa only [sub_eq_add_neg] using (sub_eq_zero.mpr h)
  have hc := primeLog_grouped_eq_zero pq hpq ab hab hz ell
  rw [Fintype.sum_sum_type] at hc
  have hn : (∑ j, if q j = ell then -b j else 0) =
      -(∑ j, if q j = ell then b j else 0) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro j _
    split_ifs <;> simp
  change (∑ i, if p i = ell then a i else 0) +
    (∑ j, if q j = ell then -b j else 0) = 0 at hc
  rw [hn] at hc
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hc)

/-- Positive algebraic weights cannot introduce primes outside the other frequency's support. -/
theorem primeLog_support_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℕ) (q : κ → ℕ) (hp : ∀ i, (p i).Prime) (hq : ∀ j, (q j).Prime)
    (a : ι → ℝ) (b : κ → ℝ) (ha : ∀ i, IsAlgebraic ℤ (a i))
    (hb : ∀ j, IsAlgebraic ℤ (b j)) (hapos : ∀ i, 0 < a i) (hbpos : ∀ j, 0 < b j)
    (h : ∑ i, a i * Real.log (p i) = ∑ j, b j * Real.log (q j)) :
    Set.range p = Set.range q := by
  classical
  have forward : ∀ i, ∃ j, q j = p i := by
    intro i
    by_contra hn
    push Not at hn
    have hz : (∑ j, if q j = p i then b j else 0) = 0 := by
      apply sum_eq_zero
      intro j _
      exact if_neg (hn j)
    have hbalance := primeLog_weight_balance p q hp hq a b ha hb h (p i)
    rw [hz] at hbalance
    have hle : a i ≤ ∑ k, if p k = p i then a k else 0 := by
      have hle := single_le_sum (f := fun k => if p k = p i then a k else 0)
        (fun k (_ : k ∈ univ) => by
        split_ifs
        · exact (hapos k).le
        · exact le_rfl) (mem_univ i)
      simpa only [ite_true] using hle
    rw [hbalance] at hle
    exact (not_le_of_gt (hapos i)) hle
  have backward : ∀ j, ∃ i, p i = q j := by
    intro j
    by_contra hn
    push Not at hn
    have hz : (∑ i, if p i = q j then a i else 0) = 0 := by
      apply sum_eq_zero
      intro i _
      exact if_neg (hn i)
    have hbalance := primeLog_weight_balance p q hp hq a b ha hb h (q j)
    rw [hz] at hbalance
    have hle : b j ≤ ∑ k, if q k = q j then b k else 0 := by
      have hle := single_le_sum (f := fun k => if q k = q j then b k else 0)
        (fun k (_ : k ∈ univ) => by
        split_ifs
        · exact (hbpos k).le
        · exact le_rfl) (mem_univ j)
      simpa only [ite_true] using hle
    rw [← hbalance] at hle
    exact (not_le_of_gt (hbpos j)) hle
  ext ell
  constructor
  · rintro ⟨i,rfl⟩
    exact forward i
  · rintro ⟨j,rfl⟩
    exact backward j

/-- A frequency using `D` distinct primes cannot be assembled from fewer positive algebraic
prime terms. With at most `D` terms, its only representations permute the prime-weight pairs. -/
theorem primeLog_short_representation {N D : ℕ} (hND : N ≤ D)
    (p : Fin N → ℕ) (q : Fin D → ℕ)
    (hp : ∀ i, (p i).Prime) (hq : ∀ j, (q j).Prime) (hqinj : Function.Injective q)
    (a : Fin N → ℝ) (b : Fin D → ℝ)
    (ha : ∀ i, IsAlgebraic ℤ (a i)) (hb : ∀ j, IsAlgebraic ℤ (b j))
    (hapos : ∀ i, 0 < a i) (hbpos : ∀ j, 0 < b j)
    (h : ∑ i, a i * Real.log (p i) = ∑ j, b j * Real.log (q j)) :
    ∃ e : Fin N ≃ Fin D, ∀ i, p i = q (e i) ∧ a i = b (e i) := by
  classical
  have hs := primeLog_support_eq p q hp hq a b ha hb hapos hbpos h
  have hm : ∀ i, ∃ j, q j = p i := by
    intro i
    change p i ∈ Set.range q
    rw [← hs]
    exact ⟨i,rfl⟩
  choose f hf using hm
  have hsurj : Function.Surjective f := by
    intro j
    have hj : q j ∈ Set.range p := by rw [hs]; exact ⟨j,rfl⟩
    obtain ⟨i,hi⟩ := hj
    exact ⟨i,hqinj ((hf i).trans hi)⟩
  have hDN : D ≤ N := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective f hsurj
  have hcard : N = D := le_antisymm hND hDN
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_surjective_and_card f).2
      ⟨hsurj,by simp only [Fintype.card_fin,hcard]⟩
  let e : Fin N ≃ Fin D := Equiv.ofBijective f hbij
  have hpinj : Function.Injective p := by
    intro i k hik
    exact hbij.1 (hqinj ((hf i).trans (hik.trans (hf k).symm)))
  refine ⟨e,fun i => ⟨(hf i).symm,?_⟩⟩
  have hbalance := primeLog_weight_balance p q hp hq a b ha hb h (p i)
  have hleft : (∑ k, if p k = p i then a k else 0) = a i := by
    rw [sum_eq_single i]
    · exact if_pos rfl
    · intro k _ hki
      exact if_neg (fun he => hki (hpinj he))
    · simp
  have hright : (∑ j, if q j = p i then b j else 0) = b (f i) := by
    rw [sum_eq_single (f i)]
    · exact if_pos (hf i)
    · intro j _ hji
      exact if_neg (fun he => hji (hqinj (he.trans (hf i).symm)))
    · simp
  rw [hleft,hright] at hbalance
  exact hbalance

/-- A prime with a positive algebraic exponent. -/
abbrev PrimeAtom := Nat.Primes × {a : ℝ // 0 < a ∧ IsAlgebraic ℤ a}

/-- The positive logarithmic frequency of a prime atom. -/
def atomFrequency (x : PrimeAtom) : ℝ := x.2.val * Real.log (x.1.val : ℝ)

/-- A short tuple sharing the frequency of a tuple on distinct primes is exactly a permutation
of its prime atoms. -/
theorem atom_tuple_frequency_iff {N D : ℕ} (hND : N ≤ D)
    (u : Fin N → PrimeAtom) (v : Fin D → PrimeAtom)
    (hv : Function.Injective (fun j => (v j).1)) :
    (∑ i, atomFrequency (u i)) = (∑ j, atomFrequency (v j)) ↔
      ∃ e : Fin N ≃ Fin D, ∀ i, u i = v (e i) := by
  constructor
  · intro h
    obtain ⟨e,he⟩ := primeLog_short_representation hND
      (fun i => (u i).1.val) (fun j => (v j).1.val)
      (fun i => (u i).1.property) (fun j => (v j).1.property)
      (fun i j hij => hv (Subtype.ext hij))
      (fun i => (u i).2.val) (fun j => (v j).2.val)
      (fun i => (u i).2.property.2) (fun j => (v j).2.property.2)
      (fun i => (u i).2.property.1) (fun j => (v j).2.property.1) h
    exact ⟨e,fun i => Prod.ext (Subtype.ext (he i).1) (Subtype.ext (he i).2)⟩
  · rintro ⟨e,he⟩
    exact Fintype.sum_equiv e _ _ (fun i => congrArg atomFrequency (he i))

/-- Fewer prime factors cannot produce a frequency carried by distinct positive algebraic atoms. -/
theorem atom_tuple_frequency_ne_of_shorter {N D : ℕ} (hND : N < D)
    (u : Fin N → PrimeAtom) (v : Fin D → PrimeAtom)
    (hv : Function.Injective (fun j => (v j).1)) :
    (∑ i, atomFrequency (u i)) ≠ (∑ j, atomFrequency (v j)) := by
  intro h
  obtain ⟨e,_⟩ := (atom_tuple_frequency_iff hND.le u v hv).mp h
  have hc := Fintype.card_congr e
  simp only [Fintype.card_fin] at hc
  omega

/-- A single algebraic prime atom is determined by its logarithmic frequency. -/
theorem atomFrequency_injective : Function.Injective atomFrequency := by
  intro u v huv
  have hsum : (∑ _ : Fin 1, atomFrequency u) = ∑ _ : Fin 1, atomFrequency v := by
    simpa only [Fin.sum_univ_one] using huv
  obtain ⟨e,he⟩ := (atom_tuple_frequency_iff (N := 1) (D := 1) le_rfl
    (fun _ => u) (fun _ => v) (fun _ _ _ => Subsingleton.elim _ _)).mp hsum
  exact he 0

#print axioms primeLog_relation
#print axioms primeLog_grouped_eq_zero
#print axioms primeLog_weight_balance
#print axioms primeLog_support_eq
#print axioms primeLog_short_representation
#print axioms atom_tuple_frequency_iff
#print axioms atom_tuple_frequency_ne_of_shorter
#print axioms atomFrequency_injective
end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlgebraicPrimeFrequency

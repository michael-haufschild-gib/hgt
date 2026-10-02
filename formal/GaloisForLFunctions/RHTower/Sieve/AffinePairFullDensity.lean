import GaloisForLFunctions.RHTower.Sieve.AffinePairSieve

/-!
# Full affine prime-pair density

For primitive slopes, prime anchors above the sieve range make every slope prime
contribute exactly one root. Away from the slopes, the discriminant distinguishes
one root from two. A genuine affine CRT equivalence gives the exact full squarefree
density pairNu(abs(discriminant)*a*b), without deleting slope primes. All local
nonvanishing facts and the full root-count remainder budget follow from the anchors.
-/

noncomputable section
open Finset
namespace RHTower.Sieve

/-- Complete affine-product root count on the literal residue interval. -/
def affinePairRootCount (e a b c d : ℕ) : ℕ :=
  ((range e).filter (fun n => e ∣ affinePairProduct a b c d n)).card

private theorem affinePairRootCount_eq_card (e : ℕ) [NeZero e] (a b c d : ℕ) :
    affinePairRootCount e a b c d =
      (univ.filter (fun x : ZMod e =>
        ((a : ZMod e) * x + c) * ((b : ZMod e) * x + d) = 0)).card := by
  classical
  unfold affinePairRootCount
  refine card_nbij' (fun n => (n : ZMod e)) (fun x => x.val) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [mem_coe, mem_filter, mem_range] at hn
    simp only [mem_coe, mem_filter, mem_univ, true_and]
    have h := (ZMod.natCast_eq_zero_iff (affinePairProduct a b c d n) e).mpr hn.2
    simpa only [affinePairProduct, Nat.cast_mul, Nat.cast_add] using h
  · intro x hx
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hx
    simp only [mem_coe, mem_filter, mem_range]
    refine ⟨ZMod.val_lt x, (ZMod.natCast_eq_zero_iff _ _).mp ?_⟩
    simpa only [affinePairProduct, Nat.cast_mul, Nat.cast_add, ZMod.natCast_zmod_val] using hx
  · intro n hn
    simp only [mem_coe, mem_filter, mem_range] at hn
    exact ZMod.val_cast_of_lt hn.1
  · intro x _
    exact ZMod.natCast_zmod_val x

/-- Full affine roots split componentwise under CRT, without inverting either slope. -/
theorem affinePairRoot_iff_chineseRemainder
    {q e : ℕ} (hcop : q.Coprime e) (a b c d : ℕ) (x : ZMod (q * e)) :
    ((a : ZMod (q * e)) * x + c) * ((b : ZMod (q * e)) * x + d) = 0 ↔
      ((a : ZMod q) * (ZMod.chineseRemainder hcop x).1 + c) *
        ((b : ZMod q) * (ZMod.chineseRemainder hcop x).1 + d) = 0 ∧
      ((a : ZMod e) * (ZMod.chineseRemainder hcop x).2 + c) *
        ((b : ZMod e) * (ZMod.chineseRemainder hcop x).2 + d) = 0 := by
  let E := ZMod.chineseRemainder hcop
  constructor
  · intro hx
    have heq := congrArg E hx
    constructor
    · have := congrArg Prod.fst heq
      simpa [E] using this
    · have := congrArg Prod.snd heq
      simpa [E] using this
  · intro hx
    apply E.injective
    apply Prod.ext
    · simpa [E] using hx.1
    · simpa [E] using hx.2

/-- Exact multiplicativity of the complete root count for coprime positive moduli. -/
theorem affinePairRootCount_mul {q e : ℕ} (hq : q ≠ 0) (he : e ≠ 0)
    (hcop : q.Coprime e) (a b c d : ℕ) :
    affinePairRootCount (q * e) a b c d =
      affinePairRootCount q a b c d * affinePairRootCount e a b c d := by
  classical
  letI : NeZero q := ⟨hq⟩
  letI : NeZero e := ⟨he⟩
  letI : NeZero (q * e) := ⟨Nat.mul_ne_zero hq he⟩
  let E : {x : ZMod (q * e) // ((a : ZMod (q * e)) * x + c) *
      ((b : ZMod (q * e)) * x + d) = 0} ≃
      {x : ZMod q // ((a : ZMod q) * x + c) * ((b : ZMod q) * x + d) = 0} ×
      {x : ZMod e // ((a : ZMod e) * x + c) * ((b : ZMod e) * x + d) = 0} :=
    ((ZMod.chineseRemainder hcop).toEquiv.subtypeEquiv
    (affinePairRoot_iff_chineseRemainder hcop a b c d)).trans Equiv.subtypeProdEquivProd
  rw [affinePairRootCount_eq_card, affinePairRootCount_eq_card,
    affinePairRootCount_eq_card, ← Fintype.card_subtype, ← Fintype.card_subtype,
    ← Fintype.card_subtype]
  exact (Fintype.card_congr E).trans (Fintype.card_prod _ _)

@[simp] theorem affinePairRootCount_one (a b c d : ℕ) : affinePairRootCount 1 a b c d = 1 := by
  simp [affinePairRootCount]

/-- Full root counts factor over all prime coordinates, including slope primes. -/
theorem affinePairRootCount_prod (s : Finset ℕ)
    (hpair : (s : Set ℕ).Pairwise Nat.Coprime) (hnz : ∀ n ∈ s, n ≠ 0) (a b c d : ℕ) :
    affinePairRootCount (∏ n ∈ s, n) a b c d = ∏ n ∈ s, affinePairRootCount n a b c d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hns ih =>
    have hn : n ≠ 0 := hnz n (mem_insert_self n s)
    have hs : ∀ m ∈ s, m ≠ 0 := fun m hm => hnz m (mem_insert_of_mem hm)
    have hprod : (∏ m ∈ s, m) ≠ 0 := prod_ne_zero_iff.mpr hs
    have hcop : n.Coprime (∏ m ∈ s, m) := by
      rw [Nat.coprime_prod_right_iff]
      intro m hm
      exact hpair (mem_insert_self n s) (mem_insert_of_mem hm) (by aesop)
    have hpair_s : (s : Set ℕ).Pairwise Nat.Coprime := hpair.mono (by simp)
    simp only [prod_insert hns]
    rw [affinePairRootCount_mul hn hprod hcop, ih hpair_s hs]

private theorem affinePairRootCount_prime_left {p a b c d : ℕ} (hp : p.Prime)
    (ha : p ∣ a) (hb : ¬ p ∣ b) (hc : ¬ p ∣ c) : affinePairRootCount p a b c d = 1 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have ha0 : (a : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr ha
  have hb0 : (b : ZMod p) ≠ 0 := fun h => hb ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hc0 : (c : ZMod p) ≠ 0 := fun h => hc ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hroot (x : ZMod p) :
      ((a : ZMod p) * x + c) * ((b : ZMod p) * x + d) = 0 ↔ x = -(d : ZMod p) / b := by
    simp only [ha0, zero_mul, zero_add, mul_eq_zero, hc0, false_or]
    rw [eq_div_iff hb0]
    constructor <;> intro hh <;> linear_combination hh
  rw [affinePairRootCount_eq_card]
  simp only [hroot, Finset.filter_eq', Finset.mem_univ, if_true, Finset.card_singleton]

private theorem affinePairRootCount_prime_right {p a b c d : ℕ} (hp : p.Prime)
    (ha : ¬ p ∣ a) (hb : p ∣ b) (hd : ¬ p ∣ d) : affinePairRootCount p a b c d = 1 := by
  have heq : affinePairRootCount p a b c d = affinePairRootCount p b a d c := by
    unfold affinePairRootCount affinePairProduct
    simp only [mul_comm]
  rw [heq]
  exact affinePairRootCount_prime_left hp hb ha hd

/-- Prime local density for primitive slopes: slope primes have exactly one root,
so the full parameter is the discriminant times both slopes. -/
theorem affinePairRootCount_prime {p a b c d : ℕ} (hp : p.Prime) (hab : Nat.Coprime a b)
    (hac : p ∣ a → ¬ p ∣ c) (hbd : p ∣ b → ¬ p ∣ d) :
    affinePairRootCount p a b c d =
      if p ∣ (affinePairDiscriminant a b c d).natAbs * a * b then 1 else 2 := by
  by_cases ha : p ∣ a
  · have hb : ¬ p ∣ b := by
      intro hb
      have hd := Nat.dvd_gcd ha hb
      rw [hab.gcd_eq_one] at hd
      exact hp.not_dvd_one hd
    rw [affinePairRootCount_prime_left hp ha hb (hac ha), if_pos]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ha _) _
  · by_cases hb : p ∣ b
    · rw [affinePairRootCount_prime_right hp ha hb (hbd hb), if_pos]
      exact dvd_mul_of_dvd_right hb _
    · have hpab : ¬ p ∣ a * b := fun h => (hp.dvd_mul.mp h).elim ha hb
      have hcop : Nat.Coprime (a * b) p := (hp.coprime_iff_not_dvd.mpr hpab).symm
      unfold affinePairRootCount
      rw [affinePair_rootCount_eq hp.pos a b c d hcop, quadraticCongruenceRootCountTotal_prime hp]
      simp only [Int.natCast_dvd, hp.dvd_mul, ha, hb, or_false]

/-- Squarefree full root density, with the local nonvanishing facts stated only at
actual slope primes. They will follow from the prime anchors in the sieve application. -/
theorem affinePair_rootDensity_full {e a b c d : ℕ} (hsq : Squarefree e)
    (hab : Nat.Coprime a b)
    (hac : ∀ p ∈ e.primeFactors, p ∣ a → ¬ p ∣ c)
    (hbd : ∀ p ∈ e.primeFactors, p ∣ b → ¬ p ∣ d) :
    pairNu ((affinePairDiscriminant a b c d).natAbs * a * b) e =
      (affinePairRootCount e a b c d : ℝ) / e := by
  have hprod := Nat.prod_primeFactors_of_squarefree hsq
  have hpair : ((e.primeFactors : Finset ℕ) : Set ℕ).Pairwise Nat.Coprime := by
    intro p hp q hq hne
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hne
  have hnz : ∀ p ∈ e.primeFactors, p ≠ 0 := fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero
  have heq : (affinePairRootCount e a b c d : ℝ) =
      ∏ p ∈ e.primeFactors, pairClassCount ((affinePairDiscriminant a b c d).natAbs * a * b) p := by
    conv_lhs => rw [← hprod, affinePairRootCount_prod _ hpair hnz]
    rw [Nat.cast_prod]
    apply prod_congr rfl
    intro p hp
    rw [affinePairRootCount_prime (Nat.prime_of_mem_primeFactors hp) hab (hac p hp) (hbd p hp)]
    unfold pairClassCount
    split_ifs <;> norm_num
  rw [heq]
  simp [pairNu, ArithmeticFunction.prodPrimeFactors_apply hsq.ne_zero]


/-- Prime anchors above the complete sifting range supply all local nonvanishing
facts, including at primes dividing a slope. -/
theorem affinePair_rootDensity_primeAnchors {e a b c d P₁ h : ℕ}
    (he : e ∣ rangePrimorial P₁ h) (hab : Nat.Coprime a b)
    (hc : c.Prime) (hd : d.Prime) (hhc : h < c) (hhd : h < d) :
    pairNu ((affinePairDiscriminant a b c d).natAbs * a * b) e =
      (affinePairRootCount e a b c d : ℝ) / e := by
  have hsq := (rangePrimorial_squarefree P₁ h).squarefree_of_dvd he
  apply affinePair_rootDensity_full hsq hab
  · intro p hp _
    have hpmem := mem_of_prime_dvd_prod (fun _ hp => rangePrimes_prime hp)
      (Nat.prime_of_mem_primeFactors hp) ((Nat.dvd_of_mem_primeFactors hp).trans he)
    exact not_dvd_of_prime_lt hc hhc hpmem
  · intro p hp _
    have hpmem := mem_of_prime_dvd_prod (fun _ hp => rangePrimes_prime hp)
      (Nat.prime_of_mem_primeFactors hp) ((Nat.dvd_of_mem_primeFactors hp).trans he)
    exact not_dvd_of_prime_lt hd hhd hpmem

/-- The full actual root count has the same two-roots-per-prime remainder budget. -/
theorem affinePairRootCount_primeAnchors_le {e a b c d P₁ h : ℕ}
    (he : e ∣ rangePrimorial P₁ h) (hab : Nat.Coprime a b)
    (hc : c.Prime) (hd : d.Prime) (hhc : h < c) (hhd : h < d) :
    (affinePairRootCount e a b c d : ℝ) ≤ (2 : ℝ) ^ e.primeFactors.card := by
  have hsq := (rangePrimorial_squarefree P₁ h).squarefree_of_dvd he
  have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast hsq.ne_zero
  have hcount := (div_left_inj' he0).mp
    ((affinePair_rootDensity_primeAnchors he hab hc hd hhc hhd).symm.trans
      (pairNu_eq_rootDensity hsq _))
  rw [hcount]
  exact rootCount_le_two_pow hsq _

end RHTower.Sieve

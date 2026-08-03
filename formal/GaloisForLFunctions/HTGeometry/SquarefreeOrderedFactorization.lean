import GaloisForLFunctions.HTGeometry.AiryTowerEnumeration
import GaloisForLFunctions.HTGeometry.OrderedSurjectionEnumeration
import Mathlib.Algebra.Order.Antidiag.Nat

/-!
# Squarefree ordered factorizations

For squarefree `N`, a `j`-tuple of factors at least two with product `N` is equivalent to a
surjection from the prime factors of `N` onto `Fin j`: a prime is sent to its unique factor.
Combining this with the semantic enumeration of finite surjections proves the ordered-Bell formula
for the actual numeric type `OrderedFactorization N`.
-/

open scoped BigOperators

namespace GaloisForLFunctions
namespace IrregularStokes

/-- A fixed-length numeric factor tuple with no unit factors. -/
@[ext]
structure SquarefreeMulTuple (N j : ℕ) where
  factor : Fin j → ℕ
  factor_ge_two : ∀ i, 2 ≤ factor i
  prod_eq : ∏ i, factor i = N

instance (N j : ℕ) : Finite (SquarefreeMulTuple N j) := by
  by_cases hN : N = 0
  · subst N
    have hempty : IsEmpty (SquarefreeMulTuple 0 j) := ⟨fun t => by
      have hprodPos : 0 < ∏ i, t.factor i := Finset.prod_pos fun i _ =>
        lt_of_lt_of_le Nat.zero_lt_two (t.factor_ge_two i)
      rw [t.prod_eq] at hprodPos
      omega⟩
    let encode : SquarefreeMulTuple 0 j → Fin 0 := fun t => isEmptyElim t
    exact Finite.of_injective encode (fun t => isEmptyElim t)
  · let encode : SquarefreeMulTuple N j → Fin j → Fin (N + 1) := fun t i =>
      ⟨t.factor i, Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hN)
        (by
          have hdvd := Finset.dvd_prod_of_mem t.factor (Finset.mem_univ i)
          simpa only [t.prod_eq] using hdvd))⟩
    exact Finite.of_injective encode fun x y h => by
      apply SquarefreeMulTuple.ext
      exact funext fun i => Fin.mk.inj (congrFun h i)

/-- A labelled assignment of the prime divisors of `N` onto `j` nonempty ordered blocks. -/
@[ext]
structure PrimeBlockSurjection (N j : ℕ) where
  block : {p : ℕ // p ∈ N.primeFactors} → Fin j
  surjective : Function.Surjective block

instance (N j : ℕ) : Finite (PrimeBlockSurjection N j) := by
  let encode : PrimeBlockSurjection N j →
      ({p : ℕ // p ∈ N.primeFactors} → Fin j) := PrimeBlockSurjection.block
  exact Finite.of_injective encode fun _ _ h => PrimeBlockSurjection.ext h

namespace PrimeBlockSurjection

/-- Product of the primes assigned to one ordered block. -/
def blockProduct {N j : ℕ} (f : PrimeBlockSurjection N j) (b : Fin j) : ℕ :=
  ∏ p ∈ N.primeFactors.attach.filter (fun p => f.block p = b), p.1

/-- A prime divisor of `N` divides a block product exactly when it was assigned to that block. -/
theorem prime_dvd_blockProduct_iff {N j : ℕ} (f : PrimeBlockSurjection N j)
    (p : {p : ℕ // p ∈ N.primeFactors}) (b : Fin j) :
    p.1 ∣ f.blockProduct b ↔ f.block p = b := by
  have hp : p.1.Prime := (Nat.mem_primeFactors.mp p.2).1
  rw [blockProduct, Prime.dvd_finsetProd_iff hp.prime]
  constructor
  · rintro ⟨q, hq, hpq⟩
    have hqData := Finset.mem_filter.mp hq
    have hqPrime : q.1.Prime := (Nat.mem_primeFactors.mp q.2).1
    have hpqEq : p.1 = q.1 := by
      rcases (Nat.dvd_prime hqPrime).mp hpq with hpone | hpqEq
      · exact False.elim (hp.ne_one hpone)
      · exact hpqEq
    have hpqSubtype : p = q := Subtype.ext hpqEq
    simpa [hpqSubtype] using hqData.2
  · intro hblock
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_attach _ p, hblock⟩, dvd_rfl⟩

/-- Fibrewise multiplication of all block products recovers the squarefree integer. -/
theorem prod_blockProduct {N j : ℕ} (hN : Squarefree N)
    (f : PrimeBlockSurjection N j) :
    ∏ b, f.blockProduct b = N := by
  unfold blockProduct
  rw [Finset.prod_fiberwise_of_maps_to]
  · simpa only [id_eq] using
      (Finset.prod_attach N.primeFactors id).trans
        (Nat.prod_primeFactors_of_squarefree hN)
  · intro p _
    exact Finset.mem_univ (f.block p)

/-- Surjectivity makes every block product nontrivial. -/
theorem two_le_blockProduct {N j : ℕ} (f : PrimeBlockSurjection N j) (b : Fin j) :
    2 ≤ f.blockProduct b := by
  obtain ⟨p, hp⟩ := f.surjective b
  have hpPrime : p.1.Prime := (Nat.mem_primeFactors.mp p.2).1
  have hprodPos : 0 < f.blockProduct b := by
    unfold blockProduct
    apply Finset.prod_pos
    intro q _
    exact (Nat.mem_primeFactors.mp q.2).1.pos
  exact hpPrime.two_le.trans
    (Nat.le_of_dvd hprodPos (f.prime_dvd_blockProduct_iff p b |>.2 hp))

/-- Prime-block assignment converted to its numeric factor tuple. -/
def toMulTuple {N j : ℕ} (hN : Squarefree N) (f : PrimeBlockSurjection N j) :
    SquarefreeMulTuple N j where
  factor := f.blockProduct
  factor_ge_two := f.two_le_blockProduct
  prod_eq := f.prod_blockProduct hN

/-- Fixed-block prime assignments have the surjection cardinal. -/
noncomputable def equivFinSurjection (N j : ℕ) :
    PrimeBlockSurjection N j ≃
      FinSurjection (Fintype.card {p : ℕ // p ∈ N.primeFactors}) j where
  toFun f :=
    { toFun := fun i => f.block ((Fintype.equivFin {p : ℕ // p ∈ N.primeFactors}).symm i)
      surjective := f.surjective.comp
        (Fintype.equivFin {p : ℕ // p ∈ N.primeFactors}).symm.surjective }
  invFun f :=
    { block := fun p => f (Fintype.equivFin {p : ℕ // p ∈ N.primeFactors} p)
      surjective := f.surjective.comp
        (Fintype.equivFin {p : ℕ // p ∈ N.primeFactors}).surjective }
  left_inv := by
    intro f
    apply PrimeBlockSurjection.ext
    funext p
    simp
  right_inv := by
    intro f
    apply FinSurjection.ext
    funext i
    simp

end PrimeBlockSurjection

namespace SquarefreeMulTuple

/-- A factor tuple is an element of the multiplicative antidiagonal. -/
theorem mem_finMulAntidiag {N j : ℕ} (hN : N ≠ 0) (t : SquarefreeMulTuple N j) :
    t.factor ∈ Nat.finMulAntidiag j N := by
  rw [Nat.mem_finMulAntidiag]
  exact ⟨t.prod_eq, hN⟩

/-- Unique block index containing a prime factor. -/
noncomputable def primeBlock {N j : ℕ} (hN : Squarefree N) (t : SquarefreeMulTuple N j)
    (p : {p : ℕ // p ∈ N.primeFactors}) : Fin j :=
  Classical.choose (Nat.finMulAntidiag_existsUnique_prime_dvd hN
    (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp p.2) t.factor
    (t.mem_finMulAntidiag hN.ne_zero))

theorem prime_dvd_factor_primeBlock {N j : ℕ} (hN : Squarefree N)
    (t : SquarefreeMulTuple N j) (p : {p : ℕ // p ∈ N.primeFactors}) :
    p.1 ∣ t.factor (t.primeBlock hN p) :=
  (Classical.choose_spec (Nat.finMulAntidiag_existsUnique_prime_dvd hN
    (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp p.2) t.factor
    (t.mem_finMulAntidiag hN.ne_zero))).1

/-- The chosen prime block is characterized exactly by divisibility. -/
theorem primeBlock_eq_iff {N j : ℕ} (hN : Squarefree N)
    (t : SquarefreeMulTuple N j) (p : {p : ℕ // p ∈ N.primeFactors}) (i : Fin j) :
    t.primeBlock hN p = i ↔ p.1 ∣ t.factor i := by
  let hex := Nat.finMulAntidiag_existsUnique_prime_dvd hN
    (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp p.2) t.factor
    (t.mem_finMulAntidiag hN.ne_zero)
  constructor
  · rintro rfl
    exact t.prime_dvd_factor_primeBlock hN p
  · intro hdvd
    exact ((Classical.choose_spec hex).2 i hdvd).symm

/-- Every nontrivial factor receives at least one prime, so the prime-block map is surjective. -/
theorem primeBlock_surjective {N j : ℕ} (hN : Squarefree N)
    (t : SquarefreeMulTuple N j) : Function.Surjective (t.primeBlock hN) := by
  intro i
  obtain ⟨p, hpPrime, hpDvd⟩ := Nat.exists_prime_and_dvd
    (ne_of_gt (lt_of_lt_of_le Nat.one_lt_two (t.factor_ge_two i)))
  have hiAnti := t.mem_finMulAntidiag hN.ne_zero
  have hfactorDvdN : t.factor i ∣ N := Nat.dvd_of_mem_finMulAntidiag hiAnti i
  have hpMem : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr
    ⟨hpPrime, hpDvd.trans hfactorDvdN, hN.ne_zero⟩
  refine ⟨⟨p, hpMem⟩, ?_⟩
  exact (t.primeBlock_eq_iff hN ⟨p, hpMem⟩ i).2 hpDvd

/-- Numeric tuple converted to its unique prime-block assignment. -/
noncomputable def toPrimeBlockSurjection {N j : ℕ} (hN : Squarefree N)
    (t : SquarefreeMulTuple N j) : PrimeBlockSurjection N j where
  block := t.primeBlock hN
  surjective := t.primeBlock_surjective hN

/-- Reconstructing a factor from the primes assigned to it recovers that factor exactly. -/
theorem blockProduct_toPrimeBlockSurjection {N j : ℕ} (hN : Squarefree N)
    (t : SquarefreeMulTuple N j) (i : Fin j) :
    (t.toPrimeBlockSurjection hN).blockProduct i = t.factor i := by
  have hiAnti := t.mem_finMulAntidiag hN.ne_zero
  have hfactorDvdN : t.factor i ∣ N := Nat.dvd_of_mem_finMulAntidiag hiAnti i
  calc
    (t.toPrimeBlockSurjection hN).blockProduct i =
        ∏ p ∈ N.primeFactors.attach, if p.1 ∣ t.factor i then p.1 else 1 := by
      unfold PrimeBlockSurjection.blockProduct
      rw [Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro p hp
      change (if t.primeBlock hN p = i then p.1 else 1) =
        if p.1 ∣ t.factor i then p.1 else 1
      rw [if_congr (t.primeBlock_eq_iff hN p i) rfl rfl]
    _ = ∏ p ∈ N.primeFactors, if p ∣ t.factor i then p else 1 := by
      exact Finset.prod_attach N.primeFactors
        (fun p => if p ∣ t.factor i then p else 1)
    _ = ∏ p ∈ {p ∈ N.primeFactors | p ∣ t.factor i}, p := by
      rw [← Finset.prod_filter]
    _ = ∏ p ∈ (t.factor i).primeFactors, p := by
      rw [Nat.primeFactors_filter_dvd_of_dvd hN.ne_zero hfactorDvdN]
    _ = t.factor i := Nat.prod_primeFactors_of_squarefree
      (hN.squarefree_of_dvd hfactorDvdN)

/-- Squarefree numeric factor tuples are exactly surjective ordered prime-block assignments. -/
noncomputable def equivPrimeBlockSurjection {N j : ℕ} (hN : Squarefree N) :
    SquarefreeMulTuple N j ≃ PrimeBlockSurjection N j where
  toFun := toPrimeBlockSurjection hN
  invFun := PrimeBlockSurjection.toMulTuple hN
  left_inv := by
    intro t
    apply SquarefreeMulTuple.ext
    funext i
    exact t.blockProduct_toPrimeBlockSurjection hN i
  right_inv := by
    intro f
    apply PrimeBlockSurjection.ext
    funext p
    apply (f.toMulTuple hN).primeBlock_eq_iff hN p (f.block p) |>.2
    exact f.prime_dvd_blockProduct_iff p (f.block p) |>.2 rfl

/-- Exact fixed-length squarefree factor count. -/
theorem card {N : ℕ} (hN : Squarefree N) (j : ℕ) :
    Nat.card (SquarefreeMulTuple N j) =
      j.factorial * Nat.stirlingSecond N.primeFactors.card j := by
  rw [Nat.card_congr (equivPrimeBlockSurjection hN)]
  rw [Nat.card_congr (PrimeBlockSurjection.equivFinSurjection N j)]
  simpa only [Fintype.card_coe] using FinSurjection.card N.primeFactors.card j

end SquarefreeMulTuple

/-- A labelled family of pairwise distinct primes. -/
structure DistinctPrimeFamily (k : ℕ) where
  primeValue : Fin k → ℕ
  prime : ∀ i, (primeValue i).Prime
  injective : Function.Injective primeValue

namespace DistinctPrimeFamily

/-- Product of all primes in the family. -/
def product {k : ℕ} (p : DistinctPrimeFamily k) : ℕ := ∏ i, p.primeValue i

/-- The prime-factor set of the product is exactly the image of the labelled family. -/
theorem primeFactors_product {k : ℕ} (p : DistinctPrimeFamily k) :
    p.product.primeFactors = Finset.univ.image p.primeValue := by
  have hprod : (∏ q ∈ Finset.univ.image p.primeValue, q) =
      ∏ i, p.primeValue i := by
    simpa only [id_eq] using
      Finset.prod_image (s := Finset.univ) (g := p.primeValue) (f := id)
        p.injective.injOn
  rw [product, ← hprod]
  exact Nat.primeFactors_prod fun q hq => by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact p.prime i

/-- The product has exactly `k` distinct prime factors. -/
theorem card_primeFactors_product {k : ℕ} (p : DistinctPrimeFamily k) :
    p.product.primeFactors.card = k := by
  rw [p.primeFactors_product, Finset.card_image_of_injective _ p.injective,
    Finset.card_univ, Fintype.card_fin]

/-- A product of pairwise distinct primes is squarefree. -/
theorem squarefree_product {k : ℕ} (p : DistinctPrimeFamily k) : Squarefree p.product := by
  unfold product
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i _ j _ hij
    change IsRelPrime (p.primeValue i) (p.primeValue j)
    rw [← Nat.coprime_iff_isRelPrime, (p.prime i).coprime_iff_not_dvd]
    intro hdvd
    rcases (Nat.dvd_prime (p.prime j)).mp hdvd with hone | heq
    · exact (p.prime i).ne_one hone
    · exact hij (p.injective heq)
  · intro i _
    exact (p.prime i).prime.irreducible.squarefree

/-- A nonempty distinct-prime product is not one. -/
theorem product_ne_one {k : ℕ} (p : DistinctPrimeFamily k) (hk : 0 < k) : p.product ≠ 1 := by
  intro hprod
  let i : Fin k := ⟨0, hk⟩
  have hdvd : p.primeValue i ∣ p.product := by
    unfold product
    exact Finset.dvd_prod_of_mem p.primeValue (Finset.mem_univ i)
  rw [hprod] at hdvd
  exact (p.prime i).not_dvd_one hdvd

end DistinctPrimeFamily

namespace OrderedFactorization

/-- Raw sigma encoding of a nonempty factor list.  Using `List.equivSigmaTuple` keeps length and
tuple transport coherent definitionally. -/
def FactorSigma (N : ℕ) :=
  {s : Σ j : ℕ, Fin j → ℕ //
    0 < s.1 ∧ (∀ i, 2 ≤ s.2 i) ∧ ∏ i, s.2 i = N}

/-- Ordered factorizations are exactly valid raw factor sigmas. -/
def equivFactorSigma (N : ℕ) : OrderedFactorization N ≃ FactorSigma N where
  toFun f :=
    ⟨⟨f.factors.length, f.factors.get⟩,
      (List.ne_nil_iff_length_pos.mp f.nonempty),
      fun i => f.factor_ge_two _ (f.factors.get_mem i),
      by rw [← List.prod_ofFn, List.ofFn_get, f.prod_eq]⟩
  invFun s :=
    { factors := List.ofFn s.1.2
      nonempty := by
        rw [List.ne_nil_iff_length_pos, List.length_ofFn]
        exact s.2.1
      factor_ge_two := by
        intro a ha
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
        exact s.2.2.1 i
      prod_eq := by rw [List.prod_ofFn]; exact s.2.2.2 }
  left_inv := by
    intro f
    apply OrderedFactorization.ext
    exact List.ofFn_get f.factors
  right_inv := by
    intro s
    apply Subtype.ext
    exact List.equivSigmaTuple.apply_symm_apply s.1

/-- Valid raw factor sigmas are bounded by the number of squarefree prime factors. -/
noncomputable def factorSigmaEquivBoundedTuples {N : ℕ} (hN : Squarefree N) (hN1 : N ≠ 1) :
    FactorSigma N ≃
      Σ j : Fin (N.primeFactors.card + 1), SquarefreeMulTuple N j where
  toFun s := by
    let t : SquarefreeMulTuple N s.1.1 :=
      { factor := s.1.2
        factor_ge_two := s.2.2.1
        prod_eq := s.2.2.2 }
    let assignment := t.toPrimeBlockSurjection hN
    have hlength : s.1.1 ≤ N.primeFactors.card := by
      simpa only [Fintype.card_fin, Fintype.card_coe] using
        Fintype.card_le_of_surjective assignment.block assignment.surjective
    exact ⟨⟨s.1.1, Nat.lt_succ_of_le hlength⟩, t⟩
  invFun t :=
    ⟨⟨t.1.val, t.2.factor⟩,
      by
        apply Nat.pos_of_ne_zero
        intro hjzero
        have hprod : (∏ i, t.2.factor i) = 1 := by
          apply Finset.prod_eq_one
          intro i _
          exact Fin.elim0 (Fin.cast hjzero i)
        exact hN1 (t.2.prod_eq.symm.trans hprod),
      t.2.factor_ge_two,
      t.2.prod_eq⟩
  left_inv := by
    rintro ⟨⟨j, factor⟩, hj, hfactor, hprod⟩
    apply Subtype.ext
    rfl
  right_inv := by
    rintro ⟨⟨j, hjbound⟩, ⟨factor, hfactor, hprod⟩⟩
    apply Sigma.ext
    · apply Fin.ext
      rfl
    · rfl

/-- Actual ordered factorizations of a squarefree integer are exactly its bounded factor tuples. -/
noncomputable def squarefreeEquivTuples {N : ℕ} (hN : Squarefree N) (hN1 : N ≠ 1) :
    OrderedFactorization N ≃
      Σ j : Fin (N.primeFactors.card + 1), SquarefreeMulTuple N j :=
  (equivFactorSigma N).trans (factorSigmaEquivBoundedTuples hN hN1)

/-- **Squarefree ordered-Bell law for actual numeric Airy towers.** -/
theorem card_squarefree {N : ℕ} (hN : Squarefree N) (hN1 : N ≠ 1) :
    Nat.card (OrderedFactorization N) =
      ∑ j ∈ Finset.Icc 1 N.primeFactors.card,
        j.factorial * Nat.stirlingSecond N.primeFactors.card j := by
  rw [Nat.card_congr (squarefreeEquivTuples hN hN1), Nat.card_sigma]
  rw [Fin.sum_univ_eq_sum_range
    (fun j => Nat.card (SquarefreeMulTuple N j)) (N.primeFactors.card + 1)]
  simp_rw [SquarefreeMulTuple.card hN]
  symm
  apply Finset.sum_subset
  · intro j hj
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hj).2)
  · intro j hjRange hjIcc
    have hjzero : j = 0 := by
      by_contra hjne
      apply hjIcc
      exact Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr hjne, Nat.le_of_lt_succ (Finset.mem_range.mp hjRange)⟩
    subst j
    have hcardPos : 0 < N.primeFactors.card := by
      rw [Finset.card_pos]
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hN1
      exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpdvd, hN.ne_zero⟩⟩
    cases hcard : N.primeFactors.card with
    | zero => omega
    | succ k => exact Nat.stirlingSecond_succ_zero k

/-- Squarefree count with an externally named number `k` of distinct prime factors. -/
theorem card_squarefree_of_primeFactors_card {N k : ℕ} (hN : Squarefree N) (hN1 : N ≠ 1)
    (hcard : N.primeFactors.card = k) :
    Nat.card (OrderedFactorization N) =
      ∑ j ∈ Finset.Icc 1 k, j.factorial * Nat.stirlingSecond k j := by
  simpa only [hcard] using card_squarefree hN hN1

/-- Exact paper statement: a product of `k` pairwise distinct primes has ordered-Bell many actual
numeric ordered factorizations. -/
theorem card_distinctPrimeProduct {k : ℕ} (p : DistinctPrimeFamily k) (hk : 0 < k) :
    Nat.card (OrderedFactorization p.product) =
      ∑ j ∈ Finset.Icc 1 k, j.factorial * Nat.stirlingSecond k j := by
  exact card_squarefree_of_primeFactors_card p.squarefree_product (p.product_ne_one hk)
    p.card_primeFactors_product

/-- Paper convention for the exact squarefree Airy-tower count. -/
theorem airyTowerCount_squarefree {N : ℕ} (hN : Squarefree N) (hN1 : N ≠ 1) :
    OrderedFactorizationTail.airyTowerCount N =
      ∑ j ∈ Finset.Icc 1 N.primeFactors.card,
        j.factorial * Nat.stirlingSecond N.primeFactors.card j := by
  have hNgt : 1 < N := by
    have hNpos : 0 < N := Nat.pos_of_ne_zero hN.ne_zero
    omega
  rw [OrderedFactorizationTail.airyTowerCount_eq_orderedFactorization hNgt]
  exact card_squarefree hN hN1

/-- Paper-convention Airy count for a product of `k` pairwise distinct primes. -/
theorem airyTowerCount_distinctPrimeProduct {k : ℕ} (p : DistinctPrimeFamily k) (hk : 0 < k) :
    OrderedFactorizationTail.airyTowerCount p.product =
      ∑ j ∈ Finset.Icc 1 k, j.factorial * Nat.stirlingSecond k j := by
  have hprodGt : 1 < p.product := by
    have hprodPos : 0 < p.product := by
      unfold DistinctPrimeFamily.product
      exact Finset.prod_pos fun i _ => (p.prime i).pos
    have hprodNe : p.product ≠ 1 := p.product_ne_one hk
    omega
  rw [OrderedFactorizationTail.airyTowerCount_eq_orderedFactorization hprodGt]
  exact card_distinctPrimeProduct p hk

end OrderedFactorization

end IrregularStokes
end GaloisForLFunctions

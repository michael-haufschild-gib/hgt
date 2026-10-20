import GaloisForLFunctions.BezoutValuationIncidence.LogFreeMultiplicativeLargeSieve
import GaloisForLFunctions.BezoutValuationIncidence.UniformLagWindowCovarianceAtQuadraticOrder
import GaloisForLFunctions.RHTower.Sieve.MontgomerySieve

/-!
# The arithmetic large sieve for squarefree moduli

Let `A ⊆ [0, N)` occupy `c_p` residue classes modulo each prime `p`, and put
`h(q) = Π_{p ∣ q} (p - c_p)/c_p` for squarefree `q`. Montgomery's inequality

`h(q) |Σ_{n ∈ A} b_n|² ≤ Σ_{ζ primitive of order q} |Σ_{n ∈ A} b_n ζ^n|²`

holds for arbitrary complex weights: at a prime it is Parseval over the `p`-th roots of unity and
Cauchy–Schwarz over the occupied classes, and it multiplies along coprime factors because the
primitive roots of order `pq` are exactly the products of primitive roots of orders `p` and `q`.
Summing over the squarefree `q ≤ Q`, whose primitive roots are disjoint response frequencies, and
applying the log-free large sieve over the roots of order at most `Q` gives

`|A| Σ_{q ≤ Q squarefree} h(q) ≤ N + 2Q² - 1`.

This is the arithmetic large sieve with unit main coefficient and no logarithm.
-/

open Finset RHTower.Sieve
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-! ## §1. Parseval over the `p`-th roots of unity -/

theorem conj_eq_pow_pred_of_mem_nthRootsFinset {p : ℕ} (hp : 0 < p) {η : ℂ}
    (hη : η ∈ Polynomial.nthRootsFinset p (1 : ℂ)) : conj η = η ^ (p - 1) := by
  have hη1 := (Polynomial.mem_nthRootsFinset hp 1).mp hη
  have hn : ‖η‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hη1 hp.ne'
  have h1 : conj η * η = 1 := conj_mul_self_of_norm_eq_one hn
  have h2 : η ^ (p - 1) * η = 1 := by rw [← pow_succ, Nat.sub_add_cancel hp, hη1]
  have hη0 : η ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  exact mul_right_cancel₀ hη0 (h1.trans h2.symm)

theorem dvd_add_pred_mul_iff {p n m : ℕ} (hp : 0 < p) :
    p ∣ n + (p - 1) * m ↔ n % p = m % p := by
  rw [← Nat.ModEq, Nat.modEq_iff_dvd, ← Int.natCast_dvd_natCast]
  push_cast [Nat.cast_sub hp]
  constructor
  · intro h
    have h' : (p : ℤ) ∣ (n + (p - 1) * m : ℤ) - p * m := dvd_sub h (dvd_mul_right _ _)
    rw [show (n + (p - 1) * m : ℤ) - p * m = -((m : ℤ) - n) by ring] at h'
    exact dvd_neg.mp h'
  · intro h
    have h' : (p : ℤ) ∣ -((m : ℤ) - n) + p * m := dvd_add (dvd_neg.mpr h) (dvd_mul_right _ _)
    rwa [show -((m : ℤ) - n) + p * m = (n + (p - 1) * m : ℤ) by ring] at h'

/-- Parseval over the `p`-th roots of unity: the energy is `p` times the class energies. -/
theorem sum_nthRootsFinset_norm_sq {p : ℕ} (hp : 0 < p) (A : Finset ℕ) (b : ℕ → ℂ) :
    ∑ η ∈ Polynomial.nthRootsFinset p (1 : ℂ), ‖∑ n ∈ A, b n * η ^ n‖ ^ 2 =
      p * ∑ h ∈ range p, ‖∑ n ∈ A.filter (fun n => n % p = h), b n‖ ^ 2 := by
  classical
  have hpair : ∀ n m : ℕ, ∑ η ∈ Polynomial.nthRootsFinset p (1 : ℂ), η ^ n * conj η ^ m =
      if n % p = m % p then (p : ℂ) else 0 := by
    intro n m
    rw [sum_congr rfl fun η hη => by
        rw [conj_eq_pow_pred_of_mem_nthRootsFinset hp hη, ← pow_mul, ← pow_add],
      sum_nthRootsFinset_pow hp]
    simp only [dvd_add_pred_mul_iff hp]
  have hcell : ∀ n m : ℕ, ∀ x : ℂ,
      ∑ h ∈ range p, (if n % p = h ∧ m % p = h then x else 0) = if n % p = m % p then x else 0 := by
    intro n m x
    by_cases hnm : n % p = m % p
    · rw [if_pos hnm, sum_eq_single_of_mem (n % p) (mem_range.mpr (Nat.mod_lt n hp))
        fun h _ hh => by rw [if_neg fun hc => hh hc.1.symm], if_pos ⟨rfl, hnm.symm⟩]
    · rw [if_neg hnm]
      exact sum_eq_zero fun h _ => by rw [if_neg fun hc => hnm (hc.1.trans hc.2.symm)]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_sum]
  have hL : ∑ η ∈ Polynomial.nthRootsFinset p (1 : ℂ), ((‖∑ n ∈ A, b n * η ^ n‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ A, ∑ m ∈ A, b n * conj (b m) * (if n % p = m % p then (p : ℂ) else 0) := by
    have h1 : ∀ η ∈ Polynomial.nthRootsFinset p (1 : ℂ),
        ((‖∑ n ∈ A, b n * η ^ n‖ ^ 2 : ℝ) : ℂ) =
          ∑ n ∈ A, ∑ m ∈ A, b n * conj (b m) * (η ^ n * conj η ^ m) := by
      intro η _
      rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, sum_mul_sum]
      refine sum_congr rfl fun n _ => sum_congr rfl fun m _ => ?_
      rw [map_mul, map_pow]
      ring
    rw [sum_congr rfl h1, sum_comm]
    refine sum_congr rfl fun n _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun m _ => by rw [← mul_sum, hpair]
  have hR : (p : ℂ) * ∑ h ∈ range p, ((‖∑ n ∈ A.filter (fun n => n % p = h), b n‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ A, ∑ m ∈ A, b n * conj (b m) * (if n % p = m % p then (p : ℂ) else 0) := by
    have h1 : ∀ h ∈ range p, ((‖∑ n ∈ A.filter (fun n => n % p = h), b n‖ ^ 2 : ℝ) : ℂ) =
        ∑ n ∈ A, ∑ m ∈ A, if n % p = h ∧ m % p = h then b n * conj (b m) else 0 := by
      intro h _
      rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, sum_mul_sum, sum_filter]
      refine sum_congr rfl fun n _ => ?_
      rw [sum_filter]
      split_ifs with hn
      · exact sum_congr rfl fun m _ => by
          by_cases hm : m % p = h <;> simp [hn, hm]
      · exact (sum_eq_zero fun m _ => by simp [hn]).symm
    rw [sum_congr rfl h1, sum_comm, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [hcell]
    split_ifs <;> ring
  rw [hL, hR]

/-! ## §2. Montgomery's inequality at a prime -/

theorem nthRootsFinset_prime_eq_insert {p : ℕ} (hp : p.Prime) :
    Polynomial.nthRootsFinset p (1 : ℂ) = insert 1 (primitiveRoots p ℂ) := by
  classical
  rw [IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots, Nat.Prime.divisors hp,
    show ({1, p} : Finset ℕ) = insert 1 {p} from rfl, biUnion_insert, singleton_biUnion,
    IsPrimitiveRoot.primitiveRoots_one, insert_eq]

/-- **Montgomery's inequality at a prime.** -/
theorem montgomery_prime_ge {p : ℕ} (hp : p.Prime) {A : Finset ℕ} (hA : A.Nonempty)
    (b : ℕ → ℂ) :
    ((p : ℝ) - (occupiedClasses p A).card) / (occupiedClasses p A).card *
        ‖∑ n ∈ A, b n‖ ^ 2 ≤ ∑ η ∈ primitiveRoots p ℂ, ‖∑ n ∈ A, b n * η ^ n‖ ^ 2 := by
  classical
  set c : ℝ := ((occupiedClasses p A).card : ℝ) with hcdef
  have hc : (0 : ℝ) < c := by
    rw [hcdef]
    exact_mod_cast occupiedClasses_card_pos hp.pos hA
  have hparse := sum_nthRootsFinset_norm_sq hp.pos A b
  have h1notin : (1 : ℂ) ∉ primitiveRoots p ℂ := by
    intro h
    have := ((mem_primitiveRoots hp.pos).mp h).eq_orderOf
    rw [orderOf_one] at this
    exact hp.one_lt.ne' this
  rw [nthRootsFinset_prime_eq_insert hp, sum_insert h1notin] at hparse
  simp only [one_pow, mul_one] at hparse
  set B : ℕ → ℂ := fun h => ∑ n ∈ A.filter (fun n => n % p = h), b n with hB
  -- the total is the sum of the occupied class sums
  have htot : ∑ n ∈ A, b n = ∑ h ∈ occupiedClasses p A, B h := by
    rw [← sum_fiberwise_of_maps_to (s := A) (t := range p) (g := fun n => n % p)
      (fun n _ => mem_range.mpr (Nat.mod_lt n hp.pos)) b]
    symm
    refine sum_subset (filter_subset _ _) fun h hh hocc => ?_
    have hzero : residueCount p A h = 0 := by
      by_contra hne
      exact hocc (mem_filter.mpr ⟨hh, hne⟩)
    have hempty : A.filter (fun n => n % p = h) = ∅ := card_eq_zero.mp hzero
    simp [hB, hempty]
  have hcs : ‖∑ n ∈ A, b n‖ ^ 2 ≤ c * ∑ h ∈ range p, ‖B h‖ ^ 2 := by
    rw [htot]
    calc ‖∑ h ∈ occupiedClasses p A, B h‖ ^ 2
        ≤ (∑ h ∈ occupiedClasses p A, ‖B h‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ c * ∑ h ∈ occupiedClasses p A, ‖B h‖ ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ c * ∑ h ∈ range p, ‖B h‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            fun _ _ _ => sq_nonneg _) hc.le
  have hval : ∑ η ∈ primitiveRoots p ℂ, ‖∑ n ∈ A, b n * η ^ n‖ ^ 2 =
      p * ∑ h ∈ range p, ‖B h‖ ^ 2 - ‖∑ n ∈ A, b n‖ ^ 2 := by linarith
  rw [hval]
  have hE : ‖∑ n ∈ A, b n‖ ^ 2 / c ≤ ∑ h ∈ range p, ‖B h‖ ^ 2 := by
    rw [div_le_iff₀ hc]
    linarith
  calc ((p : ℝ) - c) / c * ‖∑ n ∈ A, b n‖ ^ 2
      = (p : ℝ) * (‖∑ n ∈ A, b n‖ ^ 2 / c) - ‖∑ n ∈ A, b n‖ ^ 2 := by field_simp
    _ ≤ (p : ℝ) * ∑ h ∈ range p, ‖B h‖ ^ 2 - ‖∑ n ∈ A, b n‖ ^ 2 := by
        have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
        nlinarith

/-! ## §3. Primitive roots of coprime orders multiply -/

theorem sum_primitiveRoots_mul_eq {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : p.Coprime q)
    (F : ℂ → ℝ) :
    ∑ ζ ∈ primitiveRoots (p * q) ℂ, F ζ =
      ∑ ξ ∈ primitiveRoots q ℂ, ∑ η ∈ primitiveRoots p ℂ, F (η * ξ) := by
  classical
  set f : ℂ × ℂ → ℂ := fun x => x.1 * x.2
  have hinj : Set.InjOn f ↑(primitiveRoots p ℂ ×ˢ primitiveRoots q ℂ) := by
    rintro ⟨η, ξ⟩ hx ⟨η', ξ'⟩ hx' hf
    simp only [coe_product, Set.mem_prod, mem_coe] at hx hx'
    have hη := (mem_primitiveRoots hp).mp hx.1
    have hξ := (mem_primitiveRoots hq).mp hx.2
    have hη' := (mem_primitiveRoots hp).mp hx'.1
    have hξ' := (mem_primitiveRoots hq).mp hx'.2
    simp only [f] at hf
    have hξ0 : ξ ≠ 0 := hξ.ne_zero hq.ne'
    have hη'0 : η' ≠ 0 := hη'.ne_zero hp.ne'
    set w := η / η' with hw
    have hwp : w ^ p = 1 := by rw [hw, div_pow, hη.pow_eq_one, hη'.pow_eq_one, div_one]
    have hwq : w ^ q = 1 := by
      have : w = ξ' / ξ := by
        rw [hw, div_eq_div_iff hη'0 hξ0]
        linear_combination hf
      rw [this, div_pow, hξ.pow_eq_one, hξ'.pow_eq_one, div_one]
    have hw1 : w = 1 := by
      have := (pow_gcd_eq_one (a := w) (m := p) (n := q)).mpr ⟨hwp, hwq⟩
      rwa [hpq.gcd_eq_one, pow_one] at this
    have hηη : η = η' := by
      rw [hw, div_eq_one_iff_eq hη'0] at hw1
      exact hw1
    rw [hηη] at hf ⊢
    exact Prod.ext rfl (mul_left_cancel₀ hη'0 hf)
  have hsub : (primitiveRoots p ℂ ×ˢ primitiveRoots q ℂ).image f ⊆ primitiveRoots (p * q) ℂ := by
    intro z hz
    obtain ⟨⟨η, ξ⟩, hx, rfl⟩ := mem_image.mp hz
    obtain ⟨hηm, hξm⟩ := mem_product.mp hx
    have hη := (mem_primitiveRoots hp).mp hηm
    have hξ := (mem_primitiveRoots hq).mp hξm
    refine (mem_primitiveRoots (Nat.mul_pos hp hq)).mpr ?_
    have hord : orderOf (η * ξ) = p * q := by
      rw [(Commute.all η ξ).orderOf_mul_eq_mul_orderOf_of_coprime
        (by rw [← hη.eq_orderOf, ← hξ.eq_orderOf]; exact hpq), ← hη.eq_orderOf, ← hξ.eq_orderOf]
    rw [← hord]
    exact IsPrimitiveRoot.orderOf _
  have hcard : (primitiveRoots (p * q) ℂ).card ≤
      ((primitiveRoots p ℂ ×ˢ primitiveRoots q ℂ).image f).card := by
    rw [card_image_of_injOn hinj, card_product,
      (Complex.isPrimitiveRoot_exp _ (Nat.mul_pos hp hq).ne').card_primitiveRoots,
      (Complex.isPrimitiveRoot_exp _ hp.ne').card_primitiveRoots,
      (Complex.isPrimitiveRoot_exp _ hq.ne').card_primitiveRoots, Nat.totient_mul hpq]
  have heq := eq_of_subset_of_card_le hsub hcard
  rw [← heq, sum_image hinj, sum_product_right]

/-! ## §4. Montgomery's inequality for products of distinct primes -/

theorem occupied_ratio_nonneg {p : ℕ} (A : Finset ℕ) :
    0 ≤ ((p : ℝ) - (occupiedClasses p A).card) / (occupiedClasses p A).card := by
  have hle : (occupiedClasses p A).card ≤ p := by
    have := card_le_card (occupiedClasses_subset p A)
    rwa [card_range] at this
  have : ((occupiedClasses p A).card : ℝ) ≤ p := by exact_mod_cast hle
  exact div_nonneg (by linarith) (Nat.cast_nonneg _)

/-- **Montgomery's inequality.** For a product `q` of distinct primes,
`h(q) |Σ_{n ∈ A} b_n|² ≤ Σ_{ζ primitive of order q} |Σ_{n ∈ A} b_n ζ^n|²`. -/
theorem montgomery_prod_primes_ge {A : Finset ℕ} (hA : A.Nonempty) (b : ℕ → ℂ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, ((p : ℝ) - (occupiedClasses p A).card) / (occupiedClasses p A).card) *
        ‖∑ n ∈ A, b n‖ ^ 2 ≤
      ∑ ζ ∈ primitiveRoots (∏ p ∈ S, p) ℂ, ‖∑ n ∈ A, b n * ζ ^ n‖ ^ 2 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp [IsPrimitiveRoot.primitiveRoots_one]
  | insert p S hpS ih =>
    have hp := hS p (mem_insert_self p S)
    have hSp : ∀ r ∈ S, r.Prime := fun r hr => hS r (mem_insert_of_mem hr)
    have hcop : p.Coprime (∏ r ∈ S, r) := Nat.Coprime.prod_right fun r hr =>
      (Nat.coprime_primes hp (hSp r hr)).mpr fun h => hpS (h ▸ hr)
    have hSpos : 0 < ∏ r ∈ S, r := prod_pos fun r hr => (hSp r hr).pos
    rw [prod_insert hpS, prod_insert hpS,
      sum_primitiveRoots_mul_eq hp.pos hSpos hcop (fun ζ => ‖∑ n ∈ A, b n * ζ ^ n‖ ^ 2)]
    have hstep : ∀ ξ ∈ primitiveRoots (∏ r ∈ S, r) ℂ,
        ((p : ℝ) - (occupiedClasses p A).card) / (occupiedClasses p A).card *
            ‖∑ n ∈ A, b n * ξ ^ n‖ ^ 2 ≤
          ∑ η ∈ primitiveRoots p ℂ, ‖∑ n ∈ A, b n * (η * ξ) ^ n‖ ^ 2 := by
      intro ξ _
      have h := montgomery_prime_ge hp hA (fun n => b n * ξ ^ n)
      refine h.trans_eq (sum_congr rfl fun η _ => ?_)
      congr 2
      exact sum_congr rfl fun n _ => by rw [mul_pow]; ring
    have hratio := occupied_ratio_nonneg (p := p) A
    calc ((p : ℝ) - (occupiedClasses p A).card) / (occupiedClasses p A).card *
          (∏ r ∈ S, ((r : ℝ) - (occupiedClasses r A).card) / (occupiedClasses r A).card) *
          ‖∑ n ∈ A, b n‖ ^ 2
        = ((p : ℝ) - (occupiedClasses p A).card) / (occupiedClasses p A).card *
          ((∏ r ∈ S, ((r : ℝ) - (occupiedClasses r A).card) / (occupiedClasses r A).card) *
            ‖∑ n ∈ A, b n‖ ^ 2) := by ring
      _ ≤ ((p : ℝ) - (occupiedClasses p A).card) / (occupiedClasses p A).card *
          ∑ ξ ∈ primitiveRoots (∏ r ∈ S, r) ℂ, ‖∑ n ∈ A, b n * ξ ^ n‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (ih hSp) hratio
      _ = ∑ ξ ∈ primitiveRoots (∏ r ∈ S, r) ℂ,
          ((p : ℝ) - (occupiedClasses p A).card) / (occupiedClasses p A).card *
            ‖∑ n ∈ A, b n * ξ ^ n‖ ^ 2 := mul_sum _ _ _
      _ ≤ _ := sum_le_sum hstep

/-! ## §5. The arithmetic large sieve -/

/-- **The arithmetic large sieve with constant `N + 2Q² - 1`.** -/
theorem arithmetic_largeSieve_logFree (N : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (A : Finset ℕ)
    (hA : A ⊆ range N) (hAne : A.Nonempty) :
    (A.card : ℝ) * ∑ q ∈ (Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors,
        ((p : ℝ) - (occupiedClasses p A).card) / (occupiedClasses p A).card ≤
      (N : ℝ) + 2 * (Q : ℝ) ^ 2 - 1 := by
  classical
  set h : ℕ → ℝ := fun q => ∏ p ∈ q.primeFactors,
    ((p : ℝ) - (occupiedClasses p A).card) / (occupiedClasses p A).card with hh
  set E : ℂ → ℝ := fun ζ => ‖∑ n ∈ A, ζ ^ n‖ ^ 2 with hE
  have hE0 : ∀ ζ, 0 ≤ E ζ := fun ζ => sq_nonneg _
  have hcardsq : ‖∑ n ∈ A, (1 : ℂ)‖ ^ 2 = (A.card : ℝ) ^ 2 := by
    rw [sum_const, nsmul_eq_mul, mul_one, Complex.norm_natCast]
  -- Montgomery at every squarefree modulus
  have hmont : ∀ q ∈ (Icc 1 Q).filter Squarefree,
      h q * (A.card : ℝ) ^ 2 ≤ ∑ ζ ∈ primitiveRoots q ℂ, E ζ := by
    intro q hq
    have hsq := (mem_filter.mp hq).2
    have hm := montgomery_prod_primes_ge hAne (fun _ => 1) q.primeFactors
      (fun p hp => Nat.prime_of_mem_primeFactors hp)
    rw [Nat.prod_primeFactors_of_squarefree hsq, hcardsq] at hm
    simpa only [one_mul, hE] using hm
  have hsum : (A.card : ℝ) ^ 2 * ∑ q ∈ (Icc 1 Q).filter Squarefree, h q ≤
      ∑ ζ ∈ responseRoots Q, E ζ := by
    have h1 : ∑ ζ ∈ responseRoots Q, (E ζ : ℂ) =
        ((∑ q ∈ Icc 1 Q, ∑ ζ ∈ primitiveRoots q ℂ, E ζ : ℝ) : ℂ) := by
      rw [sum_responseRoots_eq_sum_primitiveRoots]
      push_cast
      rfl
    have h2 : ∑ ζ ∈ responseRoots Q, E ζ = ∑ q ∈ Icc 1 Q, ∑ ζ ∈ primitiveRoots q ℂ, E ζ := by
      exact_mod_cast h1
    rw [h2, mul_sum]
    calc ∑ q ∈ (Icc 1 Q).filter Squarefree, (A.card : ℝ) ^ 2 * h q
        ≤ ∑ q ∈ (Icc 1 Q).filter Squarefree, ∑ ζ ∈ primitiveRoots q ℂ, E ζ :=
          sum_le_sum fun q hq => by rw [mul_comm]; exact hmont q hq
      _ ≤ ∑ q ∈ Icc 1 Q, ∑ ζ ∈ primitiveRoots q ℂ, E ζ :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun q _ _ =>
            sum_nonneg fun ζ _ => hE0 ζ
  -- the log-free large sieve over the roots of order at most `Q`
  set y : ℕ → ℂ := fun n => if n ∈ A then 1 else 0 with hy
  have hls := largeSieve_responseRoots_range hQ (subset_refl _) N y
  have hyA : ∀ ζ : ℂ, ∑ n ∈ range N, y n * ζ ^ n = ∑ n ∈ A, ζ ^ n := by
    intro ζ
    simp only [hy, ite_mul, one_mul, zero_mul]
    rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr hA]
  have hyn : ∑ n ∈ range N, ‖y n‖ ^ 2 = (A.card : ℝ) := by
    simp only [hy, apply_ite (fun z : ℂ => ‖z‖ ^ 2), norm_one, one_pow, norm_zero,
      zero_pow two_ne_zero]
    rw [sum_ite_mem, inter_eq_right.mpr hA, sum_const, nsmul_eq_mul, mul_one]
  simp only [hyA, hyn] at hls
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast card_pos.mpr hAne
  have key : (A.card : ℝ) * ((A.card : ℝ) * ∑ q ∈ (Icc 1 Q).filter Squarefree, h q) ≤
      (A.card : ℝ) * ((N : ℝ) + 2 * (Q : ℝ) ^ 2 - 1) := by
    calc (A.card : ℝ) * ((A.card : ℝ) * ∑ q ∈ (Icc 1 Q).filter Squarefree, h q)
        = (A.card : ℝ) ^ 2 * ∑ q ∈ (Icc 1 Q).filter Squarefree, h q := by ring
      _ ≤ ∑ ζ ∈ responseRoots Q, E ζ := hsum
      _ ≤ ((N : ℝ) + 2 * (Q : ℝ) ^ 2 - 1) * (A.card : ℝ) := hls
      _ = _ := by ring
  exact le_of_mul_le_mul_left key hcard

/-- **The sieve bound.** `|A| ≤ (N + 2Q² - 1)/L` whenever `L ≤ Σ_{q ≤ Q squarefree} h(q)`. -/
theorem card_le_of_arithmetic_largeSieve (N : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (A : Finset ℕ)
    (hA : A ⊆ range N) (hAne : A.Nonempty) {L : ℝ} (hL : 0 < L)
    (hLle : L ≤ ∑ q ∈ (Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors,
        ((p : ℝ) - (occupiedClasses p A).card) / (occupiedClasses p A).card) :
    (A.card : ℝ) ≤ ((N : ℝ) + 2 * (Q : ℝ) ^ 2 - 1) / L := by
  rw [le_div_iff₀ hL]
  exact (mul_le_mul_of_nonneg_left hLle (Nat.cast_nonneg _)).trans
    (arithmetic_largeSieve_logFree N hQ A hA hAne)

end

end GaloisForLFunctions.BezoutValuationIncidence

import GaloisForLFunctions.ArithmeticIntersectionTheory.TheTowerFormOfAPrime

/-!
# Weil's prime kernel is a sum of transverse towers

For a prime `p` the orders split into **`p`-ladders**: `m` and `n` lie on the same ladder when they
agree away from `p`, `ordCompl[p] m = ordCompl[p] n`. On a ladder Weil's prime kernel is the tower
form of `p` minus the identity (`TheTowerFormOfAPrime`). This module assembles the ladders.

* **Transversality** (`eq_of_sameLadder_of_sameLadder`): two distinct orders lie on a common ladder for
  at most one prime. Ladders of different primes meet in at most one point: the exponent lattice
  `⊕_p ℕ` has independent coordinates.
* **Decomposition** (`weilPrimeKernel_eq_sum_ladderKernel`): `P(m, n) = Σ_p L_p(m, n)`, where `L_p` is
  the `p`-ladder kernel (`ladderKernel`). Exactly one prime contributes to each nonzero entry.
* **Tensor form** (`ladderKernel_eq_tensor`): `L_p(m, n) = [v_ℓ(m) = v_ℓ(n) ∀ ℓ ≠ p] · log p ·
  (K_{p^{−1/2}} − 1)(v_p(m), v_p(n))`: `L_p = log p (K_p − 1) ⊗ 1` on `ℓ²(⊕_p ℕ)`.
* **Quadratic form** (`primeForm_eq_sum_localForm`): `Σ_{m,n ∈ S} x_m x_n P(m,n) = Σ_p Q_p(x)`.
* **Local Hodge index** (`localForm_lower`, `localForm_upper`): each local form satisfies
  `−2q log p |x|² ≤ (1 + q) Q_p(x)` and `(1 − q) Q_p(x) ≤ 2q log p |x|²`, `q = p^{−1/2}`.

Each local form is bounded, uniformly in the cycle. Their sum is the prime form: local bounds sum to
`Σ_p 2 log p/(√p ± 1)`, which diverges, and the global sign is not the sum of the local ones.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.ArithmeticIntersectionTheory

open ArithmeticEffectivityTheory

/-! ### Ladders -/

theorem eq_ordCompl_mul_pow (p n : ℕ) : n = ordCompl[p] n * p ^ n.factorization p := by
  rw [mul_comm]; exact (Nat.ordProj_mul_ordCompl_eq_self n p).symm

/-- **Transversality.** Two orders on a common `p`-ladder and a common `p'`-ladder, `p ≠ p'`, are equal. -/
theorem eq_of_sameLadder_of_sameLadder {p p' m n : ℕ} (hpp' : p ≠ p') (hm : m ≠ 0) (hn : n ≠ 0)
    (h : ordCompl[p] m = ordCompl[p] n) (h' : ordCompl[p'] m = ordCompl[p'] n) : m = n := by
  have e := congrArg Nat.factorization h
  have e' := congrArg Nat.factorization h'
  rw [Nat.factorization_ordCompl, Nat.factorization_ordCompl] at e e'
  refine Nat.eq_of_factorization_eq hm hn fun ℓ => ?_
  rcases eq_or_ne ℓ p with rfl | hℓ
  · have := congrArg (· ℓ) e'
    simpa [Finsupp.erase_ne hpp'] using this
  · have := congrArg (· ℓ) e
    simpa [Finsupp.erase_ne hℓ] using this

/-- On a common ladder, equal exponents mean equal orders. -/
theorem eq_of_sameLadder_of_factorization_eq {p m n : ℕ} (h : ordCompl[p] m = ordCompl[p] n)
    (hv : m.factorization p = n.factorization p) : m = n := by
  rw [eq_ordCompl_mul_pow p m, eq_ordCompl_mul_pow p n, h, hv]

/-- The **`p`-ladder kernel**: Weil's prime kernel between distinct orders on a common `p`-ladder. -/
def ladderKernel (p m n : ℕ) : ℝ :=
  if m ≠ n ∧ ordCompl[p] m = ordCompl[p] n then
    Real.log p * kmsEntry (1 / Real.sqrt p) (m.factorization p) (n.factorization p)
  else 0

/-- On a common ladder the ladder kernel is Weil's prime kernel. -/
theorem ladderKernel_eq_weilPrimeKernel {p m n : ℕ} (hp : p.Prime) (hm : m ≠ 0)
    (h : ordCompl[p] m = ordCompl[p] n) : ladderKernel p m n = weilPrimeKernel m n := by
  have hc : 0 < ordCompl[p] m := Nat.ordCompl_pos p hm
  have hP := weilPrimeKernel_ladder hp hc (m.factorization p) (n.factorization p)
  rw [← eq_ordCompl_mul_pow, h, ← eq_ordCompl_mul_pow] at hP
  by_cases hmn : m = n
  · subst hmn
    simp [ladderKernel, weilPrimeKernel]
  · have hv : m.factorization p ≠ n.factorization p :=
      fun hv => hmn (eq_of_sameLadder_of_factorization_eq h hv)
    rw [ladderKernel, if_pos ⟨hmn, h⟩, hP, if_neg hv]

/-- A nonzero entry of Weil's prime kernel lies on the ladder of a prime dividing `mn`. -/
theorem exists_sameLadder_of_weilPrimeKernel_ne_zero {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : weilPrimeKernel m n ≠ 0) :
    ∃ p ∈ (m * n).primeFactors, m ≠ n ∧ ordCompl[p] m = ordCompl[p] n := by
  -- a prime-power ratio puts both orders on one ladder
  have key : ∀ a b : ℕ, a ≠ 0 → b ≠ 0 → a ∣ b → a ≠ b → Λ (b / a) ≠ 0 →
      ∃ p ∈ (a * b).primeFactors, ordCompl[p] a = ordCompl[p] b := by
    intro a b ha hb hab _ hΛ
    have hpp : IsPrimePow (b / a) := by
      by_contra hnp
      exact hΛ (by rw [ArithmeticFunction.vonMangoldt_apply, if_neg hnp])
    obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff _).mp hpp
    have hb' : b = p ^ k * a := by rw [hpk, Nat.div_mul_cancel hab]
    refine ⟨p, ?_, ?_⟩
    · rw [Nat.mem_primeFactors]
      exact ⟨hp, dvd_mul_of_dvd_right (hb' ▸ dvd_mul_of_dvd_left (dvd_pow_self p hk.ne') a) a,
        mul_ne_zero ha hb⟩
    · rw [hb', Nat.ordCompl_self_pow_mul a k hp]
  unfold weilPrimeKernel at h
  split_ifs at h with h1 h2
  · obtain ⟨p, hp, he⟩ := key m n hm hn h1.1 h1.2 (fun h0 => h (by rw [h0, zero_div]))
    exact ⟨p, hp, h1.2, he⟩
  · obtain ⟨p, hp, he⟩ := key n m hn hm h2.1 h2.2 (fun h0 => h (by rw [h0, zero_div]))
    exact ⟨p, by rwa [mul_comm], h2.2.symm, he.symm⟩
  · exact absurd rfl h

/-- **Weil's prime kernel is the sum of the ladder kernels**, one prime per nonzero entry. -/
theorem weilPrimeKernel_eq_sum_ladderKernel {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    weilPrimeKernel m n = ∑ p ∈ (m * n).primeFactors, ladderKernel p m n := by
  by_cases hex : ∃ p ∈ (m * n).primeFactors, m ≠ n ∧ ordCompl[p] m = ordCompl[p] n
  · obtain ⟨p, hp, hmn, he⟩ := hex
    rw [sum_eq_single p, ladderKernel_eq_weilPrimeKernel (Nat.prime_of_mem_primeFactors hp) hm he]
    · intro p' _ hp'
      rw [ladderKernel, if_neg]
      rintro ⟨-, he'⟩
      exact hmn (eq_of_sameLadder_of_sameLadder (Ne.symm hp') hm hn he he')
    · intro h; exact absurd hp h
  · push Not at hex
    rw [sum_eq_zero fun p hp => by
      rw [ladderKernel, if_neg fun h => hex p hp h.1 h.2]]
    by_contra h
    obtain ⟨p, hp, hmn, he⟩ := exists_sameLadder_of_weilPrimeKernel_ne_zero hm hn h
    exact hex p hp hmn he

/-- Away from the primes of `mn` every ladder through `m` and `n` is trivial. -/
theorem ladderKernel_eq_zero_of_not_mem {p m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hp : p ∉ (m * n).primeFactors) : ladderKernel p m n = 0 := by
  rw [ladderKernel, if_neg]
  rintro ⟨hmn, h⟩
  have hvm : m.factorization p = 0 := by
    by_contra hv
    exact hp (Nat.primeFactors_mul hm hn ▸ mem_union_left _
      (Nat.support_factorization m ▸ Finsupp.mem_support_iff.mpr hv))
  have hvn : n.factorization p = 0 := by
    by_contra hv
    exact hp (Nat.primeFactors_mul hm hn ▸ mem_union_right _
      (Nat.support_factorization n ▸ Finsupp.mem_support_iff.mpr hv))
  exact hmn (eq_of_sameLadder_of_factorization_eq h (hvm.trans hvn.symm))

open scoped Classical in
/-- **Tensor form of a ladder kernel**: on `⊕_ℓ ℕ`, `L_p = log p (K_p − 1) ⊗ 1`. -/
theorem ladderKernel_eq_tensor {p m n : ℕ} (hp : p.Prime) (hm : m ≠ 0) (hn : n ≠ 0) :
    ladderKernel p m n =
      if ∀ ℓ, ℓ ≠ p → m.factorization ℓ = n.factorization ℓ then
        Real.log p * (kmsEntry (1 / Real.sqrt p) (m.factorization p) (n.factorization p) -
          if m.factorization p = n.factorization p then 1 else 0)
      else 0 := by
  have hiff : ordCompl[p] m = ordCompl[p] n ↔
      ∀ ℓ, ℓ ≠ p → m.factorization ℓ = n.factorization ℓ := by
    constructor
    · intro h ℓ hℓ
      have := congrArg (fun k => k.factorization ℓ) h
      simpa [Nat.factorization_ordCompl, Finsupp.erase_ne hℓ] using this
    · intro h
      refine Nat.eq_of_factorization_eq (Nat.ordCompl_pos p hm).ne'
        (Nat.ordCompl_pos p hn).ne' fun ℓ => ?_
      rw [Nat.factorization_ordCompl, Nat.factorization_ordCompl]
      rcases eq_or_ne ℓ p with rfl | hℓ
      · simp
      · rw [Finsupp.erase_ne hℓ, Finsupp.erase_ne hℓ]; exact h ℓ hℓ
  by_cases hl : ordCompl[p] m = ordCompl[p] n
  · rw [if_pos (hiff.mp hl)]
    by_cases hv : m.factorization p = n.factorization p
    · have hmn := eq_of_sameLadder_of_factorization_eq hl hv
      subst hmn
      simp [ladderKernel, kmsEntry_self]
    · have hmn : m ≠ n := fun h => hv (h ▸ rfl)
      rw [ladderKernel, if_pos ⟨hmn, hl⟩, if_neg hv, sub_zero]
  · rw [if_neg (fun h => hl (hiff.mpr h)), ladderKernel, if_neg fun h => hl h.2]

/-! ### Quadratic forms -/

variable (S : Finset ℕ) (x : ℕ → ℝ)

/-- The prime form `Σ_{m,n ∈ S} x_m x_n P(m, n)`. -/
def primeForm : ℝ := ∑ m ∈ S, ∑ n ∈ S, x m * x n * weilPrimeKernel m n

/-- The local form at `p`: `Q_p(x) = Σ_{m,n ∈ S} x_m x_n L_p(m, n)`. -/
def localForm (p : ℕ) : ℝ := ∑ m ∈ S, ∑ n ∈ S, x m * x n * ladderKernel p m n

/-- **The prime form is the sum of the local forms** over the primes of `∏ S`. -/
theorem primeForm_eq_sum_localForm (hS : ∀ n ∈ S, n ≠ 0) :
    primeForm S x = ∑ p ∈ (∏ n ∈ S, n).primeFactors, localForm S x p := by
  have hsub : ∀ m ∈ S, ∀ n ∈ S, (m * n).primeFactors ⊆ (∏ k ∈ S, k).primeFactors := by
    intro m hm n hn
    rw [Nat.primeFactors_mul (hS m hm) (hS n hn)]
    exact union_subset
      (Nat.primeFactors_mono (dvd_prod_of_mem _ hm) (prod_ne_zero_iff.mpr hS))
      (Nat.primeFactors_mono (dvd_prod_of_mem _ hn) (prod_ne_zero_iff.mpr hS))
  have hentry : ∀ m ∈ S, ∀ n ∈ S, weilPrimeKernel m n =
      ∑ p ∈ (∏ k ∈ S, k).primeFactors, ladderKernel p m n := by
    intro m hm n hn
    rw [weilPrimeKernel_eq_sum_ladderKernel (hS m hm) (hS n hn)]
    exact sum_subset (hsub m hm n hn) fun p _ hp =>
      ladderKernel_eq_zero_of_not_mem (hS m hm) (hS n hn) hp
  simp only [primeForm, localForm]
  calc ∑ m ∈ S, ∑ n ∈ S, x m * x n * weilPrimeKernel m n
      = ∑ m ∈ S, ∑ n ∈ S, ∑ p ∈ (∏ k ∈ S, k).primeFactors, x m * x n * ladderKernel p m n :=
        sum_congr rfl fun m hm => sum_congr rfl fun n hn => by rw [hentry m hm n hn, mul_sum]
    _ = ∑ m ∈ S, ∑ p ∈ (∏ k ∈ S, k).primeFactors, ∑ n ∈ S, x m * x n * ladderKernel p m n :=
        sum_congr rfl fun m _ => sum_comm
    _ = _ := sum_comm

/-! ### Local bounds -/

/-- A Kac–Murdock–Szegő form over a finite set of exponents is a tower form on an interval. -/
theorem sum_sum_kmsEntry_eq_kmsForm (q : ℝ) (E : Finset ℕ) (y : ℕ → ℝ) {N : ℕ}
    (hE : E ⊆ range N) :
    ∑ a ∈ E, ∑ b ∈ E, y a * y b * kmsEntry q a b =
      kmsForm q N (fun a => if a ∈ E then y a else 0) := by
  rw [kmsForm]
  have h : ∀ f : ℕ → ℝ, ∑ a ∈ range N, (if a ∈ E then f a else 0) = ∑ a ∈ E, f a := by
    intro f
    rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr hE]
  rw [← h]
  refine sum_congr rfl fun a _ => ?_
  rw [← h]
  split_ifs <;> simp_all

theorem sum_sq_ite (E : Finset ℕ) (y : ℕ → ℝ) {N : ℕ} (hE : E ⊆ range N) :
    ∑ a ∈ range N, (if a ∈ E then y a else 0) ^ 2 = ∑ a ∈ E, y a ^ 2 := by
  have : ∀ a ∈ range N, (if a ∈ E then y a else 0) ^ 2 = if a ∈ E then y a ^ 2 else 0 := by
    intro a _; split_ifs <;> simp
  rw [sum_congr rfl this, ← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr hE]

/-- The tower form on a set of orders:
`Σ_{m,n ∈ S, same ladder} x_m x_n q^{|v_p m − v_p n|}`. -/
def towerOnSet (p : ℕ) : ℝ :=
  ∑ m ∈ S, ∑ n ∈ S, if ordCompl[p] m = ordCompl[p] n then
    x m * x n * kmsEntry (1 / Real.sqrt p) (m.factorization p) (n.factorization p) else 0

/-- The local form is `log p` times (the tower form on `S` minus the identity). -/
theorem localForm_eq (p : ℕ) :
    localForm S x p = Real.log p * (towerOnSet S x p - ∑ n ∈ S, x n ^ 2) := by
  simp only [localForm, towerOnSet, ladderKernel, mul_sub, mul_sum]
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun m hm => ?_
  rw [← sum_erase_add _ _ hm, ← sum_erase_add (S) _ hm]
  simp only [ne_eq, not_true_eq_false, false_and, if_false, mul_zero, if_true, kmsEntry_self]
  have : ∀ n ∈ S.erase m, x m * x n * (if ¬m = n ∧ ordCompl[p] m = ordCompl[p] n then
      Real.log p * kmsEntry (1 / Real.sqrt p) (m.factorization p) (n.factorization p) else 0) =
      Real.log p * (if ordCompl[p] m = ordCompl[p] n then x m * x n *
        kmsEntry (1 / Real.sqrt p) (m.factorization p) (n.factorization p) else 0) := by
    intro n hn
    have hmn : ¬ m = n := fun h => (ne_of_mem_erase hn) h.symm
    by_cases hl : ordCompl[p] m = ordCompl[p] n
    · rw [if_pos ⟨hmn, hl⟩, if_pos hl]; ring
    · rw [if_neg (fun h => hl h.2), if_neg hl]; ring
  rw [sum_congr rfl this]
  ring

/-- The tower form on a set of orders is a sum over ladders of interval tower forms. -/
theorem towerOnSet_eq_sum_fibres (p : ℕ) :
    towerOnSet S x p = ∑ c ∈ S.image (fun m => ordCompl[p] m),
      ∑ a ∈ (S.filter fun m => ordCompl[p] m = c).image (fun m => m.factorization p),
      ∑ b ∈ (S.filter fun m => ordCompl[p] m = c).image (fun m => m.factorization p),
        x (c * p ^ a) * x (c * p ^ b) * kmsEntry (1 / Real.sqrt p) a b := by
  rw [towerOnSet]
  -- group the outer sum by ladders
  rw [← sum_fiberwise_of_maps_to (g := fun m => ordCompl[p] m) (t := S.image fun m => ordCompl[p] m)
    (fun m hm => mem_image_of_mem _ hm)]
  refine sum_congr rfl fun c _ => ?_
  -- on a ladder the exponent map is injective
  have hinj : Set.InjOn (fun m : ℕ => m.factorization p)
      ↑(S.filter fun m => ordCompl[p] m = c) := by
    intro m hm n hn hv
    simp only [coe_filter, Set.mem_setOf_eq] at hm hn
    exact eq_of_sameLadder_of_factorization_eq (hm.2.trans hn.2.symm) hv
  have hx : ∀ m ∈ S.filter (fun m => ordCompl[p] m = c), x m = x (c * p ^ m.factorization p) := by
    intro m hm
    rw [(mem_filter.mp hm).2.symm, ← eq_ordCompl_mul_pow]
  rw [sum_image hinj]
  refine sum_congr rfl fun m hm => ?_
  rw [sum_image hinj, ← sum_filter_add_sum_filter_not S (fun n => ordCompl[p] n = c)]
  rw [sum_eq_zero (s := S.filter fun n => ¬ ordCompl[p] n = c) fun n hn => by
    rw [if_neg]; rw [(mem_filter.mp hm).2]; exact fun h => (mem_filter.mp hn).2 h.symm, add_zero]
  refine sum_congr rfl fun n hn => ?_
  rw [if_pos ((mem_filter.mp hm).2.trans (mem_filter.mp hn).2.symm), ← hx m hm, ← hx n hn]

theorem sum_sq_eq_sum_fibres (p : ℕ) :
    ∑ n ∈ S, x n ^ 2 = ∑ c ∈ S.image (fun m => ordCompl[p] m),
      ∑ a ∈ (S.filter fun m => ordCompl[p] m = c).image (fun m => m.factorization p),
        x (c * p ^ a) ^ 2 := by
  rw [← sum_fiberwise_of_maps_to (g := fun m => ordCompl[p] m) (t := S.image fun m => ordCompl[p] m)
    (fun m hm => mem_image_of_mem _ hm)]
  refine sum_congr rfl fun c _ => ?_
  have hinj : Set.InjOn (fun m : ℕ => m.factorization p)
      ↑(S.filter fun m => ordCompl[p] m = c) := by
    intro m hm n hn hv
    simp only [coe_filter, Set.mem_setOf_eq] at hm hn
    exact eq_of_sameLadder_of_factorization_eq (hm.2.trans hn.2.symm) hv
  rw [sum_image hinj]
  refine sum_congr rfl fun m hm => ?_
  rw [(mem_filter.mp hm).2.symm, ← eq_ordCompl_mul_pow]

/-- **Local Hodge index at `p`, lower half**: `−2q log p |x|² ≤ (1 + q) Q_p(x)`, `q = p^{−1/2}`. -/
theorem localForm_lower {p : ℕ} (hp : p.Prime) :
    -(2 * (1 / Real.sqrt p) * Real.log p * ∑ n ∈ S, x n ^ 2) ≤
      (1 + 1 / Real.sqrt p) * localForm S x p := by
  set q := 1 / Real.sqrt p
  have hq0 : 0 ≤ q := inv_sqrt_prime_nonneg p
  have hq1 : q < 1 := inv_sqrt_prime_lt_one hp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  -- the tower form dominates `(1 − q)/(1 + q)` times the mass, fibre by fibre
  have htower : (1 - q) * ∑ n ∈ S, x n ^ 2 ≤ (1 + q) * towerOnSet S x p := by
    rw [towerOnSet_eq_sum_fibres S x p, sum_sq_eq_sum_fibres S x p, mul_sum, mul_sum]
    refine sum_le_sum fun c _ => ?_
    set E := (S.filter fun m => ordCompl[p] m = c).image (fun m => m.factorization p)
    obtain ⟨N, hN⟩ : ∃ N, E ⊆ range N := ⟨E.sup id + 1, fun a ha => mem_range.mpr
      (Nat.lt_succ_of_le (le_sup (f := id) ha))⟩
    rw [sum_sum_kmsEntry_eq_kmsForm q E (fun a => x (c * p ^ a)) hN,
      ← sum_sq_ite E (fun a => x (c * p ^ a)) hN]
    exact kmsForm_lower hq0 hq1.le N _
  rw [localForm_eq]
  nlinarith [mul_le_mul_of_nonneg_left htower hlog]

/-- **Local Hodge index at `p`, upper half**: `(1 − q) Q_p(x) ≤ 2q log p |x|²`, `q = p^{−1/2}`. -/
theorem localForm_upper {p : ℕ} (hp : p.Prime) :
    (1 - 1 / Real.sqrt p) * localForm S x p ≤
      2 * (1 / Real.sqrt p) * Real.log p * ∑ n ∈ S, x n ^ 2 := by
  set q := 1 / Real.sqrt p
  have hq0 : 0 ≤ q := inv_sqrt_prime_nonneg p
  have hq1 : q < 1 := inv_sqrt_prime_lt_one hp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have htower : (1 - q) * towerOnSet S x p ≤ (1 + q) * ∑ n ∈ S, x n ^ 2 := by
    rw [towerOnSet_eq_sum_fibres S x p, sum_sq_eq_sum_fibres S x p, mul_sum, mul_sum]
    refine sum_le_sum fun c _ => ?_
    set E := (S.filter fun m => ordCompl[p] m = c).image (fun m => m.factorization p)
    obtain ⟨N, hN⟩ : ∃ N, E ⊆ range N := ⟨E.sup id + 1, fun a ha => mem_range.mpr
      (Nat.lt_succ_of_le (le_sup (f := id) ha))⟩
    rw [sum_sum_kmsEntry_eq_kmsForm q E (fun a => x (c * p ^ a)) hN,
      ← sum_sq_ite E (fun a => x (c * p ^ a)) hN]
    exact kmsForm_upper hq0 hq1.le N _
  rw [localForm_eq]
  nlinarith [mul_le_mul_of_nonneg_left htower hlog]

end GaloisForLFunctions.ArithmeticIntersectionTheory

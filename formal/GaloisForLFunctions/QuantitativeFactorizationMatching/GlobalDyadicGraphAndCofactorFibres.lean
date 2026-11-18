import GaloisForLFunctions.QuantitativeFactorizationMatching.OreDeficiencyAndCascadeConservation
import GaloisForLFunctions.RHTower.PrimeWindowLogPowerCount
import Mathlib.NumberTheory.Bertrand

/-!
# Global Dyadic `(1 ↔ 2)` Cofactor Graph, Universal Non-Isolation, and Even-Prefix Fibres

Complete structural characterization of the minimal extra moves needed once prescribed-prime and
short-cell restrictions are lifted on dyadic blocks `(X, 2X]`:

1. **Multiplicative sum-freeness and `(1 ↔ 2)` minimality (`dyadic_no_pure_insertion_deletion`)**:
   No distinct `a, b ∈ (X, 2X]` satisfy `a ∣ b` or `b ∣ a`, so every opposite-parity common-cofactor
   exchange `a = c u ↔ b = c v` inside `(X, 2X]` has `ω(u) ≥ 1`, `ω(v) ≥ 1`, and `ω(u) + ω(v) ≥ 3`,
   making `(1 ↔ 2)` (`c p ↔ c q r`) strictly minimal.
2. **Global non-isolation for `X ≥ 6` (`globalDyadicOneTwo_isolatedVertices_empty`) and uniform
   degree growth (`eventually_globalDyadicOneTwo_degree_ge`)**: In the unconstrained dyadic `(1 ↔ 2)`
   graph `GlobalDyadicOneTwoRel` on `(X, 2X]`, **every** squarefree integer has an opposite-parity
   neighbor for all `X ≥ 6`, and for every `D : ℕ`, eventually **every** squarefree integer in
   `(X, 2X]` has at least `D` distinct opposite-parity neighbors uniformly across all cofactors and
   all factor counts `ω(n)`.
3. **Canonical collision-free even-prefix cofactor partition (`evenPrefixCofactor`) and fibre-boundary
   debt (`eventually_evenPrefixFibre_debt_ge`)**: Deleting the largest prime factor (for odd `ω`) or
   the two largest prime factors (for even `ω`) partitions `Q(X)` into pairwise-disjoint complete
   bipartite subgraphs `fibrePos X a × fibreNeg X a ⊆ GlobalDyadicOneTwoRel` with zero target
   collisions across `a`. However, cofactors `a` with `a P⁺(a)² ≥ 2X` have `fibrePos X a = ∅`,
   generating `≥ c X / (log X)³` uncompensated fibre-boundary sources on every large dyadic block
   and proving that sub-`X^θ` matchings in `GlobalDyadicOneTwoRel` must cross cofactor fibres.
-/

open Finset Filter Topology
open RHTower RHTower.PrimeCells
open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.QuantitativeFactorizationMatching

/-! ### 1. Multiplicative sum-freeness of `(X, 2X]` and minimality of `(1 ↔ 2)` exchanges -/

/-- No distinct integers in `(X, 2X]` divide one another, so every opposite-parity common-cofactor
exchange `a = c u ↔ b = c v` in `(X, 2X]` satisfies `1 ≤ ω(u)`, `1 ≤ ω(v)`, and `3 ≤ ω(u) + ω(v)`. -/
theorem dyadic_no_pure_insertion_deletion {X a b : ℕ}
    (ha : a ∈ squarefreeOf (Ioc X (2 * X))) (hb : b ∈ squarefreeOf (Ioc X (2 * X))) :
    (a ≠ b → ¬ a ∣ b ∧ ¬ b ∣ a) ∧
    (∀ {c u v : ℕ}, μ a = -μ b → a = c * u → b = c * v →
      1 ≤ u.primeFactors.card ∧ 1 ≤ v.primeFactors.card ∧
      3 ≤ u.primeFactors.card + v.primeFactors.card) := by
  obtain ⟨haIoc, hsq_a⟩ := mem_filter.mp ha
  obtain ⟨hbIoc, hsq_b⟩ := mem_filter.mp hb
  obtain ⟨haX, ha2X⟩ := mem_Ioc.mp haIoc
  obtain ⟨hbX, hb2X⟩ := mem_Ioc.mp hbIoc
  have hnot_dvd : ∀ {x y : ℕ}, X < x → X < y → y ≤ 2 * X → x ≠ y → ¬ x ∣ y := by
    rintro x y hxX hyX hy2X hne ⟨k, rfl⟩
    rcases eq_or_ne k 0 with rfl | hk0
    · rw [mul_zero] at hyX; omega
    rcases eq_or_ne k 1 with rfl | hk1
    · exact hne (mul_one x).symm
    · have hmul : (X + 1) * 2 ≤ x * k := Nat.mul_le_mul hxX (by omega)
      omega
  refine ⟨fun hne => ⟨hnot_dvd haX hbX hb2X hne, hnot_dvd hbX haX ha2X hne.symm⟩,
    fun {c u v} hμ hac hbc => ?_⟩
  have hab_ne : a ≠ b := by
    intro heq; subst heq
    rcases moebius_eq_one_or_neg_one_of_squarefree hsq_a with h1 | h1 <;> omega
  have hu_ge2 : 2 ≤ u := by
    rcases eq_or_ne u 0 with rfl | hu0
    · rw [mul_zero] at hac; omega
    rcases eq_or_ne u 1 with rfl | hu1
    · rw [mul_one] at hac; subst hac
      exact False.elim (hnot_dvd haX hbX hb2X hab_ne ⟨v, hbc⟩)
    · omega
  have hv_ge2 : 2 ≤ v := by
    rcases eq_or_ne v 0 with rfl | hv0
    · rw [mul_zero] at hbc; omega
    rcases eq_or_ne v 1 with rfl | hv1
    · rw [mul_one] at hbc; subst hbc
      exact False.elim (hnot_dvd hbX haX ha2X hab_ne.symm ⟨u, hac⟩)
    · omega
  have hu_pf : 1 ≤ u.primeFactors.card :=
    card_pos.mpr ⟨u.minFac, Nat.mem_primeFactors.mpr
      ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd u, by omega⟩⟩
  have hv_pf : 1 ≤ v.primeFactors.card :=
    card_pos.mpr ⟨v.minFac, Nat.mem_primeFactors.mpr
      ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd v, by omega⟩⟩
  have hcard_ne : u.primeFactors.card ≠ v.primeFactors.card := by
    intro hcard_eq
    obtain ⟨hcop_cu, _, hsq_u⟩ := Nat.squarefree_mul_iff.mp (hac ▸ hsq_a)
    obtain ⟨hcop_cv, _, hsq_v⟩ := Nat.squarefree_mul_iff.mp (hbc ▸ hsq_b)
    have hμa : μ a = μ c * (-1 : ℤ) ^ u.primeFactors.card := by
      rw [hac, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_cu,
        moebius_eq_neg_one_pow_omega hsq_u]
    have hμb : μ b = μ c * (-1 : ℤ) ^ v.primeFactors.card := by
      rw [hbc, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_cv,
        moebius_eq_neg_one_pow_omega hsq_v]
    rw [hcard_eq, ← hμb] at hμa
    rcases moebius_eq_one_or_neg_one_of_squarefree hsq_b with h1 | h1 <;> omega
  exact ⟨hu_pf, hv_pf, by omega⟩

/-- The global unconstrained dyadic `(1 ↔ 2)` common-cofactor graph relation: squarefree integers
`a, b` of opposite Möbius sign linked as `c * p` and `c * (q * r)` for an unrestricted common
cofactor `c` and primes `p` and `q < r`. -/
def GlobalDyadicOneTwoRel (a b : ℕ) : Prop :=
  Squarefree a ∧ Squarefree b ∧ μ a = -μ b ∧
    ∃ c p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ q < r ∧
      ((a = c * p ∧ b = c * (q * r)) ∨ (b = c * p ∧ a = c * (q * r)))

theorem GlobalDyadicOneTwoRel.symm {a b : ℕ} (h : GlobalDyadicOneTwoRel a b) :
    GlobalDyadicOneTwoRel b a := by
  obtain ⟨hsq_a, hsq_b, hμ, c, p, q, r, hp, hq, hr, hqr, hor⟩ := h
  exact ⟨hsq_b, hsq_a, by omega, c, p, q, r, hp, hq, hr, hqr, hor.symm⟩

/-! ### 2. Peeling largest primes, universal non-isolation (`X ≥ 6`), and uniform degree growth -/

private theorem peel_one_maxPrime {n : ℕ} (hsq : Squarefree n) (h1 : 1 ≤ n.primeFactors.card) :
    let r := n.primeFactors.max' (card_pos.mp h1)
    let c := n / r
    r.Prime ∧ Squarefree c ∧ n = c * r ∧ c.primeFactors = n.primeFactors.erase r ∧
      c.primeFactors.card + 1 = n.primeFactors.card ∧
      (∀ s ∈ c.primeFactors, s < r) := by
  dsimp only
  have hne : n.primeFactors.Nonempty := card_pos.mp h1
  obtain ⟨r, hr_def⟩ : ∃ r : ℕ, r = n.primeFactors.max' hne := ⟨_, rfl⟩
  rw [← hr_def]
  have hr_mem : r ∈ n.primeFactors := hr_def ▸ max'_mem _ hne
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr_mem
  have hdvd : r ∣ n := Nat.dvd_of_mem_primeFactors hr_mem
  obtain ⟨c, hc_def⟩ : ∃ c : ℕ, c = n / r := ⟨_, rfl⟩
  rw [← hc_def]
  have hmul : c * r = n := hc_def ▸ Nat.div_mul_cancel hdvd
  obtain ⟨hcop_cr, hsq_c, _⟩ := Nat.squarefree_mul_iff.mp (hmul ▸ hsq)
  have hc_pos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | hpos
    · rw [zero_mul] at hmul; exact False.elim (hsq.ne_zero hmul.symm)
    · exact hpos
  have hr_notMem : r ∉ c.primeFactors := fun hmem =>
    hrp.not_dvd_one (hcop_cr.symm.gcd_eq_one ▸
      Nat.dvd_gcd dvd_rfl (Nat.dvd_of_mem_primeFactors hmem))
  have hpf_n : n.primeFactors = insert r c.primeFactors := by
    rw [← hmul, Nat.primeFactors_mul hc_pos.ne' hrp.ne_zero, hrp.primeFactors, union_comm,
      singleton_union]
  have hpf_c : c.primeFactors = n.primeFactors.erase r := by
    rw [hpf_n, erase_insert hr_notMem]
  have hcard : c.primeFactors.card + 1 = n.primeFactors.card := by
    rw [hpf_n, card_insert_of_notMem hr_notMem]
  refine ⟨hrp, hsq_c, hmul.symm, hpf_c, hcard, fun s hs => ?_⟩
  have hs_n : s ∈ n.primeFactors := by rw [hpf_n]; exact mem_insert_of_mem hs
  have hs_le : s ≤ r := hr_def ▸ le_max' _ s hs_n
  have hs_ne : s ≠ r := fun heq => hr_notMem (heq ▸ hs)
  omega

private theorem peel_two_maxPrimes {X n : ℕ} (hsq : Squarefree n) (h2 : 2 ≤ n.primeFactors.card) :
    ∃ c q r : ℕ, q.Prime ∧ r.Prime ∧ q < r ∧ Squarefree c ∧ 0 < c ∧
      n = c * (q * r) ∧ c.primeFactors = (n.primeFactors.erase r).erase q ∧
      c.primeFactors.card + 2 = n.primeFactors.card ∧
      (∀ s ∈ c.primeFactors, s < q) ∧
      (∀ s ∈ n.primeFactors, s ≤ r) ∧
      (∀ p : ℕ, p.Prime → n ≤ 2 * X → X / c < p → Nat.Coprime c p) := by
  have h1_card : 1 ≤ n.primeFactors.card := by omega
  have h1 := peel_one_maxPrime hsq h1_card
  dsimp only at h1
  obtain ⟨r, hr_def⟩ : ∃ r : ℕ, r = n.primeFactors.max' (card_pos.mp h1_card) := ⟨_, rfl⟩
  rw [← hr_def] at h1
  obtain ⟨m, hm_def⟩ : ∃ m : ℕ, m = n / r := ⟨_, rfl⟩
  rw [← hm_def] at h1
  obtain ⟨hrp, hsq_m, hnm, hpf_m, hcard_m, hlt_r⟩ := h1
  have hm1 : 1 ≤ m.primeFactors.card := by omega
  have h2_step := peel_one_maxPrime hsq_m hm1
  dsimp only at h2_step
  obtain ⟨q, hq_def⟩ : ∃ q : ℕ, q = m.primeFactors.max' (card_pos.mp hm1) := ⟨_, rfl⟩
  rw [← hq_def] at h2_step
  obtain ⟨c, hc_def⟩ : ∃ c : ℕ, c = m / q := ⟨_, rfl⟩
  rw [← hc_def] at h2_step
  obtain ⟨hqp, hsq_c, hmc, hpf_c, hcard_c, hlt_q⟩ := h2_step
  have hq_mem_m : q ∈ m.primeFactors := hq_def ▸ max'_mem _ (card_pos.mp hm1)
  have hqr : q < r := hlt_r q hq_mem_m
  have hmul : n = c * (q * r) := by rw [hnm, hmc, mul_assoc]
  have hc_pos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | hpos
    · rw [zero_mul] at hmul; exact False.elim (hsq.ne_zero hmul)
    · exact hpos
  have hall_le_r : ∀ s ∈ n.primeFactors, s ≤ r := fun s hs => hr_def ▸ le_max' _ s hs
  refine ⟨c, q, r, hqp, hrp, hqr, hsq_c, hc_pos, hmul, by rw [hpf_c, hpf_m], by omega, hlt_q,
    hall_le_r, fun p hp hn2X hXcp => ?_⟩
  refine Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr fun hdvd => ?_)
  have hp_mem : p ∈ c.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hdvd, hc_pos.ne'⟩
  have hpq : p + 1 ≤ q := hlt_q p hp_mem
  have hr2 : 2 ≤ r := hrp.two_le
  have h2_p1_qr : 2 * (p + 1) ≤ q * r := by nlinarith
  have hmul_2X : 2 * ((p + 1) * c) ≤ 2 * X := by
    calc 2 * ((p + 1) * c) = c * (2 * (p + 1)) := by ring
      _ ≤ c * (q * r) := Nat.mul_le_mul_left c h2_p1_qr
      _ = n := hmul.symm
      _ ≤ 2 * X := hn2X
  have hp1_le_Xc : p + 1 ≤ X / c := (Nat.le_div_iff_mul_le hc_pos).mpr (by omega)
  omega

/-- **Complete global non-isolation (`X ≥ 6`)**: For every `X ≥ 6`, **every** squarefree integer in
`(X, 2X]` has an opposite-parity neighbor in `(X, 2X]` under `GlobalDyadicOneTwoRel`
(`isolatedVertices GlobalDyadicOneTwoRel (Ioc X (2 * X)) = ∅`). -/
theorem globalDyadicOneTwo_isolatedVertices_empty {X : ℕ} (hX : 6 ≤ X) :
    isolatedVertices GlobalDyadicOneTwoRel (Ioc X (2 * X)) = ∅ := by
  -- Construct an opposite-parity neighbor `m ∈ squarefreeOf (Ioc X (2 * X))` for any `n`
  have hex_nb : ∀ n ∈ squarefreeOf (Ioc X (2 * X)),
      ∃ m ∈ squarefreeOf (Ioc X (2 * X)), GlobalDyadicOneTwoRel n m := by
    intro n hn
    obtain ⟨hnIoc, hsq_n⟩ := mem_filter.mp hn
    obtain ⟨hnX, hn2X⟩ := mem_Ioc.mp hnIoc
    have hn_gt1 : 1 < n := by omega
    have hcard_pos : 1 ≤ n.primeFactors.card :=
      card_pos.mpr ⟨n.minFac, Nat.mem_primeFactors.mpr
        ⟨Nat.minFac_prime hn_gt1.ne', Nat.minFac_dvd n, by omega⟩⟩
    rcases eq_or_lt_of_le hcard_pos with hcard1 | hcard_ge2
    · -- `ω(n) = 1`: `n` is prime; pair `n = 1 * n` with `1 * (2 * r)` via Bertrand on `X / 2`
      obtain ⟨p, hp⟩ := card_eq_one.mp hcard1.symm
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hp]; simp)
      have hnp : n = p := by
        rw [← Nat.prod_primeFactors_of_squarefree hsq_n, hp, prod_singleton]
      rw [hnp] at hsq_n ⊢
      obtain ⟨r, hrp, hr_gt, hr_le⟩ :=
        Nat.exists_prime_lt_and_le_two_mul (X / 2) (by omega)
      have h2r_gt : 2 < r := by omega
      have hcop_2r : Nat.Coprime 2 r := (Nat.coprime_primes Nat.prime_two hrp).mpr (by omega)
      have hsq_2r : Squarefree (2 * r) :=
        Nat.squarefree_mul_iff.mpr ⟨hcop_2r, Irreducible.squarefree Nat.prime_two,
          Irreducible.squarefree hrp⟩
      have h2r_Ioc : 2 * r ∈ Ioc X (2 * X) := by
        refine mem_Ioc.mpr ⟨by omega, ?_⟩
        calc 2 * r ≤ 2 * (2 * (X / 2)) := Nat.mul_le_mul_left 2 hr_le
          _ = 2 * (2 * (X / 2)) := rfl
          _ ≤ 2 * X := Nat.mul_le_mul_left 2 (Nat.mul_div_le X 2)
      have hμ_p : μ p = -1 := ArithmeticFunction.moebius_apply_prime hpp
      have hμ_2r : μ (2 * r) = 1 := by
        rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_2r,
          ArithmeticFunction.moebius_apply_prime Nat.prime_two,
          ArithmeticFunction.moebius_apply_prime hrp]
        norm_num
      refine ⟨2 * r, mem_filter.mpr ⟨h2r_Ioc, hsq_2r⟩,
        hsq_n, hsq_2r, by omega, 1, p, 2, r, hpp, Nat.prime_two, hrp, h2r_gt,
        Or.inl ⟨by simp, by simp⟩⟩
    · -- `ω(n) ≥ 2`: peel the two largest primes `q < r` (`n = c * (q * r)`) and apply Bertrand on `X / c`
      obtain ⟨c, q, r, hqp, hrp, hqr, hsq_c, hc_pos, hmul, _, hcard_c, _, _, hcop_fn⟩ :=
        peel_two_maxPrimes (X := X) hsq_n hcard_ge2
      have hqr_ge6 : 6 ≤ q * r := by
        have hq2 := hqp.two_le
        have hr3 : 3 ≤ r := by omega
        nlinarith
      have hXc_ge3 : 3 ≤ X / c := by
        rw [Nat.le_div_iff_mul_le hc_pos]
        have : 6 * c ≤ 2 * X := by
          calc 6 * c = c * 6 := mul_comm _ _
            _ ≤ c * (q * r) := Nat.mul_le_mul_left c hqr_ge6
            _ = n := hmul.symm
            _ ≤ 2 * X := hn2X
        omega
      obtain ⟨p, hpp, hp_gt, hp_le⟩ :=
        Nat.exists_prime_lt_and_le_two_mul (X / c) (by omega)
      have hcop_cp : Nat.Coprime c p := hcop_fn p hpp hn2X hp_gt
      have hsq_cp : Squarefree (c * p) :=
        Nat.squarefree_mul_iff.mpr ⟨hcop_cp, hsq_c, Irreducible.squarefree hpp⟩
      have hcp_Ioc : c * p ∈ Ioc X (2 * X) := by
        refine mem_Ioc.mpr ⟨?_, ?_⟩
        · rw [Nat.div_lt_iff_lt_mul hc_pos, mul_comm] at hp_gt
          exact hp_gt
        · calc c * p ≤ c * (2 * (X / c)) := Nat.mul_le_mul_left c hp_le
            _ = 2 * (c * (X / c)) := by ring
            _ ≤ 2 * X := Nat.mul_le_mul_left 2 (Nat.mul_div_le X c)
      have hp_not_c : p ∉ c.primeFactors := fun hmem =>
        hpp.not_dvd_one (hcop_cp.gcd_eq_one ▸
          Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hmem) dvd_rfl)
      have hcard_cp : (c * p).primeFactors.card = c.primeFactors.card + 1 := by
        rw [Nat.primeFactors_mul hc_pos.ne' hpp.ne_zero, hpp.primeFactors, union_comm,
          singleton_union, card_insert_of_notMem hp_not_c]
      have hμ_opp : μ n = -μ (c * p) := by
        rw [moebius_eq_neg_one_pow_omega hsq_n, moebius_eq_neg_one_pow_omega hsq_cp,
          ← hcard_c, hcard_cp,
          show c.primeFactors.card + 2 = (c.primeFactors.card + 1) + 1 by omega,
          pow_succ, mul_neg_one]
      refine ⟨c * p, mem_filter.mpr ⟨hcp_Ioc, hsq_cp⟩,
        hsq_n, hsq_cp, hμ_opp, c, p, q, r, hpp, hqp, hrp, hqr, Or.inr ⟨rfl, hmul⟩⟩
  classical
  refine eq_empty_iff_forall_notMem.mpr fun n hn => ?_
  rw [isolatedVertices, mem_union] at hn
  rcases hn with hnP | hnN
  · obtain ⟨hn_pos, hiso⟩ := mem_filter.mp hnP
    have hn_sq : n ∈ squarefreeOf (Ioc X (2 * X)) := by
      rw [squarefreeOf_eq_posParity_union_negParity]; exact mem_union_left _ hn_pos
    obtain ⟨m, hm_sq, hrel⟩ := hex_nb n hn_sq
    have hm_neg : m ∈ negParity (Ioc X (2 * X)) := by
      have hμn := (mem_filter.mp hn_pos).2
      have hμm : μ m = -1 := by have := hrel.2.2.1; omega
      exact mem_filter.mpr ⟨(mem_filter.mp hm_sq).1, hμm⟩
    exact hiso m hm_neg hrel
  · obtain ⟨hn_neg, hiso⟩ := mem_filter.mp hnN
    have hn_sq : n ∈ squarefreeOf (Ioc X (2 * X)) := by
      rw [squarefreeOf_eq_posParity_union_negParity]; exact mem_union_right _ hn_neg
    obtain ⟨m, hm_sq, hrel⟩ := hex_nb n hn_sq
    have hm_pos : m ∈ posParity (Ioc X (2 * X)) := by
      have hμn := (mem_filter.mp hn_neg).2
      have hμm : μ m = 1 := by have := hrel.2.2.1; omega
      exact mem_filter.mpr ⟨(mem_filter.mp hm_sq).1, hμm⟩
    exact hiso m hm_pos hrel.symm

open scoped Classical in
/-- **Uniform arbitrary-`D` degree growth**: For every `D : ℕ`, eventually on `(X, 2X]` **every**
squarefree integer has at least `D` distinct opposite-parity `GlobalDyadicOneTwoRel`-neighbors,
uniformly across all cofactors and all factor counts `ω(n)`. -/
theorem eventually_globalDyadicOneTwo_degree_ge (D : ℕ) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∀ n ∈ squarefreeOf (Ioc X (2 * X)),
        D ≤ ((squarefreeOf (Ioc X (2 * X))).filter (GlobalDyadicOneTwoRel n ·)).card := by
  obtain ⟨C_θ, hC_θ, T_θ, hT_θ, hθ⟩ := exists_abs_theta_sub_le 1
  -- Find threshold `U_D` such that every window `(u, 2 u]` with `u ≥ U_D` has `≥ D + 2` primes
  have hev_u : ∀ᶠ u : ℝ in atTop,
      T_θ ≤ u ∧ 6 ≤ u ∧ 8 * C_θ ≤ Real.log u ∧
      (6 * ((D : ℝ) + 2)) ^ 2 ≤ u ∧ 4 ≤ u ^ (1 / 2 : ℝ) :=
    (eventually_ge_atTop _).and ((eventually_ge_atTop 6).and
      ((Real.tendsto_log_atTop.eventually_ge_atTop _).and
        ((eventually_ge_atTop _).and
          ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop 4))))
  obtain ⟨U_D, hU_D⟩ := eventually_atTop.mp hev_u
  have hwin_D : ∀ u : ℝ, max U_D 6 ≤ u → D + 2 ≤ (windowPrimes u (2 * u)).card := by
    intro u hu
    obtain ⟨hTu, hu6, hCu, hDu, hu_half⟩ := hU_D u ((le_max_left _ _).trans hu)
    have hu0 : 0 < u := by linarith
    have hab : u ≤ 2 * u := by linarith
    have hlogu : 0 < Real.log u := Real.log_pos (by linarith)
    have hlog2u : 0 < Real.log (2 * u) := Real.log_pos (by linarith)
    have hinc := abs_theta_increment_le hC_θ.le hT_θ hθ hTu hab
    have herr : 2 * C_θ * (2 * u) / Real.log u ^ (1 : ℕ) ≤ u / 2 := by
      rw [pow_one, div_le_iff₀ hlogu]; nlinarith
    have hθ_ge : u / 2 ≤ Chebyshev.theta (2 * u) - Chebyshev.theta u := by
      have := (abs_le.mp hinc).1; linarith
    have hcard := theta_sub_le_card_mul_log hu0.le hab
    -- Bound `Real.log (2 * u) ≤ 3 * u ^ (1 / 2)` via `t ≤ exp t`
    have h_uhalf_pos : 0 < u ^ (1 / 2 : ℝ) := by positivity
    have hexp1 := Real.pow_div_factorial_le_exp (Real.log (u ^ (1 / 2 : ℝ)))
      (by rw [Real.log_rpow hu0]; positivity) 1
    rw [Real.exp_log h_uhalf_pos, pow_one, Nat.factorial_one, Nat.cast_one, div_one,
      Real.log_rpow hu0] at hexp1
    have hlog2u_le : Real.log (2 * u) ≤ 3 * u ^ (1 / 2 : ℝ) := by
      rw [Real.log_mul (by norm_num) hu0.ne']
      have : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      linarith
    have h_usq : u ^ (1 / 2 : ℝ) * u ^ (1 / 2 : ℝ) = u := by
      rw [← Real.rpow_add hu0]; norm_num
    have hD_sqrt : 6 * ((D : ℝ) + 2) ≤ u ^ (1 / 2 : ℝ) := by
      have hsq : (6 * ((D : ℝ) + 2)) ^ 2 ≤ (u ^ (1 / 2 : ℝ)) ^ 2 := by
        conv_rhs => rw [sq, h_usq]
        exact hDu
      exact (pow_le_pow_iff_left₀ (by positivity) h_uhalf_pos.le two_ne_zero).mp hsq
    have hgoal_r : ((D : ℝ) + 2) * Real.log (2 * u) ≤ u / 2 := by
      calc ((D : ℝ) + 2) * Real.log (2 * u)
          ≤ ((D : ℝ) + 2) * (3 * u ^ (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hlog2u_le (by positivity)
        _ = (6 * ((D : ℝ) + 2)) * u ^ (1 / 2 : ℝ) / 2 := by ring
        _ ≤ (u ^ (1 / 2 : ℝ) * u ^ (1 / 2 : ℝ)) / 2 := by gcongr
        _ = u / 2 := by rw [h_usq]
    have hle_c : ((D : ℝ) + 2) ≤ ((windowPrimes u (2 * u)).card : ℝ) :=
      le_of_mul_le_mul_right (hgoal_r.trans (hθ_ge.trans hcard)) hlog2u
    exact_mod_cast hle_c
  -- Uniform primorial compactness cutoff `P_bound = ∏_{p ≤ ⌈2 * max U_D 6⌉₊} p`
  obtain ⟨B_cut, hB_def⟩ : ∃ B_cut : ℕ, B_cut = ⌈2 * max U_D 6⌉₊ := ⟨_, rfl⟩
  obtain ⟨P_bound, hP_def⟩ : ∃ P_bound : ℕ, P_bound = ∏ p ∈ Nat.primesLE B_cut, p := ⟨_, rfl⟩
  refine ⟨max P_bound B_cut + 6, fun X hX n hn => ?_⟩
  classical
  obtain ⟨hnIoc, hsq_n⟩ := mem_filter.mp hn
  obtain ⟨hnX, hn2X⟩ := mem_Ioc.mp hnIoc
  have hn_gt1 : 1 < n := by omega
  have hcard_pos : 1 ≤ n.primeFactors.card :=
    card_pos.mpr ⟨n.minFac, Nat.mem_primeFactors.mpr
      ⟨Nat.minFac_prime hn_gt1.ne', Nat.minFac_dvd n, by omega⟩⟩
  rcases eq_or_lt_of_le hcard_pos with hcard1 | hcard_ge2
  · -- `ω(n) = 1`: `n = p`, inject `windowPrimes (X / 2) X` via `r ↦ 2 * r`
    obtain ⟨p, hp⟩ := card_eq_one.mp hcard1.symm
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hp]; simp)
    have hnp : n = p := by
      rw [← Nat.prod_primeFactors_of_squarefree hsq_n, hp, prod_singleton]
    rw [hnp] at hsq_n ⊢
    have hX_ge_2U : 2 * max U_D 6 ≤ (X : ℝ) := by
      calc 2 * max U_D 6 ≤ B_cut := by rw [hB_def]; exact Nat.le_ceil _
        _ ≤ X := by exact_mod_cast (show B_cut ≤ X by omega)
    let W := windowPrimes ((X : ℝ) / 2) (2 * ((X : ℝ) / 2))
    have hW_card : D + 2 ≤ W.card := hwin_D ((X : ℝ) / 2) (by linarith)
    have himg_sub : W.image (2 * ·) ⊆
        (squarefreeOf (Ioc X (2 * X))).filter (GlobalDyadicOneTwoRel p ·) := by
      intro m hm
      obtain ⟨r, hrW, rfl⟩ := mem_image.mp hm
      obtain ⟨hrp, hr_gt, hr_le⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hrW
      have h2r_gt : 2 < r := by
        have : (6 : ℝ) ≤ (X : ℝ) / 2 := by linarith [le_max_right U_D 6]
        have : (2 : ℝ) < r := by linarith
        exact_mod_cast this
      have hcop : Nat.Coprime 2 r := (Nat.coprime_primes Nat.prime_two hrp).mpr (by omega)
      have hsq_2r : Squarefree (2 * r) :=
        Nat.squarefree_mul_iff.mpr ⟨hcop, Irreducible.squarefree Nat.prime_two,
          Irreducible.squarefree hrp⟩
      have hIoc_2r : 2 * r ∈ Ioc X (2 * X) := by
        refine mem_Ioc.mpr ⟨?_, ?_⟩
        · exact_mod_cast (show (X : ℝ) < (2 * r : ℕ) by push_cast; linarith)
        · exact_mod_cast (show ((2 * r : ℕ) : ℝ) ≤ (2 * X : ℕ) by push_cast; linarith)
      have hμ_p : μ p = -1 := ArithmeticFunction.moebius_apply_prime hpp
      have hμ_2r : μ (2 * r) = 1 := by
        rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
          ArithmeticFunction.moebius_apply_prime Nat.prime_two,
          ArithmeticFunction.moebius_apply_prime hrp]
        norm_num
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨hIoc_2r, hsq_2r⟩,
        hsq_n, hsq_2r, by omega, 1, p, 2, r, hpp, Nat.prime_two, hrp, h2r_gt,
        Or.inl ⟨by simp, by simp⟩⟩
    have hinj : Set.InjOn (2 * ·) ↑W := fun r₁ _ r₂ _ h =>
      Nat.eq_of_mul_eq_mul_left (by norm_num) h
    have hcard_img := card_image_of_injOn hinj
    have hle := card_le_card himg_sub
    omega
  · -- `ω(n) ≥ 2`: `n = c * (q * r)`, primorial compactness forces `(X : ℝ) / c ≥ max U_D 6`
    obtain ⟨c, q, r, hqp, hrp, hqr, hsq_c, hc_pos, hmul, _, hcard_c, _, hall_le_r, hcop_fn⟩ :=
      peel_two_maxPrimes (X := X) hsq_n hcard_ge2
    have hc_r_pos : (0 : ℝ) < c := by exact_mod_cast hc_pos
    have hXc_ge : max U_D 6 ≤ (X : ℝ) / c := by
      by_contra hlt
      push Not at hlt
      rw [div_lt_iff₀ hc_r_pos] at hlt
      have hqr_lt : (q * r : ℝ) < 2 * max U_D 6 := by
        have h1 : (c : ℝ) * (q * r) ≤ 2 * X := by
          have : c * (q * r) ≤ 2 * X := hmul ▸ hn2X
          exact_mod_cast this
        have h2 : 2 * (X : ℝ) < 2 * (max U_D 6 * c) := by linarith
        nlinarith
      have hr_le_B : r ≤ B_cut := by
        have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hqp.two_le
        have hr_lt : (r : ℝ) ≤ 2 * max U_D 6 := by nlinarith
        have hB_ge : 2 * max U_D 6 ≤ (B_cut : ℝ) := by rw [hB_def]; exact Nat.le_ceil _
        exact_mod_cast hr_lt.trans hB_ge
      have hn_pf_sub : n.primeFactors ⊆ Nat.primesLE B_cut := by
        intro s hs
        have hsp : s.Prime := Nat.prime_of_mem_primeFactors hs
        exact Nat.mem_primesLE.mpr ⟨(hall_le_r s hs).trans hr_le_B, hsp⟩
      have hP_pos : 0 < P_bound := by
        rw [hP_def]
        exact prod_pos fun p hp => (Nat.mem_primesLE.mp hp).2.pos
      have hn_le_P : n ≤ P_bound := by
        rw [← Nat.prod_primeFactors_of_squarefree hsq_n, hP_def]
        exact Nat.le_of_dvd (hP_def ▸ hP_pos)
          (prod_dvd_prod_of_subset n.primeFactors (Nat.primesLE B_cut) id hn_pf_sub)
      omega
    let W := windowPrimes ((X : ℝ) / c) (2 * ((X : ℝ) / c))
    have hW_card : D + 2 ≤ W.card := hwin_D ((X : ℝ) / c) hXc_ge
    have himg_sub : W.image (c * ·) ⊆
        (squarefreeOf (Ioc X (2 * X))).filter (GlobalDyadicOneTwoRel n ·) := by
      intro m hm
      obtain ⟨p, hpW, rfl⟩ := mem_image.mp hm
      obtain ⟨hpp, hp_gt, hp_le⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hpW
      have hp_gt_nat : X / c < p := by
        have hfl_le : ((X / c : ℕ) : ℝ) ≤ (X : ℝ) / c := Nat.cast_div_le
        exact_mod_cast hfl_le.trans_lt hp_gt
      have hcop_cp : Nat.Coprime c p := hcop_fn p hpp hn2X hp_gt_nat
      have hsq_cp : Squarefree (c * p) :=
        Nat.squarefree_mul_iff.mpr ⟨hcop_cp, hsq_c, Irreducible.squarefree hpp⟩
      have hcp_Ioc : c * p ∈ Ioc X (2 * X) := by
        rw [div_lt_iff₀ hc_r_pos] at hp_gt
        rw [mul_div_assoc', le_div_iff₀ hc_r_pos] at hp_le
        refine mem_Ioc.mpr ⟨?_, ?_⟩
        · exact_mod_cast (show (X : ℝ) < (c * p : ℕ) by push_cast; linarith)
        · exact_mod_cast (show ((c * p : ℕ) : ℝ) ≤ (2 * X : ℕ) by push_cast; linarith)
      have hp_not_c : p ∉ c.primeFactors := fun hmem =>
        hpp.not_dvd_one (hcop_cp.gcd_eq_one ▸
          Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hmem) dvd_rfl)
      have hcard_cp : (c * p).primeFactors.card = c.primeFactors.card + 1 := by
        rw [Nat.primeFactors_mul hc_pos.ne' hpp.ne_zero, hpp.primeFactors, union_comm,
          singleton_union, card_insert_of_notMem hp_not_c]
      have hμ_opp : μ n = -μ (c * p) := by
        rw [moebius_eq_neg_one_pow_omega hsq_n, moebius_eq_neg_one_pow_omega hsq_cp,
          ← hcard_c, hcard_cp,
          show c.primeFactors.card + 2 = (c.primeFactors.card + 1) + 1 by omega,
          pow_succ, mul_neg_one]
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨hcp_Ioc, hsq_cp⟩,
        hsq_n, hsq_cp, hμ_opp, c, p, q, r, hpp, hqp, hrp, hqr, Or.inr ⟨rfl, hmul⟩⟩
    have hinj : Set.InjOn (c * ·) ↑W := fun p₁ _ p₂ _ h =>
      Nat.eq_of_mul_eq_mul_left hc_pos h
    have hcard_img := card_image_of_injOn hinj
    have hle := card_le_card himg_sub
    omega

/-! ### 3. Canonical collision-free even-prefix cofactor fibres and `≫ X / (log X)³` boundary debt -/

/-- The canonical even-`ω` prefix cofactor of a squarefree integer `n > 1`: deletes the largest
prime factor when `ω(n)` is odd, or the two largest prime factors when `ω(n)` is even. -/
noncomputable def evenPrefixCofactor (n : ℕ) : ℕ :=
  if hne : n.primeFactors.Nonempty then
    let r := n.primeFactors.max' hne
    if Even n.primeFactors.card then
      if hne2 : (n.primeFactors.erase r).Nonempty then
        n / ((n.primeFactors.erase r).max' hne2 * r)
      else 1
    else n / r
  else 1

/-- Positive-Möbius (`ω` even) fibre over even-prefix cofactor `a` in `(X, 2X]`. -/
noncomputable def fibrePos (X a : ℕ) : Finset ℕ := by
  classical exact (posParity (Ioc X (2 * X))).filter (evenPrefixCofactor · = a)

/-- Negative-Möbius (`ω` odd) fibre over even-prefix cofactor `a` in `(X, 2X]`. -/
noncomputable def fibreNeg (X a : ℕ) : Finset ℕ := by
  classical exact (negParity (Ioc X (2 * X))).filter (evenPrefixCofactor · = a)

theorem mem_fibrePos_structure {X a m : ℕ} (hX1 : 1 ≤ X) (hm : m ∈ fibrePos X a) :
    Squarefree a ∧ Even a.primeFactors.card ∧
      ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ q < r ∧ m = a * (q * r) ∧
        (∀ s ∈ a.primeFactors, s < q) := by
  classical
  obtain ⟨hm_pos, h_eq⟩ := mem_filter.mp hm
  have hm_sq_mem : m ∈ squarefreeOf (Ioc X (2 * X)) := by
    rw [squarefreeOf_eq_posParity_union_negParity]; exact mem_union_left _ hm_pos
  obtain ⟨hmIoc, hsq_m⟩ := mem_filter.mp hm_sq_mem
  have hm_gt1 : 1 < m := lt_of_le_of_lt hX1 (mem_Ioc.mp hmIoc).1
  have hμm : μ m = 1 := (mem_filter.mp hm_pos).2
  have heven : Even m.primeFactors.card := by
    rcases Nat.even_or_odd m.primeFactors.card with he | ho
    · exact he
    · have := moebius_eq_neg_one_pow_omega hsq_m
      rw [ho.neg_one_pow] at this; omega
  have hne1 : m.primeFactors.Nonempty :=
    ⟨m.minFac, Nat.mem_primeFactors.mpr
      ⟨Nat.minFac_prime hm_gt1.ne', Nat.minFac_dvd m, by omega⟩⟩
  have hcard_ge2 : 2 ≤ m.primeFactors.card := by
    obtain ⟨k, hk⟩ := heven
    have hpos := card_pos.mpr hne1
    omega
  -- Match `evenPrefixCofactor m` with `peel_one_maxPrime` twice
  have h1 := peel_one_maxPrime hsq_m (card_pos.mpr hne1)
  dsimp only at h1
  obtain ⟨r, hr_def⟩ : ∃ r : ℕ, r = m.primeFactors.max' hne1 := ⟨_, rfl⟩
  rw [← hr_def] at h1
  obtain ⟨m₁, hm₁_def⟩ : ∃ m₁ : ℕ, m₁ = m / r := ⟨_, rfl⟩
  rw [← hm₁_def] at h1
  obtain ⟨hrp, hsq_m₁, hmm₁, hpf_m₁, hcard_m₁, hlt_r⟩ := h1
  have hm₁_pos_card : 1 ≤ m₁.primeFactors.card := by omega
  have hne2 : (m.primeFactors.erase r).Nonempty := by
    rw [← hpf_m₁]; exact card_pos.mp hm₁_pos_card
  obtain ⟨q, hq_def⟩ : ∃ q : ℕ, q = (m.primeFactors.erase r).max' hne2 := ⟨_, rfl⟩
  have hq_eq : q = m₁.primeFactors.max' (card_pos.mp hm₁_pos_card) := by
    rw [hq_def]
    apply le_antisymm
    · refine max'_le _ _ _ fun s hs => le_max' _ s (hpf_m₁.symm ▸ hs)
    · refine max'_le _ _ _ fun s hs => le_max' _ s (hpf_m₁ ▸ hs)
  have h2 := peel_one_maxPrime hsq_m₁ hm₁_pos_card
  dsimp only at h2
  rw [← hq_eq] at h2
  obtain ⟨hqp, hsq_c, hm₁c, _, hcard_c, hlt_q⟩ := h2
  have ha_eq : a = m₁ / q := by
    rw [← h_eq]
    unfold evenPrefixCofactor
    simp only [dif_pos hne1, if_pos heven, ← hr_def, dif_pos hne2, ← hq_def, hm₁_def]
    rw [Nat.div_div_eq_div_mul, mul_comm r q]
  rw [← ha_eq] at hsq_c hm₁c hcard_c hlt_q
  have hqr : q < r := hlt_r q (hq_eq ▸ max'_mem _ (card_pos.mp hm₁_pos_card))
  have heven_a : Even a.primeFactors.card := by
    obtain ⟨k, hk⟩ := heven
    refine ⟨k - 1, ?_⟩
    omega
  exact ⟨hsq_c, heven_a, q, r, hqp, hrp, hqr, by rw [hmm₁, hm₁c, mul_assoc], hlt_q⟩

theorem mem_fibreNeg_structure {X a n : ℕ} (hX1 : 1 ≤ X) (hn : n ∈ fibreNeg X a) :
    Squarefree a ∧ Even a.primeFactors.card ∧
      ∃ p : ℕ, p.Prime ∧ n = a * p ∧ (∀ s ∈ a.primeFactors, s < p) := by
  classical
  obtain ⟨hn_neg, h_eq⟩ := mem_filter.mp hn
  have hn_sq_mem : n ∈ squarefreeOf (Ioc X (2 * X)) := by
    rw [squarefreeOf_eq_posParity_union_negParity]; exact mem_union_right _ hn_neg
  obtain ⟨hnIoc, hsq_n⟩ := mem_filter.mp hn_sq_mem
  have hn_gt1 : 1 < n := lt_of_le_of_lt hX1 (mem_Ioc.mp hnIoc).1
  have hμn : μ n = -1 := (mem_filter.mp hn_neg).2
  have hodd : Odd n.primeFactors.card := by
    rcases Nat.even_or_odd n.primeFactors.card with he | ho
    · have := moebius_eq_neg_one_pow_omega hsq_n
      rw [he.neg_one_pow] at this; omega
    · exact ho
  have hnot_even : ¬ Even n.primeFactors.card := Nat.not_even_iff_odd.mpr hodd
  have hne1 : n.primeFactors.Nonempty :=
    ⟨n.minFac, Nat.mem_primeFactors.mpr
      ⟨Nat.minFac_prime hn_gt1.ne', Nat.minFac_dvd n, by omega⟩⟩
  have h1 := peel_one_maxPrime hsq_n (card_pos.mpr hne1)
  dsimp only at h1
  obtain ⟨p, hp_def⟩ : ∃ p : ℕ, p = n.primeFactors.max' hne1 := ⟨_, rfl⟩
  rw [← hp_def] at h1
  obtain ⟨hpp, hsq_c, hnc, _, hcard_c, hlt_p⟩ := h1
  have ha_eq : a = n / p := by
    rw [← h_eq]
    unfold evenPrefixCofactor
    simp only [dif_pos hne1, if_neg hnot_even, ← hp_def]
  rw [← ha_eq] at hsq_c hnc hcard_c hlt_p
  obtain ⟨k, hk⟩ := hodd
  have heven_a : Even a.primeFactors.card := ⟨k, by omega⟩
  exact ⟨hsq_c, heven_a, p, hpp, hnc, hlt_p⟩

/-- **Target-collision-free complete bipartite fibre theorem**:
1. Distinct cofactors `a₁ ≠ a₂` have disjoint positive fibres and disjoint negative fibres;
2. Every pair `(m, n) ∈ fibrePos X a × fibreNeg X a` is an edge of `GlobalDyadicOneTwoRel`! -/
theorem evenPrefixCofactor_complete_bipartite_fibres {X : ℕ} (hX1 : 1 ≤ X) :
    (∀ {a₁ a₂ : ℕ}, a₁ ≠ a₂ →
      Disjoint (fibrePos X a₁) (fibrePos X a₂) ∧ Disjoint (fibreNeg X a₁) (fibreNeg X a₂)) ∧
    (∀ {a m n : ℕ}, m ∈ fibrePos X a → n ∈ fibreNeg X a → GlobalDyadicOneTwoRel m n) := by
  classical
  refine ⟨fun {a₁ a₂} hne => ⟨?_, ?_⟩, fun {a m n} hm hn => ?_⟩
  · rw [disjoint_left]
    intro x h1 h2
    exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
  · rw [disjoint_left]
    intro x h1 h2
    exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
  · obtain ⟨_, _, q, r, hqp, hrp, hqr, hma, _⟩ := mem_fibrePos_structure hX1 hm
    obtain ⟨_, _, p, hpp, hna, _⟩ := mem_fibreNeg_structure hX1 hn
    have hm_pos := (mem_filter.mp hm).1
    have hn_neg := (mem_filter.mp hn).1
    have hsq_m : Squarefree m :=
      squarefree_iff_moebius_ne_zero.mpr (by have := (mem_filter.mp hm_pos).2; omega)
    have hsq_n : Squarefree n :=
      squarefree_iff_moebius_ne_zero.mpr (by have := (mem_filter.mp hn_neg).2; omega)
    have hμ : μ m = -μ n := by
      have h1 := (mem_filter.mp hm_pos).2
      have h2 := (mem_filter.mp hn_neg).2
      omega
    exact ⟨hsq_m, hsq_n, hμ, a, p, q, r, hpp, hqp, hrp, hqr, Or.inr ⟨hna, hma⟩⟩

/-- **Fibre-boundary empty-target obstruction**: Whenever `s ∈ a.primeFactors` satisfies
`2 * X ≤ a * s²`, the positive fibre `fibrePos X a` is empty. -/
theorem fibrePos_eq_empty_of_primeFactor_sq_ge {X a s : ℕ} (hX1 : 1 ≤ X)
    (hs : s ∈ a.primeFactors) (hge : 2 * X ≤ a * s ^ 2) :
    fibrePos X a = ∅ := by
  classical
  refine eq_empty_iff_forall_notMem.mpr fun m hm => ?_
  obtain ⟨_, _, q, r, _, _, hqr, hma, hlt_q⟩ := mem_fibrePos_structure hX1 hm
  have hm2X : m ≤ 2 * X := (mem_Ioc.mp (mem_filter.mp (mem_filter.mp hm).1).1).2
  have hsq : s + 1 ≤ q := hlt_q s hs
  have hsr : s + 2 ≤ r := by omega
  have ha_pos : 0 < a := by
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · simp at hs
    · exact hpos
  have hqr_gt : s ^ 2 < q * r := by nlinarith
  have hm_gt : a * s ^ 2 < m := by
    rw [hma]
    exact Nat.mul_lt_mul_of_pos_left hqr_gt ha_pos
  omega

/-- Constant-ratio prime window lower bound: for every `α > 1`, eventually `(u, α u]` contains
at least `((α - 1) / 2) * u / log (α u)` primes. -/
private lemma exists_const_ratio_windowPrimes_ge {α : ℝ} (hα : 1 < α) :
    ∃ U_α : ℝ, 4 ≤ U_α ∧ ∀ u : ℝ, U_α ≤ u →
      ((α - 1) / 2) * u / Real.log (α * u) ≤ ((windowPrimes u (α * u)).card : ℝ) := by
  obtain ⟨C_θ, hC_θ, T_θ, hT_θ, hθ⟩ := exists_abs_theta_sub_le 1
  have hα0 : 0 < α - 1 := by linarith only [hα]
  have hev_α : ∀ᶠ u : ℝ in atTop,
      T_θ ≤ u ∧ 4 ≤ u ∧ 4 * C_θ * α / (α - 1) ≤ Real.log u :=
    (eventually_ge_atTop _).and ((eventually_ge_atTop 4).and
      (Real.tendsto_log_atTop.eventually_ge_atTop _))
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hev_α
  refine ⟨max U₀ 4, le_max_right _ _, fun u hu => ?_⟩
  obtain ⟨hTu, hu4, hCu⟩ := hU₀ u ((le_max_left _ _).trans hu)
  clear hev_α hU₀
  have hu0 : 0 < u := by linarith only [hu4]
  have hab : u ≤ α * u := by nlinarith [hα, hu0]
  have hlogu : 0 < Real.log u := Real.log_pos (by linarith only [hu4])
  have hlogαu : 0 < Real.log (α * u) := Real.log_pos (by linarith only [hu4, hab])
  have hinc := abs_theta_increment_le hC_θ.le hT_θ hθ hTu hab
  have herr : 2 * C_θ * (α * u) / Real.log u ^ (1 : ℕ) ≤ ((α - 1) / 2) * u := by
    rw [pow_one, div_le_iff₀ hlogu]
    rw [div_le_iff₀ hα0] at hCu
    nlinarith [hCu, hu0]
  have hθ_ge : ((α - 1) / 2) * u ≤ Chebyshev.theta (α * u) - Chebyshev.theta u := by
    have hlow := (abs_le.mp hinc).1
    linarith only [hlow, herr]
  have hcard := theta_sub_le_card_mul_log hu0.le hab
  rw [div_le_iff₀ hlogαu]
  linarith only [hθ_ge, hcard]

/-- **Quantitative fibre-boundary debt (`≫ X / (log X)³`)**: There exists an explicit constant
`c > 0` such that on every sufficiently large dyadic block `(X, 2X]`, at least `c X / (log X)³`
negative-Möbius squarefree integers `n ∈ (X, 2X]` lie in even-prefix cofactor fibres with
`fibrePos X (evenPrefixCofactor n) = ∅`. Consequently, **every** matching restricted to preserving
`evenPrefixCofactor` leaves at least `c X / (log X)³` unmatched integers on every large dyadic block. -/
theorem eventually_evenPrefixFibre_debt_ge :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      c * (X : ℝ) / Real.log X ^ (3 : ℕ) ≤
        (((negParity (Ioc X (2 * X))).filter
          (fun n => fibrePos X (evenPrefixCofactor n) = ∅)).card : ℝ) ∧
      ∀ M : OppositeParityMatching
          (fun a b => GlobalDyadicOneTwoRel a b ∧ evenPrefixCofactor a = evenPrefixCofactor b)
          (Ioc X (2 * X)),
        c * (X : ℝ) / Real.log X ^ (3 : ℕ) ≤ (M.unmatchedSet.card : ℝ) := by
  -- Use constant-ratio prime window bounds for `(u, (4/3) u]`, `(u, (9/8) u]`, and `(u, 2 u]`
  obtain ⟨U₁, hU₁_4, hw_43⟩ := exists_const_ratio_windowPrimes_ge (α := 4 / 3) (by norm_num)
  obtain ⟨U₂, _, hw_98⟩ := exists_const_ratio_windowPrimes_ge (α := 9 / 8) (by norm_num)
  obtain ⟨U₃, _, hw_2⟩ := exists_const_ratio_windowPrimes_ge (α := 2) (by norm_num)
  obtain ⟨c_debt, hc_def⟩ : ∃ c_debt : ℝ, c_debt = (1 / 48) * (1 / 8) * (4 / 3) := ⟨_, rfl⟩
  have hc_pos : 0 < c_debt := by rw [hc_def]; positivity
  have hrpow_3 : Tendsto (fun x : ℝ => x ^ (1 / 3 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hev : ∀ᶠ x : ℝ in atTop,
      64 ≤ x ∧ 8 * U₁ ≤ x ^ (1 / 3 : ℝ) ∧ U₂ ≤ 2 * x ^ (1 / 3 : ℝ) ∧
      U₃ ≤ (8 / 3) * x ^ (1 / 3 : ℝ) :=
    (eventually_ge_atTop 64).and ((hrpow_3.eventually_ge_atTop _).and
      (((hrpow_3.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).eventually_ge_atTop _).and
        ((hrpow_3.const_mul_atTop (by norm_num : (0 : ℝ) < 8 / 3)).eventually_ge_atTop _)))
  obtain ⟨X_cut, hX_cut⟩ := eventually_atTop.mp hev
  refine ⟨c_debt, hc_pos, max 1 ⌈X_cut⌉₊, fun X hX => ?_⟩
  classical
  have hX1 : 1 ≤ X := le_of_max_le_left hX
  have hX_ge : X_cut ≤ (X : ℝ) :=
    (Nat.le_ceil X_cut).trans (by exact_mod_cast le_of_max_le_right hX)
  obtain ⟨hX64, hU1, hU2, hU3⟩ := hX_cut X hX_ge
  clear hrpow_3 hev hX_cut hX_ge
  have hX0 : (0 : ℝ) < X := by linarith only [hX64]
  have hL0 : 0 < Real.log X := Real.log_pos (by linarith only [hX64])
  obtain ⟨Y, hY_def⟩ : ∃ Y : ℝ, Y = (X : ℝ) ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
  rw [← hY_def] at hU1 hU2 hU3
  have hY_pos : 0 < Y := by rw [hY_def]; positivity
  have hY3 : Y ^ (3 : ℕ) = (X : ℝ) := by
    rw [hY_def, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
    norm_num
  have hY_ge4 : 4 ≤ Y := by
    have h4_3 : (4 : ℝ) ^ (3 : ℕ) ≤ Y ^ (3 : ℕ) := by rw [hY3]; norm_num at *; linarith
    exact (pow_le_pow_iff_left₀ (by norm_num) hY_pos.le (by omega)).mp h4_3
  -- Three disjoint prime windows: `W₁ = (Y/8, Y/6]`, `W₂ = (2Y, 9Y/4]`, `W₃(p₁,p₂) = (X/(p₁p₂), 2X/(p₁p₂)]`
  obtain ⟨W₁, hW₁_def⟩ : ∃ W₁ : Finset ℕ, W₁ = windowPrimes (Y / 8) (4 / 3 * (Y / 8)) := ⟨_, rfl⟩
  obtain ⟨W₂, hW₂_def⟩ : ∃ W₂ : Finset ℕ, W₂ = windowPrimes (2 * Y) (9 / 8 * (2 * Y)) := ⟨_, rfl⟩
  obtain ⟨Tri, hTri_def⟩ : ∃ Tri : Finset ℕ, Tri = (W₁ ×ˢ W₂).biUnion fun pq =>
    (windowPrimes ((X : ℝ) / (pq.1 * pq.2)) (2 * ((X : ℝ) / (pq.1 * pq.2)))).image
      fun p₃ => pq.1 * pq.2 * p₃ := ⟨_, rfl⟩
  -- Every `n = p₁ * p₂ * p₃ ∈ Tri` lies in `negParity (Ioc X (2X))` with `evenPrefixCofactor n = p₁ * p₂`
  -- and `fibrePos X (p₁ * p₂) = ∅`
  have hTri_info : ∀ pq ∈ W₁ ×ˢ W₂,
      ∀ p₃ ∈ windowPrimes ((X : ℝ) / (pq.1 * pq.2)) (2 * ((X : ℝ) / (pq.1 * pq.2))),
        let p₁ := pq.1; let p₂ := pq.2; let n := p₁ * p₂ * p₃
        p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ < p₂ ∧ p₂ < p₃ ∧
          n.primeFactors.filter (· ≤ ⌊Y / 6⌋₊) = {p₁} ∧
          n.primeFactors.filter (fun p => ⌊Y / 6⌋₊ < p ∧ p ≤ ⌊9 / 4 * Y⌋₊) = {p₂} ∧
          n ∈ negParity (Ioc X (2 * X)) ∧
          evenPrefixCofactor n = p₁ * p₂ ∧
          fibrePos X (p₁ * p₂) = ∅ := by
    rintro ⟨p₁, p₂⟩ hpq p₃ hp₃
    dsimp only at hp₃ ⊢
    obtain ⟨hp₁W, hp₂W⟩ := mem_product.mp hpq
    dsimp only at hp₁W hp₂W
    rw [hW₁_def] at hp₁W
    rw [hW₂_def] at hp₂W
    obtain ⟨hp₁_pr, hp₁_lt, hp₁_le⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hp₁W
    obtain ⟨hp₂_pr, hp₂_lt, hp₂_le⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hp₂W
    have hp₁_le' : (p₁ : ℝ) ≤ Y / 6 := by linarith only [hp₁_le]
    have hp₂_le' : (p₂ : ℝ) ≤ 9 / 4 * Y := by linarith only [hp₂_le]
    have hpq_pos : 0 < p₁ * p₂ := Nat.mul_pos hp₁_pr.pos hp₂_pr.pos
    have hpq_r_pos : (0 : ℝ) < (p₁ : ℝ) * p₂ := by exact_mod_cast hpq_pos
    obtain ⟨hp₃_pr, hp₃_lt, hp₃_le⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hp₃
    have hpq_up : (p₁ : ℝ) * p₂ ≤ (3 / 8) * Y ^ (2 : ℕ) := by
      calc (p₁ : ℝ) * p₂ ≤ (Y / 6) * (9 / 4 * Y) :=
            mul_le_mul hp₁_le' hp₂_le' (Nat.cast_nonneg _) (by positivity)
        _ = (3 / 8) * Y ^ (2 : ℕ) := by ring
    have hXpq_low : (8 / 3) * Y ≤ (X : ℝ) / ((p₁ : ℝ) * p₂) := by
      rw [le_div_iff₀ hpq_r_pos]
      calc (8 / 3) * Y * ((p₁ : ℝ) * p₂) ≤ (8 / 3) * Y * ((3 / 8) * Y ^ (2 : ℕ)) :=
            mul_le_mul_of_nonneg_left hpq_up (by positivity)
        _ = Y ^ (3 : ℕ) := by ring
        _ = X := hY3
    have hp₁_lt_p₂ : p₁ < p₂ := by
      exact_mod_cast (show (p₁ : ℝ) < p₂ by linarith only [hp₁_le', hp₂_lt, hY_pos])
    have hp₂_lt_p₃ : p₂ < p₃ := by
      exact_mod_cast (show (p₂ : ℝ) < p₃ by linarith only [hp₂_le', hXpq_low, hp₃_lt, hY_pos])
    have hcop_12 : Nat.Coprime p₁ p₂ := (Nat.coprime_primes hp₁_pr hp₂_pr).mpr hp₁_lt_p₂.ne
    have hcop_123 : Nat.Coprime (p₁ * p₂) p₃ :=
      Nat.Coprime.mul_left ((Nat.coprime_primes hp₁_pr hp₃_pr).mpr (by omega))
        ((Nat.coprime_primes hp₂_pr hp₃_pr).mpr hp₂_lt_p₃.ne)
    have hsq_12 : Squarefree (p₁ * p₂) :=
      Nat.squarefree_mul_iff.mpr ⟨hcop_12, Irreducible.squarefree hp₁_pr,
        Irreducible.squarefree hp₂_pr⟩
    have hsq_n : Squarefree (p₁ * p₂ * p₃) :=
      Nat.squarefree_mul_iff.mpr ⟨hcop_123, hsq_12, Irreducible.squarefree hp₃_pr⟩
    have hpf_n : (p₁ * p₂ * p₃).primeFactors = {p₁, p₂, p₃} := by
      rw [Nat.primeFactors_mul hpq_pos.ne' hp₃_pr.ne_zero,
        Nat.primeFactors_mul hp₁_pr.ne_zero hp₂_pr.ne_zero,
        hp₁_pr.primeFactors, hp₂_pr.primeFactors, hp₃_pr.primeFactors]
      ext q; simp only [mem_union, mem_singleton, mem_insert]; tauto
    have hcard_n : (p₁ * p₂ * p₃).primeFactors.card = 3 := by
      rw [hpf_n, card_insert_of_notMem (by simp; omega),
        card_insert_of_notMem (by simp; omega), card_singleton]
    have hfil_1 : (p₁ * p₂ * p₃).primeFactors.filter (· ≤ ⌊Y / 6⌋₊) = {p₁} := by
      rw [hpf_n]
      ext q; simp only [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hq1 | hq2 | hq3, hq_le⟩
        · exact hq1
        · rw [hq2] at hq_le
          have hb : (p₂ : ℝ) ≤ Y / 6 := (Nat.cast_le.mpr hq_le).trans (Nat.floor_le (by positivity))
          linarith only [hb, hp₂_lt, hY_pos]
        · rw [hq3] at hq_le
          have hb : (p₃ : ℝ) ≤ Y / 6 := (Nat.cast_le.mpr hq_le).trans (Nat.floor_le (by positivity))
          linarith only [hb, hp₃_lt, hXpq_low, hY_pos]
      · rintro rfl; exact ⟨Or.inl rfl, Nat.le_floor hp₁_le'⟩
    have hfil_2 : (p₁ * p₂ * p₃).primeFactors.filter
        (fun p => ⌊Y / 6⌋₊ < p ∧ p ≤ ⌊9 / 4 * Y⌋₊) = {p₂} := by
      rw [hpf_n]
      ext q; simp only [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hq1 | hq2 | hq3, hx1, hx2⟩
        · rw [hq1] at hx1; have := Nat.le_floor hp₁_le'; omega
        · exact hq2
        · rw [hq3] at hx2
          have hb : (p₃ : ℝ) ≤ 9 / 4 * Y := (Nat.cast_le.mpr hx2).trans (Nat.floor_le (by positivity))
          linarith only [hb, hp₃_lt, hXpq_low, hY_pos]
      · intro hq_eq
        rw [hq_eq]
        refine ⟨Or.inr (Or.inl rfl), ?_, Nat.le_floor hp₂_le'⟩
        have hfl_lt : (⌊Y / 6⌋₊ : ℝ) < p₂ :=
          (Nat.floor_le (by positivity)).trans_lt (by linarith only [hp₂_lt, hY_pos])
        exact_mod_cast hfl_lt
    have hn_Ioc : p₁ * p₂ * p₃ ∈ Ioc X (2 * X) := by
      rw [div_lt_iff₀ hpq_r_pos] at hp₃_lt
      rw [mul_div_assoc', le_div_iff₀ hpq_r_pos] at hp₃_le
      refine mem_Ioc.mpr ⟨?_, ?_⟩
      · exact_mod_cast (show (X : ℝ) < (p₁ * p₂ * p₃ : ℕ) by push_cast; linarith only [hp₃_lt])
      · exact_mod_cast (show ((p₁ * p₂ * p₃ : ℕ) : ℝ) ≤ (2 * X : ℕ) by push_cast; linarith only [hp₃_le])
    have hn_neg : p₁ * p₂ * p₃ ∈ negParity (Ioc X (2 * X)) := by
      refine mem_filter.mpr ⟨hn_Ioc, ?_⟩
      rw [moebius_eq_neg_one_pow_omega hsq_n, hcard_n]
      norm_num
    have hmax_n : ∀ hne, (p₁ * p₂ * p₃).primeFactors.max' hne = p₃ := by
      intro hne
      apply le_antisymm
      · refine max'_le _ _ _ fun q hq => ?_
        rw [hpf_n] at hq
        rcases mem_insert.mp hq with rfl | hq'
        · omega
        · rcases mem_insert.mp hq' with rfl | hq''
          · omega
          · rw [mem_singleton.mp hq'']
      · exact le_max' _ p₃ (by rw [hpf_n]; simp)
    have hnot_even3 : ¬ Even (p₁ * p₂ * p₃).primeFactors.card := by
      rw [hcard_n]; decide
    have hne_n : (p₁ * p₂ * p₃).primeFactors.Nonempty := by rw [hpf_n]; simp
    have hepc : evenPrefixCofactor (p₁ * p₂ * p₃) = p₁ * p₂ := by
      unfold evenPrefixCofactor
      rw [dif_pos hne_n, if_neg hnot_even3, hmax_n hne_n]
      exact Nat.mul_div_cancel _ hp₃_pr.pos
    have hfib_empty : fibrePos X (p₁ * p₂) = ∅ := by
      have hp₂_mem : p₂ ∈ (p₁ * p₂).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp₂_pr, dvd_mul_left p₂ p₁, hpq_pos.ne'⟩
      apply fibrePos_eq_empty_of_primeFactor_sq_ge hX1 hp₂_mem
      have hgt_2X : 2 * (X : ℝ) ≤ ((p₁ * p₂) * p₂ ^ 2 : ℕ) := by
        push_cast
        have hp₂_cube : 8 * Y ^ (3 : ℕ) ≤ (p₂ : ℝ) ^ (3 : ℕ) := by
          calc 8 * Y ^ (3 : ℕ) = (2 * Y) ^ (3 : ℕ) := by ring
            _ ≤ (p₂ : ℝ) ^ (3 : ℕ) := pow_le_pow_left₀ (by positivity) hp₂_lt.le 3
        calc 2 * (X : ℝ) ≤ (Y / 8) * (8 * Y ^ (3 : ℕ)) := by
              rw [hY3]
              have : 2 * (X : ℝ) ≤ (4 / 8) * (8 * X) := by linarith
              nlinarith
          _ ≤ (p₁ : ℝ) * (p₂ : ℝ) ^ (3 : ℕ) :=
              mul_le_mul hp₁_lt.le hp₂_cube (by positivity) (Nat.cast_nonneg _)
          _ = (p₁ : ℝ) * p₂ * (p₂ : ℝ) ^ 2 := by ring
      exact_mod_cast hgt_2X
    exact ⟨hp₁_pr, hp₂_pr, hp₃_pr, hp₁_lt_p₂, hp₂_lt_p₃, hfil_1, hfil_2,
      hn_neg, hepc, hfib_empty⟩
  have hTri_sub : Tri ⊆ (negParity (Ioc X (2 * X))).filter
      (fun n => fibrePos X (evenPrefixCofactor n) = ∅) := by
    intro n hn
    rw [hTri_def] at hn
    obtain ⟨pq, hpq, hn_img⟩ := mem_biUnion.mp hn
    obtain ⟨p₃, hp₃, rfl⟩ := mem_image.mp hn_img
    have hi := hTri_info pq hpq p₃ hp₃
    refine mem_filter.mpr ⟨hi.2.2.2.2.2.2.2.1, ?_⟩
    rw [hi.2.2.2.2.2.2.2.2.1]
    exact hi.2.2.2.2.2.2.2.2.2
  have hTri_card : Tri.card = ∑ pq ∈ W₁ ×ˢ W₂,
      (windowPrimes ((X : ℝ) / (pq.1 * pq.2)) (2 * ((X : ℝ) / (pq.1 * pq.2)))).card := by
    rw [hTri_def, card_biUnion]
    · refine sum_congr rfl fun pq hpq => card_image_of_injOn fun r₁ hr₁ r₂ _ heq => ?_
      have hi := hTri_info pq hpq r₁ hr₁
      exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hi.1.pos hi.2.1.pos) heq
    · rintro ⟨p₁, p₂⟩ hpq₁ ⟨q₁, q₂⟩ hpq₂ hne
      simp only [Function.onFun]
      rw [disjoint_left]
      intro n hn₁ hn₂
      obtain ⟨r₁, hr₁, rfl⟩ := mem_image.mp hn₁
      obtain ⟨r₂, hr₂, heq⟩ := mem_image.mp hn₂
      have hi₁ := hTri_info (p₁, p₂) hpq₁ r₁ hr₁
      have hi₂ := hTri_info (q₁, q₂) hpq₂ r₂ hr₂
      have heq1 : p₁ = q₁ := singleton_injective
        (hi₁.2.2.2.2.2.1.symm.trans (heq ▸ hi₂.2.2.2.2.2.1))
      have heq2 : p₂ = q₂ := singleton_injective
        (hi₁.2.2.2.2.2.2.1.symm.trans (heq ▸ hi₂.2.2.2.2.2.2.1))
      exact hne (Prod.ext heq1 heq2)
  -- Lower bound `#W₁`, `#W₂`, and each inner window `#W₃`
  have hY_le_X : Y ≤ X := by
    calc Y = (X : ℝ) ^ (1 / 3 : ℝ) := hY_def
      _ ≤ (X : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith only [hX64]) (by norm_num)
      _ = X := Real.rpow_one _
  have hW₁_ge : (1 / 48) * Y / Real.log X ≤ (W₁.card : ℝ) := by
    have hw := hw_43 (Y / 8) (by linarith only [hU1])
    rw [← hW₁_def] at hw
    have hlog_le : Real.log (4 / 3 * (Y / 8)) ≤ Real.log X :=
      Real.log_le_log (by positivity) (by linarith only [hY_le_X, hY_pos])
    have hlog_pos : 0 < Real.log (4 / 3 * (Y / 8)) :=
      Real.log_pos (by linarith only [hU₁_4, hU1])
    calc (1 / 48) * Y / Real.log X
        ≤ (1 / 48) * Y / Real.log (4 / 3 * (Y / 8)) :=
          div_le_div_of_nonneg_left (by positivity) hlog_pos hlog_le
      _ = ((4 / 3 - 1) / 2) * (Y / 8) / Real.log (4 / 3 * (Y / 8)) := by ring
      _ ≤ (W₁.card : ℝ) := hw
  have hW₂_ge : (1 / 8) * Y / Real.log X ≤ (W₂.card : ℝ) := by
    have hw := hw_98 (2 * Y) hU2
    rw [← hW₂_def] at hw
    have h94Y_le_X : 9 / 8 * (2 * Y) ≤ X := by
      have hY2 : (9 / 4 : ℝ) ≤ Y ^ (2 : ℕ) := by nlinarith [hY_ge4]
      calc 9 / 8 * (2 * Y) = (9 / 4) * Y := by ring
        _ ≤ Y ^ (2 : ℕ) * Y := mul_le_mul_of_nonneg_right hY2 hY_pos.le
        _ = Y ^ (3 : ℕ) := by ring
        _ = X := hY3
    have hlog_le : Real.log (9 / 8 * (2 * Y)) ≤ Real.log X :=
      Real.log_le_log (by positivity) h94Y_le_X
    have hlog_pos : 0 < Real.log (9 / 8 * (2 * Y)) :=
      Real.log_pos (by linarith only [hY_ge4])
    calc (1 / 8) * Y / Real.log X
        ≤ (1 / 8) * Y / Real.log (9 / 8 * (2 * Y)) :=
          div_le_div_of_nonneg_left (by positivity) hlog_pos hlog_le
      _ = ((9 / 8 - 1) / 2) * (2 * Y) / Real.log (9 / 8 * (2 * Y)) := by ring
      _ ≤ (W₂.card : ℝ) := hw
  have hW₃_ge : ∀ pq ∈ W₁ ×ˢ W₂,
      (4 / 3) * Y / Real.log X ≤
        ((windowPrimes ((X : ℝ) / (pq.1 * pq.2)) (2 * ((X : ℝ) / (pq.1 * pq.2)))).card : ℝ) := by
    rintro ⟨p₁, p₂⟩ hpq
    dsimp only
    obtain ⟨hp₁W, hp₂W⟩ := mem_product.mp hpq
    dsimp only at hp₁W hp₂W
    rw [hW₁_def] at hp₁W
    rw [hW₂_def] at hp₂W
    obtain ⟨hp₁_pr, _, hp₁_le⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hp₁W
    obtain ⟨hp₂_pr, _, hp₂_le⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hp₂W
    have hp₁_le' : (p₁ : ℝ) ≤ Y / 6 := by linarith only [hp₁_le]
    have hp₂_le' : (p₂ : ℝ) ≤ 9 / 4 * Y := by linarith only [hp₂_le]
    have hpq_r_pos : (0 : ℝ) < (p₁ : ℝ) * p₂ := by
      exact_mod_cast Nat.mul_pos hp₁_pr.pos hp₂_pr.pos
    have hpq_up : (p₁ : ℝ) * p₂ ≤ (3 / 8) * Y ^ (2 : ℕ) := by
      calc (p₁ : ℝ) * p₂ ≤ (Y / 6) * (9 / 4 * Y) :=
            mul_le_mul hp₁_le' hp₂_le' (Nat.cast_nonneg _) (by positivity)
        _ = (3 / 8) * Y ^ (2 : ℕ) := by ring
    have hXpq_low : (8 / 3) * Y ≤ (X : ℝ) / ((p₁ : ℝ) * p₂) := by
      rw [le_div_iff₀ hpq_r_pos]
      calc (8 / 3) * Y * ((p₁ : ℝ) * p₂) ≤ (8 / 3) * Y * ((3 / 8) * Y ^ (2 : ℕ)) :=
            mul_le_mul_of_nonneg_left hpq_up (by positivity)
        _ = Y ^ (3 : ℕ) := by ring
        _ = X := hY3
    have hw := hw_2 ((X : ℝ) / ((p₁ : ℝ) * p₂)) (hU3.trans hXpq_low)
    have hpq_ge2 : (2 : ℝ) ≤ (p₁ : ℝ) * p₂ := by
      have hp₁_2 : (2 : ℝ) ≤ p₁ := by exact_mod_cast hp₁_pr.two_le
      have hp₂_2 : (2 : ℝ) ≤ p₂ := by exact_mod_cast hp₂_pr.two_le
      nlinarith [hp₁_2, hp₂_2]
    have h2Xpq_le_X : 2 * ((X : ℝ) / ((p₁ : ℝ) * p₂)) ≤ X := by
      rw [mul_div_assoc', div_le_iff₀ hpq_r_pos]
      nlinarith [hpq_ge2, hX0]
    have hlog_le : Real.log (2 * ((X : ℝ) / ((p₁ : ℝ) * p₂))) ≤ Real.log X :=
      Real.log_le_log (by positivity) h2Xpq_le_X
    have hlog_pos : 0 < Real.log (2 * ((X : ℝ) / ((p₁ : ℝ) * p₂))) :=
      Real.log_pos (by linarith only [hXpq_low, hY_ge4])
    calc (4 / 3) * Y / Real.log X
        ≤ ((2 - 1) / 2) * ((X : ℝ) / ((p₁ : ℝ) * p₂)) / Real.log X := by
          have hnum : (4 / 3) * Y ≤ ((2 - 1) / 2) * ((X : ℝ) / ((p₁ : ℝ) * p₂)) := by
            linarith only [hXpq_low]
          exact div_le_div_of_nonneg_right hnum hL0.le
      _ ≤ ((2 - 1) / 2) * ((X : ℝ) / ((p₁ : ℝ) * p₂)) /
            Real.log (2 * ((X : ℝ) / ((p₁ : ℝ) * p₂))) :=
          div_le_div_of_nonneg_left (by positivity) hlog_pos hlog_le
      _ ≤ ((windowPrimes ((X : ℝ) / (p₁ * p₂)) (2 * ((X : ℝ) / (p₁ * p₂)))).card : ℝ) := hw
  obtain ⟨Bad, hBad_def⟩ : ∃ Bad, Bad =
      (negParity (Ioc X (2 * X))).filter (fun n => fibrePos X (evenPrefixCofactor n) = ∅) := ⟨_, rfl⟩
  have hTri_card_ge : c_debt * (X : ℝ) / Real.log X ^ (3 : ℕ) ≤ (Tri.card : ℝ) := by
    have hsum_ge : ((W₁ ×ˢ W₂).card : ℝ) * ((4 / 3) * Y / Real.log X) ≤ (Tri.card : ℝ) := by
      rw [hTri_card, Nat.cast_sum]
      calc ((W₁ ×ˢ W₂).card : ℝ) * ((4 / 3) * Y / Real.log X)
          = ∑ _pq ∈ W₁ ×ˢ W₂, ((4 / 3) * Y / Real.log X) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ pq ∈ W₁ ×ˢ W₂,
              ((windowPrimes ((X : ℝ) / (pq.1 * pq.2))
                (2 * ((X : ℝ) / (pq.1 * pq.2)))).card : ℝ) :=
            sum_le_sum hW₃_ge
    have hprod_card : ((W₁ ×ˢ W₂).card : ℝ) = (W₁.card : ℝ) * (W₂.card : ℝ) := by
      rw [card_product, Nat.cast_mul]
    have h12 : ((1 / 48) * Y / Real.log X) * ((1 / 8) * Y / Real.log X) ≤
        (W₁.card : ℝ) * (W₂.card : ℝ) :=
      mul_le_mul hW₁_ge hW₂_ge (by positivity) (Nat.cast_nonneg _)
    calc c_debt * (X : ℝ) / Real.log X ^ (3 : ℕ)
        = c_debt * Y ^ (3 : ℕ) / Real.log X ^ (3 : ℕ) := by rw [hY3]
      _ = ((1 / 48) * Y / Real.log X) * ((1 / 8) * Y / Real.log X) *
            ((4 / 3) * Y / Real.log X) := by
          rw [hc_def]; ring
      _ ≤ ((W₁.card : ℝ) * (W₂.card : ℝ)) * ((4 / 3) * Y / Real.log X) :=
          mul_le_mul_of_nonneg_right h12 (by positivity)
      _ = ((W₁ ×ˢ W₂).card : ℝ) * ((4 / 3) * Y / Real.log X) := by rw [hprod_card]
      _ ≤ (Tri.card : ℝ) := hsum_ge
  have hBad_ge : c_debt * (X : ℝ) / Real.log X ^ (3 : ℕ) ≤ (Bad.card : ℝ) :=
    hTri_card_ge.trans (by rw [hBad_def]; exact_mod_cast card_le_card hTri_sub)
  refine ⟨by rw [← hBad_def]; exact hBad_ge, fun M => hBad_ge.trans ?_⟩
  have hBad_sub : Bad ⊆ M.unmatchedSet := by
    intro n hn
    rw [hBad_def] at hn
    obtain ⟨hn_neg, hfib_empty⟩ := mem_filter.mp hn
    have hn_sq : n ∈ squarefreeOf (Ioc X (2 * X)) := by
      rw [squarefreeOf_eq_posParity_union_negParity]; exact mem_union_right _ hn_neg
    refine mem_sdiff.mpr ⟨hn_sq, fun hm => ?_⟩
    rcases mem_union.mp hm with hsrc | htgt
    · exact disjoint_left.mp (disjoint_posParity_negParity (Ioc X (2 * X)))
        (M.sources_subset hsrc) hn_neg
    · obtain ⟨a, ha_src, rfl⟩ := mem_image.mp htgt
      have ha_fib : a ∈ fibrePos X (evenPrefixCofactor (M.partner a)) :=
        mem_filter.mpr ⟨M.sources_subset ha_src, (M.adj a ha_src).2⟩
      rw [hfib_empty] at ha_fib
      exact notMem_empty a ha_fib
  exact_mod_cast card_le_card hBad_sub

end GaloisForLFunctions.QuantitativeFactorizationMatching

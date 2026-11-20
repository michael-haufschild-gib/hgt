import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheExtremalFakePrimeMeasure

/-!
# Hoeffding degree truncation on smooth cosets and biprime variance of floor rows

Freezing the `Y`-smooth prime-power coordinates on a Chinese Remainder coset truncates the
combinatorial interaction degree of every floor sawtooth sum on `[2, K]`, while on semiprime
moduli `p q` almost all `L²` variance resides in the pure degree-2 Hoeffding interaction:

* **Prime-factor degree truncation (`card_primeFactors_gt_le_of_lt_pow`,
  `card_primeFactors_above_sqrt_le_one`, `card_primeFactors_above_cubeRoot_le_two`).** Every
  `1 ≤ k < (Y + 1)^{d+1}` has at most `d` distinct prime divisors `> Y`: at most `1` when
  `K < (Y + 1)²` and at most `2` when `K < (Y + 1)³`.
* **Exact degree-1 coset additivity above `√K` (`saw_coset_above_sqrt_eq_add_sum`).** When
  `K < (Y + 1)²`, on every coset `r ≡ z (mod smoothModulus Y K)` the sawtooth sum `saw q K r`
  splits into `F₀(z) + ∑_{p ∈ (Y, K] prime} Φ_{z,p}(r mod p)` with zero pairwise interactions.
* **Exact biprime Hoeffding ANOVA decomposition (`biprime_hoeffding_orthogonal`,
  `biprime_interaction_variance`).** For coprime `p, q ≥ 1`, the centered normalized residue
  `X(t) = (t mod pq)/(pq) - (pq - 1)/(2pq)` decomposes orthogonally on `range (pq)` into
  `M₁(t) + M₂(t) + Ψ(t)` with marginal variances `(p² - 1)/(12 p² q²)` and `(q² - 1)/(12 p² q²)`
  and pure degree-2 interaction variance `(p² - 1)(q² - 1)/(12 p² q²)`.
* **First-order Bernoulli slope nonnegativity at `θ = 0` (`IsFeasible.sum_singleton_saw_nonneg`).**
  Because `saw q K 0 = 0` and `saw q K ≥ 0` everywhere, the linear variation around `A = ∅` of any
  subset-sampled sawtooth expectation is nonnegative.
* **Coset fiber expectations, individual rough-prime positivity above `√K`, and solo-prime
  divisibility rigidity above `K / 2` (`coset_fiber_sum_mod`,
  `IsFeasible.cosetPrimeSaw_zero_nonneg`, `IsProducer.sum_multiples_prime_above_sqrt_nonpos`,
  `IsProducer.solo_prime_dvd_and_nonpos`).** On the zero smooth coset, every individual prime
  `p ∈ (Y, K]` above `√K` has `cosetPrimeSaw q Y K 0 p v ≥ 0` for all `v`, forcing
  `∑_{1 ≤ u ≤ K/p} c(u p) ≤ 0` for every prime `p > √K`; above `K / 2`, every prime `p` additionally
  satisfies `p ∣ c(p)` and `c(p) ≤ 0`.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum

open GaloisForLFunctions.ArithmeticAuxiliaryDynamics
open GaloisForLFunctions.ArithmeticKreinLangerTheory

/-! ### Part 1: Prime-factor degree bounds and coset additivity above `√K` -/

/-- Any positive integer `k < (Y + 1)^{d + 1}` has at most `d` distinct prime divisors strictly
greater than `Y`. -/
theorem card_primeFactors_gt_le_of_lt_pow {k Y d : ℕ} (hk : 1 ≤ k)
    (hlt : k < (Y + 1) ^ (d + 1)) :
    (k.primeFactors.filter (fun p => Y < p)).card ≤ d := by
  by_contra hgt
  have hge : d + 1 ≤ (k.primeFactors.filter (fun p => Y < p)).card := by omega
  obtain ⟨T, hT_sub, hT_card⟩ := exists_subset_card_eq hge
  have hT_pf : T ⊆ k.primeFactors := hT_sub.trans (filter_subset _ _)
  have hpow_le : (Y + 1) ^ (d + 1) ≤ ∏ p ∈ T, p := by
    rw [← hT_card, ← prod_const]
    refine prod_le_prod (fun _ _ => Nat.zero_le _) fun p hp => ?_
    have hpY := (mem_filter.mp (hT_sub hp)).2
    omega
  have hprod_dvd : (∏ p ∈ T, p) ∣ k :=
    (prod_dvd_prod_of_subset T k.primeFactors id hT_pf).trans (Nat.prod_primeFactors_dvd k)
  have hprod_le : ∏ p ∈ T, p ≤ k := Nat.le_of_dvd hk hprod_dvd
  omega

/-- Above `Y` with `K ≤ Y²`, every letter `1 ≤ k ≤ K` has at most `1` prime divisor `> Y`. -/
theorem card_primeFactors_above_sqrt_le_one {k K Y : ℕ} (hk1 : 1 ≤ k) (hkK : k ≤ K)
    (hKY : K < (Y + 1) ^ 2) :
    (k.primeFactors.filter (fun p => Y < p)).card ≤ 1 :=
  card_primeFactors_gt_le_of_lt_pow hk1 (lt_of_le_of_lt hkK hKY)

/-- Above `Y` with `K < (Y + 1)³`, every letter `1 ≤ k ≤ K` has at most `2` distinct prime divisors
`> Y`. -/
theorem card_primeFactors_above_cubeRoot_le_two {k K Y : ℕ} (hk1 : 1 ≤ k) (hkK : k ≤ K)
    (hKY : K < (Y + 1) ^ 3) :
    (k.primeFactors.filter (fun p => Y < p)).card ≤ 2 :=
  card_primeFactors_gt_le_of_lt_pow hk1 (lt_of_le_of_lt hkK hKY)

/-- Least common multiple of all `Y`-smooth positive integers in `[1, K]`. -/
def smoothModulus (Y K : ℕ) : ℕ :=
  ((Icc 1 K).filter (fun m => ∀ p ∈ m.primeFactors, p ≤ Y)).lcm id

theorem dvd_smoothModulus {Y K m : ℕ} (hm1 : 1 ≤ m) (hmK : m ≤ K)
    (hsmooth : ∀ p ∈ m.primeFactors, p ≤ Y) :
    m ∣ smoothModulus Y K :=
  Finset.dvd_lcm (f := id) (mem_filter.mpr ⟨mem_Icc.mpr ⟨hm1, hmK⟩, hsmooth⟩)

/-- Canonical CRT lift on `ℤ/(up)ℤ` from a fixed `u`-residue `a` and variable `p`-residue `b`: the
unique `x ∈ range (u * p)` with `x % u = a % u` and `x % p = b % p` when `Coprime u p`. -/
def crtPairLift (u p a b : ℕ) : ℕ :=
  if h : Nat.Coprime u p then (Nat.chineseRemainder h a b).val % (u * p) else 0

private lemma crtPairLift_eq_mod {u p r z : ℕ} (hcop : Nat.Coprime u p)
    (hru : r % u = z % u) :
    crtPairLift u p z (r % p) = r % (u * p) := by
  unfold crtPairLift
  rw [dif_pos hcop]
  set c := Nat.chineseRemainder hcop z (r % p)
  have hcu : c.val ≡ r [MOD u] := c.property.1.trans hru.symm
  have hcp : c.val ≡ r [MOD p] := c.property.2.trans (Nat.mod_modEq r p)
  have hcup : c.val ≡ r [MOD u * p] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hcu, hcp⟩
  change c.val % (u * p) = r % (u * p) at hcup
  exact hcup

/-- Univariate contribution of a single prime `p ∈ (Y, K]` to `saw q K` on the coset of `z`. -/
def cosetPrimeSaw (q : ℕ → ℝ) (Y K z p v : ℕ) : ℝ :=
  ∑ u ∈ (Icc 1 (K / p)).filter (fun u => ∀ l ∈ u.primeFactors, l ≤ Y),
    if u * p ∈ Icc 2 K then q (u * p) * ((crtPairLift u p z v : ℕ) : ℝ) else 0

/-- Smooth constant part of `saw q K` on the coset of `z`. -/
def cosetSmoothSaw (q : ℕ → ℝ) (Y K z : ℕ) : ℝ :=
  ∑ k ∈ (Icc 2 K).filter (fun k => ∀ l ∈ k.primeFactors, l ≤ Y), q k * ((z % k : ℕ) : ℝ)

/-- **Exact degree-1 coset additivity above `√K`.** Whenever `K < (Y + 1)²` and
`r ≡ z (mod smoothModulus Y K)`, `saw q K r` decomposes into `cosetSmoothSaw q Y K z` plus a purely
additive sum over primes `p ∈ (Y, K]` depending only on `r % p`. -/
theorem saw_coset_above_sqrt_eq_add_sum (q : ℕ → ℝ) {Y K z r : ℕ} (hKY : K < (Y + 1) ^ 2)
    (hcong : r % smoothModulus Y K = z % smoothModulus Y K) :
    saw q K r = cosetSmoothSaw q Y K z +
      ∑ p ∈ (Ioc Y K).filter Nat.Prime, cosetPrimeSaw q Y K z p (r % p) := by
  classical
  have hmod_smooth : ∀ {m : ℕ}, 1 ≤ m → m ≤ K → (∀ l ∈ m.primeFactors, l ≤ Y) → r % m = z % m := by
    intro m hm1 hmK hsm
    have hdvd := dvd_smoothModulus hm1 hmK hsm
    rw [← Nat.mod_mod_of_dvd r hdvd, hcong, Nat.mod_mod_of_dvd z hdvd]
  rw [saw]
  rw [← sum_filter_add_sum_filter_not (Icc 2 K) (fun k => ∀ l ∈ k.primeFactors, l ≤ Y)]
  have hfirst :
      ∑ k ∈ (Icc 2 K).filter (fun k => ∀ l ∈ k.primeFactors, l ≤ Y), q k * ((r % k : ℕ) : ℝ) =
        cosetSmoothSaw q Y K z := by
    unfold cosetSmoothSaw
    refine sum_congr rfl fun k hk => ?_
    obtain ⟨hkI, hsm⟩ := mem_filter.mp hk
    obtain ⟨hk2, hkK⟩ := mem_Icc.mp hkI
    rw [hmod_smooth (by omega) hkK hsm]
  rw [hfirst]
  congr 1
  set R_rough := (Icc 2 K).filter (fun k => ¬ ∀ l ∈ k.primeFactors, l ≤ Y)
  set P_large := (Ioc Y K).filter Nat.Prime
  have hrough_fact : ∀ k ∈ R_rough, ∃! p, p ∈ P_large ∧ p ∣ k := by
    intro k hk
    obtain ⟨hkI, hnot⟩ := mem_filter.mp hk
    obtain ⟨hk2, hkK⟩ := mem_Icc.mp hkI
    push Not at hnot
    obtain ⟨p, hp_pf, hpY⟩ := hnot
    have hp_prime := Nat.prime_of_mem_primeFactors hp_pf
    have hp_dvd := Nat.dvd_of_mem_primeFactors hp_pf
    have hpK : p ≤ K := (Nat.le_of_dvd (by omega) hp_dvd).trans hkK
    have hcard := card_primeFactors_above_sqrt_le_one (by omega) hkK hKY
    refine ⟨p, ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpY, hpK⟩, hp_prime⟩, hp_dvd⟩, ?_⟩
    rintro p' ⟨hp'P, hp'dvd⟩
    obtain ⟨hp'I, hp'pr⟩ := mem_filter.mp hp'P
    have hp'_mem : p' ∈ k.primeFactors.filter (fun l => Y < l) :=
      mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp'pr, hp'dvd, by omega⟩, (mem_Ioc.mp hp'I).1⟩
    have hp_mem : p ∈ k.primeFactors.filter (fun l => Y < l) :=
      mem_filter.mpr ⟨hp_pf, hpY⟩
    by_contra hne
    have htwo : 2 ≤ (k.primeFactors.filter (fun l => Y < l)).card :=
      one_lt_card.mpr ⟨p', hp'_mem, p, hp_mem, hne⟩
    omega
  have hpart : ∑ k ∈ R_rough, q k * ((r % k : ℕ) : ℝ) =
      ∑ p ∈ P_large, ∑ k ∈ R_rough.filter (fun k => p ∣ k), q k * ((r % k : ℕ) : ℝ) := by
    rw [← sum_biUnion]
    · refine sum_congr ?_ fun _ _ => rfl
      ext k
      simp only [mem_biUnion, mem_filter]
      exact ⟨fun hk => let ⟨p, ⟨hpP, hpd⟩, _⟩ := hrough_fact k hk; ⟨p, hpP, hk, hpd⟩,
        fun ⟨_, _, hk, _⟩ => hk⟩
    · intro p₁ hp₁ p₂ hp₂ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro k hk₁ hk₂
      obtain ⟨hkR, hd₁⟩ := mem_filter.mp hk₁
      obtain ⟨_, hd₂⟩ := mem_filter.mp hk₂
      obtain ⟨p, _, huniq⟩ := hrough_fact k hkR
      exact hne ((huniq p₁ ⟨hp₁, hd₁⟩).trans (huniq p₂ ⟨hp₂, hd₂⟩).symm)
  rw [hpart]
  refine sum_congr rfl fun p hp => ?_
  obtain ⟨hpI, hp_pr⟩ := mem_filter.mp hp
  obtain ⟨hpY, hpK⟩ := mem_Ioc.mp hpI
  unfold cosetPrimeSaw
  set U_p := (Icc 1 (K / p)).filter (fun u => ∀ l ∈ u.primeFactors, l ≤ Y)
  have hbij : ∑ k ∈ R_rough.filter (fun k => p ∣ k), q k * ((r % k : ℕ) : ℝ) =
      ∑ u ∈ U_p, if u * p ∈ Icc 2 K then q (u * p) * (((u * p |> (r % ·)) : ℕ) : ℝ) else 0 := by
    rw [← sum_filter]
    refine sum_nbij' (fun k => k / p) (fun u => u * p) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      have hkR : k ∈ R_rough := (mem_filter.mp hk).1
      have hpd : p ∣ k := (mem_filter.mp hk).2
      have hkI : k ∈ Icc 2 K := (mem_filter.mp hkR).1
      obtain ⟨hk2, hkK⟩ := mem_Icc.mp hkI
      clear hk hkR hkI
      obtain ⟨u, rfl⟩ := hpd
      rw [Nat.mul_comm p u, Nat.mul_div_cancel _ hp_pr.pos]
      have hu1 : 1 ≤ u := by
        rcases Nat.eq_zero_or_pos u with rfl | hu
        · simp at hk2
        · exact hu
      have hu_lt : u ≤ Y := by
        by_contra huY
        have hup : (Y + 1) ^ 2 ≤ p * u := by
          calc (Y + 1) ^ 2 = (Y + 1) * (Y + 1) := sq _
            _ ≤ p * u := Nat.mul_le_mul (by omega) (by omega)
        omega
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hu1, ?_⟩, ?_⟩, ?_⟩
      · exact (Nat.le_div_iff_mul_le hp_pr.pos).mpr (by rw [Nat.mul_comm]; exact hkK)
      · intro l hl
        exact (Nat.le_of_dvd hu1 (Nat.dvd_of_mem_primeFactors hl)).trans hu_lt
      · rw [Nat.mul_comm]
        exact mem_Icc.mpr ⟨hk2, hkK⟩
    · intro u hu
      obtain ⟨huU, huI⟩ := mem_filter.mp hu
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨huI, ?_⟩, dvd_mul_left p u⟩
      intro hall
      exact (not_le.mpr hpY) (hall p (Nat.mem_primeFactors.mpr
        ⟨hp_pr, dvd_mul_left p u, by have := (mem_Icc.mp huI).1; omega⟩))
    · intro k hk
      exact Nat.div_mul_cancel (mem_filter.mp hk).2
    · intro u _
      exact Nat.mul_div_cancel u hp_pr.pos
    · intro k hk
      rw [Nat.div_mul_cancel (mem_filter.mp hk).2]
  rw [hbij]
  refine sum_congr rfl fun u hu => ?_
  split_ifs with hupI
  · obtain ⟨huI, husm⟩ := mem_filter.mp hu
    obtain ⟨hu1, huKp⟩ := mem_Icc.mp huI
    have hupK := (mem_Icc.mp hupI).2
    have hu_le_Y : u ≤ Y := by
      by_contra huY
      have hge : (Y + 1) ^ 2 ≤ u * p := by
        calc (Y + 1) ^ 2 = (Y + 1) * (Y + 1) := sq _
          _ ≤ u * p := Nat.mul_le_mul (by omega) (by omega)
      omega
    have hcop : Nat.Coprime u p :=
      (hp_pr.coprime_iff_not_dvd.mpr fun hpu => by
        have := Nat.le_of_dvd hu1 hpu; omega).symm
    have hru : r % u = z % u := hmod_smooth hu1 (hu_le_Y.trans (by omega)) husm
    rw [crtPairLift_eq_mod hcop hru]
  · rfl

/-! ### Part 2: Exact Hoeffding ANOVA variance of `(t mod pq) / (pq)` on `ℤ/(pq)ℤ` -/

/-- Centered normalized residue `(t mod M) / M - (M - 1) / (2 M)`. -/
def centRes (M t : ℕ) : ℝ := ((t % M : ℕ) : ℝ) / (M : ℝ) - ((M : ℝ) - 1) / (2 * (M : ℝ))

private lemma sum_range_cast_id (M : ℕ) :
    ∑ j ∈ range M, (j : ℝ) = (M : ℝ) * ((M : ℝ) - 1) / 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private lemma sum_range_cast_sq (M : ℕ) :
    ∑ j ∈ range M, (j : ℝ) ^ 2 = (M : ℝ) * ((M : ℝ) - 1) * (2 * (M : ℝ) - 1) / 6 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Mean-zero property of `centRes M` over one period `range M`. -/
theorem sum_range_centRes (M : ℕ) : ∑ t ∈ range M, centRes M t = 0 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  have hMR : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hcongr : ∑ t ∈ range M, centRes M t =
      ∑ j ∈ range M, ((j : ℝ) / (M : ℝ) - ((M : ℝ) - 1) / (2 * (M : ℝ))) := by
    refine sum_congr rfl fun j hj => ?_
    unfold centRes
    rw [Nat.mod_eq_of_lt (mem_range.mp hj)]
  rw [hcongr, sum_sub_distrib, ← sum_div, sum_range_cast_id, sum_const, card_range, nsmul_eq_mul]
  field_simp
  ring

/-- Exact sum of squares of `centRes M` over `range M`. -/
theorem sum_range_centRes_sq {M : ℕ} (hM : 1 ≤ M) :
    ∑ t ∈ range M, (centRes M t) ^ 2 = ((M : ℝ) ^ 2 - 1) / (12 * (M : ℝ)) := by
  have hMR : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcongr : ∑ t ∈ range M, (centRes M t) ^ 2 =
      (1 / (4 * (M : ℝ) ^ 2)) *
        ∑ j ∈ range M, (4 * (j : ℝ) ^ 2 - 4 * ((M : ℝ) - 1) * (j : ℝ) + ((M : ℝ) - 1) ^ 2) := by
    rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    unfold centRes
    rw [Nat.mod_eq_of_lt (mem_range.mp hj)]
    field_simp
    ring
  rw [hcongr, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum,
    sum_range_cast_sq, sum_range_cast_id, sum_const, card_range, nsmul_eq_mul]
  field_simp
  ring

/-- First-coordinate Hoeffding marginal `(1 / q) · centRes p t` of `centRes (p * q) t`. -/
def biprimeMarginalLeft (p q t : ℕ) : ℝ := (1 / (q : ℝ)) * centRes p t

/-- Second-coordinate Hoeffding marginal `(1 / p) · centRes q t` of `centRes (p * q) t`. -/
def biprimeMarginalRight (p q t : ℕ) : ℝ := (1 / (p : ℝ)) * centRes q t

/-- Pure degree-2 Hoeffding interaction component of `centRes (p * q) t` on `ℤ/pℤ × ℤ/qℤ`. -/
def biprimeInteraction (p q t : ℕ) : ℝ :=
  centRes (p * q) t - biprimeMarginalLeft p q t - biprimeMarginalRight p q t

/-- Exact conditional average of `centRes (p * q)` along each `p`-fiber `a + j * p` (`a < p`). -/
theorem biprime_fiber_sum_left {p q a : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (ha : a < p) :
    ∑ j ∈ range q, centRes (p * q) (a + j * p) = centRes p a := by
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hterm : ∀ j ∈ range q, centRes (p * q) (a + j * p) =
      ((a : ℝ) + (j : ℝ) * (p : ℝ)) / ((p : ℝ) * (q : ℝ)) -
        ((p : ℝ) * (q : ℝ) - 1) / (2 * ((p : ℝ) * (q : ℝ))) := by
    intro j hj
    have hjq := mem_range.mp hj
    have hlt : a + j * p < p * q := by
      calc a + j * p < p + j * p := Nat.add_lt_add_right ha _
        _ = (j + 1) * p := by ring
        _ ≤ q * p := Nat.mul_le_mul_right p (by omega)
        _ = p * q := Nat.mul_comm q p
    unfold centRes
    rw [Nat.mod_eq_of_lt hlt]
    push_cast
    rfl
  rw [sum_congr rfl hterm, sum_sub_distrib, ← sum_div, sum_add_distrib, ← sum_mul,
    sum_range_cast_id, sum_const, sum_const, card_range, nsmul_eq_mul, nsmul_eq_mul]
  unfold centRes
  rw [Nat.mod_eq_of_lt ha]
  field_simp
  ring

private lemma sum_centRes_prog_eq_zero {p q a : ℕ} (hq : 1 ≤ q) (hcop : Nat.Coprime p q) :
    ∑ j ∈ range q, centRes q (a + j * p) = 0 := by
  have hinj : Set.InjOn (fun j : ℕ => (a + j * p) % q) (range q : Set ℕ) := by
    intro j₁ hj₁ j₂ hj₂ heq
    have h₁ : j₁ < q := mem_range.mp hj₁
    have h₂ : j₂ < q := mem_range.mp hj₂
    change (a + j₁ * p) % q = (a + j₂ * p) % q at heq
    have hmod : a + j₁ * p ≡ a + j₂ * p [MOD q] := heq
    have hmul : j₁ * p ≡ j₂ * p [MOD q] := Nat.ModEq.add_left_cancel' a hmod
    rcases le_total j₂ j₁ with hle | hle
    · have hdvd : q ∣ (j₁ - j₂) * p := by
        have hsub : j₂ * p + (j₁ - j₂) * p = j₁ * p := by
          rw [← Nat.add_mul, Nat.add_sub_of_le hle]
        have h0 : 0 + j₂ * p ≡ (j₁ - j₂) * p + j₂ * p [MOD q] := by
          rw [Nat.zero_add, Nat.add_comm ((j₁ - j₂) * p), hsub]
          exact hmul.symm
        exact Nat.dvd_of_mod_eq_zero (Nat.ModEq.add_right_cancel' (j₂ * p) h0).symm
      have hdvd' : q ∣ j₁ - j₂ := hcop.symm.dvd_of_dvd_mul_right hdvd
      have hzero : j₁ - j₂ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd' (by omega)
      omega
    · have hdvd : q ∣ (j₂ - j₁) * p := by
        have hsub : j₁ * p + (j₂ - j₁) * p = j₂ * p := by
          rw [← Nat.add_mul, Nat.add_sub_of_le hle]
        have h0 : 0 + j₁ * p ≡ (j₂ - j₁) * p + j₁ * p [MOD q] := by
          rw [Nat.zero_add, Nat.add_comm ((j₂ - j₁) * p), hsub]
          exact hmul
        exact Nat.dvd_of_mod_eq_zero (Nat.ModEq.add_right_cancel' (j₁ * p) h0).symm
      have hdvd' : q ∣ j₂ - j₁ := hcop.symm.dvd_of_dvd_mul_right hdvd
      have hzero : j₂ - j₁ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd' (by omega)
      omega
  have himg : (range q).image (fun j => (a + j * p) % q) = range q := by
    refine eq_of_subset_of_card_le (fun b hb => ?_) ?_
    · obtain ⟨j, _, rfl⟩ := mem_image.mp hb
      exact mem_range.mpr (Nat.mod_lt _ hq)
    · rw [card_image_of_injOn hinj]
  have hsum_img := sum_image (f := fun b => centRes q b) hinj
  have hcongr : ∑ j ∈ range q, centRes q ((a + j * p) % q) =
      ∑ j ∈ range q, centRes q (a + j * p) := by
    refine sum_congr rfl fun j _ => ?_
    unfold centRes
    rw [Nat.mod_mod]
  rw [← hcongr, ← hsum_img, himg, sum_range_centRes]

private lemma sum_range_mul_decomp {p q : ℕ} (hp : 1 ≤ p) (f : ℕ → ℝ) :
    ∑ t ∈ range (p * q), f t = ∑ a ∈ range p, ∑ j ∈ range q, f (a + j * p) := by
  rw [← sum_product']
  refine sum_nbij' (fun t => (t % p, t / p)) (fun x => x.1 + x.2 * p) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    have hlt := mem_range.mp ht
    refine mem_product.mpr ⟨mem_range.mpr (Nat.mod_lt t hp), mem_range.mpr ?_⟩
    exact (Nat.div_lt_iff_lt_mul hp).mpr (by rw [Nat.mul_comm]; exact hlt)
  · intro x hx
    obtain ⟨ha, hj⟩ := mem_product.mp hx
    have hap := mem_range.mp ha
    have hjq := mem_range.mp hj
    refine mem_range.mpr ?_
    calc x.1 + x.2 * p < p + x.2 * p := Nat.add_lt_add_right hap _
      _ = (x.2 + 1) * p := by ring
      _ ≤ q * p := Nat.mul_le_mul_right p (by omega)
      _ = p * q := Nat.mul_comm q p
  · intro t _
    dsimp only
    rw [Nat.mul_comm (t / p) p, Nat.mod_add_div]
  · intro x hx
    obtain ⟨ha, _⟩ := mem_product.mp hx
    have hap := mem_range.mp ha
    ext
    · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hap]
    · rw [Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hap, zero_add]
  · intro t _
    dsimp only
    rw [Nat.mul_comm (t / p) p, Nat.mod_add_div]

private lemma biprimeInteraction_fiber_sum_left {p q a : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcop : Nat.Coprime p q) (ha : a < p) :
    ∑ j ∈ range q, biprimeInteraction p q (a + j * p) = 0 := by
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold biprimeInteraction biprimeMarginalLeft biprimeMarginalRight
  rw [sum_sub_distrib, sum_sub_distrib, biprime_fiber_sum_left hp hq ha]
  have hm1 : ∑ j ∈ range q, (1 / (q : ℝ)) * centRes p (a + j * p) = centRes p a := by
    have hc : ∀ j ∈ range q, (1 / (q : ℝ)) * centRes p (a + j * p) =
        (1 / (q : ℝ)) * centRes p a := by
      intro j _
      unfold centRes
      rw [Nat.add_mul_mod_self_right]
    rw [sum_congr rfl hc, sum_const, card_range, nsmul_eq_mul]
    field_simp
  have hm2 : ∑ j ∈ range q, (1 / (p : ℝ)) * centRes q (a + j * p) = 0 := by
    rw [← mul_sum, sum_centRes_prog_eq_zero hq hcop, mul_zero]
  rw [hm1, hm2]
  ring

/-- **Pairwise orthogonality of the biprime Hoeffding decomposition** on `range (p * q)` for
coprime `p, q ≥ 1`. -/
theorem biprime_hoeffding_orthogonal {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcop : Nat.Coprime p q) :
    (∑ t ∈ range (p * q), biprimeMarginalLeft p q t * biprimeMarginalRight p q t = 0) ∧
      (∑ t ∈ range (p * q), biprimeMarginalLeft p q t * biprimeInteraction p q t = 0) ∧
      (∑ t ∈ range (p * q), biprimeMarginalRight p q t * biprimeInteraction p q t = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [sum_range_mul_decomp hp]
    refine sum_eq_zero fun a _ => ?_
    have hc : ∀ j ∈ range q,
        biprimeMarginalLeft p q (a + j * p) * biprimeMarginalRight p q (a + j * p) =
          biprimeMarginalLeft p q a * ((1 / (p : ℝ)) * centRes q (a + j * p)) := by
      intro j _
      unfold biprimeMarginalLeft biprimeMarginalRight centRes
      rw [Nat.add_mul_mod_self_right]
    rw [sum_congr rfl hc, ← mul_sum, ← mul_sum, sum_centRes_prog_eq_zero hq hcop, mul_zero,
      mul_zero]
  · rw [sum_range_mul_decomp hp]
    refine sum_eq_zero fun a ha => ?_
    have hc : ∀ j ∈ range q,
        biprimeMarginalLeft p q (a + j * p) * biprimeInteraction p q (a + j * p) =
          biprimeMarginalLeft p q a * biprimeInteraction p q (a + j * p) := by
      intro j _
      unfold biprimeMarginalLeft centRes
      rw [Nat.add_mul_mod_self_right]
    rw [sum_congr rfl hc, ← mul_sum,
      biprimeInteraction_fiber_sum_left hp hq hcop (mem_range.mp ha), mul_zero]
  · rw [Nat.mul_comm p q, sum_range_mul_decomp hq]
    refine sum_eq_zero fun b hb => ?_
    have hswap : ∀ t : ℕ, biprimeInteraction p q t = biprimeInteraction q p t := by
      intro t
      unfold biprimeInteraction biprimeMarginalLeft biprimeMarginalRight centRes
      rw [Nat.mul_comm p q]
      push_cast
      ring
    have hc : ∀ i ∈ range p,
        biprimeMarginalRight p q (b + i * q) * biprimeInteraction p q (b + i * q) =
          biprimeMarginalRight p q b * biprimeInteraction q p (b + i * q) := by
      intro i _
      rw [hswap]
      unfold biprimeMarginalRight centRes
      rw [Nat.add_mul_mod_self_right]
    rw [sum_congr rfl hc, ← mul_sum,
      biprimeInteraction_fiber_sum_left hq hp hcop.symm (mem_range.mp hb), mul_zero]

/-- Exact marginal variances of `biprimeMarginalLeft` and `biprimeMarginalRight` on `range (pq)`. -/
theorem biprime_marginal_variances {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ((1 / ((p * q : ℕ) : ℝ)) * ∑ t ∈ range (p * q), (biprimeMarginalLeft p q t) ^ 2 =
        ((p : ℝ) ^ 2 - 1) / (12 * (p : ℝ) ^ 2 * (q : ℝ) ^ 2)) ∧
      ((1 / ((p * q : ℕ) : ℝ)) * ∑ t ∈ range (p * q), (biprimeMarginalRight p q t) ^ 2 =
        ((q : ℝ) ^ 2 - 1) / (12 * (p : ℝ) ^ 2 * (q : ℝ) ^ 2)) := by
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨?_, ?_⟩
  · rw [sum_range_mul_decomp hp]
    have hc : ∀ a ∈ range p, ∑ j ∈ range q, (biprimeMarginalLeft p q (a + j * p)) ^ 2 =
        (1 / (q : ℝ)) * (centRes p a) ^ 2 := by
      intro a _
      have hjc : ∀ j ∈ range q, (biprimeMarginalLeft p q (a + j * p)) ^ 2 =
          (1 / (q : ℝ) ^ 2) * (centRes p a) ^ 2 := by
        intro j _
        unfold biprimeMarginalLeft centRes
        rw [Nat.add_mul_mod_self_right]
        ring
      rw [sum_congr rfl hjc, sum_const, card_range, nsmul_eq_mul]
      field_simp
    rw [sum_congr rfl hc, ← mul_sum, sum_range_centRes_sq hp]
    push_cast
    field_simp
  · rw [Nat.mul_comm p q, sum_range_mul_decomp hq]
    have hc : ∀ b ∈ range q, ∑ i ∈ range p, (biprimeMarginalRight p q (b + i * q)) ^ 2 =
        (1 / (p : ℝ)) * (centRes q b) ^ 2 := by
      intro b _
      have hic : ∀ i ∈ range p, (biprimeMarginalRight p q (b + i * q)) ^ 2 =
          (1 / (p : ℝ) ^ 2) * (centRes q b) ^ 2 := by
        intro i _
        unfold biprimeMarginalRight centRes
        rw [Nat.add_mul_mod_self_right]
        ring
      rw [sum_congr rfl hic, sum_const, card_range, nsmul_eq_mul]
      field_simp
    rw [sum_congr rfl hc, ← mul_sum, sum_range_centRes_sq hq]
    push_cast
    field_simp

/-- **Exact pure degree-2 Hoeffding interaction variance on `ℤ/(pq)ℤ`.** For coprime `p, q ≥ 1`,
`(1 / (pq)) ∑_{t < pq} Ψ(t)² = (p² - 1)(q² - 1) / (12 p² q²)`. -/
theorem biprime_interaction_variance {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcop : Nat.Coprime p q) :
    (1 / ((p * q : ℕ) : ℝ)) * ∑ t ∈ range (p * q), (biprimeInteraction p q t) ^ 2 =
      (((p : ℝ) ^ 2 - 1) * ((q : ℝ) ^ 2 - 1)) / (12 * (p : ℝ) ^ 2 * (q : ℝ) ^ 2) := by
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨ho12, ho1Ψ, ho2Ψ⟩ := biprime_hoeffding_orthogonal hp hq hcop
  obtain ⟨hm1, hm2⟩ := biprime_marginal_variances hp hq
  have hpyth : ∑ t ∈ range (p * q), (centRes (p * q) t) ^ 2 =
      (∑ t ∈ range (p * q), (biprimeMarginalLeft p q t) ^ 2) +
        (∑ t ∈ range (p * q), (biprimeMarginalRight p q t) ^ 2) +
        (∑ t ∈ range (p * q), (biprimeInteraction p q t) ^ 2) := by
    have hpt : ∀ t : ℕ, (centRes (p * q) t) ^ 2 =
        (biprimeMarginalLeft p q t) ^ 2 + (biprimeMarginalRight p q t) ^ 2 +
          (biprimeInteraction p q t) ^ 2 +
          2 * (biprimeMarginalLeft p q t * biprimeMarginalRight p q t) +
          2 * (biprimeMarginalLeft p q t * biprimeInteraction p q t) +
          2 * (biprimeMarginalRight p q t * biprimeInteraction p q t) := by
      intro t
      unfold biprimeInteraction
      ring
    simp_rw [hpt, sum_add_distrib, ← mul_sum, ho12, ho1Ψ, ho2Ψ]
    ring
  have htot : (1 / ((p * q : ℕ) : ℝ)) * ∑ t ∈ range (p * q), (centRes (p * q) t) ^ 2 =
      ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 - 1) / (12 * (p : ℝ) ^ 2 * (q : ℝ) ^ 2) := by
    rw [sum_range_centRes_sq (Nat.mul_pos hp hq)]
    push_cast
    field_simp
  have hmul_pyth := congrArg (fun x : ℝ => (1 / ((p * q : ℕ) : ℝ)) * x) hpyth
  rw [mul_add, mul_add, htot, hm1, hm2] at hmul_pyth
  have hsub :
      (1 / ((p * q : ℕ) : ℝ)) * ∑ t ∈ range (p * q), (biprimeInteraction p q t) ^ 2 =
        ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 - 1) / (12 * (p : ℝ) ^ 2 * (q : ℝ) ^ 2) -
          ((p : ℝ) ^ 2 - 1) / (12 * (p : ℝ) ^ 2 * (q : ℝ) ^ 2) -
          ((q : ℝ) ^ 2 - 1) / (12 * (p : ℝ) ^ 2 * (q : ℝ) ^ 2) := by
    linarith [hmul_pyth]
  rw [hsub]
  field_simp
  ring

/-! ### Part 3: First-order Bernoulli slope nonnegativity at `θ = 0` -/

/-- Because `saw q K 0 = 0` and every feasible sawtooth is nonnegative, the first-order Bernoulli
slope around `A = ∅` (`∑_{i ∈ I} saw q K (r i)`) is nonnegative for every index family. -/
theorem _root_.GaloisForLFunctions.ArithmeticAuxiliaryDynamics.IsFeasible.sum_singleton_saw_nonneg
    {K : ℕ} {S : Finset ℕ} {q : ℕ → ℝ} (hF : IsFeasible K S q)
    {ι : Type*} (I : Finset ι) (r : ι → ℕ) :
    saw q K 0 = 0 ∧ 0 ≤ ∑ i ∈ I, saw q K (r i) :=
  ⟨saw_zero q K, sum_nonneg fun i _ => hF.saw_nonneg (r i)⟩

/-! ### Part 4: Coset fiber expectations, rough-prime positivity above `√K`, and solo-prime rigidity -/

/-- **General coset conditional expectation identity.** Freezing the `k₁`-residue at `a < k₁`
collapses `(a + j * k₁) mod (k₁ * k₂)` in expectation over `j ∈ range k₂` to
`a + k₁ * (k₂ - 1) / 2`. -/
theorem coset_fiber_sum_mod {k₁ k₂ a : ℕ} (hk₂ : 1 ≤ k₂) (ha : a < k₁) :
    ∑ j ∈ range k₂, (((a + j * k₁) % (k₁ * k₂) : ℕ) : ℝ) =
      (k₂ : ℝ) * ((a : ℝ) + (k₁ : ℝ) * ((k₂ : ℝ) - 1) / 2) := by
  have hcongr : ∑ j ∈ range k₂, (((a + j * k₁) % (k₁ * k₂) : ℕ) : ℝ) =
      ∑ j ∈ range k₂, ((a : ℝ) + (j : ℝ) * (k₁ : ℝ)) := by
    refine sum_congr rfl fun j hj => ?_
    have hjlt := mem_range.mp hj
    have hlt : a + j * k₁ < k₁ * k₂ := by
      calc a + j * k₁ < k₁ + j * k₁ := Nat.add_lt_add_right ha _
        _ = (j + 1) * k₁ := by ring
        _ ≤ k₂ * k₁ := Nat.mul_le_mul_right k₁ (by omega)
        _ = k₁ * k₂ := Nat.mul_comm k₂ k₁
    rw [Nat.mod_eq_of_lt hlt]
    push_cast
    rfl
  rw [hcongr, sum_add_distrib, ← sum_mul, sum_range_cast_id, sum_const, card_range, nsmul_eq_mul]
  have hk₂R : (k₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

private lemma coprime_prod_right {ι : Type*} {p : ℕ} {s : Finset ι} {f : ι → ℕ}
    (h : ∀ x ∈ s, p.Coprime (f x)) : p.Coprime (∏ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (mem_insert_self a s)).mul_right (ih fun x hx => h x (mem_insert_of_mem hx))

private lemma dvd_prod_id {s : Finset ℕ} {x : ℕ} (hx : x ∈ s) : x ∣ ∏ y ∈ s, y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hx
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    rcases mem_insert.mp hx with rfl | hxs
    · exact dvd_mul_right _ _
    · exact (ih hxs).trans (dvd_mul_left _ _)

private lemma crtPairLift_zero_zero (u p : ℕ) : crtPairLift u p 0 0 = 0 := by
  by_cases hcop : Nat.Coprime u p
  · have h := crtPairLift_eq_mod (r := 0) (z := 0) hcop rfl
    simpa using h
  · simp [crtPairLift, hcop]

private lemma crtPairLift_mod_right (u p z v : ℕ) :
    crtPairLift u p z (v % p) = crtPairLift u p z v := by
  by_cases hcop : Nat.Coprime u p
  · unfold crtPairLift
    rw [dif_pos hcop, dif_pos hcop]
    set c₁ := Nat.chineseRemainder hcop z (v % p)
    set c₂ := Nat.chineseRemainder hcop z v
    have h1 : c₁.val ≡ c₂.val [MOD u] := c₁.property.1.trans c₂.property.1.symm
    have h2 : c₁.val ≡ c₂.val [MOD p] :=
      (c₁.property.2.trans (Nat.mod_modEq v p)).trans c₂.property.2.symm
    have h12 : c₁.val ≡ c₂.val [MOD u * p] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h1, h2⟩
    change c₁.val % (u * p) = c₂.val % (u * p) at h12
    exact h12
  · simp [crtPairLift, hcop]

/-- **Individual rough-prime coset nonnegativity above `√K`.** When `K < (Y + 1)²`, on the zero
`Y`-smooth coset every individual prime `p₀ ∈ (Y, K]` satisfies `0 ≤ cosetPrimeSaw q Y K 0 p₀ v`
for every residue `v`. -/
theorem _root_.GaloisForLFunctions.ArithmeticAuxiliaryDynamics.IsFeasible.cosetPrimeSaw_zero_nonneg
    {K : ℕ} {S : Finset ℕ} {q : ℕ → ℝ} (hF : IsFeasible K S q)
    {Y p₀ : ℕ} (hKY : K < (Y + 1) ^ 2) (hp₀ : p₀.Prime) (hpY : Y < p₀) (hpK : p₀ ≤ K)
    (v : ℕ) :
    0 ≤ cosetPrimeSaw q Y K 0 p₀ v := by
  classical
  set S_sm := (Icc 1 K).filter (fun m => ∀ l ∈ m.primeFactors, l ≤ Y)
  set P_oth := ((Ioc Y K).filter Nat.Prime).erase p₀
  set M_oth := (∏ m ∈ S_sm, m) * (∏ p ∈ P_oth, p)
  have hcop_sm : p₀.Coprime (∏ m ∈ S_sm, m) := by
    refine coprime_prod_right fun m hm => ?_
    obtain ⟨hmI, hsm⟩ := mem_filter.mp hm
    have hm1 := (mem_Icc.mp hmI).1
    exact hp₀.coprime_iff_not_dvd.mpr fun hd =>
      (not_le.mpr hpY) (hsm p₀ (Nat.mem_primeFactors.mpr ⟨hp₀, hd, by omega⟩))
  have hcop_oth : p₀.Coprime (∏ p ∈ P_oth, p) := by
    refine coprime_prod_right fun p hp => ?_
    have hne : p ≠ p₀ := ne_of_mem_erase hp
    have hp_pr : p.Prime := (mem_filter.mp (mem_of_mem_erase hp)).2
    exact hp₀.coprime_iff_not_dvd.mpr fun hd =>
      hne (((Nat.dvd_prime hp_pr).mp hd).resolve_left hp₀.ne_one).symm
  have hcop : p₀.Coprime M_oth := hcop_sm.mul_right hcop_oth
  set r := (Nat.chineseRemainder hcop v 0).val
  have hr_M : M_oth ∣ r := Nat.dvd_of_mod_eq_zero (Nat.chineseRemainder hcop v 0).property.2
  have hsm_dvd : smoothModulus Y K ∣ M_oth :=
    (Finset.lcm_dvd fun m hm => dvd_prod_id hm).trans (dvd_mul_right _ _)
  have hr_sm : r % smoothModulus Y K = 0 % smoothModulus Y K := by
    rw [Nat.mod_eq_zero_of_dvd (hsm_dvd.trans hr_M), Nat.zero_mod]
  have hsaw := saw_coset_above_sqrt_eq_add_sum q hKY hr_sm
  have h0_sm : cosetSmoothSaw q Y K 0 = 0 := by simp [cosetSmoothSaw]
  have hsum_eq : ∑ p ∈ (Ioc Y K).filter Nat.Prime, cosetPrimeSaw q Y K 0 p (r % p) =
      cosetPrimeSaw q Y K 0 p₀ v := by
    rw [sum_eq_single p₀]
    · have hrp₀ : r % p₀ = v % p₀ := (Nat.chineseRemainder hcop v 0).property.1
      unfold cosetPrimeSaw
      simp_rw [hrp₀, crtPairLift_mod_right]
    · intro p hp hne
      have hp_er : p ∈ P_oth := mem_erase.mpr ⟨hne, hp⟩
      have hp_dvd : p ∣ M_oth := (dvd_prod_id hp_er).trans (dvd_mul_left _ _)
      have hrp : r % p = 0 := Nat.mod_eq_zero_of_dvd (hp_dvd.trans hr_M)
      simp [cosetPrimeSaw, hrp, crtPairLift_zero_zero]
    · intro hnot
      exact absurd (mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpY, hpK⟩, hp₀⟩) hnot
  have hnn := hF.saw_nonneg r
  rw [hsaw, h0_sm, zero_add, hsum_eq] at hnn
  exact hnn

private lemma sum_crtPairLift_zero_range {u p : ℕ} (hu1 : 1 ≤ u) (hp : p.Prime) (hu : u < p) :
    ∑ v ∈ range p, ((crtPairLift u p 0 v : ℕ) : ℝ) =
      ((p : ℝ) * ((p : ℝ) - 1) / 2) * (u : ℝ) := by
  have hcop : Nat.Coprime u p :=
    (hp.coprime_iff_not_dvd.mpr fun hd => by have := Nat.le_of_dvd hu1 hd; omega).symm
  have hinj : Set.InjOn (fun j : ℕ => (j * u) % p) (range p : Set ℕ) := by
    intro j₁ hj₁ j₂ hj₂ heq
    have h₁ : j₁ < p := mem_range.mp hj₁
    have h₂ : j₂ < p := mem_range.mp hj₂
    change (j₁ * u) % p = (j₂ * u) % p at heq
    have hmul : j₁ * u ≡ j₂ * u [MOD p] := heq
    rcases le_total j₂ j₁ with hle | hle
    · have hdvd : p ∣ (j₁ - j₂) * u := by
        have hsub : j₂ * u + (j₁ - j₂) * u = j₁ * u := by
          rw [← Nat.add_mul, Nat.add_sub_of_le hle]
        have h0 : 0 + j₂ * u ≡ (j₁ - j₂) * u + j₂ * u [MOD p] := by
          rw [Nat.zero_add, Nat.add_comm ((j₁ - j₂) * u), hsub]
          exact hmul.symm
        exact Nat.dvd_of_mod_eq_zero (Nat.ModEq.add_right_cancel' (j₂ * u) h0).symm
      have hdvd' : p ∣ j₁ - j₂ := hcop.symm.dvd_of_dvd_mul_right hdvd
      have hzero : j₁ - j₂ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd' (by omega)
      omega
    · have hdvd : p ∣ (j₂ - j₁) * u := by
        have hsub : j₁ * u + (j₂ - j₁) * u = j₂ * u := by
          rw [← Nat.add_mul, Nat.add_sub_of_le hle]
        have h0 : 0 + j₁ * u ≡ (j₂ - j₁) * u + j₁ * u [MOD p] := by
          rw [Nat.zero_add, Nat.add_comm ((j₂ - j₁) * u), hsub]
          exact hmul
        exact Nat.dvd_of_mod_eq_zero (Nat.ModEq.add_right_cancel' (j₁ * u) h0).symm
      have hdvd' : p ∣ j₂ - j₁ := hcop.symm.dvd_of_dvd_mul_right hdvd
      have hzero : j₂ - j₁ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd' (by omega)
      omega
  have himg : (range p).image (fun j => (j * u) % p) = range p := by
    refine eq_of_subset_of_card_le (fun b hb => ?_) ?_
    · obtain ⟨j, _, rfl⟩ := mem_image.mp hb
      exact mem_range.mpr (Nat.mod_lt _ hp.pos)
    · rw [card_image_of_injOn hinj]
  have hsum_img := sum_image (f := fun v => ((crtPairLift u p 0 v : ℕ) : ℝ)) hinj
  rw [← himg, hsum_img]
  have hterm : ∀ j ∈ range p, ((crtPairLift u p 0 ((j * u) % p) : ℕ) : ℝ) = (j : ℝ) * (u : ℝ) := by
    intro j hj
    have hjlt := mem_range.mp hj
    have hru : (j * u) % u = 0 % u := by rw [Nat.mul_mod_left, Nat.zero_mod]
    rw [crtPairLift_eq_mod hcop hru]
    have hlt : j * u < u * p := by
      calc j * u < p * u := Nat.mul_lt_mul_of_pos_right hjlt hu1
        _ = u * p := Nat.mul_comm p u
    rw [Nat.mod_eq_of_lt hlt]
    push_cast
    rfl
  rw [sum_congr rfl hterm, ← sum_mul, sum_range_cast_id]

/-- **Weighted multiple nonnegativity for every prime `p > √K`.** For any feasible sawtooth `q` on
`[2, K]` and every prime `p ≤ K` with `K < p²`, `0 ≤ ∑_{u=1}^{K/p} u · q(u p)`. -/
theorem _root_.GaloisForLFunctions.ArithmeticAuxiliaryDynamics.IsFeasible.sum_multiples_prime_above_sqrt_nonneg
    {K : ℕ} {S : Finset ℕ} {q : ℕ → ℝ} (hF : IsFeasible K S q)
    {p : ℕ} (hp : p.Prime) (hpK : p ≤ K) (hp2 : K < p ^ 2) :
    0 ≤ ∑ u ∈ Icc 1 (K / p), (u : ℝ) * q (u * p) := by
  have hp_ge2 := hp.two_le
  have hKY : K < (p - 1 + 1) ^ 2 := by
    rwa [Nat.sub_add_cancel hp.one_le]
  have hsum_nn : 0 ≤ ∑ v ∈ range p, cosetPrimeSaw q (p - 1) K 0 p v :=
    sum_nonneg fun v _ => hF.cosetPrimeSaw_zero_nonneg hKY hp (by omega) hpK v
  have hfilt : (Icc 1 (K / p)).filter (fun u => ∀ l ∈ u.primeFactors, l ≤ p - 1) = Icc 1 (K / p) := by
    refine filter_true_of_mem fun u hu => ?_
    obtain ⟨hu1, huKp⟩ := mem_Icc.mp hu
    have hup_le : u * p ≤ K := Nat.mul_le_of_le_div p u K huKp
    have hu_lt_p : u < p := by
      by_contra hge
      have hsq : p ^ 2 ≤ u * p := by
        calc p ^ 2 = p * p := sq p
          _ ≤ u * p := Nat.mul_le_mul_right p (by omega)
      omega
    intro l hl
    exact (Nat.le_of_dvd hu1 (Nat.dvd_of_mem_primeFactors hl)).trans (by omega)
  have hrew : ∀ v ∈ range p, cosetPrimeSaw q (p - 1) K 0 p v =
      ∑ u ∈ Icc 1 (K / p), q (u * p) * ((crtPairLift u p 0 v : ℕ) : ℝ) := by
    intro v _
    unfold cosetPrimeSaw
    rw [hfilt]
    refine sum_congr rfl fun u hu => ?_
    obtain ⟨hu1, huKp⟩ := mem_Icc.mp hu
    have hup_le : u * p ≤ K := Nat.mul_le_of_le_div p u K huKp
    have hup_ge : 2 ≤ u * p := by nlinarith
    rw [if_pos (mem_Icc.mpr ⟨hup_ge, hup_le⟩)]
  rw [sum_congr rfl hrew, sum_comm] at hsum_nn
  have heval : ∑ u ∈ Icc 1 (K / p), ∑ v ∈ range p, q (u * p) * ((crtPairLift u p 0 v : ℕ) : ℝ) =
      ((p : ℝ) * ((p : ℝ) - 1) / 2) * ∑ u ∈ Icc 1 (K / p), (u : ℝ) * q (u * p) := by
    rw [mul_sum]
    refine sum_congr rfl fun u hu => ?_
    obtain ⟨hu1, huKp⟩ := mem_Icc.mp hu
    have hup_le : u * p ≤ K := Nat.mul_le_of_le_div p u K huKp
    have hu_lt_p : u < p := by
      by_contra hge
      have hsq : p ^ 2 ≤ u * p := by
        calc p ^ 2 = p * p := sq p
          _ ≤ u * p := Nat.mul_le_mul_right p (by omega)
      omega
    rw [← mul_sum, sum_crtPairLift_zero_range hu1 hp hu_lt_p]
    ring
  rw [heval] at hsum_nn
  have hpos : 0 < (p : ℝ) * ((p : ℝ) - 1) / 2 := by
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_ge2
    nlinarith
  exact nonneg_of_mul_nonneg_right hsum_nn hpos

private lemma stepWeight_eq_saw {c : ℕ →₀ ℤ} {m B K : ℕ} (hP : IsProducer c m B)
    (hK : AlphabetLE c K) (r : ℕ) :
    (stepWeight c r : ℝ) = saw (fun k => -(c k : ℝ) / (k : ℝ)) K r := by
  classical
  rw [stepWeight_eq_sum_mod hP.zero hP.balanced, saw]
  have h1 : ∑ k ∈ c.support, (-(c k : ℝ) / k) * ((r % k : ℕ) : ℝ) =
      ∑ k ∈ c.support.filter (fun k => 2 ≤ k), (-(c k : ℝ) / k) * ((r % k : ℕ) : ℝ) := by
    symm
    refine sum_subset (filter_subset _ _) fun k hk hnot => ?_
    have hk0 : k ≠ 0 := fun h => Finsupp.mem_support_iff.mp hk (h ▸ hP.zero)
    have hk1 : k = 1 := by
      by_contra hne
      exact hnot (mem_filter.mpr ⟨hk, by omega⟩)
    subst hk1
    simp [Nat.mod_one]
  rw [h1]
  refine sum_subset (fun k hk => ?_) (fun k hkI hnot => ?_)
  · obtain ⟨hks, hk2⟩ := mem_filter.mp hk
    exact mem_Icc.mpr ⟨hk2, hK k hks⟩
  · have hc0 : c k = 0 := by
      by_contra hne
      exact hnot (mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne, (mem_Icc.mp hkI).1⟩)
    simp [hc0]

private lemma isFeasible_empty_of_isProducer {c : ℕ →₀ ℤ} {m B K : ℕ} (hP : IsProducer c m B)
    (hK : AlphabetLE c K) :
    IsFeasible K ∅ (fun k => -(c k : ℝ) / (k : ℝ)) where
  nonneg r _ _ := by
    rw [← stepWeight_eq_saw hP hK r]
    exact_mod_cast hP.nonneg r
  target _ hr := by simp at hr

/-- **Rough-prime multiple sum nonpositivity above `√K` for integer producers.** For every producer
`(c, m, B)` on `[1, K]` and every prime `p` with `K < p²`, `∑_{u=1}^{K/p} c(u p) ≤ 0`. -/
theorem _root_.GaloisForLFunctions.ArithmeticAuxiliaryDynamics.IsProducer.sum_multiples_prime_above_sqrt_nonpos
    {c : ℕ →₀ ℤ} {m B K p : ℕ} (hP : IsProducer c m B) (hK : AlphabetLE c K)
    (hp : p.Prime) (hp2 : K < p ^ 2) :
    ∑ u ∈ Icc 1 (K / p), c (u * p) ≤ 0 := by
  by_cases hpK : p ≤ K
  · have hnn := (isFeasible_empty_of_isProducer hP hK).sum_multiples_prime_above_sqrt_nonneg hp hpK hp2
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    have hmul : 0 ≤ (p : ℝ) * ∑ u ∈ Icc 1 (K / p), (u : ℝ) * (-(c (u * p) : ℝ) / ((u * p : ℕ) : ℝ)) :=
      mul_nonneg hpR.le hnn
    have hsimp : (p : ℝ) * ∑ u ∈ Icc 1 (K / p), (u : ℝ) * (-(c (u * p) : ℝ) / ((u * p : ℕ) : ℝ)) =
        -((∑ u ∈ Icc 1 (K / p), c (u * p) : ℤ) : ℝ) := by
      rw [mul_sum, Int.cast_sum, ← sum_neg_distrib]
      refine sum_congr rfl fun u hu => ?_
      have hu1 := (mem_Icc.mp hu).1
      have huR : (u : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hpR' : (p : ℝ) ≠ 0 := hpR.ne'
      push_cast
      field_simp
    rw [hsimp] at hmul
    have hR : ((∑ u ∈ Icc 1 (K / p), c (u * p) : ℤ) : ℝ) ≤ 0 := by linarith
    exact_mod_cast hR
  · have hdiv0 : K / p = 0 := Nat.div_eq_of_lt (by omega)
    simp [hdiv0]

/-- **Solo-prime sign rigidity above `K / 2` for feasible LP weights.** Every prime `p ∈ (K/2, K]`
has `0 ≤ q p`. -/
theorem _root_.GaloisForLFunctions.ArithmeticAuxiliaryDynamics.IsFeasible.solo_prime_nonneg
    {K : ℕ} {S : Finset ℕ} {q : ℕ → ℝ} (hF : IsFeasible K S q)
    {p : ℕ} (hp : p.Prime) (hpK : p ≤ K) (hp2 : K < 2 * p) :
    0 ≤ q p := by
  have hp_sq : K < p ^ 2 := by
    have hp_ge2 := hp.two_le
    nlinarith
  have hdiv1 : K / p = 1 := by
    refine le_antisymm ?_ ((Nat.le_div_iff_mul_le hp.pos).mpr (by omega))
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hp.pos).mpr (by omega))
  have hnn := hF.sum_multiples_prime_above_sqrt_nonneg hp hpK hp_sq
  rw [hdiv1] at hnn
  simpa using hnn

/-- **Solo-prime divisibility and sign rigidity above `K / 2` for integer producers.** For every
producer `(c, m, B)` on `[1, K]` and every prime `p` with `K < 2 * p`, `p ∣ c(p)` and `c(p) ≤ 0`. -/
theorem _root_.GaloisForLFunctions.ArithmeticAuxiliaryDynamics.IsProducer.solo_prime_dvd_and_nonpos
    {c : ℕ →₀ ℤ} {m B K p : ℕ} (hP : IsProducer c m B) (hK : AlphabetLE c K)
    (hp : p.Prime) (hp2 : K < 2 * p) :
    (p : ℤ) ∣ c p ∧ c p ≤ 0 := by
  classical
  by_cases hpK : p ≤ K
  · set P_oth := (Icc 2 K).erase p
    set M := ∏ k ∈ P_oth, k
    have hcop : p.Coprime M := by
      refine coprime_prod_right fun k hk => ?_
      have hne : k ≠ p := ne_of_mem_erase hk
      obtain ⟨hk2, hkK⟩ := mem_Icc.mp (mem_of_mem_erase hk)
      refine hp.coprime_iff_not_dvd.mpr fun hd => ?_
      obtain ⟨d, rfl⟩ := hd
      have hd0 : d ≠ 0 := by rintro rfl; simp at hk2
      have hd1 : d ≠ 1 := fun h => hne (by rw [h, mul_one])
      have hge : 2 * p ≤ p * d := by
        calc 2 * p ≤ d * p := Nat.mul_le_mul_right p (by omega)
          _ = p * d := Nat.mul_comm d p
      omega
    set r := (Nat.chineseRemainder hcop (p - 1) 0).val
    have hrp : r % p = p - 1 := by
      have h1 : r % p = (p - 1) % p := (Nat.chineseRemainder hcop (p - 1) 0).property.1
      rw [h1, Nat.mod_eq_of_lt (by have := hp.two_le; omega)]
    have hrM : M ∣ r := Nat.dvd_of_mod_eq_zero (Nat.chineseRemainder hcop (p - 1) 0).property.2
    have hstep_p : (stepWeight c r : ℝ) = (-(c p : ℝ) / (p : ℝ)) * ((p - 1 : ℕ) : ℝ) := by
      rw [stepWeight_eq_saw hP hK r, saw, sum_eq_single p]
      · rw [hrp]
      · intro k hk hne
        have hkM : k ∣ M := dvd_prod_id (mem_erase.mpr ⟨hne, hk⟩)
        rw [Nat.mod_eq_zero_of_dvd (hkM.trans hrM)]
        simp
      · intro hnot
        exact absurd (mem_Icc.mpr ⟨hp.two_le, hpK⟩) hnot
    have hpR_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hmulR : ((p : ℤ) * stepWeight c r : ℝ) = ((-c p * ((p : ℤ) - 1) : ℤ) : ℝ) := by
      push_cast
      rw [hstep_p, Nat.cast_sub hp.one_le]
      push_cast
      field_simp
    have hmulZ : (p : ℤ) * stepWeight c r = -c p * ((p : ℤ) - 1) := by exact_mod_cast hmulR
    have hdvd : (p : ℤ) ∣ c p := ⟨c p + stepWeight c r, by linarith⟩
    have hnn : 0 ≤ stepWeight c r := hP.nonneg r
    have hpZ : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    have hnonpos : c p ≤ 0 := by nlinarith
    exact ⟨hdvd, hnonpos⟩
  · have hcp : c p = 0 := by
      by_contra hne
      have := hK p (Finsupp.mem_support_iff.mpr hne)
      omega
    exact ⟨⟨0, by simp [hcp]⟩, by simp [hcp]⟩

#print axioms card_primeFactors_gt_le_of_lt_pow
#print axioms card_primeFactors_above_sqrt_le_one
#print axioms card_primeFactors_above_cubeRoot_le_two
#print axioms saw_coset_above_sqrt_eq_add_sum
#print axioms biprime_hoeffding_orthogonal
#print axioms biprime_marginal_variances
#print axioms biprime_interaction_variance
#print axioms GaloisForLFunctions.ArithmeticAuxiliaryDynamics.IsFeasible.sum_singleton_saw_nonneg
#print axioms coset_fiber_sum_mod
#print axioms GaloisForLFunctions.ArithmeticAuxiliaryDynamics.IsFeasible.cosetPrimeSaw_zero_nonneg
#print axioms GaloisForLFunctions.ArithmeticAuxiliaryDynamics.IsFeasible.sum_multiples_prime_above_sqrt_nonneg
#print axioms GaloisForLFunctions.ArithmeticAuxiliaryDynamics.IsProducer.sum_multiples_prime_above_sqrt_nonpos
#print axioms GaloisForLFunctions.ArithmeticAuxiliaryDynamics.IsFeasible.solo_prime_nonneg
#print axioms GaloisForLFunctions.ArithmeticAuxiliaryDynamics.IsProducer.solo_prime_dvd_and_nonpos

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum

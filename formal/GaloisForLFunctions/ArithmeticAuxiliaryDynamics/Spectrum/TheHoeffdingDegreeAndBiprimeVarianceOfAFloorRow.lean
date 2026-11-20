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
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum

open GaloisForLFunctions.ArithmeticAuxiliaryDynamics

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
  (Nat.chineseRemainder (a := a) (b := b)
    (if h : Nat.Coprime u p then h else Nat.coprime_one_left p) : ℕ) % (u * p)

private lemma crtPairLift_eq_mod {u p r z : ℕ} (hu : 0 < u) (hp : 0 < p) (hcop : Nat.Coprime u p)
    (hru : r % u = z % u) :
    crtPairLift u p z (r % p) = r % (u * p) := by
  unfold crtPairLift
  rw [dif_pos hcop]
  set c := Nat.chineseRemainder hcop z (r % p)
  have hcu : c.val ≡ r [MOD u] := c.property.1.trans hru.symm
  have hcp : c.val ≡ r [MOD p] := c.property.2.trans (Nat.mod_modEq r p)
  have hcup : c.val ≡ r [MOD u * p] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hcu, hcp⟩
  exact hcup.symm

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
      obtain ⟨⟨hkI, _⟩, hpd⟩ := mem_filter.mp hk
      obtain ⟨hk2, hkK⟩ := mem_Icc.mp hkI
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
      · rwa [Nat.mul_comm]
    · intro u hu
      obtain ⟨huU, huI⟩ := mem_filter.mp hu
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨huI, ?_⟩, ⟨u, Nat.mul_comm p u⟩⟩
      intro hall
      exact (not_le.mpr hpY) (hall p (Nat.mem_primeFactors.mpr
        ⟨hp_pr, ⟨u, Nat.mul_comm p u⟩, by have := (mem_Icc.mp huI).1; omega⟩))
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
    rw [crtPairLift_eq_mod hu1 hp_pr.pos hcop hru]
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
    rw [Nat.mul_comm, Nat.div_add_mod]
  · intro x hx
    obtain ⟨ha, _⟩ := mem_product.mp hx
    have hap := mem_range.mp ha
    ext
    · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hap]
    · rw [Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hap, zero_add]
  · intro _ _
    rfl

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
      rw [Nat.add_mul_mod_self_right, Nat.mod_mod]
    rw [sum_congr rfl hc, ← mul_sum, ← mul_sum, sum_centRes_prog_eq_zero hq hcop, mul_zero,
      mul_zero]
  · rw [sum_range_mul_decomp hp]
    refine sum_eq_zero fun a ha => ?_
    have hc : ∀ j ∈ range q,
        biprimeMarginalLeft p q (a + j * p) * biprimeInteraction p q (a + j * p) =
          biprimeMarginalLeft p q a * biprimeInteraction p q (a + j * p) := by
      intro j _
      unfold biprimeMarginalLeft centRes
      rw [Nat.add_mul_mod_self_right, Nat.mod_mod]
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
      rw [Nat.add_mul_mod_self_right, Nat.mod_mod]
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
        rw [Nat.add_mul_mod_self_right, Nat.mod_mod]
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
        rw [Nat.add_mul_mod_self_right, Nat.mod_mod]
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
  dsimp only at hmul_pyth
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

#print axioms card_primeFactors_gt_le_of_lt_pow
#print axioms card_primeFactors_above_sqrt_le_one
#print axioms card_primeFactors_above_cubeRoot_le_two
#print axioms saw_coset_above_sqrt_eq_add_sum
#print axioms biprime_hoeffding_orthogonal
#print axioms biprime_marginal_variances
#print axioms biprime_interaction_variance
#print axioms GaloisForLFunctions.ArithmeticAuxiliaryDynamics.IsFeasible.sum_singleton_saw_nonneg

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum

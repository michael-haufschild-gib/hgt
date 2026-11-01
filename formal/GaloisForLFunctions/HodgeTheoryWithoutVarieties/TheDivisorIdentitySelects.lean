import GaloisForLFunctions.HodgeTheoryWithoutVarieties.StarsAreLowerHorizons

/-!
# The divisor identity selects the weight

The star of `d` is a copy of the lower horizon for every weight `λ`
(`dilationForm_starRestrict`). The counterterm, i.e. the degree diagonal, is a copy too exactly
when the boundary flux `flux(d, m) = (λ ∗ 1)(dm) − (λ ∗ 1)(m)` does not depend on the vertex `m`
of the star. Call such a weight **self-similar** (`SelfSimilarFlux`). For Weil's weight the flux is
`log d` (`starFlux_vonMangoldt`), because `Λ ∗ 1 = log`.

**Classification** (`selfSimilarFlux_iff`). A weight is self-similar iff it is a *generalized von
Mangoldt function*:
- it vanishes on every `n > 1` that is not a prime power;
- it is constant along every prime tower, `λ(p^k) = λ(p)` for `k ≥ 1`.

In that case `λ ∗ 1 − λ(1)` is completely additive and the flux is `Σ_p v_p(d) λ(p)`. The mechanism
is the **one-prime step** (`inDegree_mul_prime_sub`):
- the divisors of `pn` that do not divide `n` contain exactly one prime power, `p^{v_p(n)+1}`;
- the flux through one prime is therefore `λ(p)`, whatever `n` is.

**Twists** (`selfSimilarFlux_twist_iff`). For a completely multiplicative twist `ω` with
`ω(p) ≠ 0`, the weight `Λω` is self-similar iff `ω(p) = 1` for every prime. On the tower,
`λ(p²) = λ(p)` reads `ω(p)² = ω(p)`. So every prime flip, the Liouville twist and every other
nontrivial twist break the self-similarity of the counterterm. Among twists, `ζ` alone has a
counterterm that is a copy of itself on every star.
-/

noncomputable section

open Finset ArithmeticFunction

namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

/-- **Self-similar counterterm**: the boundary flux into every star is constant along the star. -/
def SelfSimilarFlux (lam : ℕ → ℝ) : Prop :=
  ∀ d m : ℕ, 0 < d → 0 < m → starFlux lam d m = starFlux lam d 1

/-- **Weil's weight is self-similar.** -/
theorem selfSimilarFlux_vonMangoldt : SelfSimilarFlux fun k => Λ k := fun d m hd hm => by
  rw [starFlux_vonMangoldt hd hm, starFlux_vonMangoldt hd one_pos]

/-! ### The one-prime step -/

/-- A prime power dividing `pn` but not `n` is `p^{v_p(n)+1}`. -/
theorem eq_pow_of_mem_sdiff_divisors {p n e : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (he : e ∈ (p * n).divisors \ n.divisors) (hpp : IsPrimePow e) :
    e = p ^ (n.factorization p + 1) := by
  obtain ⟨q, j, hq, hj, rfl⟩ := (isPrimePow_nat_iff e).mp hpp
  have hpn : p * n ≠ 0 := mul_ne_zero hp.ne_zero hn
  simp only [mem_sdiff, Nat.mem_divisors] at he
  obtain ⟨⟨hdvd, -⟩, hndvd⟩ := he
  have hndvd' : ¬ q ^ j ∣ n := fun h => hndvd ⟨h, hn⟩
  rw [hq.pow_dvd_iff_le_factorization hpn, Nat.factorization_mul hp.ne_zero hn,
    Finsupp.add_apply, hp.factorization] at hdvd
  rw [hq.pow_dvd_iff_le_factorization hn] at hndvd'
  by_cases hqp : q = p
  · rw [hqp, Finsupp.single_eq_same] at hdvd
    rw [hqp] at hndvd'
    rw [hqp]
    congr 1
    omega
  · rw [Finsupp.single_apply, if_neg (Ne.symm hqp), zero_add] at hdvd
    exact absurd hdvd hndvd'

/-- `p^{v_p(n)+1}` divides `pn` and not `n`. -/
theorem pow_mem_sdiff_divisors {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    p ^ (n.factorization p + 1) ∈ (p * n).divisors \ n.divisors := by
  simp only [mem_sdiff, Nat.mem_divisors]
  refine ⟨⟨?_, mul_ne_zero hp.ne_zero hn⟩, fun h => Nat.pow_succ_factorization_not_dvd hn hp h.1⟩
  rw [pow_succ, mul_comm]
  exact Nat.mul_dvd_mul_left p (Nat.ordProj_dvd n p)

/-- The in-degree increment along one prime is the sum over the new divisors. -/
theorem inDegree_mul_prime_sub_eq_sum_sdiff (lam : ℕ → ℝ) {p n : ℕ} (hp : p.Prime)
    (hn : n ≠ 0) :
    inDegree lam (p * n) - inDegree lam n = ∑ e ∈ (p * n).divisors \ n.divisors, lam e := by
  rw [inDegree, inDegree, ← sum_sdiff (Nat.divisors_subset_of_dvd (mul_ne_zero hp.ne_zero hn)
    (dvd_mul_left n p))]
  ring

/-- **The one-prime step.** For a generalized von Mangoldt weight the flux through one prime is
`λ(p)` at every vertex. -/
theorem inDegree_mul_prime_sub (lam : ℕ → ℝ)
    (htower : ∀ p k : ℕ, p.Prime → 1 ≤ k → lam (p ^ k) = lam p)
    (hvanish : ∀ n : ℕ, 1 < n → ¬ IsPrimePow n → lam n = 0) {p n : ℕ} (hp : p.Prime)
    (hn : n ≠ 0) : inDegree lam (p * n) - inDegree lam n = lam p := by
  rw [inDegree_mul_prime_sub_eq_sum_sdiff lam hp hn,
    sum_eq_single_of_mem _ (pow_mem_sdiff_divisors hp hn), htower p _ hp (by omega)]
  intro e he hne
  have he0 : 0 < e := Nat.pos_of_mem_divisors (mem_sdiff.mp he).1
  have he1 : e ≠ 1 := by
    rintro rfl
    exact (mem_sdiff.mp he).2 (Nat.mem_divisors.mpr ⟨one_dvd n, hn⟩)
  exact hvanish e (by omega) fun hpp => hne (eq_pow_of_mem_sdiff_divisors hp hn he hpp)

/-! ### Classification -/

/-- The in-degree increment along a prime power of a self-similar weight. -/
theorem lam_prime_pow_of_selfSimilar {lam : ℕ → ℝ} (h : SelfSimilarFlux lam) {p k : ℕ}
    (hp : p.Prime) (hk : 1 ≤ k) : lam (p ^ k) = lam p := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hflux := h p (p ^ j) hp.pos (pow_pos hp.pos j)
  simp only [starFlux, mul_one] at hflux
  have hstep : inDegree lam (p * p ^ j) - inDegree lam (p ^ j) = lam (p ^ (j + 1)) := by
    rw [← pow_succ', inDegree, inDegree, Nat.divisors_prime_pow hp, Nat.divisors_prime_pow hp,
      sum_map, sum_map, Finset.sum_range_succ _ (j + 1)]
    simp
  have hone : inDegree lam p - inDegree lam 1 = lam p := by
    rw [inDegree, inDegree, hp.divisors, Nat.divisors_one,
      sum_pair (Ne.symm hp.one_lt.ne'), sum_singleton]
    ring
  rw [← hstep, hflux, hone]

/-- **The classification of self-similar counterterms.** The boundary flux of every star is
constant along the star iff the weight vanishes off prime powers and is constant along every prime
tower. -/
theorem selfSimilarFlux_iff (lam : ℕ → ℝ) :
    SelfSimilarFlux lam ↔
      (∀ p k : ℕ, p.Prime → 1 ≤ k → lam (p ^ k) = lam p) ∧
        (∀ n : ℕ, 1 < n → ¬ IsPrimePow n → lam n = 0) := by
  constructor
  · intro h
    have htower : ∀ p k : ℕ, p.Prime → 1 ≤ k → lam (p ^ k) = lam p :=
      fun p k hp hk => lam_prime_pow_of_selfSimilar h hp hk
    refine ⟨htower, fun n => ?_⟩
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro hn hnpp
    set p := n.minFac with hpdef
    have hp : p.Prime := Nat.minFac_prime (by omega)
    obtain ⟨n', hn'⟩ : p ∣ n := Nat.minFac_dvd n
    have hn'0 : n' ≠ 0 := by rintro rfl; simp at hn'; omega
    have hone : inDegree lam p - inDegree lam 1 = lam p := by
      rw [inDegree, inDegree, hp.divisors, Nat.divisors_one,
        sum_pair (Ne.symm hp.one_lt.ne'), sum_singleton]
      ring
    have hflux := h p n' hp.pos (Nat.pos_of_ne_zero hn'0)
    simp only [starFlux, mul_one] at hflux
    rw [inDegree_mul_prime_sub_eq_sum_sdiff lam hp hn'0, hone] at hflux
    -- The new divisors of `n = pn'` are `n`, the prime power `p^{v_p(n)}`, and
    -- non-prime-powers below `n`, on which `λ` vanishes by induction.
    have hqmem := pow_mem_sdiff_divisors hp hn'0
    have hnmem : p * n' ∈ (p * n').divisors \ n'.divisors := by
      refine mem_sdiff.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_refl _, by rw [← hn']; omega⟩, fun hd => ?_⟩
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn'0) (Nat.mem_divisors.mp hd).1
      nlinarith [hp.two_le, Nat.pos_of_ne_zero hn'0]
    have hqn : p ^ (n'.factorization p + 1) ≠ p * n' := fun hq =>
      hnpp (by rw [hn', ← hq]; exact hp.isPrimePow.pow (by omega))
    have hsum : ∑ e ∈ (p * n').divisors \ n'.divisors, lam e =
        lam (p * n') + lam (p ^ (n'.factorization p + 1)) := by
      rw [← sum_pair hqn.symm]
      refine (sum_subset (by
        intro e he
        simp only [mem_insert, mem_singleton] at he
        rcases he with rfl | rfl
        · exact hnmem
        · exact hqmem) fun e he hne => ?_).symm
      simp only [mem_insert, mem_singleton, not_or] at hne
      have he0 : 0 < e := Nat.pos_of_mem_divisors (mem_sdiff.mp he).1
      have he1 : e ≠ 1 := by
        rintro rfl
        exact (mem_sdiff.mp he).2 (Nat.mem_divisors.mpr ⟨one_dvd n', hn'0⟩)
      have hepp : ¬ IsPrimePow e := fun hpp =>
        hne.2 (eq_pow_of_mem_sdiff_divisors hp hn'0 he hpp)
      have hlt : e < n := by
        rw [hn']
        exact lt_of_le_of_ne (Nat.divisor_le (mem_sdiff.mp he).1) hne.1
      exact ih e hlt (by omega) hepp
    rw [hsum, htower p _ hp (by omega)] at hflux
    rw [hn']
    linarith
  · rintro ⟨htower, hvanish⟩ d m hd hm
    -- Induction on `d` through its least prime factor.
    induction d using Nat.strong_induction_on generalizing m with
    | _ d ih =>
    rcases Nat.lt_or_ge d 2 with hd1 | hd2
    · obtain rfl : d = 1 := by omega
      simp [starFlux]
    · set p := d.minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      obtain ⟨d', hd'⟩ : p ∣ d := Nat.minFac_dvd d
      have hd'0 : 0 < d' := by
        rcases Nat.eq_zero_or_pos d' with h0 | h0
        · subst h0; simp at hd'; omega
        · exact h0
      have hlt : d' < d := by rw [hd']; nlinarith [hp.two_le]
      have step : ∀ k : ℕ, 0 < k →
          starFlux lam d k = lam p + starFlux lam d' k := fun k hk => by
        simp only [starFlux]
        rw [hd', mul_assoc]
        have := inDegree_mul_prime_sub lam htower hvanish hp (n := d' * k)
          (Nat.mul_pos hd'0 hk).ne'
        linarith
      rw [step m hm, step 1 one_pos, ih d' hlt m hd'0 hm]

/-! ### Twists -/

/-- **Among twists only `ζ` is self-similar.** For a completely multiplicative `ω` with nonzero
prime values, `Λω` has a self-similar counterterm iff `ω(p) = 1` for every prime. -/
theorem selfSimilarFlux_twist_iff (ω : ℕ → ℝ) (hω1 : ω 1 = 1)
    (hωmul : ∀ a b : ℕ, ω (a * b) = ω a * ω b) (hω0 : ∀ p : ℕ, p.Prime → ω p ≠ 0) :
    SelfSimilarFlux (fun k => Λ k * ω k) ↔ ∀ p : ℕ, p.Prime → ω p = 1 := by
  constructor
  · intro h p hp
    have h2 := lam_prime_pow_of_selfSimilar h hp (k := 2) (by norm_num)
    simp only [vonMangoldt_apply_pow two_ne_zero, vonMangoldt_apply_prime hp] at h2
    rw [pow_two, hωmul] at h2
    have hlog : Real.log p ≠ 0 := by
      have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      exact (Real.log_pos this).ne'
    have h3 : ω p * ω p = ω p := mul_left_cancel₀ hlog h2
    have : ω p * (ω p - 1) = 0 := by rw [mul_sub, h3]; ring
    rcases mul_eq_zero.mp this with h0 | h1
    · exact absurd h0 (hω0 p hp)
    · linarith
  · intro h
    have hall : ∀ n : ℕ, 0 < n → ω n = 1 := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
      intro hn
      rcases Nat.lt_or_ge n 2 with h1 | h2
      · obtain rfl : n = 1 := by omega
        exact hω1
      · have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
        obtain ⟨n', hn'⟩ := Nat.minFac_dvd n
        have hn'0 : 0 < n' := by
          rcases Nat.eq_zero_or_pos n' with h0 | h0
          · subst h0; simp at hn'; omega
          · exact h0
        rw [hn', hωmul, h _ hp, ih n' (by rw [hn']; nlinarith [hp.two_le]) hn'0, one_mul]
    have heq : (fun k => Λ k * ω k) = fun k => Λ k := by
      funext k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · rw [hall k hk, mul_one]
    rw [heq]
    exact selfSimilarFlux_vonMangoldt

end GaloisForLFunctions.HodgeTheoryWithoutVarieties

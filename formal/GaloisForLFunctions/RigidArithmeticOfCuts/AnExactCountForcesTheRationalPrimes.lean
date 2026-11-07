import GaloisForLFunctions.RHTower.BeurlingSystemGibbsGauge

/-!
# An exact count forces the rational primes

A Beurling system with integer norms has an integer-valued count `N(x)`. So `N(x) − ⌊x⌋` is either at least
`1` in size or exactly `0`, and integer norms give a jump at every level: `N(x) − ⌊x⌋ → 0` means that from
some point on, every integer `n` has exactly one generalized integer of norm `n`.

That already forces the system. **If every large integer has exactly one factorization in a Beurling system
with integer norms, the system is the rational primes.** Nothing is assumed below the threshold, and no
analytic input is used. A label of composite norm, a repeated label or a missing prime each gives two
factorizations of some large integer.

Above the integrality gap the picture changes: exchanging a prime for composite norms gives systems with
`N(x) − ⌊x⌋` of size `(log x)^C`, which is the subject of the exchange law.
-/

open RHTower

namespace GaloisForLFunctions.RigidArithmeticOfCuts

variable (B : BeurlingSystem)

/-- Every label of `B` has an integer norm. -/
def HasIntegerNorms : Prop := ∀ p : B.Label, ∃ n : ℕ, B.labelNorm p = n

/-- From `n₀` on, each integer is the norm of exactly one generalized integer. -/
def HasEventuallyExactCount (n₀ : ℕ) : Prop :=
  ∀ n : ℕ, n₀ ≤ n → ∃! g : B.Integer, B.intNorm g = n

variable {B} {n₀ : ℕ}

/-- The norm of a label is an integer at least `2`. -/
private lemma exists_norm (h : HasIntegerNorms B) (p : B.Label) :
    ∃ n : ℕ, 2 ≤ n ∧ B.labelNorm p = n := by
  obtain ⟨n, hn⟩ := h p
  refine ⟨n, ?_, hn⟩
  have h1 := B.one_lt_labelNorm p
  rw [hn] at h1
  exact_mod_cast h1

/-- A generalized integer of integer norm: its norm is a natural number. -/
private lemma exists_intNorm (h : HasIntegerNorms B) (g : B.Integer) :
    ∃ n : ℕ, 1 ≤ n ∧ B.intNorm g = n := by
  classical
  induction g using Multiset.induction_on with
  | empty => exact ⟨1, le_rfl, by simp⟩
  | cons p g ih =>
    obtain ⟨n, hn1, hn⟩ := ih
    obtain ⟨m, hm2, hm⟩ := exists_norm h p
    refine ⟨m * n, Nat.mul_pos (by omega) hn1, ?_⟩
    rw [← Multiset.singleton_add, B.intNorm_add, B.intNorm_singleton, hn, hm]
    push_cast
    rfl

/-- Two generalized integers of the same large norm coincide. -/
private lemma eq_of_intNorm_eq (hc : HasEventuallyExactCount B n₀) {g h : B.Integer} {n : ℕ}
    (hn : n₀ ≤ n) (hg : B.intNorm g = n) (hh : B.intNorm h = n) : g = h :=
  (hc n hn).unique hg hh

/-- Multiply a generalized integer by a label to pass any threshold. -/
private lemma exists_large (h : HasIntegerNorms B) (p : B.Label) (n₀ : ℕ) :
    ∃ k : ℕ, ∃ N : ℕ, n₀ ≤ N ∧ B.intNorm (Multiset.replicate k p) = N := by
  obtain ⟨m, hm2, hm⟩ := exists_norm h p
  refine ⟨n₀, m ^ n₀, ?_, ?_⟩
  · exact (Nat.lt_pow_self (by omega)).le
  · rw [B.intNorm_replicate, hm]
    push_cast
    rfl

/-- **Labels are determined by their norms.** -/
theorem label_eq_of_labelNorm_eq (h : HasIntegerNorms B) (hc : HasEventuallyExactCount B n₀)
    {p q : B.Label} (hpq : B.labelNorm p = B.labelNorm q) : p = q := by
  classical
  obtain ⟨k, N, hN, hk⟩ := exists_large h p n₀
  obtain ⟨m, hm2, hm⟩ := exists_norm h p
  have hg : B.intNorm ({p} + Multiset.replicate k p) = ((m * N : ℕ) : ℝ) := by
    rw [B.intNorm_add, B.intNorm_singleton, hk, hm]
    push_cast
    rfl
  have hh : B.intNorm ({q} + Multiset.replicate k p) = ((m * N : ℕ) : ℝ) := by
    rw [B.intNorm_add, B.intNorm_singleton, hk, ← hpq, hm]
    push_cast
    rfl
  have hle : n₀ ≤ m * N := hN.trans (Nat.le_mul_of_pos_left N (by omega))
  have heq := eq_of_intNorm_eq hc hle hg hh
  have := (add_left_inj _).mp heq
  simpa using this

/-- A generalized integer whose norm is prime is a single label of that norm. -/
private lemma exists_label_of_intNorm_prime (h : HasIntegerNorms B) {g : B.Integer} {r : ℕ}
    (hr : r.Prime) (hg : B.intNorm g = r) : ∃ p : B.Label, g = {p} ∧ B.labelNorm p = r := by
  classical
  induction g using Multiset.induction_on with
  | empty =>
    rw [B.intNorm_zero] at hg
    have : r = 1 := by exact_mod_cast hg.symm
    exact absurd this hr.ne_one
  | cons p g _ =>
    rw [← Multiset.singleton_add, B.intNorm_add, B.intNorm_singleton] at hg
    obtain ⟨m, hm2, hm⟩ := exists_norm h p
    obtain ⟨n, hn1, hn⟩ := exists_intNorm h g
    rw [hm, hn] at hg
    have hmul : m * n = r := by exact_mod_cast hg
    have hm1 : m ≠ 1 := by omega
    have hn' : n = 1 := ((Nat.prime_mul_iff.mp (hmul ▸ hr)).elim (fun hh => hh.2)
      (fun hh => absurd hh.2 hm1))
    have hg0 : g = 0 := by
      by_contra hne
      obtain ⟨q, hq⟩ := Multiset.exists_mem_of_ne_zero hne
      obtain ⟨rest, hrest⟩ := Multiset.exists_cons_of_mem hq
      obtain ⟨u, hu2, hu⟩ := exists_norm h q
      obtain ⟨v, hv1, hv⟩ := exists_intNorm h rest
      have hnorm : B.intNorm g = (u * v : ℕ) := by
        rw [hrest, ← Multiset.singleton_add, B.intNorm_add, B.intNorm_singleton, hu, hv]
        push_cast
        rfl
      rw [hn] at hnorm
      have huv : n = u * v := by exact_mod_cast hnorm
      rw [hn'] at huv
      have := Nat.eq_one_of_mul_eq_one_right huv.symm
      omega
    refine ⟨p, by simp [hg0], ?_⟩
    rw [hn', mul_one] at hmul
    rw [hm, hmul]

/-- **Every large prime is a label.** -/
theorem exists_label_of_prime_of_le (h : HasIntegerNorms B) (hc : HasEventuallyExactCount B n₀)
    {r : ℕ} (hr : r.Prime) (hle : n₀ ≤ r) : ∃ p : B.Label, B.labelNorm p = r := by
  obtain ⟨g, hg, -⟩ := hc r hle
  obtain ⟨p, -, hp⟩ := exists_label_of_intNorm_prime h hr hg
  exact ⟨p, hp⟩

/-- A label for two large primes: `r`, `r'` distinct, both beyond `n₀` and `a`. -/
private lemma exists_two_large_primes (n₀ a : ℕ) :
    ∃ r r' : ℕ, r.Prime ∧ r'.Prime ∧ r ≠ r' ∧ n₀ ≤ r ∧ n₀ ≤ r' ∧ a < r ∧ a < r' := by
  obtain ⟨r, hr1, hr⟩ := Nat.exists_infinite_primes (max n₀ a + 1)
  obtain ⟨r', hr'1, hr'⟩ := Nat.exists_infinite_primes (r + 1)
  have h1 : n₀ ≤ max n₀ a := le_max_left _ _
  have h2 : a ≤ max n₀ a := le_max_right _ _
  exact ⟨r, r', hr, hr', by omega, by omega, by omega, by omega, by omega⟩

/-- Pull a label out of a generalized integer. -/
private lemma intNorm_of_mem (h : HasIntegerNorms B) {p : B.Label} {g : B.Integer} (hp : p ∈ g)
    {u n : ℕ} (hu : B.labelNorm p = u) (hg : B.intNorm g = n) :
    ∃ rest : B.Integer, g = p ::ₘ rest ∧ ∃ v : ℕ, B.intNorm rest = v ∧ u * v = n := by
  classical
  obtain ⟨rest, hrest⟩ := Multiset.exists_cons_of_mem hp
  obtain ⟨v, -, hv⟩ := exists_intNorm h rest
  refine ⟨rest, hrest, v, hv, ?_⟩
  rw [hrest, ← Multiset.singleton_add, B.intNorm_add, B.intNorm_singleton, hu, hv] at hg
  exact_mod_cast hg

/-- **Every prime is a label.** With `l` prime and `r`, `r'` large primes, the generalized integers of
norms `l r` and `l r'` multiply to the same large norm as the one of norm `l² r` times the label `r'`. So
the label `r'` occurs in the generalized integer of norm `l r'`, and what remains has norm `l`. -/
theorem exists_label_of_prime (h : HasIntegerNorms B) (hc : HasEventuallyExactCount B n₀)
    {l : ℕ} (hl : l.Prime) : ∃ p : B.Label, B.labelNorm p = l := by
  classical
  obtain ⟨r, r', hr, hr', hne, hr0, hr'0, hlr, hlr'⟩ := exists_two_large_primes n₀ l
  have hlpos : 0 < l := hl.pos
  obtain ⟨R', hR'⟩ := exists_label_of_prime_of_le h hc hr' hr'0
  have hbig1 : n₀ ≤ l * r := hr0.trans (Nat.le_mul_of_pos_left r hlpos)
  have hbig2 : n₀ ≤ l * r' := hr'0.trans (Nat.le_mul_of_pos_left r' hlpos)
  have hbig3 : n₀ ≤ l * l * r := hr0.trans (Nat.le_mul_of_pos_left r (Nat.mul_pos hlpos hlpos))
  obtain ⟨g₁, hg₁, -⟩ := hc (l * r) hbig1
  obtain ⟨g₂, hg₂, -⟩ := hc (l * r') hbig2
  obtain ⟨g₃, hg₃, -⟩ := hc (l * l * r) hbig3
  have hN : n₀ ≤ l * l * r * r' := hbig3.trans (Nat.le_mul_of_pos_right _ hr'.pos)
  have hleft : B.intNorm (g₁ + g₂) = ((l * l * r * r' : ℕ) : ℝ) := by
    rw [B.intNorm_add, hg₁, hg₂]
    push_cast
    ring
  have hright : B.intNorm (g₃ + {R'}) = ((l * l * r * r' : ℕ) : ℝ) := by
    rw [B.intNorm_add, hg₃, B.intNorm_singleton, hR']
    push_cast
    ring
  have heq := eq_of_intNorm_eq hc hN hleft hright
  have hmem : R' ∈ g₁ + g₂ := by
    rw [heq]
    simp
  rcases Multiset.mem_add.mp hmem with hin | hin
  · obtain ⟨_, _, v, _, huv⟩ := intNorm_of_mem h hin hR' hg₁
    have hd : r' ∣ l * r := ⟨v, huv.symm⟩
    rcases (hr'.dvd_mul).mp hd with h1 | h1
    · exact absurd (Nat.le_of_dvd hlpos h1) (by omega)
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr' hr).mp h1).symm hne
  · obtain ⟨rest, _, v, hv, huv⟩ := intNorm_of_mem h hin hR' hg₂
    have hvl : v = l := by
      have : r' * v = r' * l := by rw [huv]; ring
      exact Nat.eq_of_mul_eq_mul_left hr'.pos this
    obtain ⟨p, -, hp⟩ := exists_label_of_intNorm_prime h hl (g := rest) (by rw [hv, hvl])
    exact ⟨p, hp⟩

/-- Every positive integer is the norm of a generalized integer. -/
theorem exists_intNorm_eq (h : HasIntegerNorms B) (hc : HasEventuallyExactCount B n₀) (n : ℕ)
    (hn : 1 ≤ n) : ∃ g : B.Integer, B.intNorm g = n := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · have : n = 1 := by omega
      exact ⟨0, by simp [this]⟩
    · have hp := Nat.minFac_prime (by omega : n ≠ 1)
      obtain ⟨t, ht⟩ := Nat.minFac_dvd n
      have htpos : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with rfl | h0
        · simp at ht
          omega
        · exact h0
      have htlt : t < n := by
        have h3 := hp.two_le
        nlinarith
      obtain ⟨g, hg⟩ := ih t htlt htpos
      obtain ⟨p, hpn⟩ := exists_label_of_prime h hc hp
      refine ⟨{p} + g, ?_⟩
      rw [B.intNorm_add, B.intNorm_singleton, hpn, hg]
      conv_rhs => rw [ht]
      push_cast
      rfl

/-- **Labels have prime norm.** A label of composite norm `m` is one factorization of `m` and the prime
labels give another, so `m r` has two factorizations for every large prime `r`. -/
theorem prime_of_labelNorm (h : HasIntegerNorms B) (hc : HasEventuallyExactCount B n₀)
    {p : B.Label} {m : ℕ} (hm : B.labelNorm p = m) : m.Prime := by
  classical
  have hm2 : 2 ≤ m := by
    have h1 := B.one_lt_labelNorm p
    rw [hm] at h1
    exact_mod_cast h1
  by_contra hnp
  have hl := Nat.minFac_prime (by omega : m ≠ 1)
  obtain ⟨t, ht⟩ := Nat.minFac_dvd m
  have htpos : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with rfl | h0
    · simp at ht
      omega
    · exact h0
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [mul_one] at ht
    exact hnp (ht ▸ hl)
  obtain ⟨g, hg⟩ := exists_intNorm_eq h hc t htpos
  obtain ⟨U, hU⟩ := exists_label_of_prime h hc hl
  obtain ⟨r, hr1, hr⟩ := Nat.exists_infinite_primes n₀
  obtain ⟨R, hR⟩ := exists_label_of_prime_of_le h hc hr hr1
  have hN : n₀ ≤ m * r := hr1.trans (Nat.le_mul_of_pos_left r (by omega))
  have h1 : B.intNorm ({p} + {R}) = ((m * r : ℕ) : ℝ) := by
    rw [B.intNorm_add, B.intNorm_singleton, B.intNorm_singleton, hm, hR]
    push_cast
    rfl
  have h2 : B.intNorm (({U} + g) + {R}) = ((m * r : ℕ) : ℝ) := by
    rw [B.intNorm_add, B.intNorm_add, B.intNorm_singleton, B.intNorm_singleton, hU, hg, hR]
    conv_rhs => rw [ht]
    push_cast
    rfl
  have heq := eq_of_intNorm_eq hc hN h1 h2
  have hcancel : ({p} : B.Integer) = {U} + g := (add_left_inj _).mp heq
  have hcard := congrArg Multiset.card hcancel
  simp only [Multiset.card_singleton, Multiset.card_add] at hcard
  have hg0 : Multiset.card g = 0 := by omega
  rw [Multiset.card_eq_zero] at hg0
  rw [hg0, B.intNorm_zero] at hg
  have : t = 1 := by exact_mod_cast hg.symm
  exact ht1 this

/-- **An exact count forces the rational primes.** A Beurling system with integer norms in which every
large integer has exactly one factorization is the system of rational primes. -/
theorem nonempty_label_equiv_primes (h : HasIntegerNorms B) (hc : HasEventuallyExactCount B n₀) :
    Nonempty {e : B.Label ≃ {p : ℕ // p.Prime} // ∀ l, B.labelNorm l = ((e l : ℕ) : ℝ)} := by
  classical
  have h' := h
  choose ν hν using h
  have hprime : ∀ l, (ν l).Prime := fun l => prime_of_labelNorm h' hc (hν l)
  let f : B.Label → {p : ℕ // p.Prime} := fun l => ⟨ν l, hprime l⟩
  have hinj : Function.Injective f := fun a b hab =>
    label_eq_of_labelNorm_eq h' hc (by
      rw [hν a, hν b]
      exact congrArg (fun x : {p : ℕ // p.Prime} => ((x : ℕ) : ℝ)) hab)
  have hsurj : Function.Surjective f := fun r => by
    obtain ⟨l, hl⟩ := exists_label_of_prime h' hc r.2
    refine ⟨l, Subtype.ext ?_⟩
    have h1 := hν l
    rw [hl] at h1
    exact_mod_cast h1.symm
  exact ⟨⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun l => hν l⟩⟩

/-! ### From the count to exact factorization -/

/-- The number of generalized integers of norm `n`. -/
noncomputable def intCount (B : BeurlingSystem) (n : ℕ) : ℕ :=
  {g : B.Integer | B.intNorm g = n}.ncard

/-- **An integer-valued count close to `⌊x⌋` is exact.** If `N(x) − ⌊x⌋ → 0` on the integers, then from some
point on each integer has exactly one factorization. -/
theorem hasEventuallyExactCount_of_tendsto
    (hcount : Filter.Tendsto (fun x : ℕ =>
      (((Finset.Ioc 0 x).sum (intCount B) : ℕ) : ℝ) - (x : ℝ)) Filter.atTop (nhds 0)) :
    ∃ n₀, HasEventuallyExactCount B n₀ := by
  have hev := hcount.eventually (Metric.ball_mem_nhds _ one_pos)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hev
  have hzero : ∀ x, X ≤ x → (Finset.Ioc 0 x).sum (intCount B) = x := by
    intro x hx
    have h1 := hX x hx
    rw [Real.dist_eq, sub_zero] at h1
    have h2 : |(((Finset.Ioc 0 x).sum (intCount B) : ℕ) : ℤ) - (x : ℤ)| < 1 := by
      have : ((|(((Finset.Ioc 0 x).sum (intCount B) : ℕ) : ℤ) - (x : ℤ)| : ℤ) : ℝ) < 1 := by
        push_cast
        exact_mod_cast h1
      exact_mod_cast this
    have h3 := Int.abs_lt_one_iff.mp h2
    omega
  refine ⟨X + 1, fun n hn => ?_⟩
  obtain ⟨y, rfl⟩ : ∃ y, n = y + 1 := ⟨n - 1, by omega⟩
  have h1 := hzero y (by omega)
  have h2 := hzero (y + 1) (by omega)
  rw [Finset.sum_Ioc_succ_top (by omega), h1] at h2
  have hone : intCount B (y + 1) = 1 := by omega
  obtain ⟨g, hg⟩ := Set.ncard_eq_one.mp hone
  refine ⟨g, ?_, fun g' hg' => ?_⟩
  · have : g ∈ {g : B.Integer | B.intNorm g = ((y + 1 : ℕ) : ℝ)} := by
      rw [hg]
      exact Set.mem_singleton g
    exact this
  · have : g' ∈ {g : B.Integer | B.intNorm g = ((y + 1 : ℕ) : ℝ)} := hg'
    rw [hg] at this
    exact this

end GaloisForLFunctions.RigidArithmeticOfCuts

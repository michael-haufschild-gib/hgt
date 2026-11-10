import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheEulerFactorsOfTheDivisorSumPayEveryContact
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheWittCarryIsTheDigitCarryUpToTheFermatQuotient

/-!
# The planar square has the contacts of the square and pays them

The ring of the coordinates of the primes pays every contact, but its graphs meet more often
than in the arithmetic square: the difference of two nodes of a chain at `p` has prime factors
other than `p`. The planar sequences form a larger subring of the square, the **planar square**,
which has exactly the contacts of the square and still pays them.

* **The ring** (`planarRing`, `planarSquare`, `payingRing_le_planarSquare`). Planar sequences are
  closed under sums and products: on a chain the polynomials add and multiply, and so do the
  factors prime to `p`. They contain the ring of the coordinates and lie in the square.
* **Separation at a second prime** (`exists_pow_mul_iterate_fermatQuot`,
  `not_dvd_iterate_fermatQuot`, `exists_planar_separating`). The Fermat quotient
  `F(z) = (z^ℓ − z)/ℓ` maps the integers to the integers, is a polynomial with a power of `ℓ` in
  the denominator, and lowers the exponent of `ℓ` in `z` by one. For primes `p ≠ ℓ` and two
  graphs with different exponents of `p`, the sequence `n ↦ F^t(y_p(n) − a)`, `a` the node of
  the first graph and `ℓ^t` the exact power of `ℓ` in the difference of the two nodes, is
  planar, vanishes on the first graph and is prime to `ℓ` on the second.
* **The contacts** (`planarContact_eq_graphIdeal`). The differences of the planar square on
  `Γ_m` and `Γ_n` generate the ideal `J(m, n)` of the square: `ℤ` when `n/m` is not a prime
  power, and `p^{v_p(m)+1}` for `n = m p^j`.
* **Payment** (`sum_contact_le_log_abs_planarSquare`). An element of the planar square that
  vanishes on a finite set of graphs and not on `Γ_m` is at least as large on `Γ_m` as the
  contacts of the normal form with the set.
* **Position** (`payingRing_lt_planarSquare`, `planarSquare_ne_top`). The planar square is
  strictly between the ring of the coordinates and the square: it separates `Γ_1` and `Γ_4`
  modulo `3`, and it does not contain `p − e_p`.
-/

open Finset Polynomial
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### The ring of planar sequences -/

theorem isPlanar_const (c : ℤ) : IsPlanar fun _ => c := fun p _ _ _ =>
  ⟨1, C c, (Nat.prime_iff_prime_int.mp p.2).not_dvd_one, fun l _ => by rw [one_mul, eval_C]⟩

theorem IsPlanar.mul {x y : ℕ+ → ℤ} (hx : IsPlanar x) (hy : IsPlanar y) : IsPlanar (x * y) := by
  intro p m hm K
  obtain ⟨D, g, hD, hg⟩ := hx p m hm K
  obtain ⟨E, h, hE, hh⟩ := hy p m hm K
  have hpz : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp p.2
  refine ⟨D * E, g * h, fun hdvd => (hpz.dvd_or_dvd hdvd).elim hD hE, fun l hl => ?_⟩
  rw [Pi.mul_apply, eval_mul, ← hg l hl, ← hh l hl]
  ring

theorem IsPlanar.add {x y : ℕ+ → ℤ} (hx : IsPlanar x) (hy : IsPlanar y) : IsPlanar (x + y) := by
  intro p m hm K
  obtain ⟨D, g, hD, hg⟩ := hx p m hm K
  obtain ⟨E, h, hE, hh⟩ := hy p m hm K
  have hpz : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp p.2
  refine ⟨D * E, C E * g + C D * h, fun hdvd => (hpz.dvd_or_dvd hdvd).elim hD hE,
    fun l hl => ?_⟩
  rw [Pi.add_apply, eval_add, eval_mul, eval_mul, eval_C, eval_C, ← hg l hl, ← hh l hl]
  ring

theorem IsPlanar.neg {x : ℕ+ → ℤ} (hx : IsPlanar x) : IsPlanar (-x) := by
  intro p m hm K
  obtain ⟨D, g, hD, hg⟩ := hx p m hm K
  refine ⟨D, -g, hD, fun l hl => ?_⟩
  rw [Pi.neg_apply, eval_neg, ← hg l hl]
  ring

/-- The ring of planar sequences. -/
def planarRing : Subring (ℕ+ → ℤ) where
  carrier := {x | IsPlanar x}
  mul_mem' := fun hx hy => hx.mul hy
  one_mem' := isPlanar_const 1
  add_mem' := fun hx hy => hx.add hy
  zero_mem' := isPlanar_const 0
  neg_mem' := fun hx => hx.neg

/-- The **planar square**: the sections of the arithmetic square that are planar. -/
def planarSquare : Subring ghostRing := planarRing.comap ghostRing.subtype

theorem mem_planarSquare {x : ghostRing} : x ∈ planarSquare ↔ IsPlanar x.1 := Iff.rfl

/-- A planar sequence as an element of the planar square. -/
def planarOf (x : ℕ+ → ℤ) (hx : IsPlanar x) : planarSquare :=
  ⟨⟨x, isGhost_of_isPlanar hx⟩, hx⟩

/-- The ring of the coordinates lies in the planar square. -/
theorem payingRing_le_planarSquare : payingRing ≤ planarSquare := by
  rintro _ ⟨f, rfl⟩
  exact isPlanar_coordHom f

theorem primeCoord_mem_planarSquare (p : Nat.Primes) : primeCoord p ∈ planarSquare := by
  have h : coordHom (MvPolynomial.X p) = primeCoord p := by simp [coordHom]
  rw [← h]
  exact isPlanar_coordHom _

/-! ### Fermat quotients separate the graphs at a second prime -/

theorem fermatQuot_zero {ℓ : ℕ} (hℓ : ℓ.Prime) : fermatQuot ℓ 0 = 0 := by
  have h := natCast_mul_fermatQuot hℓ 0
  rw [zero_pow hℓ.ne_zero, sub_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hℓ.ne_zero)

/-- An iterate of the Fermat quotient is a polynomial with a power of `ℓ` in the denominator. -/
theorem exists_pow_mul_iterate_fermatQuot {ℓ : ℕ} (hℓ : ℓ.Prime) (t : ℕ) :
    ∃ (e : ℕ) (G : ℤ[X]), ∀ z : ℤ, (ℓ : ℤ) ^ e * (fermatQuot ℓ)^[t] z = G.eval z := by
  induction t with
  | zero => exact ⟨0, X, fun z => by simp⟩
  | succ t ih =>
    obtain ⟨e, G, hG⟩ := ih
    have hexp : e * (ℓ - 1) + e = e * ℓ := by
      obtain ⟨k, hk⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by have := hℓ.pos; omega⟩
      rw [hk, Nat.add_sub_cancel]
      ring
    refine ⟨e * ℓ + 1, G ^ ℓ - C ((ℓ : ℤ) ^ (e * (ℓ - 1))) * G, fun z => ?_⟩
    have hF := natCast_mul_fermatQuot hℓ ((fermatQuot ℓ)^[t] z)
    rw [Function.iterate_succ_apply', eval_sub, eval_pow, eval_mul, eval_C, ← hG z]
    have h1 : (ℓ : ℤ) ^ (e * ℓ + 1) * fermatQuot ℓ ((fermatQuot ℓ)^[t] z) =
        (ℓ : ℤ) ^ (e * ℓ) * (((fermatQuot ℓ)^[t] z) ^ ℓ - (fermatQuot ℓ)^[t] z) := by
      rw [pow_succ, mul_assoc, hF]
    have h2 : ((ℓ : ℤ) ^ e * (fermatQuot ℓ)^[t] z) ^ ℓ =
        (ℓ : ℤ) ^ (e * ℓ) * ((fermatQuot ℓ)^[t] z) ^ ℓ := by
      rw [mul_pow, ← pow_mul]
    have h3 : (ℓ : ℤ) ^ (e * (ℓ - 1)) * ((ℓ : ℤ) ^ e * (fermatQuot ℓ)^[t] z) =
        (ℓ : ℤ) ^ (e * ℓ) * (fermatQuot ℓ)^[t] z := by
      rw [← mul_assoc, ← pow_add, hexp]
    rw [h1, h2, h3, mul_sub]

/-- **The Fermat quotient lowers the exponent of `ℓ` by one.** If `ℓ^t` is the exact power of
`ℓ` in `c`, the `t`-th iterate at `c` is prime to `ℓ`. -/
theorem not_dvd_iterate_fermatQuot {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∀ (t : ℕ) (c : ℤ), (ℓ : ℤ) ^ t ∣ c → ¬ (ℓ : ℤ) ^ (t + 1) ∣ c →
      ¬ (ℓ : ℤ) ∣ (fermatQuot ℓ)^[t] c := by
  intro t
  induction t with
  | zero =>
    intro c _ h
    simpa using h
  | succ t ih =>
    intro c hc hnc
    rw [Function.iterate_succ_apply]
    obtain ⟨u, rfl⟩ := hc
    have hℓz : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
    have hu : ¬ (ℓ : ℤ) ∣ u := fun ⟨u', hu'⟩ => hnc ⟨u', by rw [hu', pow_succ]; ring⟩
    -- `c^ℓ` is divisible by `ℓ^{t+2}`
    have hle : t + 2 ≤ (t + 1) * ℓ := by nlinarith [hℓ.two_le]
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hle
    have hval : fermatQuot ℓ ((ℓ : ℤ) ^ (t + 1) * u) =
        (ℓ : ℤ) ^ t * ((ℓ : ℤ) * ((ℓ : ℤ) ^ r * u ^ ℓ) - u) := by
      refine mul_left_cancel₀ hℓz ?_
      rw [natCast_mul_fermatQuot hℓ, mul_pow, ← pow_mul, hr]
      ring
    rw [hval]
    refine ih _ (dvd_mul_right _ _) fun hdiv => hu ?_
    rw [pow_succ] at hdiv
    have h1 : (ℓ : ℤ) ∣ (ℓ : ℤ) * ((ℓ : ℤ) ^ r * u ^ ℓ) - u :=
      (mul_dvd_mul_iff_left (pow_ne_zero t hℓz)).mp hdiv
    exact (dvd_sub_right (dvd_mul_right _ _)).mp h1

/-- Along the chain at a prime `q ≠ p` the exponent of `p` does not change. -/
theorem factorization_chain_of_ne {p q : Nat.Primes} (hpq : p ≠ q) (m : ℕ+) (l : ℕ) :
    ((m * primePNat q ^ l : ℕ+) : ℕ).factorization p = (m : ℕ).factorization p := by
  rw [PNat.mul_coe, PNat.pow_coe, primePNat_coe,
    Nat.factorization_mul m.ne_zero (pow_ne_zero _ q.2.ne_zero), Finsupp.add_apply,
    Nat.factorization_pow, q.2.factorization, Finsupp.smul_apply,
    Finsupp.single_eq_of_ne (fun h => hpq (Subtype.ext h)), smul_zero, add_zero]

/-- **Separation at a second prime.** For primes `p ≠ ℓ` and two graphs with different exponents
of `p`, a planar sequence vanishes on the first graph and is prime to `ℓ` on the second. -/
theorem exists_planar_separating {m n : ℕ+} {p ℓ : Nat.Primes} (hpl : p ≠ ℓ)
    (hv : (m : ℕ).factorization p ≠ (n : ℕ).factorization p) :
    ∃ x : ℕ+ → ℤ, IsPlanar x ∧ x m = 0 ∧ ¬ ((ℓ : ℕ) : ℤ) ∣ x n := by
  obtain ⟨a, ha⟩ : ∃ a, a = chainNode p ((m : ℕ).factorization p) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = chainNode p ((n : ℕ).factorization p) - a := ⟨_, rfl⟩
  have hc0 : c ≠ 0 := by
    rw [hc, ha]
    exact sub_ne_zero.mpr fun h => hv ((chainNode_strictMono p.2.pos).injective h).symm
  -- the exact power of `ℓ` in the difference of the nodes
  obtain ⟨t, ht1, ht2⟩ : ∃ t : ℕ, ((ℓ : ℕ) : ℤ) ^ t ∣ c ∧ ¬ ((ℓ : ℕ) : ℤ) ^ (t + 1) ∣ c := by
    refine ⟨c.natAbs.factorization ℓ, ?_, ?_⟩
    · rw [← Nat.cast_pow, Int.natCast_dvd]
      exact Nat.ordProj_dvd _ _
    · rw [← Nat.cast_pow, Int.natCast_dvd]
      exact Nat.pow_succ_factorization_not_dvd (Int.natAbs_ne_zero.mpr hc0) ℓ.2
  refine ⟨fun k => (fermatQuot ℓ)^[t] (chainNode p ((k : ℕ).factorization p) - a), ?_, ?_, ?_⟩
  · intro q k hk K
    by_cases hqp : q = p
    · -- on a chain at `p`: a polynomial in the node, with a power of `ℓ` in the denominator
      rw [hqp] at hk ⊢
      obtain ⟨e, G, hG⟩ := exists_pow_mul_iterate_fermatQuot ℓ.2 t
      refine ⟨((ℓ : ℕ) : ℤ) ^ e, G.comp (X - C a), fun hdvd => ?_, fun l _ => ?_⟩
      · have h1 := (Nat.prime_iff_prime_int.mp p.2).dvd_of_dvd_pow hdvd
        have h2 : (p : ℕ) ∣ (ℓ : ℕ) := by exact_mod_cast h1
        exact hpl (Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.2 ℓ.2).mp h2))
      · beta_reduce
        rw [factorization_chain p hk, eval_comp, eval_sub, eval_X, eval_C]
        exact hG _
    · -- on a chain at another prime: constant
      refine ⟨1, C ((fermatQuot ℓ)^[t] (chainNode p ((k : ℕ).factorization p) - a)),
        (Nat.prime_iff_prime_int.mp q.2).not_dvd_one, fun l _ => ?_⟩
      beta_reduce
      rw [one_mul, eval_C, factorization_chain_of_ne (Ne.symm hqp) k l]
  · beta_reduce
    rw [← ha, sub_self]
    exact Function.iterate_fixed (fermatQuot_zero ℓ.2) t
  · beta_reduce
    rw [← hc]
    exact not_dvd_iterate_fermatQuot ℓ.2 t c ht1 ht2

/-! ### The contacts of the planar square -/

/-- The ideal generated by the differences of the planar square on `Γ_m` and `Γ_n`. -/
def planarContact (m n : ℕ+) : Ideal ℤ :=
  Ideal.span (Set.range fun x : planarSquare => ghostComponent m x.1 - ghostComponent n x.1)

theorem planarContact_le_graphIdeal (m n : ℕ+) : planarContact m n ≤ graphIdeal m n :=
  Ideal.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact Ideal.subset_span ⟨x.1, rfl⟩)

theorem planarContact_comm (m n : ℕ+) : planarContact m n = planarContact n m := by
  refine le_antisymm ?_ ?_ <;>
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨x, rfl⟩
    refine (Ideal.neg_mem_iff _).mp ?_
    rw [neg_sub]
    exact Ideal.subset_span ⟨x, rfl⟩

/-- A separating sequence gives an element of the contact ideal prime to `ℓ`. -/
theorem exists_mem_planarContact_not_dvd {m n : ℕ+} {p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime)
    (hpl : p ≠ ℓ) (hv : (m : ℕ).factorization p ≠ (n : ℕ).factorization p) :
    ∃ z ∈ planarContact m n, ¬ (ℓ : ℤ) ∣ z := by
  obtain ⟨x, hx, hxm, hxn⟩ := exists_planar_separating (m := m) (n := n) (p := ⟨p, hp⟩)
    (ℓ := ⟨ℓ, hℓ⟩) (fun h => hpl (congrArg Subtype.val h)) hv
  refine ⟨x m - x n, Ideal.subset_span ⟨planarOf x hx, rfl⟩, ?_⟩
  rw [hxm, zero_sub, dvd_neg]
  exact hxn

/-- An ideal of `ℤ` with an element prime to `ℓ` for every prime `ℓ` is the unit ideal. -/
theorem ideal_eq_top_of_forall_prime {I : Ideal ℤ}
    (h : ∀ ℓ : ℕ, ℓ.Prime → ∃ z ∈ I, ¬ (ℓ : ℤ) ∣ z) : I = ⊤ := by
  by_contra hI
  have hd : ¬ IsUnit (Submodule.IsPrincipal.generator I) := fun hu => hI (by
    rw [← Ideal.span_singleton_generator I]
    exact Ideal.span_singleton_eq_top.mpr hu)
  obtain ⟨π, hπ, hπd⟩ :=
    Int.exists_prime_and_dvd fun h1 => hd (Int.isUnit_iff_natAbs_eq.mpr h1)
  obtain ⟨z, hz, hnz⟩ := h π.natAbs (Int.prime_iff_natAbs_prime.mp hπ)
  exact hnz (Int.natAbs_dvd.mpr
    (hπd.trans ((Submodule.IsPrincipal.mem_iff_generator_dvd I).mp hz)))

/-- An ideal of `ℤ` inside `(r^k)` that contains `r^k s` with `s` prime to `r`, and for every
prime `ℓ ≠ r` an element prime to `ℓ`, contains `r^k`. -/
theorem prime_pow_mem_of_forall_prime {I : Ideal ℤ} {r : ℕ} (hr : r.Prime) {k : ℕ} {s : ℤ}
    (hle : I ≤ Ideal.span {(r : ℤ) ^ k}) (hs : ¬ (r : ℤ) ∣ s) (hmem : (r : ℤ) ^ k * s ∈ I)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ r → ∃ z ∈ I, ¬ (ℓ : ℤ) ∣ z) : (r : ℤ) ^ k ∈ I := by
  obtain ⟨d, hd⟩ : ∃ d, d = Submodule.IsPrincipal.generator I := ⟨_, rfl⟩
  have hdI : d ∈ I := hd ▸ Submodule.IsPrincipal.generator_mem I
  have hdvd : ∀ z ∈ I, d ∣ z := fun z hz =>
    hd ▸ (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp hz
  obtain ⟨d', hd'⟩ := Ideal.mem_span_singleton.mp (hle hdI)
  have hrk : (r : ℤ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hr.ne_zero)
  have hd's : d' ∣ s := by
    have h1 := hdvd _ hmem
    rw [hd'] at h1
    exact (mul_dvd_mul_iff_left hrk).mp h1
  by_cases hu : IsUnit d'
  · rcases Int.isUnit_iff.mp hu with h1 | h1
    · rw [h1, mul_one] at hd'
      exact hd' ▸ hdI
    · rw [h1, mul_neg, mul_one] at hd'
      have h2 := I.neg_mem hdI
      rwa [hd', neg_neg] at h2
  · exfalso
    obtain ⟨π, hπ, hπd⟩ :=
      Int.exists_prime_and_dvd fun h1 => hu (Int.isUnit_iff_natAbs_eq.mpr h1)
    have hne : π.natAbs ≠ r := fun heq => hs (by
      rw [← heq]
      exact Int.natAbs_dvd.mpr (hπd.trans hd's))
    obtain ⟨z, hz, hnz⟩ := h π.natAbs (Int.prime_iff_natAbs_prime.mp hπ) hne
    refine hnz (Int.natAbs_dvd.mpr ?_)
    have h2 := hdvd z hz
    rw [hd'] at h2
    exact (hπd.trans (dvd_mul_left d' _)).trans h2

/-- On a chain the contact of the square is attained in the planar square. -/
theorem graphIdeal_le_planarContact_chain (m : ℕ+) {r : ℕ+} (hr : r.Prime) {j : ℕ}
    (hj : j ≠ 0) : graphIdeal m (m * r ^ j) ≤ planarContact m (m * r ^ j) := by
  have hr' : (r : ℕ).Prime := hr
  have hvn : ((m * r ^ j : ℕ+) : ℕ).factorization r = (m : ℕ).factorization r + j := by
    rw [PNat.mul_coe, PNat.pow_coe, Nat.factorization_mul m.ne_zero (pow_ne_zero _ hr'.ne_zero),
      Finsupp.add_apply, Nat.factorization_pow, hr'.factorization, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one]
  rw [graphIdeal_mul_prime_pow m hr hj, Ideal.span_singleton_le_iff_mem]
  refine prime_pow_mem_of_forall_prime hr' (s := -∑ i ∈ range j, ((r : ℕ) : ℤ) ^ i) ?_ ?_ ?_ ?_
  · rw [← graphIdeal_mul_prime_pow m hr hj]
    exact planarContact_le_graphIdeal _ _
  · rw [dvd_neg]
    exact not_dvd_geomSum hr' hj
  · -- the coordinate of `r` differs on the two graphs by `r^{v+1}` times a geometric sum
    have hmem : ghostComponent m (primeCoord r) - ghostComponent (m * r ^ j) (primeCoord r) ∈
        planarContact m (m * r ^ j) :=
      Ideal.subset_span ⟨⟨primeCoord r, primeCoord_mem_planarSquare ⟨r, hr⟩⟩, rfl⟩
    rw [ghostComponent_primeCoord, ghostComponent_primeCoord, hvn, ← neg_sub,
      chainNode_sub r (Nat.le_add_right _ j), Nat.add_sub_cancel_left] at hmem
    rwa [mul_neg]
  · intro ℓ hℓ hne
    exact exists_mem_planarContact_not_dvd hr' hℓ (Ne.symm hne) (by rw [hvn]; omega)

/-- Two positive integers whose exponents agree away from a prime `R`: the one with the larger
exponent of `R` is the other times a power of `R`. -/
theorem eq_mul_prime_pow_of_factorization {a b R : ℕ+} (hr : R.Prime)
    (hab : ∀ q : ℕ, q.Prime → q ≠ (R : ℕ) → (a : ℕ).factorization q = (b : ℕ).factorization q)
    (hlt : (a : ℕ).factorization R < (b : ℕ).factorization R) :
    b = a * R ^ ((b : ℕ).factorization R - (a : ℕ).factorization R) := by
  have hr' : (R : ℕ).Prime := hr
  refine PNat.eq (Nat.eq_of_factorization_eq b.ne_zero (PNat.ne_zero _) fun q => ?_)
  rw [PNat.mul_coe, PNat.pow_coe,
    Nat.factorization_mul a.ne_zero (pow_ne_zero _ hr'.ne_zero), Nat.factorization_pow,
    hr'.factorization, Finsupp.add_apply, Finsupp.smul_apply]
  by_cases hq : q = (R : ℕ)
  · rw [hq, Finsupp.single_eq_same, smul_eq_mul, mul_one]
    omega
  · rw [Finsupp.single_eq_of_ne hq, smul_zero, add_zero]
    by_cases hqp : q.Prime
    · exact (hab q hqp hq).symm
    · rw [Nat.factorization_eq_zero_of_not_prime _ hqp,
        Nat.factorization_eq_zero_of_not_prime _ hqp]

/-- **The planar square has the contacts of the square.** For every pair of graphs the
differences of the planar square generate the ideal `J(m, n)` of their intersection in the
arithmetic square. -/
theorem planarContact_eq_graphIdeal (m n : ℕ+) : planarContact m n = graphIdeal m n := by
  refine le_antisymm (planarContact_le_graphIdeal m n) ?_
  rcases eq_or_ne m n with hmn | hmn
  · rw [hmn]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨x, rfl⟩
    simp
  obtain ⟨r, hr, hne⟩ := exists_prime_factorization_ne hmn
  by_cases hex : ∃ q : ℕ, q.Prime ∧ q ≠ r ∧ (m : ℕ).factorization q ≠ (n : ℕ).factorization q
  · -- two primes separate the graphs: the planar contact is the unit ideal
    obtain ⟨q, hq, hqr, hq2⟩ := hex
    have htop : planarContact m n = ⊤ := by
      refine ideal_eq_top_of_forall_prime fun ℓ hℓ => ?_
      by_cases hℓr : r = ℓ
      · exact exists_mem_planarContact_not_dvd hq hℓ (fun h => hqr (h.trans hℓr.symm)) hq2
      · exact exists_mem_planarContact_not_dvd hr hℓ hℓr hne
    rw [htop]
    exact le_top
  · -- one prime: a chain
    push Not at hex
    obtain ⟨R, rfl⟩ : ∃ R : ℕ+, (R : ℕ) = r := ⟨⟨r, hr.pos⟩, rfl⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨j, hj, hn⟩ : ∃ j : ℕ, j ≠ 0 ∧ n = m * R ^ j :=
        ⟨_, (Nat.sub_pos_of_lt hlt).ne', eq_mul_prime_pow_of_factorization hr hex hlt⟩
      rw [hn]
      exact graphIdeal_le_planarContact_chain m hr hj
    · obtain ⟨j, hj, hm⟩ : ∃ j : ℕ, j ≠ 0 ∧ m = n * R ^ j :=
        ⟨_, (Nat.sub_pos_of_lt hgt).ne',
          eq_mul_prime_pow_of_factorization hr (fun q hq hqr => (hex q hq hqr).symm) hgt⟩
      rw [hm, graphIdeal_comm, planarContact_comm]
      exact graphIdeal_le_planarContact_chain n hr hj

/-! ### Payment and position -/

/-- **The planar square pays every contact.** An element of the planar square that vanishes on
the graphs of a finite set and not on `Γ_m` is at least as large on `Γ_m` as the contacts of
the normal form of the pairing with the set. -/
theorem sum_contact_le_log_abs_planarSquare {x : ghostRing} (hx : x ∈ planarSquare) (m : ℕ+)
    (S : Finset ℕ+) (hvan : ∀ n ∈ S, ghostComponent n x = 0) (hne : ghostComponent m x ≠ 0) :
    ∑ n ∈ S, ((if (m : ℕ) ∣ n then (Λ ((n : ℕ) / m) : ℝ) else 0) +
        (if (n : ℕ) ∣ m then (Λ ((m : ℕ) / n) : ℝ) else 0)) ≤
      Real.log |((ghostComponent m x : ℤ) : ℝ)| :=
  sum_contact_le_log_abs_of_isPlanar hx m S hvan hne

/-- **The planar square is larger than the ring of the coordinates**: it separates `Γ_1` and
`Γ_4` modulo `3`. -/
theorem payingRing_lt_planarSquare : payingRing < planarSquare := by
  refine lt_of_le_of_ne payingRing_le_planarSquare fun heq => ?_
  have hv : ((1 : ℕ+) : ℕ).factorization 2 ≠ ((4 : ℕ+) : ℕ).factorization 2 := by
    rw [PNat.one_coe, Nat.factorization_one, show ((4 : ℕ+) : ℕ) = 2 ^ 2 from rfl,
      Nat.prime_two.factorization_pow]
    simp
  obtain ⟨x, hx, hx1, hx4⟩ := exists_planar_separating (m := 1) (n := 4)
    (p := ⟨2, Nat.prime_two⟩) (ℓ := ⟨3, Nat.prime_three⟩) (by decide) hv
  have hmem : (planarOf x hx).1 ∈ payingRing := by
    rw [heq]
    exact (planarOf x hx).2
  have h3 := three_dvd_sub_of_mem_payingRing hmem
  change (3 : ℤ) ∣ x 1 - x 4 at h3
  rw [hx1, zero_sub, dvd_neg] at h3
  exact hx4 h3

/-- **The planar square is smaller than the square**: it does not contain `p − e_p`. -/
theorem planarSquare_ne_top : planarSquare ≠ ⊤ := by
  intro htop
  have h : (((2 : ℕ) : ℤ) : ghostRing) - orbit (primePNat ⟨2, Nat.prime_two⟩) ∈ planarSquare := by
    rw [htop]
    exact Subring.mem_top _
  exact not_isPlanar_prime_sub_orbit ⟨2, Nat.prime_two⟩ h

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ

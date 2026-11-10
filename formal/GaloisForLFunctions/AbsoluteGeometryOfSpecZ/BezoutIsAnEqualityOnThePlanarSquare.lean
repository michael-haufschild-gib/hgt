import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ThePlanarSquareHasTheContactsOfTheSquareAndPaysThem

/-!
# Bézout is an equality on the planar square

On a regular surface a function that vanishes on some curves through a point of another curve
`Γ` restricts to `Γ` with a zero of order the sum of the intersection numbers, and that order is
attained. For the graphs of the arithmetic square this fails: `p − e_p` vanishes on `Γ_p` and
`Γ_{p²}` and is `p` on the diagonal, where the two contacts multiply to `p²`.

On the planar square it holds, for every finite set of graphs:

* **The forced values** (`planarValues`, `planarValues_eq_prod`). For `m ∉ S` the values on `Γ_m`
  of the planar sections that vanish on the graphs of `S` form the ideal `Π_{n ∈ S} J(m, n)`, the
  product of the contact ideals of the square.
* **Attained** (`exists_planar_vanishing`). Every element of a contact ideal is a difference of
  one planar section on the two graphs, and the product over `n ∈ S` of sections `y − y_n` with
  `(y − y_n)_m` a generator of `J(m, n)` vanishes on `S` and has the product of the generators
  on `Γ_m`.
* **Forced** (`prod_contactNat_dvd_of_isPlanar`). A contact ideal `J(m, n)` contains every
  integer that divides exactly one of `m`, `n`, so its generator divides
  `p^{min(v_p m, v_p n)+1}` when the exponents of `p` differ, and is prime to `p` when `m` and
  `n` differ away from `p` (`contactNat_dvd_prime_pow`, `factorization_contactNat_le`). The
  payment along the chains gives these exponents in the value of a planar section.
* **Not in the square** (`exists_ghost_vanishing_not_mem_prod`). `p − e_p` vanishes on `Γ_p` and
  `Γ_{p²}`, and its value `p` on `Γ_1` is not in `J(1, p)·J(1, p²)`.

So the planar square is glued as the trace of a regular surface on its graphs: on the first
graphs `Γ_1, …, Γ_n` the last one carries the conditions `Π_{k < n} J(k, n)`.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### The contact numbers of the square -/

/-- The order of the contact of `Γ_m` and `Γ_n` in the square: the nonnegative generator of
`J(m, n)`. -/
def contactNat (m n : ℕ+) : ℕ := (Submodule.IsPrincipal.generator (graphIdeal m n)).natAbs

theorem graphIdeal_eq_span_contactNat (m n : ℕ+) :
    graphIdeal m n = Ideal.span {(contactNat m n : ℤ)} := by
  rw [contactNat, Int.span_natAbs, Ideal.span_singleton_generator]

theorem contactNat_dvd_of_mem {m n : ℕ+} {z : ℤ} (hz : z ∈ graphIdeal m n) :
    (contactNat m n : ℤ) ∣ z := by
  rw [graphIdeal_eq_span_contactNat] at hz
  exact Ideal.mem_span_singleton.mp hz

/-- When the exponents of `p` in `m` and `n` differ, the contact number divides
`p^{min(v_p m, v_p n)+1}`: this power divides exactly one of `m`, `n`. -/
theorem contactNat_dvd_prime_pow {m n : ℕ+} {p : ℕ} (hp : p.Prime)
    (hv : (m : ℕ).factorization p ≠ (n : ℕ).factorization p) :
    contactNat m n ∣ p ^ (min ((m : ℕ).factorization p) ((n : ℕ).factorization p) + 1) := by
  have hmem : ((p ^ (min ((m : ℕ).factorization p) ((n : ℕ).factorization p) + 1) : ℕ) : ℤ) ∈
      graphIdeal m n := by
    rw [graphIdeal_eq_span]
    refine Ideal.subset_span ⟨_, ?_, rfl⟩
    rcases lt_or_gt_of_ne hv with h | h
    · rw [min_eq_left h.le]
      exact Or.inr ⟨(hp.pow_dvd_iff_le_factorization n.ne_zero).mpr h, fun hd => by
        have := (hp.pow_dvd_iff_le_factorization m.ne_zero).mp hd
        omega⟩
    · rw [min_eq_right h.le]
      exact Or.inl ⟨(hp.pow_dvd_iff_le_factorization m.ne_zero).mpr h, fun hd => by
        have := (hp.pow_dvd_iff_le_factorization n.ne_zero).mp hd
        omega⟩
  exact Int.natCast_dvd_natCast.mp (contactNat_dvd_of_mem hmem)

theorem contactNat_ne_zero {m n : ℕ+} (hmn : m ≠ n) : contactNat m n ≠ 0 := by
  obtain ⟨p, hp, hv⟩ := exists_prime_factorization_ne hmn
  intro h0
  have h := contactNat_dvd_prime_pow hp hv
  rw [h0, zero_dvd_iff] at h
  exact pow_ne_zero _ hp.ne_zero h

/-- The exponent of `p` in the contact number of two distinct graphs: at most
`min(v_p m, v_p n) + 1` when the graphs lie on one chain at `p`, and zero otherwise. -/
theorem factorization_contactNat_le {m n : ℕ+} (hmn : m ≠ n) {p : ℕ} (hp : p.Prime) :
    (contactNat m n).factorization p ≤
      if (n : ℕ) * p ^ (m : ℕ).factorization p = (m : ℕ) * p ^ (n : ℕ).factorization p then
        min ((m : ℕ).factorization p) ((n : ℕ).factorization p) + 1 else 0 := by
  have hc0 := contactNat_ne_zero hmn
  split_ifs with hR
  · -- one chain at `p`: the exponents of `p` differ
    have hv : (m : ℕ).factorization p ≠ (n : ℕ).factorization p := by
      intro hv
      rw [hv] at hR
      exact hmn (PNat.eq (Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos _) hR)).symm
    have h := (Nat.factorization_le_iff_dvd hc0 (pow_ne_zero _ hp.ne_zero)).mpr
      (contactNat_dvd_prime_pow hp hv) p
    rwa [hp.factorization_pow, Finsupp.single_eq_same] at h
  · -- the graphs differ at a second prime `r`, and the contact number divides a power of `r`
    obtain ⟨r, hr, hrp, hvr⟩ : ∃ r : ℕ, r.Prime ∧ r ≠ p ∧
        (m : ℕ).factorization r ≠ (n : ℕ).factorization r := by
      by_contra hcon
      push Not at hcon
      refine hR (Nat.eq_of_factorization_eq
        (mul_ne_zero n.ne_zero (pow_ne_zero _ hp.ne_zero))
        (mul_ne_zero m.ne_zero (pow_ne_zero _ hp.ne_zero)) fun r => ?_)
      rw [Nat.factorization_mul n.ne_zero (pow_ne_zero _ hp.ne_zero),
        Nat.factorization_mul m.ne_zero (pow_ne_zero _ hp.ne_zero), Nat.factorization_pow,
        Nat.factorization_pow, hp.factorization, Finsupp.add_apply, Finsupp.add_apply,
        Finsupp.smul_apply, Finsupp.smul_apply]
      by_cases hrp : r = p
      · rw [hrp, Finsupp.single_eq_same, smul_eq_mul, smul_eq_mul, mul_one, mul_one]
        exact add_comm _ _
      · rw [Finsupp.single_eq_of_ne hrp, smul_zero, smul_zero, add_zero, add_zero]
        by_cases hrprime : r.Prime
        · exact (hcon r hrprime hrp).symm
        · rw [Nat.factorization_eq_zero_of_not_prime _ hrprime,
            Nat.factorization_eq_zero_of_not_prime _ hrprime]
    have h := (Nat.factorization_le_iff_dvd hc0 (pow_ne_zero _ hr.ne_zero)).mpr
      (contactNat_dvd_prime_pow hr hvr) p
    rwa [hr.factorization_pow, Finsupp.single_eq_of_ne (Ne.symm hrp)] at h

/-! ### The forced values are attained -/

/-- Every element of the contact ideal of the planar square is the difference of one planar
section on the two graphs. -/
theorem exists_of_mem_planarContact {m n : ℕ+} {z : ℤ} (hz : z ∈ planarContact m n) :
    ∃ x : planarSquare, ghostComponent m x.1 - ghostComponent n x.1 = z := by
  unfold planarContact at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, rfl⟩ := hz
    exact ⟨x, rfl⟩
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    exact ⟨x + y, by
      simp only [Subring.coe_add, map_add]
      ring⟩
  | smul c a _ ha =>
    obtain ⟨x, rfl⟩ := ha
    refine ⟨(c : planarSquare) * x, ?_⟩
    simp only [Subring.coe_mul, Subring.coe_intCast, map_mul, map_intCast, smul_eq_mul,
      Int.cast_id]
    ring

/-- **The forced zeros are attained.** For a finite set `S` of graphs a planar section vanishes
on `S` and has on `Γ_m` the product of the contact numbers of `Γ_m` with the graphs of `S`. -/
theorem exists_planar_vanishing (S : Finset ℕ+) (m : ℕ+) :
    ∃ x : planarSquare, (∀ n ∈ S, ghostComponent n x.1 = 0) ∧
      ghostComponent m x.1 = ∏ n ∈ S, (contactNat m n : ℤ) := by
  have h : ∀ n : ℕ+, ∃ y : planarSquare,
      ghostComponent m y.1 - ghostComponent n y.1 = (contactNat m n : ℤ) := fun n =>
    exists_of_mem_planarContact (by
      rw [planarContact_eq_graphIdeal, graphIdeal_eq_span_contactNat]
      exact Ideal.mem_span_singleton_self _)
  choose y hy using h
  refine ⟨∏ n ∈ S, (y n - ((ghostComponent n (y n).1 : ℤ) : planarSquare)), fun k hk => ?_, ?_⟩
  · have hcoe : ((∏ n ∈ S, (y n - ((ghostComponent n (y n).1 : ℤ) : planarSquare)) :
        planarSquare) : ghostRing) =
        ∏ n ∈ S, ((y n).1 - ((ghostComponent n (y n).1 : ℤ) : ghostRing)) := by
      simp
    rw [hcoe, map_prod]
    refine Finset.prod_eq_zero hk ?_
    rw [map_sub, map_intCast, Int.cast_id, sub_self]
  · have hcoe : ((∏ n ∈ S, (y n - ((ghostComponent n (y n).1 : ℤ) : planarSquare)) :
        planarSquare) : ghostRing) =
        ∏ n ∈ S, ((y n).1 - ((ghostComponent n (y n).1 : ℤ) : ghostRing)) := by
      simp
    rw [hcoe, map_prod]
    refine Finset.prod_congr rfl fun n _ => ?_
    rw [map_sub, map_intCast, Int.cast_id, hy n]

/-! ### The forced values are forced -/

/-- **Exact payment.** A planar sequence that vanishes on the graphs of a finite set `S` is
divisible on `Γ_m`, `m ∉ S`, by the product of the contact numbers of `Γ_m` with the graphs of
`S`. -/
theorem prod_contactNat_dvd_of_isPlanar {x : ℕ+ → ℤ} (hx : IsPlanar x) (m : ℕ+)
    (S : Finset ℕ+) (hm : m ∉ S) (hvan : ∀ n ∈ S, x n = 0) :
    (∏ n ∈ S, (contactNat m n : ℤ)) ∣ x m := by
  rcases eq_or_ne (x m) 0 with h0 | hne
  · rw [h0]
    exact dvd_zero _
  have hmn : ∀ n ∈ S, m ≠ n := fun n hn h => hm (h ▸ hn)
  have hG0 : ∏ n ∈ S, contactNat m n ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun n hn => contactNat_ne_zero (hmn n hn)
  have hN0 : (x m).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hne
  have hdvd : ∏ n ∈ S, contactNat m n ∣ (x m).natAbs := by
    refine (Nat.factorization_le_iff_dvd hG0 hN0).mp fun p => ?_
    by_cases hp : p.Prime
    · rw [Nat.factorization_prod fun n hn => contactNat_ne_zero (hmn n hn), Finset.sum_apply']
      calc ∑ n ∈ S, (contactNat m n).factorization p
          ≤ ∑ n ∈ S, if (n : ℕ) * p ^ (m : ℕ).factorization p =
              (m : ℕ) * p ^ (n : ℕ).factorization p then
              min ((m : ℕ).factorization p) ((n : ℕ).factorization p) + 1 else 0 :=
            Finset.sum_le_sum fun n hn => factorization_contactNat_le (hmn n hn) hp
        _ = ∑ n ∈ S.filter (fun n : ℕ+ => (n : ℕ) * p ^ (m : ℕ).factorization p =
              (m : ℕ) * p ^ (n : ℕ).factorization p),
              (min ((m : ℕ).factorization p) ((n : ℕ).factorization p) + 1) :=
            (Finset.sum_filter _ _).symm
        _ ≤ (x m).natAbs.factorization p := sum_chain_le_factorization hx m S hvan hne hp
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
      exact Nat.zero_le _
  rw [← Nat.cast_prod]
  exact Int.natCast_dvd.mpr hdvd

/-! ### Bézout as an equality -/

/-- The values on `Γ_m` of the planar sections that vanish on the graphs of `S`. -/
def planarValues (S : Finset ℕ+) (m : ℕ+) : Ideal ℤ :=
  Ideal.span {z | ∃ x ∈ planarSquare, (∀ n ∈ S, ghostComponent n x = 0) ∧ ghostComponent m x = z}

/-- **Bézout is an equality on the planar square.** For `m ∉ S` the values on `Γ_m` of the
planar sections vanishing on the graphs of `S` are the product of the contact ideals of `Γ_m`
with these graphs. -/
theorem planarValues_eq_prod {S : Finset ℕ+} {m : ℕ+} (hm : m ∉ S) :
    planarValues S m = ∏ n ∈ S, graphIdeal m n := by
  have hprod : ∏ n ∈ S, graphIdeal m n = Ideal.span {∏ n ∈ S, (contactNat m n : ℤ)} := by
    rw [← Ideal.prod_span_singleton]
    exact Finset.prod_congr rfl fun n _ => graphIdeal_eq_span_contactNat m n
  rw [hprod]
  refine le_antisymm (Ideal.span_le.mpr ?_) ?_
  · rintro z ⟨x, hx, hvan, rfl⟩
    exact Ideal.mem_span_singleton.mpr
      (prod_contactNat_dvd_of_isPlanar (mem_planarSquare.mp hx) m S hm hvan)
  · rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨x, hvan, hval⟩ := exists_planar_vanishing S m
    exact Ideal.subset_span ⟨x.1, x.2, hvan, hval⟩

/-- **In the square Bézout is not an equality.** `p − e_p` vanishes on `Γ_p` and `Γ_{p²}`, and
its value on the diagonal is not in the product of the two contact ideals. -/
theorem exists_ghost_vanishing_not_mem_prod (p : Nat.Primes) :
    ∃ x : ghostRing, ghostComponent (primePNat p) x = 0 ∧
      ghostComponent (primePNat p ^ 2) x = 0 ∧
      ghostComponent 1 x ∉ graphIdeal 1 (primePNat p) * graphIdeal 1 (primePNat p ^ 2) := by
  have hp : (primePNat p).Prime := p.2
  have hcomp : ∀ n : ℕ+, ghostComponent n ((((p : ℕ) : ℤ) : ghostRing) - orbit (primePNat p)) =
      ((p : ℕ) : ℤ) - if (p : ℕ) ∣ n then ((p : ℕ) : ℤ) else 0 := by
    intro n
    rw [map_sub, map_intCast, ghostComponent_apply, orbit_apply, primePNat_coe]
    simp
  refine ⟨(((p : ℕ) : ℤ) : ghostRing) - orbit (primePNat p), ?_, ?_, ?_⟩
  · rw [hcomp, primePNat_coe, if_pos dvd_rfl, sub_self]
  · rw [hcomp, PNat.pow_coe, primePNat_coe, if_pos (dvd_pow_self _ two_ne_zero), sub_self]
  · rw [hcomp, PNat.one_coe, if_neg (by rw [Nat.dvd_one]; exact p.2.ne_one), sub_zero]
    have h1 : graphIdeal 1 (primePNat p) = Ideal.span {((p : ℕ) : ℤ)} := by
      have := graphIdeal_one_prime_pow hp one_ne_zero
      rwa [pow_one] at this
    have h2 : graphIdeal 1 (primePNat p ^ 2) = Ideal.span {((p : ℕ) : ℤ)} :=
      graphIdeal_one_prime_pow hp two_ne_zero
    rw [h1, h2, Ideal.span_singleton_mul_span_singleton, Ideal.mem_span_singleton]
    intro hdvd
    have hpz : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp p.2
    have h' : ((p : ℕ) : ℤ) * (p : ℕ) ∣ ((p : ℕ) : ℤ) * 1 := by rwa [mul_one]
    exact hpz.not_dvd_one ((mul_dvd_mul_iff_left hpz.ne_zero).mp h')

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ

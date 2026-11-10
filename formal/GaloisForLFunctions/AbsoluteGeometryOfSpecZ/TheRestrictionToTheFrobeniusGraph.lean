import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheArithmeticSquareIsCofree

/-!
# The restriction to the Frobenius graph

Stepanov's count restricts a section vanishing to order `ℓ` on the diagonal to the graph of the
Frobenius and counts its zeros there. On the arithmetic square the restriction to `Γ_p` is

  `x_p = x_1^p + p · (δ_p x)_1`   (`ghostComponent_prime_eq_pow_add_delta`):

the `p`-th power of the restriction to the diagonal plus `p` times the derivative at `p`.

* **First order is free.** If `x` vanishes on the diagonal, `p ∣ x_{p^k}` for every prime `p` and
  every `k ≥ 1` (`prime_dvd_ghostComponent_prime_pow`): one linear condition gives a zero at the
  fixed point of every Frobenius.
* **Higher order is the derivative, and the derivatives are independent.** For `x_1 = 0`,
  `(δ_p x)_1 = b_p(x)`, the necklace coordinate (`ghostComponent_one_delta_eq_coord`), and
  `p^{m+1} ∣ x_p ⟺ p^m ∣ b_p(x)` (`pow_succ_dvd_ghostComponent_prime_iff`). The coordinates at
  different primes are free: every prescription of `x_p/p` on a finite set of primes is realized
  (`exists_ghostComponent_prime_eq`). There is one derivative for each prime, not one for all.
* **The forced zeros are the contacts.** The restriction to `Γ_n` of the `ℓ`-th power of the ideal of
  the diagonal is `J(1, n)^ℓ` (`map_ghostComponent_ker_pow`): `(p^ℓ)` if `n` is a power of `p`
  (`map_ghostComponent_ker_pow_prime_pow`), attained by the orbit `e_p^ℓ`
  (`ghostComponent_orbit_pow`), and the unit ideal otherwise. A section vanishing to order `ℓ` on
  the diagonal has no forced zero on `Γ_n` beyond `ℓ · (Γ_1 ∩ Γ_n)`: Stepanov's count on a graph
  returns the product formula.
-/

open Finset

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### The restriction formula -/

/-- **The restriction to `Γ_p`**: `x_p = x_1^p + p (δ_p x)_1`. -/
theorem ghostComponent_prime_eq_pow_add_delta (p : ℕ+) (hp : p.Prime) (x : ghostRing) :
    ghostComponent p x =
      ghostComponent 1 x ^ (p : ℕ) + ((p : ℕ) : ℤ) * ghostComponent 1 (delta p hp x) := by
  have h := congrArg (ghostComponent 1) (frobenius_eq_pow_add_delta p hp x)
  rw [ghostComponent_frobenius, mul_one, map_add, map_pow, map_mul, map_natCast] at h
  exact h

theorem ghostComponent_one_eq_coord (x : ghostRing) : ghostComponent 1 x = coord x 1 := by
  rw [ghostComponent_eq_sum_coord, PNat.one_coe, Nat.divisors_one, Finset.sum_singleton]
  simp

/-- `x_p = x_1 + p b_p(x)`. -/
theorem ghostComponent_prime_eq (x : ghostRing) {p : ℕ+} (hp : p.Prime) :
    ghostComponent p x = ghostComponent 1 x + ((p : ℕ) : ℤ) * coord x p := by
  have hp' : (p : ℕ).Prime := hp
  rw [ghostComponent_eq_sum_coord, hp'.divisors, Finset.sum_pair hp'.one_lt.ne,
    ghostComponent_one_eq_coord]
  simp

/-- **On the diagonal ideal the derivative at `p` is the necklace coordinate at `p`.** -/
theorem ghostComponent_one_delta_eq_coord {x : ghostRing} (hx : ghostComponent 1 x = 0) {p : ℕ+}
    (hp : p.Prime) : ghostComponent 1 (delta p hp x) = coord x p := by
  have hp' : (p : ℕ).Prime := hp
  have hp0 : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hp'.ne_zero
  have h1 := ghostComponent_prime_eq_pow_add_delta p hp x
  have h2 := ghostComponent_prime_eq x hp
  rw [hx, zero_pow hp'.ne_zero, zero_add] at h1
  rw [hx, zero_add] at h2
  exact mul_left_cancel₀ hp0 (h1.symm.trans h2)

/-- **Order `m + 1` at `p` on `Γ_p` is order `m` of the derivative**: for `x_1 = 0`,
`p^{m+1} ∣ x_p ⟺ p^m ∣ b_p(x)`. -/
theorem pow_succ_dvd_ghostComponent_prime_iff {x : ghostRing} (hx : ghostComponent 1 x = 0)
    {p : ℕ+} (hp : p.Prime) (m : ℕ) :
    ((p : ℕ) : ℤ) ^ (m + 1) ∣ ghostComponent p x ↔ ((p : ℕ) : ℤ) ^ m ∣ coord x p := by
  have hp' : (p : ℕ).Prime := hp
  have hp0 : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hp'.ne_zero
  rw [ghostComponent_prime_eq x hp, hx, zero_add, pow_succ']
  exact mul_dvd_mul_iff_left hp0

/-- **First order is free.** A section vanishing on the diagonal vanishes at `p` on every graph
`Γ_{p^k}`, `k ≥ 1`. -/
theorem prime_dvd_ghostComponent_prime_pow {x : ghostRing} (hx : ghostComponent 1 x = 0) {p : ℕ+}
    (hp : p.Prime) {k : ℕ} (hk : k ≠ 0) : ((p : ℕ) : ℤ) ∣ ghostComponent (p ^ k) x := by
  have hmem : ghostComponent 1 x - ghostComponent (p ^ k) x ∈ graphIdeal 1 (p ^ k) :=
    Ideal.subset_span ⟨x, rfl⟩
  rw [graphIdeal_one_prime_pow hp hk, hx, zero_sub] at hmem
  exact (dvd_neg).mp (Ideal.mem_span_singleton.mp hmem)

/-- **The derivatives at different primes are independent.** Every prescription `x_p = p t_p` on a
finite set of primes is realized by a section vanishing on the diagonal. -/
theorem exists_ghostComponent_prime_eq (S : Finset ℕ+) (hS : ∀ p ∈ S, p.Prime) (t : ℕ+ → ℤ) :
    ∃ x : ghostRing, ghostComponent 1 x = 0 ∧
      ∀ p ∈ S, ghostComponent p x = ((p : ℕ) : ℤ) * t p := by
  refine ⟨∑ q ∈ S, t q • orbit q, ?_, fun p hpS => ?_⟩
  · rw [map_sum]
    refine Finset.sum_eq_zero fun q hq => ?_
    have hq' : (q : ℕ).Prime := hS q hq
    have hq1 : ¬ (q : ℕ) ∣ ((1 : ℕ+) : ℕ) := by
      rw [PNat.one_coe, Nat.dvd_one]
      exact hq'.one_lt.ne'
    rw [map_zsmul, ghostComponent_apply, orbit_apply, if_neg hq1, smul_zero]
  · rw [map_sum, Finset.sum_eq_single p]
    · rw [map_zsmul, ghostComponent_apply, orbit_apply, if_pos dvd_rfl, smul_eq_mul, mul_comm]
    · intro q hq hqp
      have hnd : ¬ (q : ℕ) ∣ (p : ℕ) := fun hd =>
        hqp (PNat.eq ((Nat.prime_dvd_prime_iff_eq (hS q hq) (hS p hpS)).mp hd))
      rw [map_zsmul, ghostComponent_apply, orbit_apply, if_neg hnd, smul_zero]
    · exact fun h => absurd hpS h

/-! ### The forced zeros are the contacts -/

/-- The restriction to `Γ_n` of the ideal of the diagonal is the graph ideal. -/
theorem map_ghostComponent_ker (n : ℕ+) :
    Ideal.map (ghostComponent n) (RingHom.ker (ghostComponent 1)) = graphIdeal 1 n := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun x hx => ?_) (Ideal.span_le.mpr ?_)
  · -- `x_1 = 0`: `x_n = −(x_1 − x_n)`
    have hx0 : ghostComponent 1 x = 0 := hx
    have hmem : ghostComponent 1 x - ghostComponent n x ∈ graphIdeal 1 n :=
      Ideal.subset_span ⟨x, rfl⟩
    rw [hx0, zero_sub] at hmem
    exact (Ideal.neg_mem_iff _).mp hmem
  · -- subtract the constant `x_1`
    rintro _ ⟨x, rfl⟩
    have hker : x - ((ghostComponent 1 x : ℤ) : ghostRing) ∈ RingHom.ker (ghostComponent 1) := by
      rw [RingHom.mem_ker, map_sub, map_intCast, Int.cast_id, sub_self]
    have h := Ideal.mem_map_of_mem (ghostComponent n) hker
    rw [map_sub, map_intCast, Int.cast_id] at h
    have h' := (Ideal.neg_mem_iff _).mpr h
    rwa [neg_sub] at h'

/-- **The forced zeros of order `ℓ`.** The restriction to `Γ_n` of the `ℓ`-th power of the ideal of
the diagonal is `J(1, n)^ℓ`: an ideal power restricts to the power of the restriction. -/
theorem map_ghostComponent_ker_pow (n : ℕ+) (l : ℕ) :
    Ideal.map (ghostComponent n) (RingHom.ker (ghostComponent 1) ^ l) = graphIdeal 1 n ^ l := by
  rw [Ideal.map_pow, map_ghostComponent_ker]

/-- On the graph of a prime power the forced zero is `p^ℓ`. -/
theorem map_ghostComponent_ker_pow_prime_pow {p : ℕ+} (hp : p.Prime) {k : ℕ} (hk : k ≠ 0) (l : ℕ) :
    Ideal.map (ghostComponent (p ^ k)) (RingHom.ker (ghostComponent 1) ^ l) =
      Ideal.span {((p : ℕ) : ℤ) ^ l} := by
  rw [map_ghostComponent_ker_pow, graphIdeal_one_prime_pow hp hk, Ideal.span_singleton_pow]

/-- Off the prime powers nothing is forced. -/
theorem map_ghostComponent_ker_pow_eq_top {n : ℕ+} (hn : 1 < n) (h : ¬ IsPrimePow (n : ℕ))
    (l : ℕ) : Ideal.map (ghostComponent n) (RingHom.ker (ghostComponent 1) ^ l) = ⊤ := by
  rw [map_ghostComponent_ker_pow, graphIdeal_one_eq_top hn h, Ideal.top_pow]

/-- **Stepanov's inequality on a graph.** A section vanishing to order `ℓ` on the diagonal is
divisible by `p^ℓ` on `Γ_{p^k}`. -/
theorem pow_dvd_ghostComponent_of_mem_ker_pow {p : ℕ+} (hp : p.Prime) {k : ℕ} (hk : k ≠ 0) {l : ℕ}
    {x : ghostRing} (hx : x ∈ RingHom.ker (ghostComponent 1) ^ l) :
    ((p : ℕ) : ℤ) ^ l ∣ ghostComponent (p ^ k) x := by
  have h := Ideal.mem_map_of_mem (ghostComponent (p ^ k)) hx
  rw [map_ghostComponent_ker_pow_prime_pow hp hk] at h
  exact Ideal.mem_span_singleton.mp h

/-- **The bound is attained**: `e_p^ℓ` vanishes to order `ℓ` on the diagonal and equals `p^ℓ` on
`Γ_{p^k}`. -/
theorem ghostComponent_orbit_pow {p : ℕ+} (hp : p.Prime) {k : ℕ} (hk : k ≠ 0) (l : ℕ) :
    orbit p ^ l ∈ RingHom.ker (ghostComponent 1) ^ l ∧
      ghostComponent (p ^ k) (orbit p ^ l) = ((p : ℕ) : ℤ) ^ l := by
  have hp' : (p : ℕ).Prime := hp
  refine ⟨Ideal.pow_mem_pow ?_ l, ?_⟩
  · have h1 : ¬ (p : ℕ) ∣ ((1 : ℕ+) : ℕ) := by
      rw [PNat.one_coe, Nat.dvd_one]; exact hp'.one_lt.ne'
    rw [RingHom.mem_ker, ghostComponent_apply, orbit_apply, if_neg h1]
  · have hd : (p : ℕ) ∣ ((p ^ k : ℕ+) : ℕ) := by
      rw [PNat.pow_coe]; exact dvd_pow_self _ hk
    rw [map_pow, ghostComponent_apply, orbit_apply, if_pos hd]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ

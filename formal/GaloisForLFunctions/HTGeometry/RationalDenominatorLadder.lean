import Mathlib

/-!
# Denominator ladders for subgroups of the rationals

A subgroup of `ℚ` containing `1` is the increasing union of the cyclic groups `(1/a_K)ℤ` for a
divisibility ladder of positive integers `a_K`.  The ladder is built from an enumeration of the
subgroup: `a_K` is the least common multiple of the denominators of the first `K + 1` members, and
the reciprocal of that lcm again lies in the subgroup because a subgroup containing a fraction in
lowest terms contains the reciprocal of its denominator (Bézout), and reciprocals of two
denominators generate the reciprocal of their lcm (Bézout again).
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- An integer multiple of a rational is an integer exactly when the denominator divides. -/
theorem exists_intCast_natMul_iff_den_dvd {n : ℕ} (hn : 0 < n) (q : ℚ) :
    (∃ m : ℤ, (n : ℚ) * q = m) ↔ q.den ∣ n := by
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  constructor
  · rintro ⟨m, hm⟩
    have hq : q = Rat.divInt m (n : ℤ) := by
      rw [Rat.divInt_eq_div]
      field_simp
      rw [← hm]
      push_cast
      ring
    have := Rat.den_dvd m (n : ℤ)
    rw [← hq] at this
    exact_mod_cast this
  · rintro ⟨t, ht⟩
    refine ⟨q.num * t, ?_⟩
    have hkey : (q.den : ℚ) * q = (q.num : ℚ) := Rat.den_mul_eq_num q
    rw [ht]
    push_cast
    rw [mul_comm ((q.den : ℚ)) (t : ℚ), mul_assoc, hkey]
    ring

/-- A subgroup of `ℚ` containing `1` and a fraction contains the reciprocal of its denominator. -/
theorem one_div_den_mem (S : AddSubgroup ℚ) (h1 : (1 : ℚ) ∈ S) {q : ℚ} (hq : q ∈ S) :
    (1 : ℚ) / (q.den : ℚ) ∈ S := by
  have hcop : IsCoprime (q.num) (q.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using q.reduced
  obtain ⟨x, y, hxy⟩ := hcop
  have hden : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.2 q.den_nz
  have hmem : (x : ℚ) • q + (y : ℚ) • (1 : ℚ) ∈ S := by
    simpa using S.add_mem (S.zsmul_mem hq x) (S.zsmul_mem h1 y)
  have hval : (x : ℚ) • q + (y : ℚ) • (1 : ℚ) = 1 / (q.den : ℚ) := by
    have hkey : (q.den : ℚ) * q = (q.num : ℚ) := Rat.den_mul_eq_num q
    have hxy' : (x : ℚ) * (q.num : ℚ) + (y : ℚ) * (q.den : ℚ) = 1 := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hxy
    rw [smul_eq_mul, smul_eq_mul, mul_one, eq_div_iff hden,
      show ((x : ℚ) * q + y) * (q.den : ℚ) = (x : ℚ) * ((q.den : ℚ) * q) + y * (q.den : ℚ) by ring,
      hkey]
    exact hxy'
  rwa [hval] at hmem

/-- Reciprocals of two denominators generate the reciprocal of their lcm. -/
theorem one_div_lcm_mem (S : AddSubgroup ℚ) {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (hdm : (1 : ℚ) / (d : ℚ) ∈ S) (hem : (1 : ℚ) / (e : ℚ) ∈ S) :
    (1 : ℚ) / ((Nat.lcm d e : ℕ) : ℚ) ∈ S := by
  have hd0 : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have he0 : (e : ℚ) ≠ 0 := Nat.cast_ne_zero.2 he.ne'
  have hg : (Nat.gcd d e : ℤ) = (d : ℤ) * Nat.gcdA d e + (e : ℤ) * Nat.gcdB d e :=
    Nat.gcd_eq_gcd_ab d e
  have hlcm : (Nat.gcd d e) * (Nat.lcm d e) = d * e := Nat.gcd_mul_lcm d e
  have hgpos : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_left _ hd
  have hlpos : 0 < Nat.lcm d e := Nat.pos_of_ne_zero (Nat.lcm_ne_zero hd.ne' he.ne')
  have hmem : (Nat.gcdB d e : ℚ) • ((1 : ℚ) / (d : ℚ))
      + (Nat.gcdA d e : ℚ) • ((1 : ℚ) / (e : ℚ)) ∈ S := by
    simpa using S.add_mem (S.zsmul_mem hdm (Nat.gcdB d e)) (S.zsmul_mem hem (Nat.gcdA d e))
  have hval : (Nat.gcdB d e : ℚ) • ((1 : ℚ) / (d : ℚ))
      + (Nat.gcdA d e : ℚ) • ((1 : ℚ) / (e : ℚ)) = (1 : ℚ) / ((Nat.lcm d e : ℕ) : ℚ) := by
    have hgQ : ((Nat.gcd d e : ℕ) : ℚ)
        = (d : ℚ) * (Nat.gcdA d e : ℚ) + (e : ℚ) * (Nat.gcdB d e : ℚ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hg
    have hlcmQ : ((Nat.gcd d e : ℕ) : ℚ) * ((Nat.lcm d e : ℕ) : ℚ) = (d : ℚ) * (e : ℚ) := by
      exact_mod_cast congrArg (fun z : ℕ => (z : ℚ)) hlcm
    have hl0 : ((Nat.lcm d e : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hlpos.ne'
    rw [smul_eq_mul, smul_eq_mul]
    field_simp
    nlinarith [hgQ, hlcmQ]
  rwa [hval] at hmem

/-- The lcm ladder of the denominators of an enumeration. -/
noncomputable def denLadder (e : ℕ → ℚ) (K : ℕ) : ℕ :=
  (Finset.range (K + 1)).lcm (fun i => (e i).den)

theorem denLadder_pos (e : ℕ → ℚ) (K : ℕ) : 0 < denLadder e K := by
  refine Nat.pos_of_ne_zero ?_
  rw [denLadder, Ne, Finset.lcm_eq_zero_iff]
  rintro ⟨i, -, hi⟩
  exact (e i).den_nz hi

theorem denLadder_dvd_succ (e : ℕ → ℚ) (K : ℕ) : denLadder e K ∣ denLadder e (K + 1) := by
  refine Finset.lcm_dvd fun i hi => ?_
  have hi' : i < K + 1 := Finset.mem_range.1 hi
  exact Finset.dvd_lcm (Finset.mem_range.2 (by omega : i < K + 2))

theorem den_dvd_denLadder (e : ℕ → ℚ) (K : ℕ) : (e K).den ∣ denLadder e K :=
  Finset.dvd_lcm (Finset.mem_range.2 (by omega))

theorem one_div_denLadder_mem (S : AddSubgroup ℚ) (h1 : (1 : ℚ) ∈ S) {e : ℕ → ℚ}
    (he : ∀ i, e i ∈ S) (K : ℕ) : (1 : ℚ) / ((denLadder e K : ℕ) : ℚ) ∈ S := by
  induction K with
  | zero =>
    have : denLadder e 0 = (e 0).den := by
      simp [denLadder, Finset.range_one, Finset.lcm_singleton, normalize_eq]
    rw [this]
    exact one_div_den_mem S h1 (he 0)
  | succ K ih =>
    have hstep : denLadder e (K + 1) = Nat.lcm (denLadder e K) (e (K + 1)).den := by
      rw [denLadder, denLadder, Finset.range_add_one, Finset.lcm_insert]
      simp [Nat.lcm_comm, lcm_eq_nat_lcm]
    rw [hstep]
    exact one_div_lcm_mem S (denLadder_pos e K) (Nat.pos_of_ne_zero (e (K + 1)).den_nz) ih
      (one_div_den_mem S h1 (he (K + 1)))

/-- **Denominator ladder.**  A subgroup of `ℚ` containing `1` is exactly the set of rationals whose
denominator divides some member of a divisibility ladder of positive integers. -/
theorem exists_denLadder (S : AddSubgroup ℚ) (h1 : (1 : ℚ) ∈ S) :
    ∃ a : ℕ → ℕ, (∀ K, 0 < a K) ∧ (∀ K, a K ∣ a (K + 1)) ∧
      ∀ q : ℚ, q ∈ S ↔ ∃ K, q.den ∣ a K := by
  obtain ⟨e, he⟩ := (Set.to_countable (S : Set ℚ)).exists_eq_range ⟨0, S.zero_mem⟩
  have hmem : ∀ i, e i ∈ S := fun i => by
    have : e i ∈ (S : Set ℚ) := by rw [he]; exact ⟨i, rfl⟩
    exact this
  refine ⟨denLadder e, denLadder_pos e, denLadder_dvd_succ e, fun q => ⟨?_, ?_⟩⟩
  · intro hq
    have : q ∈ Set.range e := by rw [← he]; exact hq
    obtain ⟨K, rfl⟩ := this
    exact ⟨K, den_dvd_denLadder e K⟩
  · rintro ⟨K, t, ht⟩
    have hL := one_div_denLadder_mem S h1 hmem K
    have hden : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.2 q.den_nz
    have hL0 : ((denLadder e K : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (denLadder_pos e K).ne'
    have hval : ((q.num * t : ℤ) : ℚ) • ((1 : ℚ) / ((denLadder e K : ℕ) : ℚ)) = q := by
      have hkey : (q.den : ℚ) * q = (q.num : ℚ) := Rat.den_mul_eq_num q
      have hLq : ((denLadder e K : ℕ) : ℚ) = (q.den : ℚ) * (t : ℚ) := by
        exact_mod_cast congrArg (fun z : ℕ => (z : ℚ)) ht
      have ht0 : (t : ℚ) ≠ 0 := by
        intro hc
        rw [hc, mul_zero] at hLq
        exact hL0 hLq
      rw [smul_eq_mul, hLq]
      push_cast
      rw [← hkey]
      field_simp
    rw [← hval]
    exact S.zsmul_mem hL _

/-- Divisibility propagates along the ladder. -/
theorem ladder_dvd_of_le {a : ℕ → ℕ} (hstep : ∀ K, a K ∣ a (K + 1)) {K k : ℕ} (hk : K ≤ k) :
    a K ∣ a k := by
  induction k with
  | zero => rw [Nat.le_zero.1 hk]
  | succ k ih =>
    rcases Nat.lt_or_ge K (k + 1) with h | h
    · exact dvd_trans (ih (by omega)) (hstep k)
    · rw [show K = k + 1 by omega]

end GaloisForLFunctions.HTGeometry

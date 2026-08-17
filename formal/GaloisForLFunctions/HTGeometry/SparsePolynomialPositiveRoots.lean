import Mathlib

/-!
# A Descartes-type bound on the positive roots of a sparse real polynomial

A nonzero real polynomial with `k` nonzero coefficients has at most `k − 1` strictly positive roots.
This is the classical sparse (Descartes) bound in the form needed to certify **generalized
Vandermonde** determinants, and mathlib has no version of it.

The proof is the standard Rolle induction: dividing out the largest power of `X` does not change the
positive roots and does not change the number of nonzero coefficients, so one may assume a nonzero
constant term; differentiating then kills that coefficient, shrinking the support by at least one,
while Rolle interleaves a root of `p'` strictly between any two consecutive positive roots of `p`.

## Main results

* `posRoots` — the finset of strictly positive real roots;
* `card_posRoots_succ_le` — `#posRoots p + 1 ≤ #p.support` for `p ≠ 0`.
-/

namespace GaloisForLFunctions

open Polynomial

/-! ### Positive roots of a sparse real polynomial -/

/-- The set of strictly positive real roots of a polynomial. -/
noncomputable def posRoots (p : ℝ[X]) : Finset ℝ :=
  p.roots.toFinset.filter (fun t => 0 < t)

theorem mem_posRoots {p : ℝ[X]} (hp : p ≠ 0) {t : ℝ} :
    t ∈ posRoots p ↔ 0 < t ∧ p.eval t = 0 := by
  classical
  rw [posRoots, Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hp]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem posRoots_X_mul {q : ℝ[X]} (hq : q ≠ 0) : posRoots (X * q) = posRoots q := by
  have hXq : (X : ℝ[X]) * q ≠ 0 := mul_ne_zero Polynomial.X_ne_zero hq
  ext t
  rw [mem_posRoots hXq, mem_posRoots hq]
  simp only [Polynomial.eval_mul, Polynomial.eval_X]
  constructor
  · rintro ⟨ht, h⟩
    refine ⟨ht, ?_⟩
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' ht.ne'
    · exact h'
  · rintro ⟨ht, h⟩
    exact ⟨ht, by rw [h, mul_zero]⟩

theorem card_support_X_mul (q : ℝ[X]) : ((X : ℝ[X]) * q).support.card = q.support.card := by
  classical
  have hset : ((X : ℝ[X]) * q).support
      = q.support.map ⟨fun n => n + 1, fun a b h => by simpa using h⟩ := by
    ext n
    simp only [Polynomial.mem_support_iff, Finset.mem_map, Function.Embedding.coeFn_mk]
    cases n with
    | zero => simp
    | succ k =>
        rw [Polynomial.coeff_X_mul]
        constructor
        · intro h
          exact ⟨k, h, rfl⟩
        · rintro ⟨m, hm, hmk⟩
          have hmk' : m = k := by omega
          subst hmk'
          exact hm
  rw [hset, Finset.card_map]

/-- Every nonzero polynomial has the same positive roots and the same number of nonzero
coefficients as one with a nonzero constant term. -/
theorem exists_coeff_zero_ne_of_ne_zero : ∀ (n : ℕ) (p : ℝ[X]), p ≠ 0 → p.natDegree ≤ n →
    ∃ q : ℝ[X], q ≠ 0 ∧ q.coeff 0 ≠ 0 ∧ q.support.card = p.support.card ∧
      posRoots q = posRoots p := by
  intro n
  induction n with
  | zero =>
      intro p hp hdeg
      refine ⟨p, hp, ?_, rfl, rfl⟩
      intro h0
      refine hp ?_
      have hc := Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hdeg)
      rw [h0, map_zero] at hc
      exact hc
  | succ n ih =>
      intro p hp hdeg
      by_cases h0 : p.coeff 0 = 0
      · have hdX : p.divX ≠ 0 := by
          intro h
          rw [Polynomial.divX_eq_zero_iff, h0, map_zero] at h
          exact hp h
        have hpx : p = X * p.divX := by
          have h := Polynomial.X_mul_divX_add p
          rw [h0, map_zero, add_zero] at h
          exact h.symm
        have hdegX : p.divX.natDegree ≤ n := by
          rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
          omega
        obtain ⟨q, hq0, hqc, hqs, hqr⟩ := ih p.divX hdX hdegX
        refine ⟨q, hq0, hqc, ?_, ?_⟩
        · rw [hqs]
          conv_rhs => rw [hpx]
          rw [card_support_X_mul]
        · rw [hqr]
          conv_rhs => rw [hpx]
          rw [posRoots_X_mul hdX]
      · exact ⟨p, hp, h0, rfl, rfl⟩

theorem card_support_derivative_succ_le {q : ℝ[X]} (hq : q.coeff 0 ≠ 0) :
    (derivative q).support.card + 1 ≤ q.support.card := by
  classical
  have hsub : (derivative q).support ⊆ (q.support.erase 0).image (fun n => n - 1) := by
    intro n hn
    rw [Polynomial.mem_support_iff, Polynomial.coeff_derivative] at hn
    rw [Finset.mem_image]
    refine ⟨n + 1, ?_, by omega⟩
    rw [Finset.mem_erase, Polynomial.mem_support_iff]
    refine ⟨by omega, ?_⟩
    intro h
    rw [h, zero_mul] at hn
    exact hn rfl
  have h0mem : (0 : ℕ) ∈ q.support := Polynomial.mem_support_iff.mpr hq
  have hcard : (derivative q).support.card ≤ (q.support.erase 0).card :=
    le_trans (Finset.card_le_card hsub) Finset.card_image_le
  rw [Finset.card_erase_of_mem h0mem] at hcard
  have hpos : 1 ≤ q.support.card := Finset.card_pos.mpr ⟨0, h0mem⟩
  omega

/-- **Descartes-type sparse root bound.**  A nonzero real polynomial with `k` nonzero coefficients
has at most `k − 1` strictly positive roots. -/
theorem card_posRoots_succ_le_card_support : ∀ (k : ℕ) (p : ℝ[X]), p ≠ 0 → p.support.card ≤ k →
    (posRoots p).card + 1 ≤ p.support.card := by
  intro k
  induction k with
  | zero =>
      intro p hp hk
      exact absurd (Polynomial.support_eq_empty.mp (Finset.card_eq_zero.mp (Nat.le_zero.mp hk))) hp
  | succ k ih =>
      intro p hp hkle
      obtain ⟨q, hq0, hqc, hqs, hqr⟩ := exists_coeff_zero_ne_of_ne_zero p.natDegree p hp le_rfl
      rw [← hqs, ← hqr]
      by_cases hd : derivative q = 0
      · have hconst : q = C (q.coeff 0) :=
          Polynomial.eq_C_of_natDegree_eq_zero
            (Polynomial.derivative_eq_zero.mp hd)
        have hpr : posRoots q = ∅ := by
          ext t
          simp only [Finset.notMem_empty, iff_false]
          rw [mem_posRoots hq0]
          rintro ⟨-, he⟩
          rw [hconst, Polynomial.eval_C] at he
          exact hqc he
        rw [hpr, Finset.card_empty, zero_add]
        exact Finset.card_pos.mpr ⟨0, Polynomial.mem_support_iff.mpr hqc⟩
      · have hdsupp : (derivative q).support.card + 1 ≤ q.support.card :=
          card_support_derivative_succ_le hqc
        have hdle : (derivative q).support.card ≤ k := by omega
        have hIH := ih (derivative q) hd hdle
        have hrolle : (posRoots q).card
            ≤ ((posRoots (derivative q)) \ (posRoots q)).card + 1 := by
          refine Finset.card_le_sdiff_of_interleaved ?_
          intro x hx y hy hxy _
          rw [mem_posRoots hq0] at hx hy
          obtain ⟨z, hz, hz0⟩ := exists_deriv_eq_zero hxy
            ((Polynomial.continuous_aeval q).continuousOn) (hx.2.trans hy.2.symm)
          refine ⟨z, ?_, hz.1, hz.2⟩
          rw [mem_posRoots hd]
          refine ⟨lt_trans hx.1 hz.1, ?_⟩
          rw [← Polynomial.deriv q]
          exact hz0
        have hle2 : ((posRoots (derivative q)) \ (posRoots q)).card
            ≤ (posRoots (derivative q)).card := Finset.card_le_card Finset.sdiff_subset
        omega

/-- A nonzero real polynomial has at most `support.card − 1` strictly positive roots. -/
theorem card_posRoots_succ_le {p : ℝ[X]} (hp : p ≠ 0) :
    (posRoots p).card + 1 ≤ p.support.card :=
  card_posRoots_succ_le_card_support p.support.card p hp le_rfl

end GaloisForLFunctions

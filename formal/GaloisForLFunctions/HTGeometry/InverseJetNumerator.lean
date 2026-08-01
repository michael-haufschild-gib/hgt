import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# The numerators of the inverse jet coefficients

Inverting a jet whose constant term is the unknown `a` produces coefficients with a power of `a` in
the denominator.  Clearing that denominator leaves a polynomial in `a`, and these numerators satisfy
a closed recursion in which each term carries an explicit power of `a`.

The point is the degree: the `k`-th numerator has degree at most `k` in the unknown constant term.
That is what makes the fibre equation of a one-deep observation a polynomial equation of degree
exactly the horizon length, with the observed reciprocal tail coefficient as its leading
coefficient.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {R : Type*} [CommRing R]

/-- The numerator of the `k`-th coefficient of the inverse jet, as a polynomial in the unknown
constant term.  The `k`-th coefficient of the inverse is this polynomial divided by the `(k+1)`-st
power of the constant term. -/
noncomputable def invNumerator (u : ℕ → R) : ℕ → R[X]
  | 0 => 1
  | (k + 1) =>
      -∑ i ∈ Finset.range (k + 1), C (u (i + 1)) * X ^ i * invNumerator u (k - i)

theorem invNumerator_zero (u : ℕ → R) : invNumerator u 0 = 1 := by
  rw [invNumerator]

theorem invNumerator_succ (u : ℕ → R) (k : ℕ) :
    invNumerator u (k + 1) =
      -∑ i ∈ Finset.range (k + 1), C (u (i + 1)) * X ^ i * invNumerator u (k - i) := by
  rw [invNumerator]

/-- **The `k`-th numerator has degree at most `k`.**  Each term of the recursion carries `a ^ i`
against a numerator of index `k - i`, so the degrees add to at most `k`. -/
theorem natDegree_invNumerator_le (u : ℕ → R) :
    ∀ k : ℕ, (invNumerator u k).natDegree ≤ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 =>
        rw [invNumerator_zero, Polynomial.natDegree_one]
    | (j + 1) =>
        rw [invNumerator_succ, Polynomial.natDegree_neg]
        refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
        rw [Finset.mem_range] at hi
        refine le_trans (Polynomial.natDegree_mul_le) ?_
        have hx : ((X : R[X]) ^ i).natDegree ≤ i := by
          refine le_trans Polynomial.natDegree_pow_le ?_
          have := Polynomial.natDegree_X_le (R := R)
          nlinarith [this]
        have h1 : (C (u (i + 1)) * X ^ i : R[X]).natDegree ≤ i := by
          refine le_trans (Polynomial.natDegree_mul_le) ?_
          rw [Polynomial.natDegree_C]
          omega
        have h2 : (invNumerator u (j - i)).natDegree ≤ j - i := ih (j - i) (by omega)
        omega

/-- **In particular the numerator has degree below the horizon.** -/
theorem natDegree_invNumerator_lt (u : ℕ → R) {L : ℕ} (hL : 0 < L) :
    (invNumerator u (L - 1)).natDegree < L :=
  lt_of_le_of_lt (natDegree_invNumerator_le u (L - 1)) (by omega)

/-! ## The numerators evaluate the inverse coefficients -/

/-- **The elimination.**  If a family `g` satisfies the coefficient recursion of an inverse jet with
constant term `a`, then its `k`-th member, cleared of its denominator, is the `k`-th numerator
evaluated at `a`. -/
theorem pow_mul_eq_invNumerator_eval (u g : ℕ → R) (a : R) (h0 : a * g 0 = 1)
    (hrec : ∀ k : ℕ, a * g (k + 1) = -∑ j ∈ Finset.range (k + 1), u (j + 1) * g (k - j)) :
    ∀ k : ℕ, a ^ (k + 1) * g k = (invNumerator u k).eval a := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 =>
        rw [invNumerator_zero, Polynomial.eval_one, pow_one]
        exact h0
    | (k + 1) =>
        have hstep : a ^ (k + 2) * g (k + 1) = a ^ (k + 1) * (a * g (k + 1)) := by ring
        rw [hstep, hrec k, mul_neg, Finset.mul_sum, invNumerator_succ]
        simp only [Polynomial.eval_neg, Polynomial.eval_finsetSum, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        have hIH : a ^ (k - j + 1) * g (k - j) = (invNumerator u (k - j)).eval a :=
          ih (k - j) (by omega)
        have hsplit : a ^ (k + 1) = a ^ j * a ^ (k - j + 1) := by
          rw [← pow_add]
          congr 1
          omega
        calc a ^ (k + 1) * (u (j + 1) * g (k - j))
            = u (j + 1) * a ^ j * (a ^ (k - j + 1) * g (k - j)) := by rw [hsplit]; ring
          _ = u (j + 1) * a ^ j * (invNumerator u (k - j)).eval a := by rw [hIH]

/-! ## Reading the recursion off a truncated inverse -/

/-- A multiple of the horizon has no coefficients below it. -/
theorem coeff_eq_zero_of_dvd_X_pow {L : ℕ} {q : R[X]} (h : (X : R[X]) ^ L ∣ q) {k : ℕ}
    (hk : k < L) : q.coeff k = 0 := by
  obtain ⟨r, rfl⟩ := h
  rw [Polynomial.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  rw [Polynomial.coeff_X_pow, if_neg (by omega), zero_mul]

/-- **The truncated inverse relation is the coefficient recursion.**  Reading `X ^ L ∣ F G - 1` in
each degree below the horizon gives the two hypotheses of the elimination. -/
theorem coeff_recursion_of_dvd {L : ℕ} {F G : R[X]} (hdvd : (X : R[X]) ^ L ∣ F * G - 1) :
    (0 < L → F.coeff 0 * G.coeff 0 = 1) ∧
      (∀ j : ℕ, j + 1 < L → F.coeff 0 * G.coeff (j + 1)
        = -∑ i ∈ Finset.range (j + 1), F.coeff (i + 1) * G.coeff (j - i)) := by
  have hzero : ∀ k : ℕ, k < L → (F * G).coeff k = (1 : R[X]).coeff k := by
    intro k hk
    have := coeff_eq_zero_of_dvd_X_pow hdvd hk
    rw [Polynomial.coeff_sub, sub_eq_zero] at this
    exact this
  have hsum : ∀ k : ℕ, (F * G).coeff k
      = (∑ i ∈ Finset.range k, F.coeff (i + 1) * G.coeff (k - (i + 1))) + F.coeff 0 * G.coeff k := by
    intro k
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => F.coeff i * G.coeff j), Finset.sum_range_succ']
    simp
  refine ⟨fun hL => ?_, fun j hj => ?_⟩
  · have h := hzero 0 hL
    rw [hsum 0, Polynomial.coeff_one_zero] at h
    simpa using h
  · have h := hzero (j + 1) hj
    rw [hsum (j + 1), Polynomial.coeff_one, if_neg (by omega)] at h
    have hshift : ∀ i ∈ Finset.range (j + 1),
        F.coeff (i + 1) * G.coeff (j + 1 - (i + 1)) = F.coeff (i + 1) * G.coeff (j - i) := by
      intro i _
      congr 2
      omega
    rw [Finset.sum_congr rfl hshift] at h
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h

/-! ## The bounded elimination -/

/-- **The elimination below the horizon.**  Only the recursion in degrees below the horizon is
needed, and it gives the numerators in those degrees. -/
theorem pow_mul_eq_invNumerator_eval_of_lt (u g : ℕ → R) (a : R) {L : ℕ} (h0 : a * g 0 = 1)
    (hrec : ∀ k : ℕ, k + 1 < L →
      a * g (k + 1) = -∑ j ∈ Finset.range (k + 1), u (j + 1) * g (k - j)) :
    ∀ k : ℕ, k < L → a ^ (k + 1) * g k = (invNumerator u k).eval a := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 =>
        intro _
        rw [invNumerator_zero, Polynomial.eval_one, pow_one]
        exact h0
    | (k + 1) =>
        intro hk
        have hstep : a ^ (k + 2) * g (k + 1) = a ^ (k + 1) * (a * g (k + 1)) := by ring
        rw [hstep, hrec k hk, mul_neg, Finset.mul_sum, invNumerator_succ]
        simp only [Polynomial.eval_neg, Polynomial.eval_finsetSum, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        have hIH : a ^ (k - j + 1) * g (k - j) = (invNumerator u (k - j)).eval a :=
          ih (k - j) (by omega) (by omega)
        have hsplit : a ^ (k + 1) = a ^ j * a ^ (k - j + 1) := by
          rw [← pow_add]
          congr 1
          omega
        calc a ^ (k + 1) * (u (j + 1) * g (k - j))
            = u (j + 1) * a ^ j * (a ^ (k - j + 1) * g (k - j)) := by rw [hsplit]; ring
          _ = u (j + 1) * a ^ j * (invNumerator u (k - j)).eval a := by rw [hIH]

end GaloisForLFunctions.HTGeometry

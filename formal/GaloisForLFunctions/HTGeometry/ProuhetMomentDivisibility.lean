import Mathlib

/-!
# Prouhet–Tarry–Escott osculation: matched moments force high-order tangency at one

The generating-function form of the Prouhet–Tarry–Escott law.  For a polynomial
`G = ∑ᵢ cᵢ Xⁱ`, the vanishing of the weighted moments `∑ᵢ (i choose k)·cᵢ` for all `k ≤ L`
is exactly the vanishing of the Taylor coefficients of `G` at the point `1` through order
`L`, hence forces `(X-1)^{L+1} ∣ G` (`pte_sub_one_pow_dvd_of_binomial_moments`).  Because a
binomial coefficient `i ↦ (i choose k)` is, over a characteristic-zero field, a degree-`k`
rational-coefficient polynomial in `i`, the ordinary power-sum moments `∑ᵢ iʲ·cᵢ` control
the same tangency: their vanishing through order `L` also forces `(X-1)^{L+1} ∣ G`
(`pte_sub_one_pow_dvd_of_power_moments`).

Read on differences of multiset generating functions this is the classical statement that
two integer multisets with equal power sums through order `L` have generating functions
agreeing to order `L+1` at `1`; the surviving cluster of a differential-algebraic coefficient
identity is therefore pinned to a Prouhet osculation hypersurface.
-/

open Polynomial

namespace GaloisForLFunctions

/-- The Taylor coefficient of `G` at `1` of order `k` is the binomial-weighted moment of the
coefficients of `G`: `eval 1 (hasseDeriv k G) = ∑ᵢ (i choose k)·cᵢ`. -/
theorem hasseDeriv_eval_one_eq_binomial_moment {R : Type*} [CommRing R] (k : ℕ)
    (G : R[X]) :
    eval 1 (hasseDeriv k G) = ∑ i ∈ G.support, (i.choose k : R) * G.coeff i := by
  rw [hasseDeriv_apply, Polynomial.sum_def, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_monomial, one_pow, mul_one]

/-- **Prouhet tangency, converse Taylor form.**  Divisibility by `(X-1)^m` kills every
Taylor coefficient at `1` below order `m`.  Translating by one sends the divisor to `X^m`,
so this is the direct converse needed when a generating polynomial is constructed by factors. -/
theorem hasseDeriv_eval_one_eq_zero_of_sub_one_pow_dvd
    {R : Type*} [CommRing R] {G : R[X]} {m k : ℕ}
    (hdiv : (X - 1) ^ m ∣ G) (hk : k < m) :
    eval 1 (hasseDeriv k G) = 0 := by
  rw [← taylor_coeff]
  apply (X_pow_dvd_iff.mp ?_) k hk
  obtain ⟨D, hD⟩ := hdiv
  refine ⟨taylor 1 D, ?_⟩
  rw [hD, taylor_mul, taylor_pow]
  simp

/-- **Prouhet tangency, converse binomial-moment form.**  A zero of order `m` at one
annihilates all binomial coefficient moments of orders strictly below `m`. -/
theorem binomial_moment_eq_zero_of_sub_one_pow_dvd
    {R : Type*} [CommRing R] {G : R[X]} {m k : ℕ}
    (hdiv : (X - 1) ^ m ∣ G) (hk : k < m) :
    ∑ i ∈ G.support, (i.choose k : R) * G.coeff i = 0 := by
  rw [← hasseDeriv_eval_one_eq_binomial_moment]
  exact hasseDeriv_eval_one_eq_zero_of_sub_one_pow_dvd hdiv hk

/-- **Prouhet tangency, converse power-moment form.**  Over a characteristic-zero field, a
zero of order `m` at one annihilates every ordinary coefficient power moment of order below
`m`.  Falling factorials give a triangular basis: their moments vanish by the binomial-moment
theorem above, and monicity recovers the top ordinary moment inductively. -/
theorem power_moment_eq_zero_of_sub_one_pow_dvd
    {R : Type*} [Field R] [CharZero R] {G : R[X]} {m k : ℕ}
    (hdiv : (X - 1) ^ m ∣ G) (hk : k < m) :
    ∑ i ∈ G.support, (i : R) ^ k * G.coeff i = 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      have hbin := binomial_moment_eq_zero_of_sub_one_pow_dvd hdiv hk
      have hfall :
          ∑ i ∈ G.support, eval (i : R) (descPochhammer R k) * G.coeff i = 0 := by
        calc
          ∑ i ∈ G.support, eval (i : R) (descPochhammer R k) * G.coeff i =
              ∑ i ∈ G.support, (k.factorial : R) *
                ((i.choose k : R) * G.coeff i) := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [descPochhammer_eval_eq_descFactorial,
                    Nat.descFactorial_eq_factorial_mul_choose]
                  push_cast
                  ring
          _ = (k.factorial : R) *
                ∑ i ∈ G.support, (i.choose k : R) * G.coeff i := by
                  rw [Finset.mul_sum]
          _ = 0 := by rw [hbin, mul_zero]
      have hdeg : (descPochhammer R k).natDegree = k := descPochhammer_natDegree R k
      have htotal :
          ∑ j ∈ Finset.range (k + 1), (descPochhammer R k).coeff j *
              (∑ i ∈ G.support, (i : R) ^ j * G.coeff i) = 0 := by
        calc
          ∑ j ∈ Finset.range (k + 1), (descPochhammer R k).coeff j *
              (∑ i ∈ G.support, (i : R) ^ j * G.coeff i) =
              ∑ i ∈ G.support,
                (∑ j ∈ Finset.range (k + 1),
                  (descPochhammer R k).coeff j * (i : R) ^ j) * G.coeff i := by
                    simp_rw [Finset.mul_sum]
                    rw [Finset.sum_comm]
                    refine Finset.sum_congr rfl fun i _ => ?_
                    rw [Finset.sum_mul]
                    refine Finset.sum_congr rfl fun j _ => by ring
          _ = ∑ i ∈ G.support,
                eval (i : R) (descPochhammer R k) * G.coeff i := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [Polynomial.eval_eq_sum_range, hdeg]
          _ = 0 := hfall
      have hlower :
          ∑ j ∈ Finset.range k, (descPochhammer R k).coeff j *
              (∑ i ∈ G.support, (i : R) ^ j * G.coeff i) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hjk := Finset.mem_range.mp hj
        rw [ih j hjk (hjk.trans hk), mul_zero]
      rw [Finset.sum_range_succ, hlower, zero_add] at htotal
      have hlead : (descPochhammer R k).coeff k = 1 := by
        simpa only [hdeg] using (monic_descPochhammer R k).coeff_natDegree
      simpa [hlead] using htotal

/-- A Prouhet zero annihilates the coefficient pairing with every polynomial whose degree is
strictly smaller than the zero order. -/
theorem polynomial_pairing_eq_zero_of_sub_one_pow_dvd
    {R : Type*} [Field R] [CharZero R] {G p : R[X]} {m : ℕ}
    (hdiv : (X - 1) ^ m ∣ G) (hp : p.natDegree < m) :
    ∑ i ∈ G.support, G.coeff i * p.eval (i : R) = 0 := by
  calc
    ∑ i ∈ G.support, G.coeff i * p.eval (i : R) =
        ∑ i ∈ G.support, ∑ j ∈ Finset.range (p.natDegree + 1),
          p.coeff j * ((i : R) ^ j * G.coeff i) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ j ∈ Finset.range (p.natDegree + 1),
        p.coeff j * (∑ i ∈ G.support, (i : R) ^ j * G.coeff i) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
    _ = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hjp : j ≤ p.natDegree := by
        have := Finset.mem_range.mp hj
        omega
      rw [power_moment_eq_zero_of_sub_one_pow_dvd hdiv (lt_of_le_of_lt hjp hp), mul_zero]

/-- Translation of the test polynomial does not change the cancellation: the coefficient packet
annihilates `p(N+i)` for every natural base point `N`. -/
theorem shifted_polynomial_pairing_eq_zero_of_sub_one_pow_dvd
    {R : Type*} [Field R] [CharZero R] {G p : R[X]} {m : ℕ} (N : ℕ)
    (hdiv : (X - 1) ^ m ∣ G) (hp : p.natDegree < m) :
    ∑ i ∈ G.support, G.coeff i * p.eval ((N + i : ℕ) : R) = 0 := by
  let q : R[X] := p.comp (X + C (N : R))
  have hq : q.natDegree < m := by
    calc
      q.natDegree ≤ p.natDegree * (X + C (N : R)).natDegree := natDegree_comp_le
      _ = p.natDegree := by rw [natDegree_X_add_C, mul_one]
      _ < m := hp
  have h := polynomial_pairing_eq_zero_of_sub_one_pow_dvd hdiv hq
  simpa only [q, eval_comp, eval_add, eval_X, eval_C, Nat.cast_add, add_comm] using h

/-- **Prouhet tangency, Taylor form.**  If every Taylor coefficient of `G` at `1` up to order
`L` vanishes, then `G` is divisible by `(X-1)^{L+1}`.  The Taylor shift transports the
vanishing into `X^{L+1} ∣ taylor 1 G`, and composing back with `X-1` restores `G`. -/
theorem pte_sub_one_pow_dvd {R : Type*} [CommRing R] {G : R[X]} {L : ℕ}
    (h : ∀ k ≤ L, eval 1 (hasseDeriv k G) = 0) : (X - 1) ^ (L + 1) ∣ G := by
  have hX : X ^ (L + 1) ∣ taylor 1 G := by
    rw [X_pow_dvd_iff]
    intro d hd
    rw [taylor_coeff]
    exact h d (by omega)
  obtain ⟨D, hD⟩ := hX
  refine ⟨D.comp (X - 1), ?_⟩
  have hcomp : ((X : R[X]) + C 1).comp (X - 1) = X := by simp
  have hg : G = (taylor 1 G).comp (X - 1) := by
    rw [taylor_apply, comp_assoc, hcomp, comp_X]
  rw [hg, hD, mul_comp, pow_comp, X_comp]

/-- **Prouhet tangency, binomial-moment form.**  Vanishing of the binomial-weighted moments
`∑ᵢ (i choose k)·cᵢ` for all `k ≤ L` forces `(X-1)^{L+1} ∣ G`. -/
theorem pte_sub_one_pow_dvd_of_binomial_moments {R : Type*} [CommRing R] {G : R[X]} {L : ℕ}
    (h : ∀ k ≤ L, ∑ i ∈ G.support, (i.choose k : R) * G.coeff i = 0) :
    (X - 1) ^ (L + 1) ∣ G := by
  refine pte_sub_one_pow_dvd fun k hk => ?_
  rw [hasseDeriv_eval_one_eq_binomial_moment]
  exact h k hk

/-- **Prouhet tangency, power-sum form.**  Over a characteristic-zero field, vanishing of the
ordinary power-sum moments `∑ᵢ iʲ·cᵢ` for all `j ≤ L` forces `(X-1)^{L+1} ∣ G`.  Each
binomial moment is `1/k!` times the falling-factorial moment, and the falling factorial is a
degree-`k` polynomial in the index, so its moment is a combination of the power-sum moments
through order `k ≤ L`. -/
theorem pte_sub_one_pow_dvd_of_power_moments {R : Type*} [Field R] [CharZero R] {G : R[X]}
    {L : ℕ} (h : ∀ j ≤ L, ∑ i ∈ G.support, (i : R) ^ j * G.coeff i = 0) :
    (X - 1) ^ (L + 1) ∣ G := by
  refine pte_sub_one_pow_dvd_of_binomial_moments fun k hk => ?_
  have hfac : (k.factorial : R) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  apply mul_left_cancel₀ hfac
  rw [Finset.mul_sum, mul_zero]
  have hstep : ∀ i, (k.factorial : R) * ((i.choose k : R) * G.coeff i)
      = eval (i : R) (descPochhammer R k) * G.coeff i := by
    intro i
    rw [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun i _ => hstep i]
  have hdeg : (descPochhammer R k).natDegree = k := descPochhammer_natDegree R k
  have hexpand : ∀ i : ℕ, eval (i : R) (descPochhammer R k)
      = ∑ j ∈ Finset.range (k + 1), (descPochhammer R k).coeff j * (i : R) ^ j := by
    intro i
    rw [Polynomial.eval_eq_sum_range, hdeg]
  rw [Finset.sum_congr rfl fun i _ => by rw [hexpand i, Finset.sum_mul]]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hjk : j < k + 1 := Finset.mem_range.mp hj
  have hjL : j ≤ L := by omega
  have : ∑ i ∈ G.support, (descPochhammer R k).coeff j * (i : R) ^ j * G.coeff i
      = (descPochhammer R k).coeff j * ∑ i ∈ G.support, (i : R) ^ j * G.coeff i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, h j hjL, mul_zero]

end GaloisForLFunctions

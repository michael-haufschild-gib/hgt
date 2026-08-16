import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.CharZero.Infinite

/-!
# The lattice simplex is a test set for bounded-degree polynomials

A polynomial in `n` variables of total degree at most `T` that vanishes at every point of the
nonnegative integer simplex `{m : Σ mᵢ ≤ T}` is the zero polynomial.  Equivalently, the
`C(n+T, T)` simplex points are a unisolvent set for the space of polynomials of total degree `≤ T`
— the multivariate Newton/Lagrange interpolation fact.  mathlib has the *box* form of this (the
Combinatorial Nullstellensatz grid), but not the simplex form, which is the one the friable
auxiliary needs: there the exponent vectors are constrained by `‖m‖₁ ≤ d`, never by a box.

The proof is an induction on the number of variables.  Split off the last variable with
`MvPolynomial.finSuccEquiv`; the leading coefficient `Q` in that variable has total degree at most
`T - k` where `k` is the degree in the last variable, so by induction it is nonzero somewhere on the
smaller simplex.  Specializing there leaves a univariate polynomial of degree exactly `k` that
vanishes at the `k + 1` integers `0, …, k` — hence is zero, a contradiction.

## Main results

* `MvPolynomial.eq_zero_of_eval_natCast_eq_zero_on_simplex` — the test-set theorem;
* `MvPolynomial.exists_natCast_eval_ne_zero_on_simplex` — its contrapositive form;
* `coeff_eq_zero_of_monomialSum_vanishes_on_simplex` — the linear-algebra form.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

/-- **The nonnegative integer simplex is a test set.**  A polynomial of total degree at most `T`
vanishing at every lattice point of the simplex `{m : Σ mᵢ ≤ T}` is zero. -/
theorem eq_zero_of_eval_natCast_eq_zero_on_simplex
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R] :
    ∀ (n T : ℕ) (P : MvPolynomial (Fin n) R), P.totalDegree ≤ T →
      (∀ m : Fin n → ℕ, (∑ i, m i) ≤ T →
        MvPolynomial.eval (fun i => ((m i : ℕ) : R)) P = 0) → P = 0 := by
  intro n
  induction n with
  | zero =>
      intro T P _ hv
      refine MvPolynomial.funext (fun x => ?_)
      have h := hv (fun _ => 0) (by simp)
      have hx : x = (fun _ : Fin 0 => ((0 : ℕ) : R)) := by
        funext i
        exact absurd i.isLt (by omega)
      rw [hx, h, map_zero]
  | succ n ih =>
      intro T P hdeg hv
      by_contra hP
      set g := finSuccEquiv R n P with hg
      have hgne : g ≠ 0 := by
        intro h
        apply hP
        have := congrArg (fun z => (finSuccEquiv R n).symm z) h
        simpa [hg] using this
      set k := g.natDegree with hk
      set Q := g.coeff k with hQ
      have hQne : Q ≠ 0 := by
        rw [hQ, hk]
        exact Polynomial.leadingCoeff_ne_zero.mpr hgne
      have hdegQ : Q.totalDegree + k ≤ T := by
        refine le_trans ?_ hdeg
        rw [hQ, hg]
        exact MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le P k (by rw [← hg, ← hQ]; exact hQne)
      have hQdeg : Q.totalDegree ≤ T - k := by omega
      have hexists : ∃ m' : Fin n → ℕ, (∑ i, m' i) ≤ T - k ∧
          MvPolynomial.eval (fun i => ((m' i : ℕ) : R)) Q ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hQne (ih (T - k) Q hQdeg hc)
      obtain ⟨m', hm'sum, hm'ne⟩ := hexists
      set h := Polynomial.map (MvPolynomial.eval (fun i => ((m' i : ℕ) : R))) g with hh
      have hhcoeff : h.coeff k = MvPolynomial.eval (fun i => ((m' i : ℕ) : R)) Q := by
        rw [hh, Polynomial.coeff_map, hQ]
      have hhne : h ≠ 0 := by
        intro hz
        apply hm'ne
        rw [← hhcoeff, hz, Polynomial.coeff_zero]
      have hdegh : h.natDegree ≤ k := by
        rw [hh, hk]
        exact Polynomial.natDegree_map_le
      have hroots : ∀ t : Fin (k + 1),
          Polynomial.eval (((t : ℕ) : R)) h = 0 := by
        intro t
        have hsum : (∑ i, (Fin.cons (t : ℕ) m' : Fin (n + 1) → ℕ) i) ≤ T := by
          rw [Fin.sum_cons]
          have htk : (t : ℕ) ≤ k := Nat.lt_succ_iff.mp t.isLt
          omega
        have hval := hv (Fin.cons (t : ℕ) m') hsum
        have hcast : (fun i : Fin (n + 1) =>
              (((Fin.cons (t : ℕ) m' : Fin (n + 1) → ℕ) i : ℕ) : R))
            = Fin.cons (((t : ℕ) : R)) (fun i => ((m' i : ℕ) : R)) := by
          funext i
          refine Fin.cases ?_ ?_ i <;> simp
        rw [hcast, MvPolynomial.eval_eq_eval_mv_eval'] at hval
        rw [hh, hg]
        exact hval
      have hinj : Function.Injective (fun t : Fin (k + 1) => ((t : ℕ) : R)) := by
        intro a b hab
        have hR : (((a : ℕ) : R)) = (((b : ℕ) : R)) := hab
        have hN : (a : ℕ) = (b : ℕ) := by exact_mod_cast hR
        exact Fin.ext hN
      have hcard : h.natDegree < Fintype.card (Fin (k + 1)) := by
        rw [Fintype.card_fin]
        omega
      exact hhne
        (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero h hinj hroots hcard)

/-- **Contrapositive form.**  A nonzero polynomial of total degree at most `T` is nonzero somewhere
on the lattice simplex of size `T`. -/
theorem exists_natCast_eval_ne_zero_on_simplex
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {n T : ℕ} {P : MvPolynomial (Fin n) R} (hdeg : P.totalDegree ≤ T) (hP : P ≠ 0) :
    ∃ m : Fin n → ℕ, (∑ i, m i) ≤ T ∧
      MvPolynomial.eval (fun i => ((m i : ℕ) : R)) P ≠ 0 := by
  by_contra hc
  push Not at hc
  exact hP (eq_zero_of_eval_natCast_eq_zero_on_simplex n T P hdeg hc)

/-- **Monomial-coefficient independence on the simplex.**  A finite combination of distinct monomials
of total degree at most `T` that vanishes at every lattice point of a simplex of size `d ≥ T` has all
coefficients zero.  This is the linear-algebra form of the test-set theorem. -/
theorem coeff_eq_zero_of_monomialSum_vanishes_on_simplex
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {n T d : ℕ} (hd : T ≤ d) (A : Finset (Fin n →₀ ℕ))
    (hA : ∀ a ∈ A, (a.sum fun _ e => e) ≤ T) (kappa : (Fin n →₀ ℕ) → R)
    (hvanish : ∀ m : Fin n → ℕ, (∑ i, m i) ≤ d →
      ∑ a ∈ A, kappa a * ∏ i, ((m i : ℕ) : R) ^ (a i) = 0) :
    ∀ a ∈ A, kappa a = 0 := by
  classical
  set P : MvPolynomial (Fin n) R := ∑ a ∈ A, MvPolynomial.monomial a (kappa a) with hP
  have hevalP : ∀ x : Fin n → R,
      MvPolynomial.eval x P = ∑ a ∈ A, kappa a * ∏ i, x i ^ (a i) := by
    intro x
    rw [hP, map_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [MvPolynomial.eval_monomial]
    congr 1
    exact Finsupp.prod_fintype a (fun i e => x i ^ e) (fun i => pow_zero (x i))
  have hdegP : P.totalDegree ≤ T := by
    refine MvPolynomial.totalDegree_finsetSum_le (fun a ha => ?_)
    exact le_trans (MvPolynomial.totalDegree_monomial_le a (kappa a)) (hA a ha)
  have hzero : P = 0 := by
    refine eq_zero_of_eval_natCast_eq_zero_on_simplex n T P hdegP (fun m hm => ?_)
    rw [hevalP]
    exact hvanish m (le_trans hm hd)
  intro a ha
  have hcoeff : MvPolynomial.coeff a P = kappa a := by
    rw [hP, MvPolynomial.coeff_sum,
      Finset.sum_congr rfl (fun a' _ => MvPolynomial.coeff_monomial a a' (kappa a')),
      Finset.sum_ite_eq' A a kappa, if_pos ha]
  rw [← hcoeff, hzero, MvPolynomial.coeff_zero]

end GaloisForLFunctions.HTGeometry

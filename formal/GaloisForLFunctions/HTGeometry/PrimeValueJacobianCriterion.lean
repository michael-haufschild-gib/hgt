import GaloisForLFunctions.HTGeometry.ArithmeticFunctionJacobianCriterion

/-!
# Algebraic independence of arithmetic functions from their prime values alone

The prime derivation `∂_q` reads off the value at `q` on the identity component, `(∂_q b)(1) = b q`,
for *every* arithmetic function — the prime-supported hypothesis is only needed to make `∂_q b` a
scalar.  Dropping it costs one induction: from

```text
∑_j (∂_j P)(g) · ∂_q g_j = 0
```

evaluate at `n`.  In the Dirichlet convolution every divisor pair except `(n, 1)` has first entry
smaller than `n`, so by strong induction only the term `(∂_j P)(g)(n) · g_j(q)` survives, and
linear independence of the prime values kills it.  Hence every partial derivative of `P` annihilates
the family, contradicting minimality of the degree.

So a finite family of arithmetic functions is algebraically independent as soon as its *prime
values* are linearly independent — with no restriction on the support.  This covers Dirichlet series
of completely multiplicative functions, which are supported on all integers and to which the
prime-supported and prime-power-packet criteria do not apply.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial ArithmeticFunction Finset

noncomputable section

/-- A finite sum of arithmetic functions is evaluated termwise. -/
theorem sum_arithmeticFunction_apply {ι : Type*} (s : Finset ι) (f : ι → ArithmeticFunction ℂ)
    (n : ℕ) : (∑ j ∈ s, f j) n = ∑ j ∈ s, f j n := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ArithmeticFunction.add_apply, ih]

/-- No nontrivial constant combination of the family vanishes at every prime. -/
def PrimeValueIndependent {ι : Type*} [Fintype ι] (g : ι → ArithmeticFunction ℂ) : Prop :=
  ∀ c : ι → ℂ, (∀ q : ℕ, q.Prime → ∑ j, c j * g j q = 0) → c = 0

/-- Tail independence of the prime columns implies prime-value independence. -/
theorem primeValueIndependent_of_tailIndependent {ι : Type*} [Fintype ι]
    (g : ι → ArithmeticFunction ℂ)
    (h : TailCoefficientIndependent (fun j => fun p : Nat.Primes => g j (p : ℕ))) :
    PrimeValueIndependent g := by
  intro c hc
  refine h c ?_
  have hempty : {p : Nat.Primes | ∑ j, c j * g j (p : ℕ) ≠ 0} = ∅ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact hc (p : ℕ) p.2
  rw [hempty]
  exact Set.finite_empty

/-- **Prime-value Jacobian criterion.**  A finite family of arithmetic functions whose prime values
are linearly independent is algebraically independent over `ℂ`. -/
theorem algebraicIndependent_of_primeValueIndependent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ArithmeticFunction ℂ) (h : PrimeValueIndependent g) :
    AlgebraicIndependent ℂ g := by
  classical
  rw [algebraicIndependent_iff_ker_eq_bot]
  by_contra hker
  obtain ⟨P, hPI, hP0, hmin⟩ :=
    GaloisForLFunctions.Ideal.exists_minimal_mvPolynomial_totalDegree_ne_zero hker
  have hPeval : MvPolynomial.aeval g P = 0 := RingHom.mem_ker.mp hPI
  set Q : ι → ArithmeticFunction ℂ := fun j => MvPolynomial.aeval g (MvPolynomial.pderiv j P)
    with hQdef
  have hchain : ∀ q : ℕ, q.Prime → ∑ j, Q j * primeDeriv q (g j) = 0 := by
    intro q hq
    have hcr := jacobian_aeval_eq_sum_pderiv (K := ℂ) (primeDeriv q) (primeDeriv_add q)
      (primeDeriv_mul q hq) (primeDeriv_algebraMap q hq) g P
    rw [hPeval] at hcr
    have hD0 : primeDeriv q (0 : ArithmeticFunction ℂ) = 0 := by
      ext n
      simp
    rw [hD0] at hcr
    exact hcr.symm
  have hQzero : ∀ n : ℕ, ∀ j, Q j n = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases eq_or_ne n 0 with rfl | hn0
      · intro j
        simp
      · have hc : ∀ q : ℕ, q.Prime → ∑ j, Q j n * g j q = 0 := by
          intro q hq
          have h0 : ∑ j, (Q j * primeDeriv q (g j)) n = 0 := by
            rw [← sum_arithmeticFunction_apply, hchain q hq]
            simp
          rw [← h0]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [ArithmeticFunction.mul_apply]
          have hmem : (n, 1) ∈ n.divisorsAntidiagonal :=
            Nat.mem_divisorsAntidiagonal.2 ⟨by simp, hn0⟩
          have hother : ∀ x ∈ n.divisorsAntidiagonal, x ≠ (n, 1) →
              Q j x.1 * primeDeriv q (g j) x.2 = 0 := by
            intro x hx hxne
            have hx1 : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.1 hx).1
            have hdvd : x.1 ∣ n := ⟨x.2, hx1.symm⟩
            have hle : x.1 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
            have hne : x.1 ≠ n := by
              intro hxeq
              refine hxne ?_
              have hx2 : x.2 = 1 := by
                have hmul : n * x.2 = n * 1 := by rw [← hxeq, hx1, mul_one, hxeq]
                exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn0) hmul
              exact Prod.ext_iff.2 ⟨hxeq, hx2⟩
            rw [ih x.1 (lt_of_le_of_ne hle hne) j, zero_mul]
          rw [Finset.sum_eq_single_of_mem (n, 1) hmem hother, primeDeriv_apply, one_mul,
            hq.factorization_self]
          push_cast
          ring
        have hzero := h (fun j => Q j n) hc
        intro j
        exact congrFun hzero j
  have hQ0 : ∀ j, Q j = 0 := by
    intro j
    ext n
    exact hQzero n j
  have hPvars : P.vars.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hvars
    have hPC := MvPolynomial.vars_eq_empty_iff_eq_C.mp hvars
    rw [hPC] at hPeval hP0
    have hcmap : algebraMap ℂ (ArithmeticFunction ℂ) (P.coeff 0) = 0 := by simpa using hPeval
    have hc : P.coeff 0 = 0 :=
      FaithfulSMul.algebraMap_injective ℂ (ArithmeticFunction ℂ) (by simpa using hcmap)
    exact hP0 (by simp [hc])
  obtain ⟨i, hi⟩ := hPvars
  obtain ⟨s, hsP, his⟩ := (MvPolynomial.mem_vars_iff_mem_support i).mp hi
  have hpderiv0 : MvPolynomial.pderiv i P ≠ 0 :=
    GaloisForLFunctions.pderiv_ne_zero_of_mem_support hsP his
  have hpI : MvPolynomial.pderiv i P ∈ RingHom.ker (MvPolynomial.aeval g).toRingHom :=
    RingHom.mem_ker.mpr (hQ0 i)
  have hle := hmin hpI hpderiv0
  have hlt := GaloisForLFunctions.totalDegree_pderiv_lt P i hpderiv0
  exact (not_lt_of_ge hle) hlt

end

end GaloisForLFunctions.HTGeometry

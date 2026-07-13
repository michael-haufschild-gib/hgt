import GaloisForLFunctions.HTGeometry.AlgebraicPrimitiveDescent
import GaloisForLFunctions.HTGeometry.DifferentialHopfPrimitive
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Kähler circuits from algebraic dependence

For a finite polynomial relation among elements `x i` of a field extension,
the universal derivation gives a linear relation among the Kähler
differentials `d(x i)`.  Choosing a relation of least total degree ensures
that its evaluated gradient is nonzero: otherwise every partial derivative
would be a smaller relation.

This is the circuit-existence half of the elementary several-automorphism
Ostrowski argument.  It is independent of parameterized Picard--Vessiot
theory.
-/

namespace GaloisForLFunctions

noncomputable section

/-- The gradient of a multivariate polynomial, evaluated at a family in a
field extension and stored as a finitely supported coefficient vector. -/
def mvPolynomialGradientEval
    {kappa K L : Type*} [Field K] [Field L] [Algebra K L]
    (x : kappa → L) (P : MvPolynomial kappa K) : kappa →₀ L :=
  Finsupp.onFinset P.vars
    (fun i ↦ MvPolynomial.aeval x (MvPolynomial.pderiv i P))
    (fun i hi ↦ by
      change MvPolynomial.aeval x (MvPolynomial.pderiv i P) ≠ 0 at hi
      by_contra hnot
      rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars hnot, map_zero] at hi
      exact hi rfl)

@[simp] theorem mvPolynomialGradientEval_apply
    {kappa K L : Type*} [Field K] [Field L] [Algebra K L]
    (x : kappa → L) (P : MvPolynomial kappa K) (i : kappa) :
    mvPolynomialGradientEval x P i =
      MvPolynomial.aeval x (MvPolynomial.pderiv i P) := by
  exact Finsupp.onFinset_apply

@[simp] theorem mvPolynomialGradientEval_C
    {kappa K L : Type*} [Field K] [Field L] [Algebra K L]
    (x : kappa → L) (c : K) :
    mvPolynomialGradientEval x (MvPolynomial.C c) = 0 := by
  ext i
  simp

theorem mvPolynomialGradientEval_add
    {kappa K L : Type*} [Field K] [Field L] [Algebra K L]
    (x : kappa → L) (P Q : MvPolynomial kappa K) :
    mvPolynomialGradientEval x (P + Q) =
      mvPolynomialGradientEval x P + mvPolynomialGradientEval x Q := by
  ext i
  simp

theorem mvPolynomialGradientEval_mul_X
    {kappa K L : Type*} [Field K] [Field L] [Algebra K L]
    (x : kappa → L) (P : MvPolynomial kappa K) (k : kappa) :
    mvPolynomialGradientEval x (P * MvPolynomial.X k) =
      x k • mvPolynomialGradientEval x P +
        Finsupp.single k (MvPolynomial.aeval x P) := by
  classical
  ext i
  simp only [mvPolynomialGradientEval_apply, MvPolynomial.pderiv_mul,
    map_add, map_mul, MvPolynomial.aeval_X, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply,
    MvPolynomial.pderiv_X, Pi.single_apply]
  by_cases h : k = i
  · subst i
    simp
    ring
  · simp [h]
    ring

/-- Multivariate chain rule for an arbitrary relative derivation. -/
theorem derivation_aeval_eq_gradient
    {kappa K L M : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup M] [Module L M] [Module K M] [IsScalarTower K L M]
    (D : Derivation K L M) (x : kappa → L) (P : MvPolynomial kappa K) :
    D (MvPolynomial.aeval x P) =
      Finsupp.linearCombination L (fun i ↦ D (x i))
        (mvPolynomialGradientEval x P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ =>
      rw [map_add (MvPolynomial.aeval x) P Q]
      rw [D.map_add, hP, hQ, mvPolynomialGradientEval_add, map_add]
  | mul_X P k hP =>
      rw [map_mul (MvPolynomial.aeval x) P (MvPolynomial.X k),
        MvPolynomial.aeval_X]
      rw [Derivation.leibniz, hP, mvPolynomialGradientEval_mul_X,
        map_add]
      simp [Finsupp.linearCombination_single, map_smul]
      exact add_comm _ _

/-- Every nonzero multivariate-polynomial ideal contains a nonzero element
of least total degree. -/
theorem Ideal.exists_minimal_mvPolynomial_totalDegree_ne_zero
    {kappa K : Type*} [Field K]
    {I : Ideal (MvPolynomial kappa K)} (hI : I ≠ ⊥) :
    ∃ P : MvPolynomial kappa K,
      P ∈ I ∧ P ≠ 0 ∧
        ∀ ⦃Q : MvPolynomial kappa K⦄, Q ∈ I → Q ≠ 0 →
          P.totalDegree ≤ Q.totalDegree := by
  classical
  have hexP : ∃ P : MvPolynomial kappa K, P ∈ I ∧ P ≠ 0 := by
    by_contra h
    apply hI
    ext P
    simp only [Ideal.mem_bot]
    constructor
    · intro hPI
      by_contra hP0
      exact h ⟨P, hPI, hP0⟩
    · rintro rfl
      exact I.zero_mem
  let d := Nat.find (show ∃ n : ℕ,
      ∃ P : MvPolynomial kappa K,
        P ∈ I ∧ P ≠ 0 ∧ P.totalDegree = n from by
      obtain ⟨P, hPI, hP0⟩ := hexP
      exact ⟨P.totalDegree, P, hPI, hP0, rfl⟩)
  obtain ⟨P, hPI, hP0, hPd⟩ := Nat.find_spec
    (show ∃ n : ℕ, ∃ P : MvPolynomial kappa K,
      P ∈ I ∧ P ≠ 0 ∧ P.totalDegree = n from by
      obtain ⟨Q, hQI, hQ0⟩ := hexP
      exact ⟨Q.totalDegree, Q, hQI, hQ0, rfl⟩)
  refine ⟨P, hPI, hP0, ?_⟩
  intro Q hQI hQ0
  rw [hPd]
  exact Nat.find_min'
    (show ∃ n : ℕ, ∃ R : MvPolynomial kappa K,
      R ∈ I ∧ R ≠ 0 ∧ R.totalDegree = n from by
      obtain ⟨R, hRI, hR0⟩ := hexP
      exact ⟨R.totalDegree, R, hRI, hR0, rfl⟩)
    ⟨Q, hQI, hQ0, rfl⟩

/-- Removing one occurrence of a variable lowers the total exponent sum by
one. -/
theorem finsupp_sum_sub_single_one
    {kappa : Type*} (s : kappa →₀ ℕ) (i : kappa) (hi : s i ≠ 0) :
    (s - Finsupp.single i 1).sum (fun _ n ↦ n) + 1 =
      s.sum (fun _ n ↦ n) := by
  have hfs := Finsupp.sub_add_single_one_cancel (u := s) hi
  have hsum := congrArg (fun t : kappa →₀ ℕ ↦ t.sum (fun _ n ↦ n)) hfs
  simpa [Finsupp.sum_add_index'] using hsum

/-- A nonzero partial derivative has strictly smaller total degree. -/
theorem totalDegree_pderiv_lt
    {kappa K : Type*} [Field K]
    (P : MvPolynomial kappa K) (i : kappa)
    (hderiv : MvPolynomial.pderiv i P ≠ 0) :
    (MvPolynomial.pderiv i P).totalDegree < P.totalDegree := by
  classical
  have hPpos : 0 < P.totalDegree := by
    by_contra h
    have hdeg : P.totalDegree = 0 := Nat.eq_zero_of_not_pos h
    have hPC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg
    rw [hPC, MvPolynomial.pderiv_C] at hderiv
    exact hderiv rfl
  have hpderiv_sum : MvPolynomial.pderiv i P =
      ∑ s ∈ P.support,
        MvPolynomial.pderiv i (MvPolynomial.monomial s (P.coeff s)) := by
    calc
      MvPolynomial.pderiv i P =
          MvPolynomial.pderiv i
            (∑ s ∈ P.support, MvPolynomial.monomial s (P.coeff s)) := by
              rw [← P.as_sum]
      _ = ∑ s ∈ P.support,
          MvPolynomial.pderiv i (MvPolynomial.monomial s (P.coeff s)) := by
            rw [map_sum]
  rw [hpderiv_sum]
  apply lt_of_le_of_lt
    (MvPolynomial.totalDegree_finsetSum_le (d := P.totalDegree - 1) ?_)
    (Nat.sub_lt hPpos Nat.zero_lt_one)
  intro s hs
  rw [MvPolynomial.pderiv_monomial]
  by_cases hi : s i = 0
  · simp [hi]
  · refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
    have hsum := finsupp_sum_sub_single_one s i hi
    have hsle : s.sum (fun _ n ↦ n) ≤ P.totalDegree :=
      MvPolynomial.le_totalDegree hs
    have hsub : (s - Finsupp.single i 1).sum (fun _ n ↦ n) =
        s.sum (fun _ n ↦ n) - 1 := by omega
    change (s - Finsupp.single i 1).sum (fun _ n ↦ n) ≤
      P.totalDegree - 1
    rw [hsub]
    exact Nat.sub_le_sub_right hsle 1

/-- Algebraic dependence in a field extension produces a nonzero Kähler
circuit among the universal differentials of the dependent family. -/
theorem exists_nonzero_kaehler_relation_of_not_algebraicIndependent
    {kappa K L : Type*} [Field K] [Field L] [Algebra K L]
    [CharZero K] (x : kappa → L)
    (hdep : ¬ AlgebraicIndependent K x) :
    ∃ c : kappa →₀ L, c ≠ 0 ∧
      Finsupp.linearCombination L
        (fun i ↦ KaehlerDifferential.D K L (x i)) c = 0 := by
  classical
  let I : Ideal (MvPolynomial kappa K) :=
    RingHom.ker (MvPolynomial.aeval x).toRingHom
  have hI : I ≠ ⊥ := by
    intro hbot
    apply hdep
    rw [algebraicIndependent_iff_ker_eq_bot]
    exact hbot
  obtain ⟨P, hPI, hP0, hmin⟩ :=
    Ideal.exists_minimal_mvPolynomial_totalDegree_ne_zero hI
  have hPeval : MvPolynomial.aeval x P = 0 := by
    exact RingHom.mem_ker.mp hPI
  have hPvars : P.vars.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hvars
    have hPC := MvPolynomial.vars_eq_empty_iff_eq_C.mp hvars
    rw [hPC] at hPeval hP0
    have hcmap : algebraMap K L (P.coeff 0) = 0 := by
      simpa using hPeval
    have hc : P.coeff 0 = 0 := by
      apply (algebraMap K L).injective
      simpa using hcmap
    exact hP0 (by simp [hc])
  obtain ⟨i, hi⟩ := hPvars
  obtain ⟨s, hsP, his⟩ :=
    (MvPolynomial.mem_vars_iff_mem_support i).mp hi
  have hpderiv0 : MvPolynomial.pderiv i P ≠ 0 :=
    pderiv_ne_zero_of_mem_support hsP his
  let c := mvPolynomialGradientEval x P
  have hc0 : c ≠ 0 := by
    intro hc
    have hcoeff : MvPolynomial.aeval x (MvPolynomial.pderiv i P) = 0 := by
      have h := congrArg (fun v : kappa →₀ L ↦ v i) hc
      simpa [c] using h
    have hpI : MvPolynomial.pderiv i P ∈ I := by
      exact RingHom.mem_ker.mpr hcoeff
    have hle := hmin hpI hpderiv0
    have hlt := totalDegree_pderiv_lt P i hpderiv0
    exact (not_lt_of_ge hle) hlt
  refine ⟨c, hc0, ?_⟩
  rw [← derivation_aeval_eq_gradient
    (KaehlerDifferential.D K L) x P]
  rw [hPeval, map_zero]

end

end GaloisForLFunctions

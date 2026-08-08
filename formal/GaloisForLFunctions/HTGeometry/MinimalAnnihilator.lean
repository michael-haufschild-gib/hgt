import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The separant of a minimal algebraic relation

If a family satisfies a nonzero polynomial relation, then it satisfies one of least total degree,
and that one has a **nonvanishing separant**: some partial derivative of it is *not* annihilated by
the family.

The mechanism replaces the classical "least order, then least degree in the highest jet" selection
by a single minimisation.  A relation of total degree zero is a constant, which cannot be
annihilated when the structure map is injective; so a minimal relation has a variable occurring in
it, its partial derivative in that variable is nonzero and of strictly smaller total degree, and
minimality forbids it from being a relation.

Characteristic zero enters only through `coeff_pderiv`: the derivative of a monomial in which the
variable actually occurs is not syntactically zero.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

variable {σ R : Type*} [CommRing R] [DecidableEq σ]

/-! ## Degrees under a partial derivative -/

/-- If the variable `j` occurs in a monomial of `P`, then `∂ⱼP ≠ 0`. -/
theorem pderiv_ne_zero_of_mem_support [NoZeroDivisors R] [CharZero R] {P : MvPolynomial σ R}
    {μ : σ →₀ ℕ} (hμ : μ ∈ P.support) {j : σ} (hj : 0 < μ j) : pderiv j P ≠ 0 := by
  classical
  set ν : σ →₀ ℕ := μ - Finsupp.single j 1 with hν
  have hadd : ν + Finsupp.single j 1 = μ := by
    rw [hν]
    ext i
    by_cases hij : i = j
    · subst hij
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
    · have hs : (Finsupp.single j (1 : ℕ)) i = 0 := by
        rw [Finsupp.single_apply, if_neg (fun hc => hij hc.symm)]
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, hs]
      omega
  have hνj : ν j = μ j - 1 := by
    rw [hν]
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
  have hcoeff := MvPolynomial.coeff_pderiv (i := j) P ν
  rw [hadd] at hcoeff
  have hPμ : MvPolynomial.coeff μ P ≠ 0 := MvPolynomial.mem_support_iff.mp hμ
  have hfac : (((ν j : ℕ) : R) + 1) ≠ 0 := by
    have hstep : (ν j) + 1 = μ j := by omega
    have hcast : ((ν j : ℕ) : R) + 1 = ((μ j : ℕ) : R) := by exact_mod_cast hstep
    rw [hcast]
    exact Nat.cast_ne_zero.mpr (by omega)
  intro hzero
  rw [hzero] at hcoeff
  simp only [MvPolynomial.coeff_zero] at hcoeff
  exact (mul_ne_zero hPμ hfac) hcoeff.symm

omit [DecidableEq σ] in
/-- A partial derivative strictly lowers the total degree, as soon as it is nonzero. -/
theorem totalDegree_pderiv_add_one_le [NoZeroDivisors R] [CharZero R] (P : MvPolynomial σ R)
    (j : σ) (h : pderiv j P ≠ 0) :
    (pderiv j P).totalDegree + 1 ≤ P.totalDegree := by
  classical
  have hne : (pderiv j P).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc
    exact h (MvPolynomial.support_eq_empty.mp hc)
  obtain ⟨μ, hμ, hsup⟩ :=
    Finset.exists_mem_eq_sup (pderiv j P).support hne (fun μ => μ.sum fun _ e => e)
  have hcoeff := MvPolynomial.coeff_pderiv (i := j) P μ
  have hne0 : MvPolynomial.coeff μ (pderiv j P) ≠ 0 := MvPolynomial.mem_support_iff.mp hμ
  rw [hcoeff] at hne0
  have hPmem : μ + Finsupp.single j 1 ∈ P.support :=
    MvPolynomial.mem_support_iff.mpr fun hc => hne0 (by rw [hc, zero_mul])
  have hle := MvPolynomial.le_totalDegree hPmem
  have hsum : (μ + Finsupp.single j 1).sum (fun _ e => e) = (μ.sum fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  rw [hsum] at hle
  rw [MvPolynomial.totalDegree, hsup]
  exact hle

/-! ## Minimal relations -/

variable {A : Type*} [CommRing A] [Algebra R A] [Fintype σ]

/-- **The separant of a minimal relation does not vanish.**  If some nonzero polynomial annihilates
`g`, then some nonzero polynomial annihilates `g` while one of its partial derivatives does not. -/
theorem exists_annihilator_with_nonvanishing_pderiv [NoZeroDivisors R] [CharZero R]
    (hinj : Function.Injective (algebraMap R A)) (g : σ → A)
    (hP : ∃ P : MvPolynomial σ R, P ≠ 0 ∧ aeval g P = 0) :
    ∃ P : MvPolynomial σ R, P ≠ 0 ∧ aeval g P = 0 ∧ ∃ j : σ, aeval g (pderiv j P) ≠ 0 := by
  classical
  obtain ⟨P₀, hP₀ne, hP₀0⟩ := hP
  have hex : ∃ d : ℕ, ∃ P : MvPolynomial σ R, P ≠ 0 ∧ aeval g P = 0 ∧ P.totalDegree = d :=
    ⟨P₀.totalDegree, P₀, hP₀ne, hP₀0, rfl⟩
  obtain ⟨P, hPne, hP0, hPd⟩ := Nat.find_spec hex
  have hmin : ∀ Q : MvPolynomial σ R, Q ≠ 0 → aeval g Q = 0 → Nat.find hex ≤ Q.totalDegree :=
    fun Q hQne hQ0 => Nat.find_le ⟨Q, hQne, hQ0, rfl⟩
  refine ⟨P, hPne, hP0, ?_⟩
  -- a minimal relation is not constant
  have hdeg : 0 < P.totalDegree := by
    rcases Nat.eq_zero_or_pos P.totalDegree with h | h
    · exfalso
      rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at h
      have hval : (algebraMap R A) (MvPolynomial.coeff 0 P) = 0 := by
        have hC : aeval g (C (MvPolynomial.coeff 0 P) : MvPolynomial σ R) = 0 := by
          rw [← h]
          exact hP0
        rwa [MvPolynomial.aeval_C] at hC
      have hzero : MvPolynomial.coeff 0 P = 0 := by
        refine hinj ?_
        rw [hval, map_zero]
      rw [h, hzero, map_zero] at hPne
      exact hPne rfl
    · exact h
  -- a variable occurs
  have hsupne : P.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc
    exact hPne (MvPolynomial.support_eq_empty.mp hc)
  obtain ⟨μ, hμ, hsup⟩ :=
    Finset.exists_mem_eq_sup P.support hsupne (fun μ => μ.sum fun _ e => e)
  have hμpos : 0 < μ.sum fun _ e => e := by
    rw [MvPolynomial.totalDegree, hsup] at hdeg
    exact hdeg
  obtain ⟨j, hj⟩ : ∃ j : σ, 0 < μ j := by
    by_contra hcon
    have hall : ∀ j : σ, μ j = 0 := by
      intro j
      have := not_exists.mp hcon j
      omega
    have hzero : μ = 0 := Finsupp.ext hall
    rw [hzero] at hμpos
    simp at hμpos
  have hpd : pderiv j P ≠ 0 := pderiv_ne_zero_of_mem_support hμ hj
  have hlt := totalDegree_pderiv_add_one_le P j hpd
  refine ⟨j, fun hzero => ?_⟩
  have hle := hmin (pderiv j P) hpd hzero
  rw [hPd] at hlt
  omega

end GaloisForLFunctions.HTGeometry

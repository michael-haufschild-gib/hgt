import GaloisForLFunctions.Hurwitz.JointPowerOrbit
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Degreewise separation on multicolumn power orbits

A single common power orbit separates all monomials only under multiplicative independence.
Independent columns carry more information: after taking one finite difference in each of `L`
columns, every polynomial of total degree at most `L` is reduced to the component that is linear in
every column.  That component only sees the degree-one nodes.  Consequently pairwise distinct
nontrivial nodes suffice for top-degree separation.
-/

open Complex

namespace HurwitzJointOrbit

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Restriction of a monomial exponent vector to one column. -/
def columnSlice {L : ℕ} (d : (ι × Fin L) →₀ ℕ) (n : Fin L) : ι →₀ ℕ :=
  Finsupp.comapDomain.addMonoidHom (fun j : ι => (j, n))
    (fun _ _ h => Prod.fst_eq_iff.mp h) d

@[simp]
theorem columnSlice_apply {L : ℕ} (d : (ι × Fin L) →₀ ℕ) (n : Fin L) (j : ι) :
    columnSlice d n j = d (j, n) := by
  rfl

/-- Value of the monomial in column `n` at the node family `q`. -/
def columnMonomialValue {L : ℕ} (q : ι → ℂ) (n : Fin L)
    (d : (ι × Fin L) →₀ ℕ) : ℂ :=
  monomialValue q (columnSlice d n)

/-- The total exponent carried by one column. -/
def columnDegree {L : ℕ} (d : (ι × Fin L) →₀ ℕ) (n : Fin L) : ℕ :=
  (columnSlice d n).degree

theorem degree_eq_sum_columnDegree {L : ℕ} (d : (ι × Fin L) →₀ ℕ) :
    d.degree = ∑ n : Fin L, columnDegree d n := by
  classical
  rw [Finsupp.degree, Finsupp.sum_fintype]
  simp only [columnDegree, Finsupp.degree, Finsupp.sum_fintype, columnSlice_apply]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- Coefficientwise finite difference in a set of independent columns. -/
def columnDifferenceSet {L : ℕ} (q : ι → ℂ) (S : Finset (Fin L))
    (P : MvPolynomial (ι × Fin L) ℂ) : MvPolynomial (ι × Fin L) ℂ :=
  P.sum fun d c =>
    MvPolynomial.monomial d (c * ∏ n ∈ S, (columnMonomialValue q n d - 1))

theorem coeff_columnDifferenceSet {L : ℕ} (q : ι → ℂ) (S : Finset (Fin L))
    (P : MvPolynomial (ι × Fin L) ℂ) (d : (ι × Fin L) →₀ ℕ) :
    MvPolynomial.coeff d (columnDifferenceSet q S P) =
      MvPolynomial.coeff d P * ∏ n ∈ S, (columnMonomialValue q n d - 1) := by
  classical
  rw [columnDifferenceSet, MvPolynomial.sum_def, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  by_cases hd : d ∈ P.support
  · rw [Finset.sum_eq_single d]
    · simp [hd]
    · intro e heP hed
      simp [hed]
    · simp [hd]
  · have hcoeff : MvPolynomial.coeff d P = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    rw [hcoeff, zero_mul]
    apply Finset.sum_eq_zero
    intro e he
    simp only
    split_ifs with h
    · subst h
      exact (hd he).elim
    · rfl

end

end HurwitzJointOrbit

import GaloisForLFunctions.HTGeometry.DifferentialPolynomialOver
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# The ordinary differential rank of a scalar differential polynomial

For one ordinary differential indeterminate, Ritt's ranking needs no general characteristic-set
machinery: compare the highest jet that occurs, then its degree.  When selecting a characteristic
polynomial inside a prime relation ideal we additionally minimize total degree; this final
tie-breaker is what makes the usual irreducibility argument valid.
-/

namespace GaloisForLFunctions

noncomputable section

/-- Highest jet order occurring in a scalar differential polynomial.  Constants have order zero. -/
def scalarDifferentialPolynomialOrder
    {K : Type*} [CommSemiring K] (P : DifferentialPolynomial Unit K) : ℕ :=
  P.vars.sup fun j ↦ j.2

/-- The highest formal jet of a scalar differential polynomial. -/
def scalarDifferentialPolynomialLeader
    {K : Type*} [CommSemiring K] (P : DifferentialPolynomial Unit K) : Unit × ℕ :=
  ((), scalarDifferentialPolynomialOrder P)

/-- Degree in the highest formal jet. -/
def scalarDifferentialPolynomialLeaderDegree
    {K : Type*} [CommSemiring K] (P : DifferentialPolynomial Unit K) : ℕ :=
  P.degreeOf (scalarDifferentialPolynomialLeader P)

@[simp]
theorem scalarDifferentialPolynomialOrder_C
    {K : Type*} [CommSemiring K] (a : K) :
    scalarDifferentialPolynomialOrder
        (MvPolynomial.C a : DifferentialPolynomial Unit K) = 0 := by
  simp [scalarDifferentialPolynomialOrder]

@[simp]
theorem scalarDifferentialPolynomialOrder_X
    {K : Type*} [CommSemiring K] [Nontrivial K] (n : ℕ) :
    scalarDifferentialPolynomialOrder
        (MvPolynomial.X ((), n) : DifferentialPolynomial Unit K) = n := by
  simp [scalarDifferentialPolynomialOrder]

@[simp]
theorem scalarDifferentialPolynomialLeaderDegree_C
    {K : Type*} [CommSemiring K] (a : K) :
    scalarDifferentialPolynomialLeaderDegree
        (MvPolynomial.C a : DifferentialPolynomial Unit K) = 0 := by
  simp [scalarDifferentialPolynomialLeaderDegree,
    scalarDifferentialPolynomialLeader]

/-- A nonconstant scalar differential polynomial genuinely contains its declared leader. -/
theorem scalarDifferentialPolynomialLeader_mem_vars
    {K : Type*} [CommSemiring K]
    {P : DifferentialPolynomial Unit K} (hP : P.vars.Nonempty) :
    scalarDifferentialPolynomialLeader P ∈ P.vars := by
  obtain ⟨j, hj, hsup⟩ := Finset.exists_mem_eq_sup P.vars hP (fun j ↦ j.2)
  have hj_eq : scalarDifferentialPolynomialLeader P = j := by
    rcases j with ⟨u, n⟩
    have hu : u = () := Subsingleton.elim _ _
    subst u
    simp only [scalarDifferentialPolynomialLeader,
      scalarDifferentialPolynomialOrder] at hsup ⊢
    exact congrArg (fun m : ℕ ↦ ((), m)) hsup
  exact hj_eq.symm ▸ hj

/-- The leader degree of a nonconstant scalar differential polynomial is positive. -/
theorem scalarDifferentialPolynomialLeaderDegree_pos
    {K : Type*} [CommSemiring K]
    {P : DifferentialPolynomial Unit K} (hP : P.vars.Nonempty) :
    0 < scalarDifferentialPolynomialLeaderDegree P := by
  rw [Nat.pos_iff_ne_zero, scalarDifferentialPolynomialLeaderDegree,
    ← MvPolynomial.mem_vars_iff_degreeOf_ne_zero]
  exact scalarDifferentialPolynomialLeader_mem_vars hP

/-- The three nested minimality conditions used for a scalar characteristic polynomial:
ordinary differential order, leader degree at that order, and total degree after both ties. -/
def IsMinimalScalarDifferentialPolynomialRank
    {K : Type*} [CommSemiring K]
    (S : Set (DifferentialPolynomial Unit K))
    (P : DifferentialPolynomial Unit K) : Prop :=
  P ∈ S ∧ P ≠ 0 ∧ P.vars.Nonempty ∧
    ∀ ⦃Q : DifferentialPolynomial Unit K⦄,
      Q ∈ S → Q ≠ 0 → Q.vars.Nonempty →
        scalarDifferentialPolynomialOrder P ≤ scalarDifferentialPolynomialOrder Q ∧
        (scalarDifferentialPolynomialOrder P = scalarDifferentialPolynomialOrder Q →
          scalarDifferentialPolynomialLeaderDegree P ≤
            scalarDifferentialPolynomialLeaderDegree Q) ∧
        (scalarDifferentialPolynomialOrder P = scalarDifferentialPolynomialOrder Q →
          scalarDifferentialPolynomialLeaderDegree P =
            scalarDifferentialPolynomialLeaderDegree Q →
          P.totalDegree ≤ Q.totalDegree)

/-- Every nonempty family of nonzero nonconstant scalar differential polynomials has an element
minimal first in differential order, then leader degree, then total degree. -/
theorem exists_minimalScalarDifferentialPolynomialRank
    {K : Type*} [CommSemiring K]
    {S : Set (DifferentialPolynomial Unit K)}
    (hS : ∃ P : DifferentialPolynomial Unit K,
      P ∈ S ∧ P ≠ 0 ∧ P.vars.Nonempty) :
    ∃ P : DifferentialPolynomial Unit K,
      IsMinimalScalarDifferentialPolynomialRank S P := by
  classical
  have hOrder : ∃ o : ℕ, ∃ P : DifferentialPolynomial Unit K,
      P ∈ S ∧ P ≠ 0 ∧ P.vars.Nonempty ∧
        scalarDifferentialPolynomialOrder P = o := by
    obtain ⟨P, hPS, hP0, hPv⟩ := hS
    exact ⟨_, P, hPS, hP0, hPv, rfl⟩
  let o := Nat.find hOrder
  have hoSpec : ∃ P : DifferentialPolynomial Unit K,
      P ∈ S ∧ P ≠ 0 ∧ P.vars.Nonempty ∧
        scalarDifferentialPolynomialOrder P = o := by
    simpa [o] using Nat.find_spec hOrder
  have hLeader : ∃ d : ℕ, ∃ P : DifferentialPolynomial Unit K,
      P ∈ S ∧ P ≠ 0 ∧ P.vars.Nonempty ∧
        scalarDifferentialPolynomialOrder P = o ∧
        scalarDifferentialPolynomialLeaderDegree P = d := by
    obtain ⟨P, hPS, hP0, hPv, hPo⟩ := hoSpec
    exact ⟨_, P, hPS, hP0, hPv, hPo, rfl⟩
  let d := Nat.find hLeader
  have hdSpec : ∃ P : DifferentialPolynomial Unit K,
      P ∈ S ∧ P ≠ 0 ∧ P.vars.Nonempty ∧
        scalarDifferentialPolynomialOrder P = o ∧
        scalarDifferentialPolynomialLeaderDegree P = d := by
    simpa [d] using Nat.find_spec hLeader
  have hTotal : ∃ t : ℕ, ∃ P : DifferentialPolynomial Unit K,
      P ∈ S ∧ P ≠ 0 ∧ P.vars.Nonempty ∧
        scalarDifferentialPolynomialOrder P = o ∧
        scalarDifferentialPolynomialLeaderDegree P = d ∧
        P.totalDegree = t := by
    obtain ⟨P, hPS, hP0, hPv, hPo, hPd⟩ := hdSpec
    exact ⟨_, P, hPS, hP0, hPv, hPo, hPd, rfl⟩
  let t := Nat.find hTotal
  have htSpec : ∃ P : DifferentialPolynomial Unit K,
      P ∈ S ∧ P ≠ 0 ∧ P.vars.Nonempty ∧
        scalarDifferentialPolynomialOrder P = o ∧
        scalarDifferentialPolynomialLeaderDegree P = d ∧
        P.totalDegree = t := by
    simpa [t] using Nat.find_spec hTotal
  obtain ⟨P, hPS, hP0, hPv, hPo, hPd, hPt⟩ := htSpec
  refine ⟨P, hPS, hP0, hPv, ?_⟩
  intro Q hQS hQ0 hQv
  have hOle : o ≤ scalarDifferentialPolynomialOrder Q :=
    Nat.find_min' hOrder ⟨Q, hQS, hQ0, hQv, rfl⟩
  refine ⟨hPo.trans_le hOle, ?_, ?_⟩
  · intro hOrderEq
    have hQo : scalarDifferentialPolynomialOrder Q = o := by
      exact hOrderEq.symm.trans hPo
    have hDle : d ≤ scalarDifferentialPolynomialLeaderDegree Q :=
      Nat.find_min' hLeader ⟨Q, hQS, hQ0, hQv, hQo, rfl⟩
    exact hPd.trans_le hDle
  · intro hOrderEq hLeaderEq
    have hQo : scalarDifferentialPolynomialOrder Q = o := by
      exact hOrderEq.symm.trans hPo
    have hQd : scalarDifferentialPolynomialLeaderDegree Q = d := by
      exact hLeaderEq.symm.trans hPd
    have hTle : t ≤ Q.totalDegree :=
      Nat.find_min' hTotal ⟨Q, hQS, hQ0, hQv, hQo, hQd, rfl⟩
    exact hPt.trans_le hTle

/-- A nonzero proper ideal in a scalar differential-polynomial ring contains a nonzero
nonconstant polynomial. -/
theorem Ideal.exists_nonzero_nonconstant_scalarDifferentialPolynomial
    {K : Type*} [Field K]
    {I : Ideal (DifferentialPolynomial Unit K)}
    (hI0 : I ≠ ⊥) (hItop : I ≠ ⊤) :
    ∃ P : DifferentialPolynomial Unit K,
      P ∈ I ∧ P ≠ 0 ∧ P.vars.Nonempty := by
  classical
  have hex : ∃ P : DifferentialPolynomial Unit K, P ∈ I ∧ P ≠ 0 := by
    by_contra h
    apply hI0
    ext P
    simp only [Ideal.mem_bot]
    constructor
    · intro hPI
      by_contra hP0
      exact h ⟨P, hPI, hP0⟩
    · intro hP
      subst P
      exact I.zero_mem
  obtain ⟨P, hPI, hP0⟩ := hex
  by_cases hPv : P.vars.Nonempty
  · exact ⟨P, hPI, hP0, hPv⟩
  · have hPvars : P.vars = ∅ := Finset.not_nonempty_iff_eq_empty.mp hPv
    have hPC : P = MvPolynomial.C (P.coeff 0) :=
      MvPolynomial.vars_eq_empty_iff_eq_C.mp hPvars
    have hc : P.coeff 0 ≠ 0 := by
      intro hc
      apply hP0
      rw [hPC, hc]
      simp
    have hunit : IsUnit P := by
      rw [hPC]
      exact IsUnit.map (MvPolynomial.C : K →+* DifferentialPolynomial Unit K) hc.isUnit
    exact (hItop (I.eq_top_of_isUnit_mem hPI hunit)).elim

/-- A nonzero proper ideal contains a scalar differential polynomial with the repaired minimal
Ritt rank: order, leader degree, and then total degree. -/
theorem Ideal.exists_minimal_scalarDifferentialPolynomialRank_ne_zero
    {K : Type*} [Field K]
    {I : Ideal (DifferentialPolynomial Unit K)}
    (hI0 : I ≠ ⊥) (hItop : I ≠ ⊤) :
    ∃ P : DifferentialPolynomial Unit K,
      IsMinimalScalarDifferentialPolynomialRank (I : Set _) P :=
  exists_minimalScalarDifferentialPolynomialRank
    (Ideal.exists_nonzero_nonconstant_scalarDifferentialPolynomial
      (I := I) hI0 hItop)

end

end GaloisForLFunctions

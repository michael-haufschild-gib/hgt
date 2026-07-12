import GaloisForLFunctions.HTGeometry.CountableDifferentialPattern
import GaloisForLFunctions.HTGeometry.PolynomialRelationDetector

/-!
# Rectangular code of a finite polynomial-coefficient differential relation

Once a finite shift packet and its jet-order rectangle are fixed, every multivariate polynomial
with coefficients in `C[z]` has a canonical finite differential-pattern code.  Its distinct
monomials are exactly the polynomial support, and its coefficient-degree bound dominates the
degree of every supported coefficient polynomial.

This is the first normalization half of the bridge from patternwise coefficient rigidity to the
standard differential-polynomial interface.  The remaining half is the exact evaluation identity
between the reconstructed coefficient vector and `specializePolynomialCoefficients`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- Maximum polynomial coefficient degree appearing in a finite multivariate support. -/
noncomputable def polynomialCoefficientDegreeBound
    {σ : Type*} (Q : MvPolynomial σ ℂ[X]) : ℕ :=
  Q.support.sup fun d ↦ (MvPolynomial.coeff d Q).natDegree

theorem polynomialCoefficient_natDegree_le_bound
    {σ : Type*} (Q : MvPolynomial σ ℂ[X])
    {d : σ →₀ ℕ} (hd : d ∈ Q.support) :
    (MvPolynomial.coeff d Q).natDegree ≤ polynomialCoefficientDegreeBound Q := by
  change (MvPolynomial.coeff d Q).natDegree ≤
    Q.support.sup (fun e ↦ (MvPolynomial.coeff e Q).natDegree)
  exact Finset.le_sup (f := fun e ↦ (MvPolynomial.coeff e Q).natDegree) hd

/-- Canonical finite pattern whose monomial list is exactly the support of `Q`. -/
noncomputable def finitePatternOfPolynomial
    {Γ : Type*} {m : ℕ} (shiftCode : Fin m → Γ)
    (hshiftCode : Function.Injective shiftCode) (orders : Fin m → ℕ)
    (Q : MvPolynomial (Σ i, Fin (orders i)) ℂ[X]) :
    FiniteDifferentialPattern Γ where
  shiftCount := m
  shiftCode := shiftCode
  orders := orders
  monomialCount := Fintype.card Q.support
  jetExponent := fun b ↦ ((Fintype.equivFin Q.support).symm b).val
  coefficientDegree := polynomialCoefficientDegreeBound Q
  shiftCode_injective := hshiftCode
  jetExponent_injective := by
    intro a b hab
    apply (Fintype.equivFin Q.support).symm.injective
    apply Subtype.ext
    exact hab

theorem finitePatternOfPolynomial_jetExponent_mem_support
    {Γ : Type*} {m : ℕ} (shiftCode : Fin m → Γ)
    (hshiftCode : Function.Injective shiftCode) (orders : Fin m → ℕ)
    (Q : MvPolynomial (Σ i, Fin (orders i)) ℂ[X])
    (b : Fin (finitePatternOfPolynomial shiftCode hshiftCode orders Q).monomialCount) :
    (finitePatternOfPolynomial shiftCode hshiftCode orders Q).jetExponent b ∈ Q.support := by
  exact ((Fintype.equivFin Q.support).symm b).property

/-- Every supported monomial occurs in the canonical pattern. -/
theorem finitePatternOfPolynomial_jetExponent_surjective
    {Γ : Type*} {m : ℕ} (shiftCode : Fin m → Γ)
    (hshiftCode : Function.Injective shiftCode) (orders : Fin m → ℕ)
    (Q : MvPolynomial (Σ i, Fin (orders i)) ℂ[X])
    {d : (Σ i, Fin (orders i)) →₀ ℕ} (hd : d ∈ Q.support) :
    ∃ b : Fin (finitePatternOfPolynomial shiftCode hshiftCode orders Q).monomialCount,
      (finitePatternOfPolynomial shiftCode hshiftCode orders Q).jetExponent b = d := by
  let x : Q.support := ⟨d, hd⟩
  refine ⟨Fintype.equivFin Q.support x, ?_⟩
  simp [finitePatternOfPolynomial, x]

/-- The canonical pattern degree bound covers every supported coefficient. -/
theorem finitePatternOfPolynomial_coefficientDegree_bound
    {Γ : Type*} {m : ℕ} (shiftCode : Fin m → Γ)
    (hshiftCode : Function.Injective shiftCode) (orders : Fin m → ℕ)
    (Q : MvPolynomial (Σ i, Fin (orders i)) ℂ[X])
    {d : (Σ i, Fin (orders i)) →₀ ℕ} (hd : d ∈ Q.support) :
    (MvPolynomial.coeff d Q).natDegree ≤
      (finitePatternOfPolynomial shiftCode hshiftCode orders Q).coefficientDegree := by
  exact polynomialCoefficient_natDegree_le_bound Q hd

/-- Coefficient vector of `Q` in its rectangular expanded basis. -/
noncomputable def polynomialPatternCoefficientVector
    {Γ : Type*} {m : ℕ} (shiftCode : Fin m → Γ)
    (hshiftCode : Function.Injective shiftCode) (orders : Fin m → ℕ)
    (Q : MvPolynomial (Σ i, Fin (orders i)) ℂ[X]) :
    PatternRow (finitePatternOfPolynomial shiftCode hshiftCode orders Q) → ℂ :=
  fun b ↦
    let p := finitePatternOfPolynomial shiftCode hshiftCode orders Q
    let md := (Fintype.equivFin (PatternShape p)).symm b
    Polynomial.coeff (MvPolynomial.coeff (p.jetExponent md.1) Q) md.2.val

/-- The rectangular coefficient vector is faithful: if all of its entries vanish, then the
original polynomial-coefficient multivariate polynomial is zero. -/
theorem polynomial_eq_zero_of_patternCoefficientVector_eq_zero
    {Γ : Type*} {m : ℕ} (shiftCode : Fin m → Γ)
    (hshiftCode : Function.Injective shiftCode) (orders : Fin m → ℕ)
    (Q : MvPolynomial (Σ i, Fin (orders i)) ℂ[X])
    (hzero : ∀ b, polynomialPatternCoefficientVector
      shiftCode hshiftCode orders Q b = 0) :
    Q = 0 := by
  apply MvPolynomial.ext
  intro d
  by_cases hd : d ∈ Q.support
  · apply Polynomial.ext
    intro n
    by_cases hn : n ≤ polynomialCoefficientDegreeBound Q
    · let r : Fin (Fintype.card Q.support) :=
        Fintype.equivFin Q.support ⟨d, hd⟩
      let j : Fin (polynomialCoefficientDegreeBound Q + 1) :=
        ⟨n, Nat.lt_succ_of_le hn⟩
      let p := finitePatternOfPolynomial shiftCode hshiftCode orders Q
      let e := Fintype.equivFin (PatternShape p)
      let b : PatternRow p := e (r, j)
      have hz := hzero b
      change Polynomial.coeff
        (MvPolynomial.coeff (p.jetExponent (e.symm b).1) Q)
        (e.symm b).2.val = 0 at hz
      have hb : e.symm b = (r, j) := e.symm_apply_apply (r, j)
      rw [hb] at hz
      have hr : (Fintype.equivFin Q.support).symm r = ⟨d, hd⟩ :=
        (Fintype.equivFin Q.support).symm_apply_apply ⟨d, hd⟩
      change Polynomial.coeff
        (MvPolynomial.coeff (((Fintype.equivFin Q.support).symm r).val) Q)
        j.val = 0 at hz
      rw [hr] at hz
      exact hz
    · have hdeg := polynomialCoefficient_natDegree_le_bound Q hd
      exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt hdeg (lt_of_not_ge hn))
  · exact not_ne_iff.mp (mt MvPolynomial.mem_support_iff.mpr hd)

/-- Exact reconstruction of specialized evaluation from the rectangular coefficient vector. -/
theorem polynomialPatternCoefficientExpansion
    {Γ : Type*} {m : ℕ} (shiftCode : Fin m → Γ)
    (hshiftCode : Function.Injective shiftCode) (orders : Fin m → ℕ)
    (Q : MvPolynomial (Σ i, Fin (orders i)) ℂ[X])
    (z : ℂ) (x : (Σ i, Fin (orders i)) → ℂ) :
    ∑ b, polynomialPatternCoefficientVector shiftCode hshiftCode orders Q b *
      z ^ patternDegree (finitePatternOfPolynomial shiftCode hshiftCode orders Q) b *
      (patternExponent (finitePatternOfPolynomial shiftCode hshiftCode orders Q) b).prod
        (fun i e ↦ x i ^ e) =
      MvPolynomial.eval x (specializePolynomialCoefficients z Q) := by
  let p := finitePatternOfPolynomial shiftCode hshiftCode orders Q
  let e := Fintype.equivFin (PatternShape p)
  let es := Fintype.equivFin Q.support
  let monomialValue : ((Σ i, Fin (orders i)) →₀ ℕ) → ℂ :=
    fun d ↦ d.prod (fun i n ↦ x i ^ n)
  calc
    ∑ b, polynomialPatternCoefficientVector shiftCode hshiftCode orders Q b *
        z ^ patternDegree p b * (patternExponent p b).prod (fun i n ↦ x i ^ n) =
        ∑ md : PatternShape p,
          polynomialPatternCoefficientVector shiftCode hshiftCode orders Q (e md) *
            z ^ patternDegree p (e md) *
            (patternExponent p (e md)).prod (fun i n ↦ x i ^ n) := by
      exact (e.sum_comp fun b ↦
        polynomialPatternCoefficientVector shiftCode hshiftCode orders Q b *
          z ^ patternDegree p b *
          (patternExponent p b).prod (fun i n ↦ x i ^ n)).symm
    _ = ∑ r : Fin (Fintype.card Q.support),
          ∑ j : Fin (polynomialCoefficientDegreeBound Q + 1),
            Polynomial.coeff (MvPolynomial.coeff ((es.symm r).val) Q) j.val *
              z ^ j.val * monomialValue (es.symm r).val := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro j hj
      have hmd : e.symm (e (r, j)) = (r, j) := e.symm_apply_apply (r, j)
      change Polynomial.coeff
          (MvPolynomial.coeff (p.jetExponent (e.symm (e (r, j))).1) Q)
          (e.symm (e (r, j))).2.val *
        z ^ patternDegree p (e (r, j)) *
          (patternExponent p (e (r, j))).prod (fun i n ↦ x i ^ n) = _
      rw [hmd]
      have hjet : p.jetExponent r = (es.symm r).val := by
        rfl
      have hdegree : patternDegree p (e (r, j)) = j.val := by
        change ((Fintype.equivFin (PatternShape p)).symm (e (r, j))).2.val = j.val
        simp [e]
      have hexponent : patternExponent p (e (r, j)) = (es.symm r).val := by
        change p.jetExponent
          ((Fintype.equivFin (PatternShape p)).symm (e (r, j))).1 = _
        rw [show (Fintype.equivFin (PatternShape p)).symm (e (r, j)) = (r, j) by
          simp [e]]
        exact hjet
      rw [hjet, hdegree, hexponent]
      rfl
    _ = ∑ r : Fin (Fintype.card Q.support),
          Polynomial.eval z (MvPolynomial.coeff ((es.symm r).val) Q) *
            monomialValue (es.symm r).val := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Polynomial.eval_eq_sum_range'
        (n := polynomialCoefficientDegreeBound Q + 1)]
      · rw [Fin.sum_univ_eq_sum_range
          (fun j ↦ Polynomial.coeff (MvPolynomial.coeff ((es.symm r).val) Q) j *
            z ^ j * monomialValue (es.symm r).val)]
        rw [Finset.sum_mul]
      · exact Nat.lt_succ_of_le
          (polynomialCoefficient_natDegree_le_bound Q (es.symm r).property)
    _ = ∑ d : Q.support,
          Polynomial.eval z (MvPolynomial.coeff d.val Q) * monomialValue d.val := by
      exact (es.symm.sum_comp fun d : Q.support ↦
        Polynomial.eval z (MvPolynomial.coeff d.val Q) * monomialValue d.val)
    _ = MvPolynomial.eval x (specializePolynomialCoefficients z Q) := by
      rw [specializePolynomialCoefficients, MvPolynomial.eval_map,
        MvPolynomial.eval₂_eq]
      rw [Finset.sum_subtype Q.support (fun _ ↦ Iff.rfl)]
      apply Finset.sum_congr rfl
      intro d hd
      simp only [monomialValue]
      rw [Finsupp.prod]
      rfl

end GaloisForLFunctions.HTGeometry

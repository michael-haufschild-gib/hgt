import GaloisForLFunctions.HTGeometry.FirstOrderMvPoly
import GaloisForLFunctions.HTGeometry.CauchySecondOrderStep

/-!
# Polynomial-coefficient monomial rows for second-order equations

Every polynomial in the four coordinates `(z, f, f′, f″)` can be regrouped canonically by the
three jet exponents.  The remaining exponent becomes a one-variable polynomial coefficient in
`z`.  This is the exact compiler from `DifferentiallyAlgebraicOfOrder f 2` to the finite row format
needed by the order-two Wiman--Valiron layer.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Exponents of the value, first derivative and second derivative in one monomial. -/
structure SecondOrderPowers where
  value : ℕ
  first : ℕ
  second : ℕ
deriving DecidableEq

/-- Jet exponents obtained by forgetting the independent-variable exponent. -/
def secondOrderPowers (m : Fin 4 →₀ ℕ) : SecondOrderPowers :=
  ⟨m 1, m 2, m 3⟩

/-- Finite set of jet-exponent triples occurring in a second-order differential polynomial. -/
def secondOrderSupport (P : MvPolynomial (Fin 4) ℂ) : Finset SecondOrderPowers :=
  P.support.image secondOrderPowers

/-- Polynomial in `z` obtained by collecting monomials with the same three jet exponents. -/
def secondOrderCoeff (P : MvPolynomial (Fin 4) ℂ) (p : SecondOrderPowers) : Polynomial ℂ :=
  ∑ m ∈ P.support with secondOrderPowers m = p,
    Polynomial.monomial (m 0) (P.coeff m)

/-- Regrouping preserves evaluation exactly. -/
theorem eval_secondOrderSupport (P : MvPolynomial (Fin 4) ℂ) (z u v w : ℂ) :
    ∑ p ∈ secondOrderSupport P,
        (secondOrderCoeff P p).eval z * u ^ p.value * v ^ p.first * w ^ p.second =
      MvPolynomial.eval ![z, u, v, w] P := by
  classical
  rw [MvPolynomial.eval_eq]
  calc
    ∑ p ∈ secondOrderSupport P,
        (secondOrderCoeff P p).eval z * u ^ p.value * v ^ p.first * w ^ p.second =
        ∑ p ∈ secondOrderSupport P,
          ∑ m ∈ P.support with secondOrderPowers m = p,
            P.coeff m * z ^ m 0 * u ^ m 1 * v ^ m 2 * w ^ m 3 := by
      refine Finset.sum_congr rfl ?_
      intro p hp
      rw [secondOrderCoeff, Polynomial.eval_finsetSum]
      simp_rw [Polynomial.eval_monomial]
      rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro m hm
      have hmp : secondOrderPowers m = p := (Finset.mem_filter.mp hm).2
      have h1 : m 1 = p.value := congrArg SecondOrderPowers.value hmp
      have h2 : m 2 = p.first := congrArg SecondOrderPowers.first hmp
      have h3 : m 3 = p.second := congrArg SecondOrderPowers.second hmp
      rw [← h1, ← h2, ← h3]
    _ = ∑ m ∈ P.support,
        P.coeff m * z ^ m 0 * u ^ m 1 * v ^ m 2 * w ^ m 3 := by
      exact Finset.sum_fiberwise_of_maps_to
        (s := P.support) (t := secondOrderSupport P)
        (g := secondOrderPowers)
        (fun m hm => Finset.mem_image.mpr ⟨m, hm, rfl⟩)
        (fun m => P.coeff m * z ^ m 0 * u ^ m 1 * v ^ m 2 * w ^ m 3)
    _ = ∑ d ∈ P.support, P.coeff d * ∏ i ∈ d.support, ![z, u, v, w] i ^ d i := by
      refine Finset.sum_congr rfl ?_
      intro m hm
      have hprod : ∏ i ∈ m.support, ![z, u, v, w] i ^ m i =
          z ^ m 0 * u ^ m 1 * v ^ m 2 * w ^ m 3 := by
        change (m.prod fun i e => ![z, u, v, w] i ^ e) = _
        rw [Finsupp.prod_fintype m (fun i e => ![z, u, v, w] i ^ e)
          (by intro i; simp), Fin.prod_univ_four]
        rfl
      rw [hprod]
      ring

/-- Jet total degree is bounded by total degree of the original differential polynomial. -/
theorem secondOrderSupport_degree_le (P : MvPolynomial (Fin 4) ℂ) {p : SecondOrderPowers}
    (hp : p ∈ secondOrderSupport P) :
    p.value + p.first + p.second ≤ P.totalDegree := by
  classical
  obtain ⟨m, hm, hmp⟩ := Finset.mem_image.mp hp
  have htotal := MvPolynomial.le_totalDegree hm
  have hsum : m.sum (fun _ e => e) = m 0 + m 1 + m 2 + m 3 := by
    rw [Finsupp.sum_fintype m (fun _ e => e) (by intro i; rfl), Fin.sum_univ_four]
  rw [hsum] at htotal
  have h1 : p.value = m 1 := by rw [← hmp]; rfl
  have h2 : p.first = m 2 := by rw [← hmp]; rfl
  have h3 : p.second = m 3 := by rw [← hmp]; rfl
  rw [h1, h2, h3]
  omega

/-- A nonzero differential polynomial leaves at least one nonzero collected coefficient. -/
theorem exists_nonzero_secondOrderCoeff {P : MvPolynomial (Fin 4) ℂ} (hP : P ≠ 0) :
    ∃ p ∈ secondOrderSupport P, secondOrderCoeff P p ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  apply hP
  apply MvPolynomial.funext
  intro x
  have hx : (![x 0, x 1, x 2, x 3] : Fin 4 → ℂ) = x := by
    funext i
    fin_cases i <;> rfl
  rw [← hx, ← eval_secondOrderSupport]
  exact Finset.sum_eq_zero (fun p hp => by rw [hcon p hp]; simp)

open GaloisForLFunctions

/-- **Canonical finite row for an arbitrary order-two ADE.**  No nondegeneracy or Newton-face
hypothesis is introduced. -/
theorem exists_secondOrderRelation_of_differentiallyAlgebraicOfOrder_two {f : ℂ → ℂ}
    (h : DifferentiallyAlgebraicOfOrder f 2) :
    ∃ (S : Finset SecondOrderPowers) (A : SecondOrderPowers → Polynomial ℂ) (d : ℕ),
      (∃ p ∈ S, A p ≠ 0) ∧
      (∀ p ∈ S, p.value + p.first + p.second ≤ d) ∧
      ∀ z : ℂ, ∑ p ∈ S, (A p).eval z * (f z) ^ p.value *
        (deriv f z) ^ p.first * (deriv (deriv f) z) ^ p.second = 0 := by
  classical
  obtain ⟨P, hP, hrel⟩ := h
  refine ⟨secondOrderSupport P, secondOrderCoeff P, P.totalDegree,
    exists_nonzero_secondOrderCoeff hP, ?_, ?_⟩
  · intro p hp
    exact secondOrderSupport_degree_le P hp
  · intro z
    rw [eval_secondOrderSupport]
    have hvec : (Fin.cons z fun j : Fin 3 => iteratedDeriv (j : ℕ) f z) =
        (![z, f z, deriv f z, deriv (deriv f) z] : Fin 4 → ℂ) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · rw [Fin.cons_succ]
        fin_cases j
        · simp [iteratedDeriv_zero]
        · simp [iteratedDeriv_one]
        · rw [show iteratedDeriv 2 f z = deriv (deriv f) z by
            rw [HTGeometry.iteratedDeriv_two]]
          rfl
    rw [← hvec]
    exact hrel z

end

end GaloisForLFunctions.HTGeometry

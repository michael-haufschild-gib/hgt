import GaloisForLFunctions.HTGeometry.ExpPolyCascade

/-!
# The two-map polynomial-coefficient cascade has differential order two

Every hypothesis is now available: the maps are transcendental entire and satisfy first-order
equations, so the composite has order at most two; and the model jets are algebraically independent,
so it has no equation of order one.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- **The first-order equation of a polynomial-coefficient map.** -/
theorem differentiallyAlgebraicOfOrder_one_expPoly (A : ℕ → Polynomial ℂ) (c d : ℕ → ℂ) (k : ℕ) :
    DifferentiallyAlgebraicOfOrder (expPoly A c d k) 1 := by
  classical
  refine ⟨MvPolynomial.X 2
      - (Polynomial.aeval (MvPolynomial.X (0 : Fin 3)) (A k).derivative)
        * (MvPolynomial.X 1 - MvPolynomial.C (d k)), ?_, ?_⟩
  · intro h0
    have h1 := congrArg (MvPolynomial.eval (![0, d k, 1] : Fin 3 → ℂ)) h0
    have hv2 : (![0, d k, 1] : Fin 3 → ℂ) 2 = 1 := rfl
    have hv1 : (![0, d k, 1] : Fin 3 → ℂ) 1 = d k := rfl
    simp only [map_sub, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, map_zero,
      hv2, hv1, sub_self, mul_zero, sub_zero] at h1
    exact one_ne_zero h1
  · intro z
    have h0 : iteratedDeriv 0 (expPoly A c d k) z = expPoly A c d k z := by
      simp [iteratedDeriv_zero]
    have h1 : iteratedDeriv 1 (expPoly A c d k) z
        = (A k).derivative.eval z * (expPoly A c d k z - d k) := by
      rw [iteratedDeriv_one, deriv_expPoly]
    have hev : MvPolynomial.eval
        (Fin.cons z (fun j : Fin 2 => iteratedDeriv (j : ℕ) (expPoly A c d k) z) : Fin 3 → ℂ)
        (Polynomial.aeval (MvPolynomial.X (0 : Fin 3)) (A k).derivative)
        = (A k).derivative.eval z := by
      induction (A k).derivative using Polynomial.induction_on with
      | C a => simp
      | add p q hp hq => simp [hp, hq]
      | monomial n a _ =>
          have hxz : (Fin.cons z
              (fun j : Fin 2 => iteratedDeriv (j : ℕ) (expPoly A c d k) z) : Fin 3 → ℂ) 0
              = z := rfl
          simp [hxz]
    simp only [map_sub, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, hev]
    rw [show (Fin.cons z (fun j : Fin 2 => iteratedDeriv (j : ℕ) (expPoly A c d k) z) :
        Fin 3 → ℂ) 2 = iteratedDeriv 1 (expPoly A c d k) z from rfl,
      show (Fin.cons z (fun j : Fin 2 => iteratedDeriv (j : ℕ) (expPoly A c d k) z) :
        Fin 3 → ℂ) 1 = iteratedDeriv 0 (expPoly A c d k) z from rfl, h0, h1]
    ring

/-! ## The nondegeneracy of the law's data -/

variable {A : ℕ → Polynomial ℂ} {c d : ℕ → ℂ}

theorem derivative_ne_zero_of_natDegree {j : ℕ} (hA : 1 ≤ (A j).natDegree) :
    (A j).derivative ≠ 0 := by
  intro h0
  rw [Polynomial.derivative_eq_zero] at h0
  omega

theorem polyV_ne_zero (d : ℕ → ℂ) (j : ℕ) : polyV d j ≠ 0 := by
  match j with
  | 0 => simp [polyV]
  | (k + 1) =>
      rw [polyV_succ]
      exact Polynomial.X_sub_C_ne_zero (d k)

theorem polyQ_ne_zero (hA : ∀ j, 1 ≤ (A j).natDegree) (j : ℕ) : polyQ A d j ≠ 0 :=
  mul_ne_zero (derivative_ne_zero_of_natDegree (hA j)) (polyV_ne_zero d j)

theorem one_le_natDegree_polyQ_succ (hA : ∀ j, 1 ≤ (A j).natDegree) (k : ℕ) :
    1 ≤ (polyQ A d (k + 1)).natDegree := by
  rw [polyQ, polyV_succ,
    Polynomial.natDegree_mul (derivative_ne_zero_of_natDegree (hA (k + 1)))
      (Polynomial.X_sub_C_ne_zero (d k)), Polynomial.natDegree_X_sub_C]
  omega

theorem derivative_polyQ_succ_ne_zero (hA : ∀ j, 1 ≤ (A j).natDegree) (k : ℕ) :
    (polyQ A d (k + 1)).derivative ≠ 0 := by
  intro h0
  rw [Polynomial.derivative_eq_zero] at h0
  have := one_le_natDegree_polyQ_succ (A := A) (d := d) hA k
  omega

/-! ## The capstone -/

/-- **A two-map cascade of first-order linear entire maps with polynomial coefficients has
differential order exactly two.** -/
theorem exactDifferentialOrder_expPolyCascade_two
    (hc : ∀ k, c k ≠ 0) (hA : ∀ k, 1 ≤ (A k).natDegree) :
    ExactDifferentialOrder (entireCascade (expPoly A c d) 2) 2 := by
  have hall : ∀ k, TranscendentalEntire (expPoly A c d k) :=
    fun k => transcendentalEntire_expPoly (hc k) (hA k)
  refine ⟨differentiallyAlgebraicOfOrder_entireCascade_of_transcendental' hall
    (fun k _ => differentiallyAlgebraicOfOrder_one_expPoly A c d k), ?_⟩
  intro m hm
  interval_cases m
  · exact not_differentiallyAlgebraicOfOrder_zero_entireCascade hall (by omega)
  · refine not_differentiallyAlgebraicOfOrder_of_model
      (δ := polyProdDerivation (polyQ A d) (polyV d))
      (Y := entireCascade (expPoly A c d)) (N := 2) (m := 1)
      (fun k => differentiable_expPolyCascade A c d k)
      (fun k z => law_expPolyCascade A c d k z)
      (fun Q hQ => exists_evalAt_ne_zero_of_transcendental hall hQ) ?_ rfl
    refine algebraicIndependent_two_map (polyV d) (Q := polyQ A d) (α := 1) (β := -(d 1))
      one_ne_zero ?_ (polyQ_ne_zero hA) (derivative_polyQ_succ_ne_zero hA 0)
    rw [polyV_succ, map_neg, map_one]
    ring

end GaloisForLFunctions.HTGeometry

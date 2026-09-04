import GaloisForLFunctions.HTGeometry.StrelitzLogJetInitialData

/-!
# Strelitz relation decomposition by value degree

This module canonically regroups a logarithmic-jet polynomial `Q(z, F, U, V)` by powers of the
function value `F`.  Its support records exactly the value degrees occurring in `Q`; every retained
coefficient polynomial in `(U, V)` is nonzero, and evaluation of the regrouped expression agrees
exactly with evaluation of `Q`.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Forget the exponent of the function-value variable, retaining the logarithmic-jet exponents. -/
def strelitzTailExponent (m : Fin 3 →₀ ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![m 1, m 2]

/-- A three-variable exponent is determined by its function-value exponent and its two tail
exponents. -/
theorem strelitzTailExponent_injective_of_value_eq
    {m n : Fin 3 →₀ ℕ} (h0 : m 0 = n 0)
    (htail : strelitzTailExponent m = strelitzTailExponent n) : m = n := by
  ext i
  fin_cases i
  · exact h0
  · have h := congrArg (fun e : Fin 2 →₀ ℕ => e 0) htail
    simpa [strelitzTailExponent] using h
  · have h := congrArg (fun e : Fin 2 →₀ ℕ => e 1) htail
    simpa [strelitzTailExponent] using h

/-- The finite set of powers of the function value occurring in a Strelitz relation. -/
def strelitzValueSupport
    (Q : MvPolynomial (Fin 3) (Polynomial ℂ)) : Finset ℕ :=
  Q.support.image (fun m => m 0)

/-- Coefficient of `F^d` after viewing a Strelitz relation as a polynomial in its function-value
variable, with polynomial coefficients in the two logarithmic-jet variables. -/
def strelitzValueCoeff
    (Q : MvPolynomial (Fin 3) (Polynomial ℂ)) (d : ℕ) :
    MvPolynomial (Fin 2) (Polynomial ℂ) :=
  ∑ m ∈ Q.support with m 0 = d,
    MvPolynomial.monomial (strelitzTailExponent m) (Q.coeff m)

/-- Every value degree recorded in the support has a nonzero logarithmic-jet coefficient. -/
theorem strelitzValueCoeff_ne_zero_of_mem
    {Q : MvPolynomial (Fin 3) (Polynomial ℂ)} {d : ℕ}
    (hd : d ∈ strelitzValueSupport Q) : strelitzValueCoeff Q d ≠ 0 := by
  classical
  obtain ⟨m, hm, hmd⟩ := Finset.mem_image.mp hd
  intro hzero
  have hcoeff := congrArg (MvPolynomial.coeff (strelitzTailExponent m)) hzero
  rw [strelitzValueCoeff, MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single m] at hcoeff
  · rw [MvPolynomial.coeff_monomial, if_pos rfl] at hcoeff
    exact (MvPolynomial.mem_support_iff.mp hm) hcoeff
  · intro n hn hne
    rw [MvPolynomial.coeff_monomial, if_neg]
    intro heq
    apply hne
    have hn0 : n 0 = d := (Finset.mem_filter.mp hn).2
    exact strelitzTailExponent_injective_of_value_eq
      (m := n) (n := m) (hn0.trans hmd.symm) heq
  · intro hnot
    exfalso
    exact hnot (Finset.mem_filter.mpr ⟨hm, hmd⟩)

/-- Evaluation formula for one coefficient in the function-value decomposition. -/
theorem eval₂_strelitzValueCoeff
    (Q : MvPolynomial (Fin 3) (Polynomial ℂ)) (d : ℕ)
    (z U V : ℂ) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![U, V]
        (strelitzValueCoeff Q d) =
      ∑ m ∈ Q.support with m 0 = d,
        (Q.coeff m).eval z * U ^ m 1 * V ^ m 2 := by
  classical
  rw [strelitzValueCoeff, MvPolynomial.eval₂_sum]
  refine Finset.sum_congr rfl ?_
  intro m hm
  rw [MvPolynomial.eval₂_monomial]
  change Polynomial.eval z (Q.coeff m) * _ = _
  have hprod :
      (strelitzTailExponent m).prod
          (fun i e => (![U, V] : Fin 2 → ℂ) i ^ e) = U ^ m 1 * V ^ m 2 := by
    rw [Finsupp.prod_fintype _ _ (by intro i; simp), Fin.prod_univ_two]
    rfl
  rw [hprod]
  ring

/-- Exact recombination formula after evaluating the coefficient variable and all three jet
variables. -/
theorem eval₂_strelitzValueSupport
    (Q : MvPolynomial (Fin 3) (Polynomial ℂ)) (z F U V : ℂ) :
    ∑ d ∈ strelitzValueSupport Q,
        MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![U, V]
          (strelitzValueCoeff Q d) * F ^ d =
      MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![F, U, V] Q := by
  classical
  rw [MvPolynomial.eval₂_eq]
  calc
    ∑ d ∈ strelitzValueSupport Q,
        MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![U, V]
          (strelitzValueCoeff Q d) * F ^ d =
        ∑ d ∈ strelitzValueSupport Q,
          ∑ m ∈ Q.support with m 0 = d,
            (Q.coeff m).eval z * F ^ m 0 * U ^ m 1 * V ^ m 2 := by
      refine Finset.sum_congr rfl ?_
      intro d hd
      rw [eval₂_strelitzValueCoeff, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro m hm
      rw [(Finset.mem_filter.mp hm).2]
      ring
    _ = ∑ m ∈ Q.support,
        (Q.coeff m).eval z * F ^ m 0 * U ^ m 1 * V ^ m 2 := by
      exact Finset.sum_fiberwise_of_maps_to
        (s := Q.support) (t := strelitzValueSupport Q)
        (g := fun m => m 0)
        (fun m hm => Finset.mem_image.mpr ⟨m, hm, rfl⟩)
        (fun m => (Q.coeff m).eval z * F ^ m 0 * U ^ m 1 * V ^ m 2)
    _ = ∑ m ∈ Q.support,
        (Polynomial.evalRingHom z) (Q.coeff m) *
          m.prod (fun i e => (![F, U, V] : Fin 3 → ℂ) i ^ e) := by
      refine Finset.sum_congr rfl ?_
      intro m hm
      have hprod : m.prod (fun i e => (![F, U, V] : Fin 3 → ℂ) i ^ e) =
          F ^ m 0 * U ^ m 1 * V ^ m 2 := by
        rw [Finsupp.prod_fintype _ _ (by intro i; simp), Fin.prod_univ_three]
        rfl
      rw [hprod]
      change (Q.coeff m).eval z * F ^ m 0 * U ^ m 1 * V ^ m 2 =
        (Q.coeff m).eval z * (F ^ m 0 * U ^ m 1 * V ^ m 2)
      ring

/-- A nonzero Strelitz relation has at least one nonzero coefficient in its function-value
decomposition. -/
theorem exists_nonzero_strelitzValueCoeff
    {Q : MvPolynomial (Fin 3) (Polynomial ℂ)} (hQ : Q ≠ 0) :
    ∃ d ∈ strelitzValueSupport Q, strelitzValueCoeff Q d ≠ 0 := by
  classical
  have hnonempty : Q.support.Nonempty := by
    by_contra hnone
    apply hQ
    apply MvPolynomial.ext
    intro m
    simp only [MvPolynomial.coeff_zero]
    by_contra hcm
    exact hnone ⟨m, MvPolynomial.mem_support_iff.mpr hcm⟩
  obtain ⟨m, hm⟩ := hnonempty
  exact ⟨m 0, Finset.mem_image.mpr ⟨m, hm, rfl⟩,
    strelitzValueCoeff_ne_zero_of_mem (Finset.mem_image.mpr ⟨m, hm, rfl⟩)⟩

end

end GaloisForLFunctions.HTGeometry

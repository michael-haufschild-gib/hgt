import GaloisForLFunctions.HTGeometry.PolynomialGrowthBound

/-!
# One-variable multivariate polynomials

A polynomial in a single indexed variable is a univariate polynomial.  The identification is needed
whenever a statement quantified over `MvPolynomial (Fin 1) ℂ` — a coefficient of a state relation at
the first edge of a cascade, where the only state is the coordinate — has to be fed to the univariate
growth estimates.

Both directions of the correspondence are recorded: evaluation agrees, and nonzero polynomials
correspond to nonzero polynomials.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

/-- A one-variable multivariate polynomial as a univariate polynomial. -/
noncomputable def toPoly (A : MvPolynomial (Fin 1) ℂ) : Polynomial ℂ :=
  Polynomial.map
    (MvPolynomial.isEmptyRingEquiv ℂ (Fin 0) : MvPolynomial (Fin 0) ℂ →+* ℂ)
    (MvPolynomial.finSuccEquiv ℂ 0 A)

/-- On the empty variable set, evaluation is the canonical isomorphism. -/
theorem eval_empty_eq (s : Fin 0 → ℂ) :
    (MvPolynomial.eval s : MvPolynomial (Fin 0) ℂ →+* ℂ)
      = (MvPolynomial.isEmptyRingEquiv ℂ (Fin 0) : MvPolynomial (Fin 0) ℂ →+* ℂ) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    rw [MvPolynomial.eval_C]
    exact (MvPolynomial.coeff_zero_C c).symm
  · intro i
    exact i.elim0

/-- **Evaluation agrees.** -/
theorem eval_toPoly (A : MvPolynomial (Fin 1) ℂ) (z : ℂ) :
    (toPoly A).eval z = MvPolynomial.eval (fun _ : Fin 1 => z) A := by
  have hcons : (Fin.cons z (fun i : Fin 0 => i.elim0) : Fin 1 → ℂ) = fun _ : Fin 1 => z := by
    funext j
    refine Fin.cases ?_ (fun i => i.elim0) j
    rfl
  have hev := MvPolynomial.eval_eq_eval_mv_eval' (R := ℂ) (n := 0)
    (fun i : Fin 0 => i.elim0) z A
  rw [hcons] at hev
  rw [toPoly, ← eval_empty_eq (fun i : Fin 0 => i.elim0)]
  exact hev.symm

/-- **Nonzero polynomials correspond.** -/
theorem toPoly_ne_zero {A : MvPolynomial (Fin 1) ℂ} (hA : A ≠ 0) : toPoly A ≠ 0 := by
  intro hzero
  apply hA
  have hmap : Polynomial.map
      (MvPolynomial.isEmptyRingEquiv ℂ (Fin 0) : MvPolynomial (Fin 0) ℂ →+* ℂ)
      (MvPolynomial.finSuccEquiv ℂ 0 A) = 0 := hzero
  have hinj : Function.Injective
      (Polynomial.map
        (MvPolynomial.isEmptyRingEquiv ℂ (Fin 0) : MvPolynomial (Fin 0) ℂ →+* ℂ)) :=
    Polynomial.map_injective _ (MvPolynomial.isEmptyRingEquiv ℂ (Fin 0)).injective
  have hfs : MvPolynomial.finSuccEquiv ℂ 0 A = 0 := hinj (by rw [hmap, Polynomial.map_zero])
  exact (MvPolynomial.finSuccEquiv ℂ 0).injective (by rw [hfs, map_zero])

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.RittTransportPolynomial

/-!
# No polynomial solution of a transport equation with a low-degree inhomogeneity

The polynomial form of the transport equation,

`A ∘ R · (R′)^J = β · A + C`,

is rigid in degrees.  The left side has degree `deg A · deg R + J·(deg R − 1)`; the right has degree
at most `max (deg A) (deg C)`.  For `deg R ≥ 2` the left exceeds `deg A` as soon as `deg A ≥ 1`, so
the only way the identity can hold is with the inhomogeneity carrying the whole left-hand degree.
An inhomogeneity of degree strictly below `deg R + J·(deg R − 1)` — the smallest value the left side
can take with `deg A ≥ 1` — therefore admits no non-constant polynomial solution, and constant
solutions determine `C` outright.

Two checkable hypotheses on the map and its inhomogeneity thus rule out every polynomial solution:
no constant works, and the inhomogeneity is of low degree.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- **No polynomial solution.** -/
theorem no_polynomial_solution_of_natDegree_lt {R : K[X]}
    (hRdeg : 2 ≤ R.natDegree) {J : ℕ} {β : K} (hβ : β ≠ 0) {Cp : K[X]}
    (hconst : ∀ α : K, α ≠ 0 →
      Cp ≠ Polynomial.C α * (derivative R) ^ J - Polynomial.C β * Polynomial.C α)
    (hdeg : Cp.natDegree < R.natDegree + J * (R.natDegree - 1))
    {A : K[X]} (hA : A ≠ 0)
    (heq : A.comp R * (derivative R) ^ J = Polynomial.C β * A + Cp) : False := by
  classical
  have hR0 : R ≠ 0 := fun h => by rw [h, natDegree_zero] at hRdeg; omega
  have hdR : (derivative R).natDegree = R.natDegree - 1 := natDegree_derivative R
  have hRd0 : derivative R ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdR
    omega
  have hcomp0 : A.comp R ≠ 0 := by
    intro h
    have hlc := Polynomial.leadingCoeff_comp (p := A) (q := R) (by omega)
    rw [h, leadingCoeff_zero] at hlc
    exact (mul_ne_zero (leadingCoeff_ne_zero.mpr hA)
      (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hR0))) hlc.symm
  rcases Nat.eq_zero_or_pos A.natDegree with hA0 | hA1
  · -- constant numerator: the inhomogeneity is determined
    obtain ⟨α, hα⟩ : ∃ α : K, A = Polynomial.C α := ⟨A.coeff 0, eq_C_of_natDegree_eq_zero hA0⟩
    have hα0 : α ≠ 0 := by
      intro h
      rw [h, map_zero] at hα
      exact hA hα
    refine hconst α hα0 ?_
    rw [hα, Polynomial.C_comp] at heq
    linear_combination -heq
  · -- nonconstant numerator: the degrees cannot match
    have hlhs : (A.comp R * (derivative R) ^ J).natDegree
        = A.natDegree * R.natDegree + J * (R.natDegree - 1) := by
      rw [natDegree_mul hcomp0 (pow_ne_zero _ hRd0), natDegree_comp, natDegree_pow, hdR]
    have hrhs : (Polynomial.C β * A + Cp).natDegree ≤ max A.natDegree Cp.natDegree := by
      refine le_trans (natDegree_add_le _ _) ?_
      rw [natDegree_C_mul hβ]
    have hkey := congrArg natDegree heq
    rw [hlhs] at hkey
    have hbig1 : A.natDegree < A.natDegree * R.natDegree + J * (R.natDegree - 1) := by
      nlinarith [hA1, hRdeg]
    have hbig2 : Cp.natDegree < A.natDegree * R.natDegree + J * (R.natDegree - 1) := by
      have : R.natDegree + J * (R.natDegree - 1)
          ≤ A.natDegree * R.natDegree + J * (R.natDegree - 1) := by
        have : R.natDegree ≤ A.natDegree * R.natDegree := Nat.le_mul_of_pos_left _ hA1
        omega
      omega
    omega



/-- **The master criterion.**  A transport equation with a polynomial inhomogeneity of low degree,
no constant solution, and no pole-carrying solution has no nonzero solution at all. -/
theorem no_transport_solution_of_criteria [IsAlgClosed K] {R : K[X]}
    (hRdeg : 2 ≤ R.natDegree) {J : ℕ} {β : K} (hβ : β ≠ 0) {Cp : K[X]}
    {hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c}
    (hconst : ∀ α : K, α ≠ 0 →
      Cp ≠ Polynomial.C α * (derivative R) ^ J - Polynomial.C β * Polynomial.C α)
    (hdeg : Cp.natDegree < R.natDegree + J * (R.natDegree - 1))
    {a : RatFunc K} (ha : a ≠ 0)
    (hpole : ∀ p : K, 0 ≤ ratOrder a p)
    (heq : IsAffineTransport R hR (J : ℤ) (RatFunc.C β)
      (algebraMap K[X] (RatFunc K) Cp) a) : False := by
  obtain ⟨A, hA, hAeq⟩ := exists_polynomial_of_ratOrder_nonneg ha hpole
  rw [hAeq] at heq
  exact no_polynomial_solution_of_natDegree_lt hRdeg hβ hconst hdeg hA
    (polynomial_identity_of_isAffineTransport heq)

end GaloisForLFunctions.HTGeometry

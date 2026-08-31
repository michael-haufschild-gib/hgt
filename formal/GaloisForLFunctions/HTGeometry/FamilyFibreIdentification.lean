import GaloisForLFunctions.HTGeometry.FamilyEvaluation

/-!
# The fibre of a graded piece is the graded piece of the fibre

```text
isXHomog_of_mul_X_sub_C     dividing by a linear factor in the extra variable keeps the x-degree
mem_ker_evalDegreeHom_iff   ** the kernel of evaluation is the multiples of that factor **
evalDegreeHom_surjective    ** and evaluation is onto **
```

The division statement is a downward induction on the coefficients: the recursion
`G_j = F_{j+1} + lam · G_{j+1}` expresses each coefficient of the quotient in terms of a coefficient
of the product and the next one, and above the degree they all vanish.

Together the two say that the degree-`e` part of the family, modulo the ideal of a point of the base
line, *is* the degree-`e` part of the fibre there — which is the identification a fibre-dimension
argument needs before it can compare the two ends of a degeneration.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {K : Type u} [Field K]

theorem coeff_mul_X_sub_C {N : ℕ} (G : Polynomial (MvPolynomial (Fin N) K)) (c : K) (j : ℕ) :
    ((Polynomial.X - Polynomial.C (MvPolynomial.C c)) * G).coeff (j + 1)
      = G.coeff j - MvPolynomial.C c * G.coeff (j + 1) := by
  rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]

/-- **Dividing by a linear factor in the extra variable keeps the `x`-degree.** -/
theorem isXHomog_of_mul_X_sub_C {N e : ℕ} {G : Polynomial (MvPolynomial (Fin N) K)} {lam : K}
    (hF : IsXHomog e ((Polynomial.X - Polynomial.C (MvPolynomial.C lam)) * G)) :
    IsXHomog e G := by
  have key : ∀ k j : ℕ, G.natDegree + 1 ≤ j + k → (G.coeff j).IsHomogeneous e := by
    intro k
    induction k with
    | zero =>
      intro j hj
      have hzero : G.coeff j = 0 := by
        refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
        omega
      rw [hzero]
      exact MvPolynomial.isHomogeneous_zero _ _ _
    | succ k ih =>
      intro j hj
      have hrec : G.coeff j
          = ((Polynomial.X - Polynomial.C (MvPolynomial.C lam)) * G).coeff (j + 1)
            + MvPolynomial.C lam * G.coeff (j + 1) := by
        rw [coeff_mul_X_sub_C]
        ring
      rw [hrec]
      refine (hF (j + 1)).add ?_
      have hC : (MvPolynomial.C lam : MvPolynomial (Fin N) K).IsHomogeneous 0 :=
        MvPolynomial.isHomogeneous_C _ _
      have hmul := hC.mul (ih (j + 1) (by omega))
      rwa [zero_add] at hmul
  intro j
  exact key (G.natDegree + 1) j (by omega)

/-- **The kernel of evaluation is the multiples of the linear factor.** -/
theorem mem_ker_evalDegreeHom_iff {N e : ℕ} {lam : K}
    {F : Submodule.restrictScalars K (xDegreeSubmodule K (Fin N) e)} :
    F ∈ LinearMap.ker (evalDegreeHom K N e lam) ↔
      ∃ G : Polynomial (MvPolynomial (Fin N) K), IsXHomog e G ∧
        (F : Polynomial (MvPolynomial (Fin N) K))
          = (Polynomial.X - Polynomial.C (MvPolynomial.C lam)) * G := by
  constructor
  · intro hF
    have hroot : (F : Polynomial (MvPolynomial (Fin N) K)).IsRoot (MvPolynomial.C lam) := by
      have : Polynomial.eval (MvPolynomial.C lam) (F : Polynomial (MvPolynomial (Fin N) K)) = 0 := by
        have h0 : evalDegreeHom K N e lam F = 0 := hF
        exact congrArg Subtype.val h0
      exact this
    obtain ⟨G, hG⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
    refine ⟨G, ?_, hG⟩
    refine isXHomog_of_mul_X_sub_C (lam := lam) ?_
    rw [← hG]
    exact F.2
  · rintro ⟨G, hG, hFG⟩
    have hzero : Polynomial.eval (MvPolynomial.C lam)
        (F : Polynomial (MvPolynomial (Fin N) K)) = 0 := by
      rw [hFG, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        sub_self, zero_mul]
    exact Subtype.ext hzero

/-- **Evaluation is surjective onto the graded piece.** -/
theorem evalDegreeHom_surjective (K : Type u) [Field K] (N e : ℕ) (lam : K) :
    Function.Surjective (evalDegreeHom K N e lam) := by
  intro p
  refine ⟨⟨Polynomial.C (p : MvPolynomial (Fin N) K), ?_⟩, ?_⟩
  · intro j
    rw [Polynomial.coeff_C]
    by_cases hj : j = 0
    · rw [if_pos hj]
      exact p.2
    · rw [if_neg hj]
      exact MvPolynomial.isHomogeneous_zero _ _ _
  · refine Subtype.ext ?_
    show Polynomial.eval (MvPolynomial.C lam)
      (Polynomial.C (p : MvPolynomial (Fin N) K)) = (p : MvPolynomial (Fin N) K)
    rw [Polynomial.eval_C]

end GaloisForLFunctions.HTGeometry

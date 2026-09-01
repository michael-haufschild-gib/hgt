import GaloisForLFunctions.HTGeometry.FamilyGradedFibre
import GaloisForLFunctions.HTGeometry.FibreNoTorsionBound

/-!
# Semicontinuity of the fibre Hilbert function of a family

```text
finrank_quotDegreePart_fibre_le  ** a point at which the family is saturated has, in every degree,
                                    fibre dimension at most that of any other point **
```

This is `finrank_quotDegreePart_fibre_eq` with the hypothesis at one point only.  Saturation at the
generic point is what the family supplies; at the special point — the one carrying the initial ideal
— the family is not saturated, and the inequality runs towards it.

Degreewise this is the one-sided fibre bound `finrank_fibre_le_of_smul_injective` applied to the
graded piece, which is a finite module over the base line because a graded piece is a finite free
module on the monomials of that degree.
-/

namespace GaloisForLFunctions.HTGeometry
open MvPolynomial Module

universe u
variable {K : Type u} [Field K] {N : ℕ}

/-- **Saturation at a point bounds its fibre Hilbert function by every other one.** -/
theorem finrank_quotDegreePart_fibre_le (A : Ideal (Polynomial (MvPolynomial (Fin N) K)))
    (hA : IsXGradedIdeal A) {lam : K}
    (hlam : ∀ F : Polynomial (MvPolynomial (Fin N) K),
      (Polynomial.X - Polynomial.C (MvPolynomial.C lam)) * F ∈ A → F ∈ A) (mu : K) (e : ℕ) :
    finrank K (quotDegreePart
        ((Ideal.map (famEval (MvPolynomial.C lam)) A).restrictScalars K) e)
      ≤ finrank K (quotDegreePart
        ((Ideal.map (famEval (MvPolynomial.C mu)) A).restrictScalars K) e) := by
  classical
  have htors : ∀ v : famCoeff K N e ⧸ famCoeffPart A e,
      (Polynomial.X - Polynomial.C lam : Polynomial K) • v = 0 → v = 0 := by
    intro v hv
    obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective (famCoeffPart A e) v
    have hmem : (Polynomial.X - Polynomial.C lam : Polynomial K) • c ∈ famCoeffPart A e := by
      have h0 : Submodule.Quotient.mk
          ((Polynomial.X - Polynomial.C lam : Polynomial K) • c) = 0 := hv
      rwa [Submodule.Quotient.mk_eq_zero] at h0
    rw [mem_famCoeffPart, famAssemble_smul] at hmem
    have hmap : Polynomial.map (MvPolynomial.C : K →+* MvPolynomial (Fin N) K)
        (Polynomial.X - Polynomial.C lam : Polynomial K)
        = Polynomial.X - Polynomial.C (MvPolynomial.C lam) := by
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rw [hmap] at hmem
    have := hlam _ hmem
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact mem_famCoeffPart.mpr this
  rw [finrank_quotDegreePart_eq_fibre A hA e lam, finrank_quotDegreePart_eq_fibre A hA e mu]
  exact finrank_fibre_le_of_smul_injective htors mu

end GaloisForLFunctions.HTGeometry

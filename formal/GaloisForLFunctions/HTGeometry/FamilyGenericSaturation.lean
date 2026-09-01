import GaloisForLFunctions.HTGeometry.FamilyUniformTorsion
import GaloisForLFunctions.HTGeometry.FamilyGradedFibreBound
import GaloisForLFunctions.HTGeometry.GenericPointFamily

/-!
# One point of the base line saturating finitely many families at once

```text
exists_generic_saturation_point   ** a single nonzero point at which finitely many families are all
                                     saturated **
exists_generic_fibre_le           ** hence a single point whose fibre Hilbert function is, in every
                                     degree and for every family in the list, at most the one at
                                     zero **
```

Each family contributes one nonzero annihilator of its torsion by
`exists_uniform_torsion_annihilator`; over an infinite field a point avoiding all their roots and the
origin exists, and there the families are saturated by `saturated_of_eval_ne_zero`.

The uniformity in the *degree* is what matters: the annihilator does not depend on the graded piece,
so one point works for the whole Hilbert function.  The uniformity in the *family* is what lets a
whole regular sequence be deformed by a single rescaling, one stage of the sequence at a time.
-/

namespace GaloisForLFunctions.HTGeometry
open MvPolynomial Module

universe u
variable {K : Type u} [Field K] {N : ℕ}

/-- **One nonzero point saturating finitely many families at once.** -/
theorem exists_generic_saturation_point [Infinite K] {n : ℕ}
    (A : Fin n → Ideal (Polynomial (MvPolynomial (Fin N) K))) :
    ∃ lam : K, lam ≠ 0 ∧ ∀ i : Fin n, ∀ F : Polynomial (MvPolynomial (Fin N) K),
      (Polynomial.X - Polynomial.C (MvPolynomial.C lam)) * F ∈ A i → F ∈ A i := by
  classical
  choose q hq0 hq using fun i => exists_uniform_torsion_annihilator (A i)
  obtain ⟨lam, hlam0, hlamS⟩ :=
    exists_nonzero_notMem_biUnion (K := K) (fun i => (q i).roots.toFinset)
  refine ⟨lam, hlam0, fun i => ?_⟩
  refine saturated_of_eval_ne_zero (hq i) ?_
  intro hroot
  refine hlamS i ?_
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (hq0 i)]
  exact hroot

/-- **And there its fibre Hilbert function is at most the one at zero.** -/
theorem exists_generic_fibre_le [Infinite K] {n : ℕ}
    (A : Fin n → Ideal (Polynomial (MvPolynomial (Fin N) K)))
    (hA : ∀ i, IsXGradedIdeal (A i)) :
    ∃ lam : K, lam ≠ 0 ∧ ∀ (i : Fin n) (e : ℕ),
      finrank K (quotDegreePart
          ((Ideal.map (famEval (MvPolynomial.C lam)) (A i)).restrictScalars K) e)
        ≤ finrank K (quotDegreePart
          ((Ideal.map (famEval (MvPolynomial.C (0 : K))) (A i)).restrictScalars K) e) := by
  obtain ⟨lam, hlam0, hsat⟩ := exists_generic_saturation_point A
  exact ⟨lam, hlam0, fun i e => finrank_quotDegreePart_fibre_le (A i) (hA i) (hsat i) 0 e⟩

end GaloisForLFunctions.HTGeometry

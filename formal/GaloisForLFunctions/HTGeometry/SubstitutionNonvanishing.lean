import GaloisForLFunctions.HTGeometry.GaugeReductionToMultiplicative
import GaloisForLFunctions.HTGeometry.ExpandedMatrixDistinctNodes

/-!
# Substitutions with surjective point maps preserve nonvanishing

A polynomial substitution acts on points by a map in the opposite direction.  If that point map hits
every point where some fixed nonzero polynomial does not vanish, then the substitution cannot kill a
nonzero polynomial: a witness of nonvanishing can be pulled back through the point map.

This replaces a fraction-field argument for triangular substitutions.  The diagonal of the
substitution supplies the polynomial whose nonvanishing locus the point map covers, because the
triangular system is solvable exactly there.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Nonvanishing is preserved by a substitution whose point map covers a nonvanishing locus.** -/
theorem subst_ne_zero_of_pointMap_surjective {σ : Type*}
    (S : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ) (T : (σ → ℂ) → (σ → ℂ))
    (hST : ∀ (P : MvPolynomial σ ℂ) (v : σ → ℂ),
      MvPolynomial.eval v (S P) = MvPolynomial.eval (T v) P)
    (g : MvPolynomial σ ℂ) (hg : g ≠ 0)
    (hsurj : ∀ w : σ → ℂ, MvPolynomial.eval w g ≠ 0 → ∃ v, T v = w)
    {P : MvPolynomial σ ℂ} (hP : P ≠ 0) : S P ≠ 0 := by
  intro hzero
  obtain ⟨w, hw⟩ := exists_eval_ne_zero (mul_ne_zero hP hg)
  rw [map_mul] at hw
  obtain ⟨hwP, hwg⟩ := mul_ne_zero_iff.1 hw
  obtain ⟨v, hv⟩ := hsurj w hwg
  have : MvPolynomial.eval v (S P) = MvPolynomial.eval w P := by
    rw [hST P v, hv]
  rw [hzero, map_zero] at this
  exact hwP this.symm

/-- **The injective form.**  Such a substitution is injective on polynomials. -/
theorem subst_injective_of_pointMap_surjective {σ : Type*}
    (S : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ) (T : (σ → ℂ) → (σ → ℂ))
    (hST : ∀ (P : MvPolynomial σ ℂ) (v : σ → ℂ),
      MvPolynomial.eval v (S P) = MvPolynomial.eval (T v) P)
    (g : MvPolynomial σ ℂ) (hg : g ≠ 0)
    (hsurj : ∀ w : σ → ℂ, MvPolynomial.eval w g ≠ 0 → ∃ v, T v = w) :
    Function.Injective S := by
  intro P Q hPQ
  by_contra hne
  have hsub : P - Q ≠ 0 := sub_ne_zero.2 hne
  have hzero : S (P - Q) = 0 := by
    rw [map_sub, hPQ, sub_self]
  exact subst_ne_zero_of_pointMap_surjective S T hST g hg hsurj hsub hzero

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.RittScalingCoefficientEigen

/-!
# A homogeneous eigenvector over an affinely moved generator is already in the base

Let the shift move a transcendental generator affinely, `σ t = a·t + b`, and let `W` in the simple
extension satisfy the purely homogeneous relation `σ W = c·W`.  Then `W⁻¹` satisfies the same kind of
relation with the inverse scalar, so the denominator identity applies to *both* `W` and `W⁻¹`.

Each application says: a coprime representation whose denominator has positive degree hands back an
affine relation

`φ(w) + N·b = a·w`,   `N ≥ 1`,

in the coefficient field, with eigenvalue exactly the generator's multiplier.  If no such relation
holds, both denominators are constant, so `W` and `W⁻¹` are both polynomials in `t`; their product
is `1`, hence both are units of the polynomial ring, hence constants.

So a homogeneous eigenvector is either already in the coefficient field, or it produces the affine
connection of the coordinate — there is no room in between.  This is the rigidity that removes the
numerator–denominator degree freedom from the jet-tower descent.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {E L : Type*} [Field E] [CharZero E] [Field L] [Algebra E L]

/-- **Homogeneous rigidity over an affinely moved generator.**  A homogeneous eigenvector is either
in the coefficient field or produces the affine connection of the coordinate. -/
theorem mem_range_or_affine_connection_of_homogeneous_eigen (σ : L →+* L) (φ : E →+* E)
    (hcomp : ∀ x : E, σ (algebraMap E L x) = algebraMap E L (φ x))
    {t : L} (ht : Transcendental E t) {a b c : E} (ha : a ≠ 0) (hc : c ≠ 0)
    (hσt : σ t = algebraMap E L a * t + algebraMap E L b)
    {W : L} (hW0 : W ≠ 0) (hW : W ∈ IntermediateField.adjoin E ({t} : Set L))
    (hrel : σ W = algebraMap E L c * W) :
    (∃ x : E, W = algebraMap E L x) ∨ algebraMap E L b = 0 ∨
      ∃ (w : E) (N : ℕ), w ≠ 0 ∧ 1 ≤ N ∧ φ w + (N : E) * b = a * w := by
  classical
  by_cases hb : b = 0
  · exact Or.inr (Or.inl (by rw [hb, map_zero]))
  by_cases hconn : ∃ (w : E) (N : ℕ), w ≠ 0 ∧ 1 ≤ N ∧ φ w + (N : E) * b = a * w
  · exact Or.inr (Or.inr hconn)
  refine Or.inl ?_
  push Not at hconn
  have hinj : Function.Injective (aeval t : E[X] →ₐ[E] L) :=
    transcendental_iff_injective.mp ht
  -- the inverse satisfies the same shape of relation
  have hWinv0 : W⁻¹ ≠ 0 := inv_ne_zero hW0
  have hWinvmem : W⁻¹ ∈ IntermediateField.adjoin E ({t} : Set L) :=
    inv_mem hW
  have hcL : algebraMap E L c ≠ 0 := (map_ne_zero_iff _ (algebraMap E L).injective).mpr hc
  have hrelinv : σ W⁻¹ = algebraMap E L c⁻¹ * W⁻¹ := by
    have hσW : σ W ≠ 0 := by
      rw [hrel]
      exact mul_ne_zero hcL hW0
    refine mul_left_cancel₀ hσW ?_
    rw [← map_mul, mul_inv_cancel₀ hW0, map_one, hrel, map_inv₀]
    field_simp
  -- both numerators are polynomials: a positive-degree denominator would give the connection
  have hpoly : ∀ (V : L), V ≠ 0 → V ∈ IntermediateField.adjoin E ({t} : Set L) →
      ∀ d : E, d ≠ 0 → σ V = algebraMap E L d * V → ∃ A : E[X], V = aeval t A := by
    intro V hV0 hVmem d hd hVrel
    obtain ⟨A, B, hB, hcop, hA0, hVeq, -, hden⟩ :=
      exists_denominator_relation_of_affine_mem_adjoin σ φ hcomp ht ha hd hσt hV0 hVmem
        (α := 0) (β := 0) (by rw [hVrel]; simp)
    have hB1 : B.natDegree = 0 := by
      by_contra hne
      have hrel' := hden (by omega)
      have hw0 : B.coeff (B.natDegree - 1) ≠ 0 := by
        intro h0
        rw [h0, map_zero, zero_add, mul_zero] at hrel'
        exact hb (by
          have hN : ((B.natDegree : E)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          exact (mul_eq_zero.mp hrel').resolve_left hN)
      exact hconn (B.coeff (B.natDegree - 1)) B.natDegree hw0 (by omega) hrel'
    have hBone : B = 1 := eq_one_of_monic_natDegree_zero hB hB1
    refine ⟨A, ?_⟩
    rw [hVeq, hBone, map_one, div_one]
  obtain ⟨A, hA⟩ := hpoly W hW0 hW c hc hrel
  obtain ⟨A', hA'⟩ := hpoly W⁻¹ hWinv0 hWinvmem c⁻¹ (inv_ne_zero hc) hrelinv
  have hprod : (aeval t : E[X] →ₐ[E] L) (A * A') = (aeval t : E[X] →ₐ[E] L) 1 := by
    rw [map_mul, map_one, ← hA, ← hA', mul_inv_cancel₀ hW0]
  have hAA' : A * A' = 1 := hinj hprod
  obtain ⟨x, _, hx⟩ := Polynomial.isUnit_iff.mp (IsUnit.of_mul_eq_one A' hAA')
  refine ⟨x, ?_⟩
  rw [hA, ← hx, aeval_C]

end GaloisForLFunctions.HTGeometry

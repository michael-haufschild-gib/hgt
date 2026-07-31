import GaloisForLFunctions.RHTower.HedenmalmCenterMixedCorrelationAngle
import GaloisForLFunctions.RHTower.HedenmalmCenterMixedOrientationBoundary
import GaloisForLFunctions.RHTower.ThetaCuspWignerGammaXiTransverseEnergyUniversalityLaw

/-!
# Three-positive source orientation for the theta-cusp Wigner current

The center-mixed theta density is not merely pointwise positive.  At every
physical aperture, its Bochner Gram matrix is positive semidefinite on every
set of at most three real nodes.  The statement is invariant under arbitrary
ordering of the nodes.

Consequently a negative Fourier-sign certificate, if one exists, has
irreducible support size at least four.  This is an unconditional finite-rank
positive-definiteness theorem for the same source current whose full
positive-definiteness is equivalent to RH.
-/

open Complex Matrix

namespace RHTower

noncomputable section

/-- Translation-invariant three-node Gram matrix of the center-mixed theta
density. -/
def thetaCuspCenterMixedGramThree
    (a : ℝ) (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => thetaCuspCenterMixedDensity a |x i - x j|

/-- Ordered nodes reduce exactly to the adjacent-gap matrix used by the
source correlation-angle theorem. -/
theorem thetaCuspCenterMixedGramThree_posSemidef_of_ordered
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (x : Fin 3 → ℝ) (h01 : x 0 ≤ x 1) (h12 : x 1 ≤ x 2) :
    Matrix.PosSemidef (thetaCuspCenterMixedGramThree a x) := by
  let p : ℝ := x 1 - x 0
  let q : ℝ := x 2 - x 1
  have hp : 0 ≤ p := sub_nonneg.mpr h01
  have hq : 0 ≤ q := sub_nonneg.mpr h12
  have hsource :=
    thetaCuspCenterMixedThreePointMatrix_posSemidef ha0 ha hp hq
  have h02 : x 0 ≤ x 2 := h01.trans h12
  have hmatrix :
      thetaCuspCenterMixedGramThree a x =
        thetaCuspCenterMixedThreePointMatrix a p q := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [thetaCuspCenterMixedGramThree,
        thetaCuspCenterMixedThreePointMatrix,
        HilbertMetric.threePointCorrelationMatrix, p, q,
        abs_of_nonneg, abs_of_nonpos, sub_nonneg.mpr h01,
        sub_nonpos.mpr h01, sub_nonneg.mpr h12,
        sub_nonpos.mpr h12, sub_nonneg.mpr h02,
        sub_nonpos.mpr h02]
  rw [hmatrix]
  exact hsource

/-- Positive semidefiniteness after any ordering equivalence implies positive
semidefiniteness in the original labels. -/
theorem thetaCuspCenterMixedGramThree_posSemidef_of_permuted_order
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (x : Fin 3 → ℝ) (e : Fin 3 ≃ Fin 3)
    (h01 : x (e 0) ≤ x (e 1)) (h12 : x (e 1) ≤ x (e 2)) :
    Matrix.PosSemidef (thetaCuspCenterMixedGramThree a x) := by
  have hordered :=
    thetaCuspCenterMixedGramThree_posSemidef_of_ordered
      ha0 ha (fun i => x (e i)) h01 h12
  apply (Matrix.posSemidef_submatrix_equiv e).mp
  change Matrix.PosSemidef
    (thetaCuspCenterMixedGramThree a (fun i => x (e i)))
  exact hordered

/-- **Permutation-invariant order-three positivity.**  For every physical
aperture and every three real nodes, the center-mixed theta Gram matrix is
positive semidefinite. -/
theorem thetaCuspCenterMixedGramThree_posSemidef
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (x : Fin 3 → ℝ) :
    Matrix.PosSemidef (thetaCuspCenterMixedGramThree a x) := by
  rcases le_total (x 0) (x 1) with h01 | h10
  · rcases le_total (x 1) (x 2) with h12 | h21
    · exact thetaCuspCenterMixedGramThree_posSemidef_of_ordered
        ha0 ha x h01 h12
    · rcases le_total (x 0) (x 2) with h02 | h20
      · let e : Fin 3 ≃ Fin 3 := Equiv.swap 1 2
        apply thetaCuspCenterMixedGramThree_posSemidef_of_permuted_order
          ha0 ha x e
        · exact h02
        · exact h21
      · let e : Fin 3 ≃ Fin 3 :=
          (Equiv.swap 1 2).trans (Equiv.swap 0 2)
        apply thetaCuspCenterMixedGramThree_posSemidef_of_permuted_order
          ha0 ha x e
        · exact h20
        · exact h01
  · rcases le_total (x 0) (x 2) with h02 | h20
    · let e : Fin 3 ≃ Fin 3 := Equiv.swap 0 1
      apply thetaCuspCenterMixedGramThree_posSemidef_of_permuted_order
        ha0 ha x e
      · exact h10
      · exact h02
    · rcases le_total (x 1) (x 2) with h12 | h21
      · let e : Fin 3 ≃ Fin 3 :=
          (Equiv.swap 1 2).trans (Equiv.swap 0 1)
        apply thetaCuspCenterMixedGramThree_posSemidef_of_permuted_order
          ha0 ha x e
        · exact h12
        · exact h20
      · let e : Fin 3 ≃ Fin 3 := Equiv.swap 0 2
        apply thetaCuspCenterMixedGramThree_posSemidef_of_permuted_order
          ha0 ha x e
        · exact h21
        · exact h10

/-- No three-atom real test measure can have negative energy against the
center-mixed theta density. -/
theorem thetaCuspCenterMixedGramThree_quadratic_nonneg
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (x c : Fin 3 → ℝ) :
    0 ≤ star c ⬝ᵥ
      (thetaCuspCenterMixedGramThree a x).mulVec c :=
  (thetaCuspCenterMixedGramThree_posSemidef ha0 ha x).dotProduct_mulVec_nonneg c

/-- A negative source-orientation witness cannot be supported on three
nodes. -/
theorem no_thetaCuspCenterMixed_negativeWitness_three
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    ¬ ∃ x c : Fin 3 → ℝ,
      star c ⬝ᵥ
          (thetaCuspCenterMixedGramThree a x).mulVec c < 0 := by
  rintro ⟨x, c, hneg⟩
  exact (not_lt_of_ge
    (thetaCuspCenterMixedGramThree_quadratic_nonneg ha0 ha x c)) hneg

end

end RHTower

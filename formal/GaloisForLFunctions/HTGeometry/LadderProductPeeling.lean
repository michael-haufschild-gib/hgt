import GaloisForLFunctions.HTGeometry.BarnesAnnihilatorExact

/-!
# Peeling one direction off a ladder product

The ladder product over a finite set of directions factors through any one of them, and the operator
ring acts by composition, so applying the product is applying the defect in that direction first and
the remaining product afterwards:

```text
(∏_{k ∈ S} (T_k - 1)) y = (∏_{k ∈ S.erase i} (T_k - 1)) (σ_{ω_i} y - y).
```

This is the peeling an induction on the number of directions performs.  The full and complementary
ladder products of the annihilator theorem are the two instances `S = univ` and `S = univ.erase j`.
-/

open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-- The ladder product over a finite set of directions. -/
def ladderProd {N : ℕ} (S : Finset (Fin N)) : MvPolynomial (Fin N) (Polynomial ℂ) :=
  ∏ k ∈ S, (MvPolynomial.X k - 1)

theorem ladderProd_univ (N : ℕ) : ladderProd (Finset.univ : Finset (Fin N)) = fullLadder N := rfl

theorem ladderProd_univ_erase {N : ℕ} (j : Fin N) :
    ladderProd (Finset.univ.erase j) = complementaryLadder j := rfl

theorem ladderProd_empty (N : ℕ) : ladderProd (∅ : Finset (Fin N)) = 1 :=
  Finset.prod_empty

theorem ladderProd_erase_mul {N : ℕ} {S : Finset (Fin N)} {i : Fin N} (hi : i ∈ S) :
    ladderProd (S.erase i) * (MvPolynomial.X i - 1) = ladderProd S := by
  rw [ladderProd, ladderProd, mul_comm]
  exact Finset.mul_prod_erase S _ hi

/-- **Peeling one direction.**  Applying the ladder product over `S` is applying the defect in one
of its directions first and the remaining product afterwards. -/
theorem diffTranslateApply_ladderProd_erase {N : ℕ} (ω : Fin N → ℂ) {S : Finset (Fin N)}
    {i : Fin N} (hi : i ∈ S) (y : meroField (Set.univ : Set ℂ)) :
    diffTranslateApply ω (ladderProd S) y
      = diffTranslateApply ω (ladderProd (S.erase i))
        (addTranslationMeroEquiv (ω i) y - y) := by
  rw [← ladderProd_erase_mul hi, diffTranslateApply_mul, diffTranslateApply_X_sub_one]

/-- Applying the empty ladder product is the identity. -/
theorem diffTranslateApply_ladderProd_empty {N : ℕ} (ω : Fin N → ℂ)
    (y : meroField (Set.univ : Set ℂ)) :
    diffTranslateApply ω (ladderProd (∅ : Finset (Fin N))) y = y := by
  rw [ladderProd_empty, diffTranslateApply_one]

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.RHTower.ProlateSignedNatBasis
import GaloisForLFunctions.RHTower.ProlateSignedLeakageOrdering

/-!
# The Fourier-parity sector families

The constrained-prolate cards work in the two compressed-Fourier sectors

```text
H_λ⁺ = closure span {h_{4j,λ}} ,      H_λ⁻ = closure span {h_{4j+2,λ}} ,
```

which in the corpus's signed indexing are the even and odd signed sublattices `n = 2j` and
`n = 2j+1`.  Both sub-families inherit orthonormality from the full signed family, since `j ↦ 2j`
and `j ↦ 2j+1` are injective.  These are the families whose leakage values are the transfer
theorems' `D a j = evenProlateSignedLeakage a (2j)` and `evenProlateSignedLeakage a (2j+1)`.
-/

noncomputable section

open scoped InnerProduct InnerProductSpace

namespace RHTower

/-- The positive-sector family: signed modes at even index. -/
def positiveSectorMode (a : ℝ) (ha : 0 < a) (j : ℕ) : evenTimeLimitedSubspace a :=
  signedNatMode a ha (2 * j)

/-- The negative-sector family: signed modes at odd index. -/
def negativeSectorMode (a : ℝ) (ha : 0 < a) (j : ℕ) : evenTimeLimitedSubspace a :=
  signedNatMode a ha (2 * j + 1)

theorem orthonormal_positiveSectorMode {a : ℝ} (ha : 0 < a) :
    Orthonormal ℂ (positiveSectorMode a ha) := by
  constructor
  · intro j
    exact (orthonormal_signedNatMode ha).1 (2 * j)
  · intro i j hij
    exact (orthonormal_signedNatMode ha).2 (by omega : 2 * i ≠ 2 * j)

theorem orthonormal_negativeSectorMode {a : ℝ} (ha : 0 < a) :
    Orthonormal ℂ (negativeSectorMode a ha) := by
  constructor
  · intro j
    exact (orthonormal_signedNatMode ha).1 (2 * j + 1)
  · intro i j hij
    exact (orthonormal_signedNatMode ha).2 (by omega : 2 * i + 1 ≠ 2 * j + 1)

/-- The positive-sector leakage values are the transfer theorems' diagonal `D`. -/
theorem positiveSectorMode_leakage (a : ℝ) (ha : 0 < a) (j : ℕ) :
    evenProlateLeakage a ((positiveSectorMode a ha j : evenTimeLimitedSubspace a) : evenSubspace)
      = ((evenProlateSignedLeakage a (2 * j) : ℝ) : ℂ)
        • ((positiveSectorMode a ha j : evenTimeLimitedSubspace a) : evenSubspace) := by
  have h := evenProlateLeakage_apply_signedMode a (2 * j)
  simpa [positiveSectorMode, signedNatMode, evenProlateSignedLeakage] using h

/-- The negative-sector leakage values. -/
theorem negativeSectorMode_leakage (a : ℝ) (ha : 0 < a) (j : ℕ) :
    evenProlateLeakage a ((negativeSectorMode a ha j : evenTimeLimitedSubspace a) : evenSubspace)
      = ((evenProlateSignedLeakage a (2 * j + 1) : ℝ) : ℂ)
        • ((negativeSectorMode a ha j : evenTimeLimitedSubspace a) : evenSubspace) := by
  have h := evenProlateLeakage_apply_signedMode a (2 * j + 1)
  simpa [negativeSectorMode, signedNatMode, evenProlateSignedLeakage] using h

end RHTower

end

import GaloisForLFunctions.HTGeometry.DegenerationRegularSequence
import GaloisForLFunctions.HTGeometry.HankelSecantLastMile
import GaloisForLFunctions.HTGeometry.HankelDegenerationHypotheses
import GaloisForLFunctions.HTGeometry.HankelDiagonalWeight
import GaloisForLFunctions.HTGeometry.LinearRegularSequence

/-!
# The Hankel secant ring is Cohen–Macaulay

```text
isHomogeneous_linearForm                a linear form is homogeneous of degree one
exists_isRegular_finiteHankelSecantIdeal
    ** the secant ideal carries a regular sequence of length `2r` **
isCohenMacaulayRing_finiteHankelSecantQuotient
    ** hence the Hankel secant ring is Cohen–Macaulay **
```

The chain complex carries a regular sequence of its own dimension, which
`exists_linear_isRegular` replaces by one of linear forms.  The concave weight `k ↦ -k²` degenerates
the secant ideal onto an ideal containing the chain ideal, and the standard monomials are a common
graded complement of the secant and chain ideals, so `exists_isRegular_of_degeneration` deforms the
linear sequence to one regular on the secant ideal itself.  Its length is the Krull dimension of the
secant ring, which is Cohen–Macaulayness.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Module RHTower

universe u

/-- A linear form is homogeneous of degree one. -/
theorem isHomogeneous_linearForm {N : ℕ} {K : Type u} [Field K] (c : Fin N → K) :
    (linearForm c).IsHomogeneous 1 := by
  rw [linearForm]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => ?_
  simpa using (MvPolynomial.isHomogeneous_C _ (c i)).mul (MvPolynomial.isHomogeneous_X K i)

/-- **The secant ideal carries a regular sequence of length `2r`.** -/
theorem exists_isRegular_finiteHankelSecantIdeal (K : Type u) [Field K] [Infinite K] (N r : ℕ)
    (hN : 2 * r ≤ N) :
    ∃ rs : List (MvPolynomial (Fin N) K), rs.length = 2 * r ∧
      RingTheory.Sequence.IsRegular
        (MvPolynomial (Fin N) K ⧸ finiteHankelSecantIdeal K N r) rs := by
  classical
  -- a regular sequence on the monomial degeneration, taken linear
  obtain ⟨rs0, hlen0, hmem0, hreg0⟩ := hasRegSeq_chainFaceFinset (K := K) N r
  rw [faceFamilyIdeal_chainFaceFinset] at hreg0
  have hlt : irrelevantIdeal K (Fin N) • (⊤ : Submodule (MvPolynomial (Fin N) K)
      (ModuleCat.of (MvPolynomial (Fin N) K)
        (MvPolynomial (Fin N) K ⧸ finiteHankelChainIdeal K N r))) < ⊤ := by
    have h := smul_top_lt_top_faceFamily (σ := Fin N) K
      (F := chainFaceFinset N r) ⟨∅, mem_chainFaceFinset.mpr (isChainFace_empty N r)⟩
    rwa [faceFamilyIdeal_chainFaceFinset] at h
  obtain ⟨cs, hcslen, hcsreg⟩ := exists_linear_isRegular (K := K) (N := N) (min N (2 * r))
    (ModuleCat.of (MvPolynomial (Fin N) K)
      (MvPolynomial (Fin N) K ⧸ finiteHankelChainIdeal K N r)) inferInstance hlt
    ⟨rs0, hlen0, hmem0, hreg0⟩
  -- deform it along the degeneration
  obtain ⟨ls', hls'len, hls'reg⟩ := exists_isRegular_of_degeneration (hankelWeight N)
    (isHomogIdeal_finiteHankelSecantIdeal K N r) (isHomogIdeal_finiteHankelChainIdeal K N r)
    (isGradedSubmodule_hankelStandardSpan K N r)
    (isCompl_finiteHankelSecantIdeal_standardSpan K N r)
    (isCompl_finiteHankelChainIdeal_standardSpan K N r)
    (finiteHankelChainIdeal_le_initialIdeal K N r)
    (cs.map linearForm) (by
      intro l hl
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp hl
      exact isHomogeneous_linearForm c)
    hcsreg
  refine ⟨ls', ?_, hls'reg⟩
  rw [hls'len, List.length_map, hcslen, min_eq_right hN]

/-- **The Hankel secant ring is Cohen–Macaulay.** -/
theorem isCohenMacaulayRing_finiteHankelSecantQuotient (K : Type) [Field K] [CharZero K]
    (N r : ℕ) (hN : 2 * r ≤ N) :
    IsCohenMacaulayRing (MvPolynomial (Fin N) K ⧸ finiteHankelSecantIdeal K N r) :=
  isCohenMacaulayRing_hankelSecantQuotient_of_regSeq K hN
    (exists_isRegular_finiteHankelSecantIdeal K N r hN)

end GaloisForLFunctions.HTGeometry

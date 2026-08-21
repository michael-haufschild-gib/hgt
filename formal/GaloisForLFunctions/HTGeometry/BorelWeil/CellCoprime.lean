import GaloisForLFunctions.HTGeometry.BorelWeil.CellMinors
import GaloisForLFunctions.HTGeometry.BorelWeil.DetTwist
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The cell equations have no common factor beyond the determinant

Sections regular on every Bruhat cell are exactly the sections regular on `GL`, that is, those whose
denominators are powers of `det`.  The inclusion `R[1/det] ⊆ ⋂_σ R[1/D_σ]` is immediate because
`det ∣ D_σ`.  The reverse inclusion rests on the statement proved here: a prime that does not divide
`det` fails to divide some cell equation `D_σ`.

The proof needs no Nullstellensatz certificate for the covering.  It base changes the greedy
factorization theorem to the residue field at the prime: over that field the generic matrix is still
invertible, so some permutation makes all of its leading minors nonzero there, and that says exactly
that the prime misses the corresponding cell equation.

## Main results

* `exists_cellDenom_not_dvd`
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k]

/-- Truncation commutes with entrywise application of a ring homomorphism. -/
theorem truncate_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (j : ℕ)
    (A : Matrix (Fin N) (Fin N) R) :
    (truncate j A).map φ = truncate j (A.map φ) := by
  ext i l
  by_cases h1 : (i : ℕ) < j
  · by_cases h2 : (l : ℕ) < j
    · rw [Matrix.map_apply, truncate_apply_of_both h1 h2, truncate_apply_of_both h1 h2,
        Matrix.map_apply]
    · rw [Matrix.map_apply, truncate_apply_of_not_right h2, truncate_apply_of_not_right h2]
      by_cases h3 : i = l <;> simp [h3]
  · rw [Matrix.map_apply, truncate_apply_of_not_left h1, truncate_apply_of_not_left h1]
    by_cases h3 : i = l <;> simp [h3]

/-- Truncation at the full size is the identity, over any commutative ring. -/
theorem truncate_self_commRing {R : Type*} [CommRing R] (A : Matrix (Fin N) (Fin N) R) :
    truncate N A = A := by
  ext i i'
  exact truncate_apply_of_both i.isLt i'.isLt

/-- The image of a cell minor under a ring homomorphism is the corresponding leading minor of the
base changed generic matrix. -/
theorem map_minorPolyAt {K : Type*} [Field K] (φ : MvPolynomial (Fin N × Fin N) k →+* K)
    (σ : Equiv.Perm (Fin N)) (j : ℕ) :
    φ (minorPolyAt N k σ j)
      = leadingMinorMat j (((genericMatrix N k).map φ).submatrix (⇑σ) id) := by
  rw [minorPolyAt, RingHom.map_det, RingHom.mapMatrix_apply, truncate_map]
  rfl

theorem detPoly_eq_det_genericMatrix : detPoly N k = (genericMatrix N k).det := by
  rw [detPoly_def, minorPoly, truncate_self_commRing]

/-- **A prime missing the determinant misses some cell equation.**  Equivalently, the cell equations
have no common irreducible factor beyond the factors of `det`. -/
theorem exists_cellDenom_not_dvd {π : MvPolynomial (Fin N × Fin N) k} (hπ : Prime π)
    (hdet : ¬ π ∣ detPoly N k) :
    ∃ σ : Equiv.Perm (Fin N), ¬ π ∣ cellDenomPoly N k σ := by
  classical
  haveI hprime : (Ideal.span ({π} : Set (MvPolynomial (Fin N × Fin N) k))).IsPrime :=
    (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  haveI : IsDomain (MvPolynomial (Fin N × Fin N) k ⧸
      Ideal.span ({π} : Set (MvPolynomial (Fin N × Fin N) k))) := Ideal.Quotient.isDomain _
  set K := FractionRing (MvPolynomial (Fin N × Fin N) k ⧸
    Ideal.span ({π} : Set (MvPolynomial (Fin N × Fin N) k))) with hK
  set φ : MvPolynomial (Fin N × Fin N) k →+* K :=
    (algebraMap _ K).comp (Ideal.Quotient.mk (Ideal.span ({π} : Set _))) with hφ
  have hker : ∀ p : MvPolynomial (Fin N × Fin N) k, φ p = 0 ↔ π ∣ p := by
    intro p
    rw [hφ, RingHom.comp_apply]
    constructor
    · intro h
      have h0 : (Ideal.Quotient.mk (Ideal.span ({π} : Set _))) p = 0 :=
        IsFractionRing.injective _ K (by rw [h, map_zero])
      rwa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h0
    · intro h
      have h0 : (Ideal.Quotient.mk (Ideal.span ({π} : Set _))) p = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
        exact h
      rw [h0, map_zero]
  have hdetne : (((genericMatrix N k).map φ).det) ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, ← detPoly_eq_det_genericMatrix]
    exact fun h => hdet ((hker _).mp h)
  obtain ⟨σ, hσ⟩ := exists_perm_leadingMinor_ne_zero hdetne
  refine ⟨σ, fun hdvd => ?_⟩
  have hzero : φ (cellDenomPoly N k σ) = 0 := (hker _).mpr hdvd
  rw [cellDenomPoly, map_prod] at hzero
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp hzero
  exact hσ j (by rw [← map_minorPolyAt φ σ ((j : ℕ) + 1)]; exact hj)

end GaloisForLFunctions.HTGeometry.BorelWeil

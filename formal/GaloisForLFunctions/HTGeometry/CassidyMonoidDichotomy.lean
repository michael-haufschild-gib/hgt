import GaloisForLFunctions.HTGeometry.Sl2CassidyImproperBranch
import GaloisForLFunctions.HTGeometry.LeftInvariantJetDerivation
import GaloisForLFunctions.HTGeometry.CassidyGroupConstants

/-!
# Cassidy's dichotomy for a matrix monoid in `SL₂`

For the vanishing ideal of a multiplicative set of determinant-one matrices containing the identity,
three of the four structural hypotheses of Cassidy's classification are theorems:

* `hone` — the identity lies in the zero set;
* `htr` — the determinant equation lies in the ideal, so tangent directions are traceless;
* `hbr` — bracket closure, from the left-invariant jet derivations.

Only Zariski density remains an input, and it is the content of irreducibility of the recurrence.
The improper branch of the dichotomy is `sl2_of_full_tangent_vanishingIdeal`, so the alternative
reads: either the whole of `SL₂` lies in the Kolchin closure of the monoid, or every entry of every
element of the group solves one nonzero linear differential operator.

* `detPoly_mem_matrixVanishingIdeal`, `trace_eq_zero_of_mem_matrixTangentM`;
* `cassidy_monoid_dichotomy`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

attribute [local instance] differentialPolynomialOverDifferential

variable {C : Type*} [Field C] [Differential C]

/-- The determinant equation lies in the vanishing ideal of a set of determinant-one matrices. -/
theorem detPoly_mem_matrixVanishingIdeal {H : Set (Matrix (Fin 2) (Fin 2) C)}
    (hHdet : ∀ h ∈ H, h.det = 1) :
    detPoly (C := C) ∈ matrixVanishingIdeal H := by
  intro h hh
  rw [evalOver_detPoly]
  have hd : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact hHdet h hh
  show h ((0 : Fin 2), (0 : Fin 2)).1 ((0 : Fin 2), (0 : Fin 2)).2
      * h ((1 : Fin 2), (1 : Fin 2)).1 ((1 : Fin 2), (1 : Fin 2)).2
    - h ((0 : Fin 2), (1 : Fin 2)).1 ((0 : Fin 2), (1 : Fin 2)).2
      * h ((1 : Fin 2), (0 : Fin 2)).1 ((1 : Fin 2), (0 : Fin 2)).2 - 1 = 0
  rw [hd, sub_self]

/-- Tangent directions of a set of determinant-one matrices are traceless. -/
theorem trace_eq_zero_of_mem_matrixTangentM {H : Set (Matrix (Fin 2) (Fin 2) C)}
    (hHdet : ∀ h ∈ H, h.det = 1)
    {hone : (1 : Matrix (Fin 2) (Fin 2) C)
      ∈ matrixZeroSet (C := C) (A := C) (matrixVanishingIdeal H)}
    {A : Matrix (Fin 2) (Fin 2) C} (hA : A ∈ matrixTangentM (matrixVanishingIdeal H) hone) :
    A.trace = 0 := by
  rw [Matrix.trace_fin_two]
  exact trace_eq_zero_of_mem_zeroSet (detPoly_mem_matrixVanishingIdeal hHdet) hA

/-- **Cassidy's dichotomy for a matrix monoid in `SL₂`.**  Either the Kolchin closure of the monoid
contains the whole of `SL₂`, or one nonzero linear differential operator annihilates every entry of
every element of the group. -/
theorem cassidy_monoid_dichotomy [IsAlgClosed C] [CharZero C]
    [IsAlgClosed (differentialConstants C)]
    (hrank : NoUniversalJetRelation C)
    {H : Set (Matrix (Fin 2) (Fin 2) C)}
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hHone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ H)
    (hHdet : ∀ h ∈ H, h.det = 1)
    (hdet : ∀ h ∈ matrixZeroSet (C := C) (A := C) (matrixVanishingIdeal H), h.det = 1)
    (hdense : ∀ Z : Matrix (Fin 2) (Fin 2) C, Z.trace = 0 →
      Z ∈ Submodule.span C
        ((matrixTangentM (matrixVanishingIdeal H)
          (subset_matrixZeroSet_vanishingIdeal H hHone) : Submodule _ _) : Set _))
    (G : Set (Matrix (Fin 2) (Fin 2) C))
    (hGdetK : ∀ g ∈ G, g.det ∈ differentialConstants C) (hGdet0 : ∀ g ∈ G, g.det ≠ 0)
    (hGinv : ∀ g ∈ G, ∃ g' : Matrix (Fin 2) (Fin 2) C, g * g' = 1 ∧
      ∀ A ∈ matrixTangentM (matrixVanishingIdeal H)
          (subset_matrixZeroSet_vanishingIdeal H hHone),
        g * A * g' ∈ matrixTangentM (matrixVanishingIdeal H)
          (subset_matrixZeroSet_vanishingIdeal H hHone)) :
    (∀ g : Matrix (Fin 2) (Fin 2) C, g.det = 1 →
        g ∈ matrixZeroSet (C := C) (A := C) (matrixVanishingIdeal H))
      ∨ ∃ (n : ℕ) (Lop : ℕ → C) (i₀ : ℕ), i₀ ∈ Finset.range (n + 1) ∧ Lop i₀ ≠ 0 ∧
          ∀ g ∈ G, ∀ i j, g i j ∈ linearJetSolutions n Lop := by
  set hone : (1 : Matrix (Fin 2) (Fin 2) C)
      ∈ matrixZeroSet (C := C) (A := C) (matrixVanishingIdeal H) :=
    subset_matrixZeroSet_vanishingIdeal H hHone with hone_def
  have hIS : ∀ P : DifferentialPolynomial (Fin 2 × Fin 2) C,
      (∀ g ∈ matrixZeroSet (C := C) (A := C) (matrixVanishingIdeal H),
        differentialPolynomialEvalOver (K := C) (fun q : Fin 2 × Fin 2 => g q.1 q.2) P = 0) →
      P ∈ matrixVanishingIdeal H := by
    intro P hP h hh
    exact hP h (subset_matrixZeroSet_vanishingIdeal H hh)
  have htrans : TangentTranslates (matrixVanishingIdeal H) hone :=
    tangentTranslates_of_leftTranslate _ hone
      (fun a ha P hP => leftTranslate_mem_matrixVanishingIdeal hH ha hP)
  rcases cassidy_group_dichotomy (matrixVanishingIdeal H) hone
    (fun A hA => trace_eq_zero_of_mem_matrixTangentM hHdet hA)
    (fun A hA B hB => bracket_mem_matrixTangentM _ htrans hIS hA hB)
    hdense G hGdetK hGdet0 hGinv with hfull | hlin
  · exact Or.inl (sl2_of_full_tangent_vanishingIdeal hrank hH hHone hdet hfull)
  · exact Or.inr hlin

end

end GaloisForLFunctions.HTGeometry

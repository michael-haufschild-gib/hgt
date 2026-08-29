import GaloisForLFunctions.HTGeometry.Sl2BigCellElimination
import GaloisForLFunctions.HTGeometry.MatrixTranslationZeroSet

/-!
# A differential algebraic monoid in `SL₂` with full Lie algebra is all of `SL₂`

This is the improper branch of Cassidy's classification, proved in characteristic zero with no
smoothness, dimension theory or Kolchin topology.  The three ingredients are: the linearisation of
the defining equations at every point of the monoid annihilates the tangent space of `SL₂` there
(closure under multiplication over the dual numbers); the vanishing ideal in the three big-cell
coordinates is therefore closed under partial derivatives, hence zero; and the fourth coordinate is
eliminated by clearing a power of `X₀₀`.

The big cell generates: every element of `SL₂` is a product of two elements with invertible
upper-left entry, so the monoid law upgrades the big cell to the whole group.

* `lowerUnipotent`, `lowerUnipotent_mul`, `exists_bigCell_factorisation`;
* `mem_of_det_eq_one_of_ne_zero` — the big cell lies in the monoid;
* `sl2_of_full_tangent` — **the monoid is all of `SL₂`.**
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C : Type*} [Field C] [Differential C]

/-! ### Factorising through the big cell -/

/-- The lower unipotent one-parameter subgroup. -/
def lowerUnipotent (t : C) : Matrix (Fin 2) (Fin 2) C := Matrix.of ![![1, 0], ![t, 1]]

omit [Differential C] in
@[simp] theorem lowerUnipotent_det (t : C) : (lowerUnipotent t).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [lowerUnipotent]

omit [Differential C] in
theorem lowerUnipotent_mul (t s : C) :
    lowerUnipotent t * lowerUnipotent s = lowerUnipotent (t + s) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [lowerUnipotent, Matrix.mul_apply, Fin.sum_univ_two]

omit [Differential C] in
@[simp] theorem lowerUnipotent_zero_zero (t : C) : lowerUnipotent t 0 0 = 1 := by
  simp [lowerUnipotent]

omit [Differential C] in
theorem mul_lowerUnipotent_zero_zero (g : Matrix (Fin 2) (Fin 2) C) (t : C) :
    (g * lowerUnipotent t) 0 0 = g 0 0 + g 0 1 * t := by
  simp [lowerUnipotent, Matrix.mul_apply, Fin.sum_univ_two]

omit [Differential C] in
/-- **Every element of `SL₂` is a product of two elements with invertible upper-left entry.** -/
theorem exists_bigCell_factorisation {g : Matrix (Fin 2) (Fin 2) C} (hdet : g.det = 1) :
    ∃ a b : Matrix (Fin 2) (Fin 2) C, a.det = 1 ∧ b.det = 1 ∧ a 0 0 ≠ 0 ∧ b 0 0 ≠ 0 ∧
      g = a * b := by
  have hdet' : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hdet
  by_cases h01 : g 0 1 = 0
  · have h00 : g 0 0 ≠ 0 := by
      intro hc
      rw [hc, h01] at hdet'
      simp at hdet'
    exact ⟨g, 1, hdet, Matrix.det_one, h00, by simp, by rw [mul_one]⟩
  · set t : C := (1 - g 0 0) / g 0 1 with ht
    refine ⟨g * lowerUnipotent t, lowerUnipotent (-t), ?_, ?_, ?_, ?_, ?_⟩
    · rw [Matrix.det_mul, hdet, lowerUnipotent_det, one_mul]
    · exact lowerUnipotent_det _
    · rw [mul_lowerUnipotent_zero_zero, ht]
      field_simp
      have hsimp : g 0 0 + (1 - g 0 0) = 1 := by ring
      rw [hsimp]
      exact one_ne_zero
    · simp
    · rw [Matrix.mul_assoc, lowerUnipotent_mul, add_neg_cancel]
      have h1 : lowerUnipotent (0 : C) = 1 := by
        refine Matrix.ext fun i j => ?_
        fin_cases i <;> fin_cases j <;> simp [lowerUnipotent]
      rw [h1, mul_one]

/-! ### The improper branch -/

variable {S : Set (DifferentialPolynomial (Fin 2 × Fin 2) C)}

/-- **The big cell of `SL₂` lies in the monoid.** -/
theorem mem_of_det_eq_one_of_ne_zero [CharZero C]
    (hrank : NoUniversalJetRelation C)
    {hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ matrixZeroSet (C := C) (A := C) S}
    (htrans : TangentTranslates S hone)
    (hfull : ∀ Z : Matrix (Fin 2) (Fin 2) C, Z.trace = 0 → Z ∈ matrixTangentM S hone)
    (hdet : ∀ h ∈ matrixZeroSet (C := C) (A := C) S, h.det = 1)
    (hrad : ∀ P : DifferentialPolynomial (Fin 2 × Fin 2) C,
      (∀ h ∈ matrixZeroSet (C := C) (A := C) S,
        differentialPolynomialEvalOver (K := C) (fun q : Fin 2 × Fin 2 => h q.1 q.2) P = 0) →
      P ∈ S)
    {g : Matrix (Fin 2) (Fin 2) C} (hg : g.det = 1) (hg00 : g 0 0 ≠ 0) :
    g ∈ matrixZeroSet (C := C) (A := C) S := by
  intro P hP
  obtain ⟨N, Q, hQvars, hQeval⟩ := exists_bigCell_elimination P
  have hQmem : Q ∈ bigCellIdeal S := by
    refine ⟨hQvars, ?_⟩
    rintro p ⟨h, hh, hh00, rfl⟩
    rw [hQeval h (hdet h hh) hh00, hh P hP, mul_zero]
  have hQzero : Q = 0 := bigCellIdeal_eq_zero hrank htrans hfull hdet hrad Q hQmem
  have hval := hQeval g hg hg00
  rw [hQzero, map_zero] at hval
  rcases mul_eq_zero.mp hval.symm with h | h
  · exact absurd h (pow_ne_zero N hg00)
  · exact h

/-- **A differential algebraic monoid in `SL₂` whose tangent space at the identity is all of `sl₂`
is the whole of `SL₂`.** -/
theorem sl2_of_full_tangent [CharZero C]
    (hrank : NoUniversalJetRelation C)
    {hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ matrixZeroSet (C := C) (A := C) S}
    (htrans : TangentTranslates S hone)
    (hmulC : ∀ a ∈ matrixZeroSet (C := C) (A := C) S,
      ∀ b ∈ matrixZeroSet (C := C) (A := C) S,
      a * b ∈ matrixZeroSet (C := C) (A := C) S)
    (hfull : ∀ Z : Matrix (Fin 2) (Fin 2) C, Z.trace = 0 → Z ∈ matrixTangentM S hone)
    (hdet : ∀ h ∈ matrixZeroSet (C := C) (A := C) S, h.det = 1)
    (hrad : ∀ P : DifferentialPolynomial (Fin 2 × Fin 2) C,
      (∀ h ∈ matrixZeroSet (C := C) (A := C) S,
        differentialPolynomialEvalOver (K := C) (fun q : Fin 2 × Fin 2 => h q.1 q.2) P = 0) →
      P ∈ S) :
    ∀ g : Matrix (Fin 2) (Fin 2) C, g.det = 1 → g ∈ matrixZeroSet (C := C) (A := C) S := by
  intro g hg
  obtain ⟨a, b, ha, hb, ha00, hb00, rfl⟩ := exists_bigCell_factorisation hg
  exact hmulC _ (mem_of_det_eq_one_of_ne_zero hrank htrans hfull hdet hrad ha ha00)
    _ (mem_of_det_eq_one_of_ne_zero hrank htrans hfull hdet hrad hb hb00)


/-- **Cassidy's improper branch for a matrix monoid.**  A multiplicative set of determinant-one
matrices containing the identity, whose Kolchin closure has all of `sl₂` as tangent space at the
identity, has the whole of `SL₂` in its closure.

Every hypothesis is a property of the monoid itself: no dual numbers, no radicality, no Hopf or
group-scheme structure.  Closure under multiplication over the dual numbers is replaced by
stability of the vanishing ideal under left translation, which is the elementary two-step
argument. -/
theorem sl2_of_full_tangent_vanishingIdeal [CharZero C]
    (hrank : NoUniversalJetRelation C)
    {H : Set (Matrix (Fin 2) (Fin 2) C)}
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hHone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ H)
    (hdet : ∀ h ∈ matrixZeroSet (C := C) (A := C) (matrixVanishingIdeal H), h.det = 1)
    (hfull : ∀ Z : Matrix (Fin 2) (Fin 2) C, Z.trace = 0 →
      Z ∈ matrixTangentM (matrixVanishingIdeal H)
        (subset_matrixZeroSet_vanishingIdeal H hHone)) :
    ∀ g : Matrix (Fin 2) (Fin 2) C, g.det = 1 →
      g ∈ matrixZeroSet (C := C) (A := C) (matrixVanishingIdeal H) := by
  have hone : (1 : Matrix (Fin 2) (Fin 2) C)
      ∈ matrixZeroSet (C := C) (A := C) (matrixVanishingIdeal H) :=
    subset_matrixZeroSet_vanishingIdeal H hHone
  refine sl2_of_full_tangent (S := matrixVanishingIdeal H) hrank
    (hone := hone)
    (tangentTranslates_of_leftTranslate _ hone
      (fun a ha P hP => leftTranslate_mem_matrixVanishingIdeal hH ha hP))
    (fun a ha b hb => mul_mem_matrixZeroSet_vanishingIdeal hH ha hb)
    hfull hdet ?_
  intro P hP h hh
  exact hP h (subset_matrixZeroSet_vanishingIdeal H hh)

end

end GaloisForLFunctions.HTGeometry

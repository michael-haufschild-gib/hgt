import GaloisForLFunctions.HTGeometry.DifferentialSubgroupCassidy
import GaloisForLFunctions.HTGeometry.MatrixTranslationPolynomial

/-!
# Translating the tangent space along a differential algebraic monoid

The Lie algebra of a differential algebraic group is read off at the identity, but the
derivation-closure argument that pins the group down needs the linearisation at *every* point of the
group.  For a zero set closed under multiplication over the dual numbers, the two are the same
datum: if `g` lies in the zero set and `1 + εZ` lies in it over `DualNumber C`, then so does the
product `g + ε(gZ)`, and the `ε`-part of the defining equations at that point is exactly the
linearisation of the equations at `g` in the direction `gZ`.

For a zero set inside `SL₂` the directions obtained this way are precisely those `W` with
`tr(adj(g)·W) = 0`, a three-dimensional space over `C` — the tangent space of `SL₂` at `g`
translated to the identity.

* `linearisationForm_eq_zero_of_dualMatrix_mem` — the `ε`-part of a dual-number point of the zero
  set is the linearisation;
* `dualMatrix_translate_mem_zeroSet` — left translation of a tangent direction;
* `linearisationForm_translate_eq_zero`;
* `linearisationForm_eq_zero_of_trace_adjugate_zero` — **the linearisation of every equation at
  every point of the monoid kills the whole tangent space of `SL₂` at that point.**
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C : Type*} [Field C] [Differential C]
variable (S : Set (DifferentialPolynomial (Fin 2 × Fin 2) C))

/-- **The `ε`-part of a dual-number point of the zero set is the linearisation.**  If `g + εW` is a
point of the zero set over the dual numbers, then the linearisation of every defining equation at
`g` annihilates `W`. -/
theorem linearisationForm_eq_zero_of_dualMatrix_mem
    {g W : Matrix (Fin 2) (Fin 2) C}
    (h : dualMatrix g W ∈ matrixZeroSet (C := C) (A := DualNumber C) S)
    {P : DifferentialPolynomial (Fin 2 × Fin 2) C} (hP : P ∈ S) :
    linearisationForm (fun q : Fin 2 × Fin 2 => g q.1 q.2) P P.vars
      (fun q : Fin 2 × Fin 2 => W q.1 q.2) = 0 := by
  have hpt : (fun q : Fin 2 × Fin 2 => dualMatrix g W q.1 q.2)
      = dualPoint (fun r : Fin 2 × Fin 2 => g r.1 r.2)
          (fun r : Fin 2 × Fin 2 => W r.1 r.2) :=
    funext fun q => dualMatrix_eq_dualPoint g W q
  have h' := h P hP
  rw [hpt] at h'
  have hsnd : (differentialPolynomialEvalOver (K := C)
      (dualPoint (fun r : Fin 2 × Fin 2 => g r.1 r.2)
        (fun r : Fin 2 × Fin 2 => W r.1 r.2)) P).snd = 0 := by
    rw [h']; simp
  rw [snd_differentialPolynomialEvalOver_dual _ _ P P.vars le_rfl] at hsnd
  rw [linearisationForm]
  exact hsnd

/-- **Left translation of a tangent direction.**  For a zero set closed under multiplication over
the dual numbers, `g + ε(g·Z)` is a point of the zero set whenever `g` is a point and `Z` is a
tangent direction at the identity. -/
theorem dualMatrix_translate_mem_zeroSet
    (hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ matrixZeroSet (C := C) (A := C) S)
    (hmul : ∀ a ∈ matrixZeroSet (C := C) (A := DualNumber C) S,
      ∀ b ∈ matrixZeroSet (C := C) (A := DualNumber C) S,
      a * b ∈ matrixZeroSet (C := C) (A := DualNumber C) S)
    {g : Matrix (Fin 2) (Fin 2) C} (hg : g ∈ matrixZeroSet (C := C) (A := C) S)
    {Z : Matrix (Fin 2) (Fin 2) C} (hZ : Z ∈ matrixTangentM S hone) :
    dualMatrix g (g * Z) ∈ matrixZeroSet (C := C) (A := DualNumber C) S := by
  have h1 : dualMatrix g 0 ∈ matrixZeroSet (C := C) (A := DualNumber C) S :=
    mem_zeroSet_dualMatrix_inl S hg
  have h2 : dualMatrix 1 Z ∈ matrixZeroSet (C := C) (A := DualNumber C) S := hZ
  have hmulres := hmul _ h1 _ h2
  rw [dualMatrix_mul, mul_one, zero_mul, add_zero] at hmulres
  exact hmulres

/-- **The tangent space translates.**  Every point of the zero set carries the tangent directions at
the identity to first-order deformations of itself inside the zero set.  This is all that the
derivation-closure argument uses, and it is weaker than closure under multiplication. -/
def TangentTranslates
    (hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ matrixZeroSet (C := C) (A := C) S) : Prop :=
  ∀ g ∈ matrixZeroSet (C := C) (A := C) S, ∀ Z ∈ matrixTangentM S hone,
    dualMatrix g (g * Z) ∈ matrixZeroSet (C := C) (A := DualNumber C) S

/-- Closure under multiplication over the dual numbers gives the translation property. -/
theorem tangentTranslates_of_mul
    (hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ matrixZeroSet (C := C) (A := C) S)
    (hmul : ∀ a ∈ matrixZeroSet (C := C) (A := DualNumber C) S,
      ∀ b ∈ matrixZeroSet (C := C) (A := DualNumber C) S,
      a * b ∈ matrixZeroSet (C := C) (A := DualNumber C) S) :
    TangentTranslates S hone :=
  fun _ hg _ hZ => dualMatrix_translate_mem_zeroSet S hone hmul hg hZ

/-- The dual numbers form a differential algebra over the base. -/
instance dualNumberDifferentialAlgebra : DifferentialAlgebra C (DualNumber C) where
  deriv_algebraMap a := by
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [deriv_dual_fst]
      simp [TrivSqZeroExt.algebraMap_eq_inl]
    · rw [deriv_dual_snd]
      simp [TrivSqZeroExt.algebraMap_eq_inl]

/-- **Stability of the defining ideal under left translation gives the translation property**, with
no reference to the dual numbers.  For the vanishing ideal of a monoid that stability is the
elementary two-step argument. -/
theorem tangentTranslates_of_leftTranslate
    (hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ matrixZeroSet (C := C) (A := C) S)
    (hL : ∀ g ∈ matrixZeroSet (C := C) (A := C) S, ∀ P ∈ S, matrixLeftTranslate g P ∈ S) :
    TangentTranslates S hone := by
  intro g hg Z hZ P hP
  have hZ' : dualMatrix 1 Z ∈ matrixZeroSet (C := C) (A := DualNumber C) S := hZ
  have hval := hZ' _ (hL g hg P hP)
  rw [evalOver_matrixLeftTranslate (A := DualNumber C)] at hval
  have hgmap : g.map (algebraMap C (DualNumber C)) = dualMatrix g 0 := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply, dualMatrix_apply, dualMk, TrivSqZeroExt.algebraMap_eq_inl]
    simp
  rw [hgmap, dualMatrix_mul, mul_one, zero_mul, add_zero] at hval
  exact hval

/-- The linearisation of every defining equation at a point `g` of the monoid annihilates every
left translate `g·Z` of a tangent direction at the identity. -/
theorem linearisationForm_translate_eq_zero
    {hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ matrixZeroSet (C := C) (A := C) S}
    (htrans : TangentTranslates S hone)
    {g : Matrix (Fin 2) (Fin 2) C} (hg : g ∈ matrixZeroSet (C := C) (A := C) S)
    {Z : Matrix (Fin 2) (Fin 2) C} (hZ : Z ∈ matrixTangentM S hone)
    {P : DifferentialPolynomial (Fin 2 × Fin 2) C} (hP : P ∈ S) :
    linearisationForm (fun q : Fin 2 × Fin 2 => g q.1 q.2) P P.vars
      (fun q : Fin 2 × Fin 2 => (g * Z) q.1 q.2) = 0 :=
  linearisationForm_eq_zero_of_dualMatrix_mem S (htrans g hg Z hZ) hP

omit [Differential C] in
/-- **The tangent space of `SL₂` at `g`, translated to the identity.**  A matrix `W` with
`tr(adj(g)·W) = 0` is `g·Z` for the traceless matrix `Z = adj(g)·W`, whenever `det g = 1`. -/
theorem exists_traceless_mul_eq_of_trace_adjugate_zero
    {g W : Matrix (Fin 2) (Fin 2) C} (hdet : g.det = 1)
    (hW : (Matrix.adjugate g * W).trace = 0) :
    ∃ Z : Matrix (Fin 2) (Fin 2) C, Z.trace = 0 ∧ g * Z = W := by
  refine ⟨Matrix.adjugate g * W, hW, ?_⟩
  rw [← Matrix.mul_assoc, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mul]

/-- **The linearisation at every point of the monoid kills the whole tangent space of `SL₂`
there.**  If the zero set is a multiplicative monoid whose tangent space at the identity is all of
`sl₂`, then for every point `g` of determinant one and every `W` in the three-dimensional space
`{W : tr(adj(g)·W) = 0}`, the linearisation of every defining equation at `g` annihilates `W`. -/
theorem linearisationForm_eq_zero_of_trace_adjugate_zero
    {hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ matrixZeroSet (C := C) (A := C) S}
    (htrans : TangentTranslates S hone)
    (hfull : ∀ Z : Matrix (Fin 2) (Fin 2) C, Z.trace = 0 → Z ∈ matrixTangentM S hone)
    {g : Matrix (Fin 2) (Fin 2) C} (hg : g ∈ matrixZeroSet (C := C) (A := C) S)
    (hdet : g.det = 1)
    {W : Matrix (Fin 2) (Fin 2) C} (hW : (Matrix.adjugate g * W).trace = 0)
    {P : DifferentialPolynomial (Fin 2 × Fin 2) C} (hP : P ∈ S) :
    linearisationForm (fun q : Fin 2 × Fin 2 => g q.1 q.2) P P.vars
      (fun q : Fin 2 × Fin 2 => W q.1 q.2) = 0 := by
  obtain ⟨Z, hZtr, hZW⟩ := exists_traceless_mul_eq_of_trace_adjugate_zero hdet hW
  have := linearisationForm_translate_eq_zero S htrans hg (hfull Z hZtr) hP
  rwa [hZW] at this

end

end GaloisForLFunctions.HTGeometry

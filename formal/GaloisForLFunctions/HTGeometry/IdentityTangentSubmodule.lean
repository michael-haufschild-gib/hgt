import GaloisForLFunctions.HTGeometry.BiDualBracketExtraction
import GaloisForLFunctions.HTGeometry.DifferentialTangentSubmodule

/-!
# The tangent space at the identity, as a module over the constants

A matrix `X` is a tangent direction at the identity of the zero set of a family `S` of differential
polynomials exactly when `1 + εX` lies in the zero set over the dual numbers.  Splitting that
condition into its two dual components identifies it: the `ε`-free part is the value at the
identity, which vanishes because the identity is in the zero set, and the `ε`-part is the
linearisation.  So the tangent directions are the intersection of the linearisation kernels, hence
a module over the differential constants.

With that, the negation and sum of tangent directions are tangent directions, and the bracket
statement loses its hypothesis on `−X`.

* `matrixTangent`, `mem_matrixTangent_iff`;
* `dualMatrix_neg_mem_zeroSet`;
* `bracket_mem_zeroSet_of_one` — bracket closure from `X`, `Y` alone.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C : Type*} [Field C] [Differential C]
variable (S : Set (DifferentialPolynomial (Fin 2 × Fin 2) C))

/-- The tangent directions at the identity, as a module over the differential constants. -/
def matrixTangent : Submodule (differentialConstants C) ((Fin 2 × Fin 2) → C) :=
  ⨅ P ∈ S, tangentSpace (fun q : Fin 2 × Fin 2 => (1 : Matrix (Fin 2) (Fin 2) C) q.1 q.2)
    P P.vars

omit [Differential C] in
theorem dualMatrix_eq_dualPoint (p X : Matrix (Fin 2) (Fin 2) C) (q : Fin 2 × Fin 2) :
    dualMatrix p X q.1 q.2
      = dualPoint (fun r : Fin 2 × Fin 2 => p r.1 r.2)
          (fun r : Fin 2 × Fin 2 => X r.1 r.2) q := by
  rw [dualMatrix_apply, dualPoint]

/-- **Membership in the tangent module is exactly membership of `1 + εX` in the zero set.** -/
theorem mem_matrixTangent_iff
    (hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ matrixZeroSet (C := C) (A := C) S)
    {X : Matrix (Fin 2) (Fin 2) C} :
    (fun q : Fin 2 × Fin 2 => X q.1 q.2) ∈ matrixTangent S
      ↔ dualMatrix 1 X ∈ matrixZeroSet (C := C) (A := DualNumber C) S := by
  constructor
  · intro hX P hP
    have hmem : (fun q : Fin 2 × Fin 2 => X q.1 q.2)
        ∈ tangentSpace (fun q : Fin 2 × Fin 2 => (1 : Matrix (Fin 2) (Fin 2) C) q.1 q.2)
          P P.vars := by
      have := Submodule.mem_iInf (ι := DifferentialPolynomial (Fin 2 × Fin 2) C) .. |>.mp hX P
      exact (Submodule.mem_iInf _).mp this hP
    rw [mem_tangentSpace_iff_snd_eq_zero le_rfl] at hmem
    have hfst := fst_differentialPolynomialEvalOver_dual
      (fun q : Fin 2 × Fin 2 => (1 : Matrix (Fin 2) (Fin 2) C) q.1 q.2)
      (fun q : Fin 2 × Fin 2 => X q.1 q.2) P
    rw [hone P hP] at hfst
    have hpt : (fun q : Fin 2 × Fin 2 => dualMatrix 1 X q.1 q.2)
        = dualPoint (fun r : Fin 2 × Fin 2 => (1 : Matrix (Fin 2) (Fin 2) C) r.1 r.2)
            (fun r : Fin 2 × Fin 2 => X r.1 r.2) := by
      funext q
      exact dualMatrix_eq_dualPoint 1 X q
    rw [hpt]
    exact TrivSqZeroExt.ext hfst hmem
  · intro hX
    refine (Submodule.mem_iInf _).mpr fun P => (Submodule.mem_iInf _).mpr fun hP => ?_
    rw [mem_tangentSpace_iff_snd_eq_zero le_rfl]
    have hpt : (fun q : Fin 2 × Fin 2 => dualMatrix 1 X q.1 q.2)
        = dualPoint (fun r : Fin 2 × Fin 2 => (1 : Matrix (Fin 2) (Fin 2) C) r.1 r.2)
            (fun r : Fin 2 × Fin 2 => X r.1 r.2) := by
      funext q
      exact dualMatrix_eq_dualPoint 1 X q
    have h := hX P hP
    rw [hpt] at h
    rw [h, TrivSqZeroExt.snd_zero]

/-- **The negative of a tangent direction is a tangent direction.** -/
theorem dualMatrix_neg_mem_zeroSet
    (hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ matrixZeroSet (C := C) (A := C) S)
    {X : Matrix (Fin 2) (Fin 2) C}
    (hX : dualMatrix 1 X ∈ matrixZeroSet (C := C) (A := DualNumber C) S) :
    dualMatrix 1 (-X) ∈ matrixZeroSet (C := C) (A := DualNumber C) S := by
  rw [← mem_matrixTangent_iff S hone] at hX ⊢
  have hneg := Submodule.neg_mem (matrixTangent S) hX
  convert hneg using 1
  funext q
  rfl

/-- **Bracket closure, with no hypothesis on `−X`.** -/
theorem bracket_mem_zeroSet_of_one
    (hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ matrixZeroSet (C := C) (A := C) S)
    (hmul : ∀ u ∈ matrixZeroSet (C := C) (A := BiDual C) S,
      ∀ v ∈ matrixZeroSet (C := C) (A := BiDual C) S,
      u * v ∈ matrixZeroSet (C := C) (A := BiDual C) S)
    {X Y : Matrix (Fin 2) (Fin 2) C}
    (hX : dualMatrix 1 X ∈ matrixZeroSet (C := C) (A := DualNumber C) S)
    (hY : dualMatrix 1 Y ∈ matrixZeroSet (C := C) (A := DualNumber C) S) :
    dualMatrix 1 (X * Y - Y * X) ∈ matrixZeroSet (C := C) (A := DualNumber C) S :=
  bracket_mem_zeroSet S hmul hX (dualMatrix_neg_mem_zeroSet S hone hX) hY

end

end GaloisForLFunctions.HTGeometry

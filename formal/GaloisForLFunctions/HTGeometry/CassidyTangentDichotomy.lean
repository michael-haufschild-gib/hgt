import GaloisForLFunctions.HTGeometry.DifferentialSubgroupCassidy
import GaloisForLFunctions.HTGeometry.Sl2AbsorbingLine
import GaloisForLFunctions.HTGeometry.TangentLineStabiliserDichotomy

/-!
# Cassidy's classification for `sl₂`, with no dimension hypothesis

`cassidy_of_matrixTangent_finite` classifies the Lie algebra of a differential algebraic subgroup of
`SL₂` under the hypothesis that it is finite dimensional over the constants, and `cassidy_dichotomy`
records the resulting excluded middle.  That hypothesis is *equivalent* to the conclusion — for the
improper group `SL₂(U)` the Lie algebra is all of `sl₂(U)`, infinite dimensional over the constants —
so the dichotomy carried no information beyond the case split.

This module replaces it by a sharp dichotomy with no hypothesis at all.  The two inputs are:

* the **line-stabiliser dichotomy** (`tangent_lineStabiliser_dichotomy`): the tangent space is cut
  out by linearisations, which are linear differential forms, so for a fixed direction `Y` either
  the whole `U`-line through `Y` is tangent, or the scalars `c` with `c · Y` tangent solve one monic
  scalar linear differential equation;
* the **absorption theorem** (`sl2_eq_of_absorbing`): a bracket-closed spanning subspace of `sl₂`
  containing one whole `U`-line is all of `sl₂`.

Together: either the Lie algebra is all of `sl₂(U)`, or every line stabiliser is a solution set of a
monic operator and `cassidy_sl2_of_differentialSolution` conjugates the Lie algebra onto `sl₂` over
the constants.

* `mem_matrixTangentM_iff_linearisation`;
* `cassidy_tangent_dichotomy` — the sharp dichotomy.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C : Type*} [Field C] [Differential C]
variable (S : Set (DifferentialPolynomial (Fin 2 × Fin 2) C))

/-- Membership in the Lie algebra, spelled out as the vanishing of every linearisation. -/
theorem mem_matrixTangentM_iff_linearisation
    (hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ matrixZeroSet (C := C) (A := C) S)
    {X : Matrix (Fin 2) (Fin 2) C} :
    X ∈ matrixTangentM S hone ↔
      ∀ P ∈ S, linearisationForm
        (fun q : Fin 2 × Fin 2 => (1 : Matrix (Fin 2) (Fin 2) C) q.1 q.2) P P.vars
        (fun q : Fin 2 × Fin 2 => X q.1 q.2) = 0 := by
  rw [mem_matrixTangentM, ← mem_matrixTangent_iff S hone]
  constructor
  · intro hX P hP
    have h1 := (Submodule.mem_iInf (ι := DifferentialPolynomial (Fin 2 × Fin 2) C) ..).mp hX P
    exact (Submodule.mem_iInf _).mp h1 hP
  · intro h
    refine (Submodule.mem_iInf _).mpr fun P => (Submodule.mem_iInf _).mpr fun hP => ?_
    exact h P hP

/-- **Cassidy's classification for the Lie algebra of a differential algebraic subgroup of `SL₂`,
unconditionally.**  Either the Lie algebra is all of `sl₂(U)`, or one conjugation carries it onto
`sl₂` over the differential constants.  No finite-dimensionality hypothesis is needed: the
alternative is decided by whether some `U`-line is absorbed. -/
theorem cassidy_tangent_dichotomy [IsAlgClosed C] [CharZero C]
    [IsAlgClosed (differentialConstants C)]
    (hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ matrixZeroSet (C := C) (A := C) S)
    (htr : ∀ A ∈ matrixTangentM S hone, A.trace = 0)
    (hbr : ∀ A ∈ matrixTangentM S hone, ∀ B ∈ matrixTangentM S hone,
      A * B - B * A ∈ matrixTangentM S hone)
    (hdense : ∀ Z : Matrix (Fin 2) (Fin 2) C, Z.trace = 0 →
      Z ∈ Submodule.span C ((matrixTangentM S hone : Submodule _ _) : Set _)) :
    (∀ Z : Matrix (Fin 2) (Fin 2) C, Z.trace = 0 → Z ∈ matrixTangentM S hone)
      ∨ ∃ P Q : Matrix (Fin 2) (Fin 2) C, P * Q = 1 ∧ Q * P = 1 ∧
          (matrixTangentM S hone).map (conjLinear (differentialConstants C) P Q)
            = Submodule.span (differentialConstants C) {sl2H C, sl2E C, sl2F C} := by
  classical
  set L := matrixTangentM S hone with hL
  by_cases hex : ∃ Y ∈ L, Y ≠ 0 ∧ ∀ c : C, c • Y ∈ L
  · obtain ⟨Y, -, hYne, hYabs⟩ := hex
    exact Or.inl (sl2_eq_of_absorbing L htr hbr hdense hYne hYabs)
  · right
    refine cassidy_sl2_of_differentialSolution L htr hbr hdense ?_
    intro Y hY hYne
    have hconv : ∀ c : C, (c • Y ∈ L ↔
        ∀ P ∈ S, linearisationForm
          (fun q : Fin 2 × Fin 2 => (1 : Matrix (Fin 2) (Fin 2) C) q.1 q.2) P P.vars
          (fun q : Fin 2 × Fin 2 => c * Y q.1 q.2) = 0) := by
      intro c
      rw [hL, mem_matrixTangentM_iff_linearisation S hone]
      simp only [Matrix.smul_apply, smul_eq_mul]
    rcases tangent_lineStabiliser_dichotomy
      (fun q : Fin 2 × Fin 2 => (1 : Matrix (Fin 2) (Fin 2) C) q.1 q.2) S
      (fun q : Fin 2 × Fin 2 => Y q.1 q.2) with hall | ⟨n, a, ha⟩
    · exact absurd ⟨Y, hY, hYne, fun c => (hconv c).mpr (hall c)⟩ hex
    · exact ⟨n, a, fun c hc => ha c ((hconv c).mp hc)⟩

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.CassidyMonoidDichotomy
import GaloisForLFunctions.HTGeometry.Sl2ProperAdjointNormalForm

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C : Type*} [Field C] [Differential C] [IsAlgClosed C] [CharZero C]

/-- If invariant lines and invariant unordered pairs are both excluded, the constant-field span of
the determinant-one Kolchin tangent space is either zero or all of `sl₂`.  This is the exact
positive-dimensional part of the algebraic subgroup classification. -/
theorem tangentSpan_eq_bot_or_dense_of_no_invariantNormalForm
    {H : Set (Matrix (Fin 2) (Fin 2) C)}
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hHone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ H)
    (hHdet : ∀ h ∈ H, h.det = 1)
    (G : Set (Matrix (Fin 2) (Fin 2) C))
    (hinv : ∀ g ∈ G, ∃ g' : Matrix (Fin 2) (Fin 2) C, g * g' = 1 ∧
      ∀ A ∈ matrixTangentM (matrixVanishingIdeal H)
          (subset_matrixZeroSet_vanishingIdeal H hHone),
        g * A * g' ∈ matrixTangentM (matrixVanishingIdeal H)
          (subset_matrixZeroSet_vanishingIdeal H hHone))
    (hnoLine : ¬ HasInvariantLineNormalForm G)
    (hnoPair : ¬ HasInvariantPairNormalForm G) :
    let V := Submodule.span C
      ((matrixTangentM (matrixVanishingIdeal H)
        (subset_matrixZeroSet_vanishingIdeal H hHone) : Submodule _ _) : Set _)
    V = ⊥ ∨ ∀ Z : Matrix (Fin 2) (Fin 2) C, Z.trace = 0 → Z ∈ V := by
  classical
  let hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈
      matrixZeroSet (C := C) (A := C) (matrixVanishingIdeal H) :=
    subset_matrixZeroSet_vanishingIdeal H hHone
  let L := matrixTangentM (matrixVanishingIdeal H) hone
  let V := Submodule.span C ((L : Submodule _ _) : Set (Matrix (Fin 2) (Fin 2) C))
  have hIS : ∀ P : DifferentialPolynomial (Fin 2 × Fin 2) C,
      (∀ g ∈ matrixZeroSet (C := C) (A := C) (matrixVanishingIdeal H),
        differentialPolynomialEvalOver (K := C) (fun q : Fin 2 × Fin 2 => g q.1 q.2) P = 0) →
      P ∈ matrixVanishingIdeal H := by
    intro P hP h hh
    exact hP h (subset_matrixZeroSet_vanishingIdeal H hh)
  have htrans : TangentTranslates (matrixVanishingIdeal H) hone :=
    tangentTranslates_of_leftTranslate _ hone
      (fun a ha P hP => leftTranslate_mem_matrixVanishingIdeal hH ha hP)
  have htrL : ∀ A ∈ L, A.trace = 0 := by
    intro A hA
    exact trace_eq_zero_of_mem_matrixTangentM hHdet hA
  have hbrL : ∀ A ∈ L, ∀ B ∈ L, A * B - B * A ∈ L := by
    intro A hA B hB
    exact bracket_mem_matrixTangentM _ htrans hIS hA hB
  have htrV : ∀ A ∈ V, A.trace = 0 := by
    intro A hA
    induction hA using Submodule.span_induction with
    | mem A hA => exact htrL A hA
    | zero => simp
    | add A B _ _ hA hB => simpa using congrArg₂ (.+.) hA hB
    | smul c A _ hA => simp [hA]
  have hbrLeft : ∀ A ∈ L, ∀ B ∈ V, A * B - B * A ∈ V := by
    intro A hA B hB
    induction hB using Submodule.span_induction with
    | mem B hB => exact Submodule.subset_span (hbrL A hA B hB)
    | zero => simp
    | add B D _ _ hB hD =>
        rw [show A * (B + D) - (B + D) * A =
          (A * B - B * A) + (A * D - D * A) by noncomm_ring]
        exact V.add_mem hB hD
    | smul c B _ hB =>
        rw [show A * (c • B) - (c • B) * A = c • (A * B - B * A) by
          simp [smul_sub]]
        exact V.smul_mem c hB
  have hbrV : ∀ A ∈ V, ∀ B ∈ V, A * B - B * A ∈ V := by
    intro A hA
    induction hA using Submodule.span_induction with
    | mem A hA => exact hbrLeft A hA
    | zero => intro B hB; simp
    | add A D _ _ hA hD =>
        intro B hB
        rw [show (A + D) * B - B * (A + D) =
          (A * B - B * A) + (D * B - B * D) by noncomm_ring]
        exact V.add_mem (hA B hB) (hD B hB)
    | smul c A _ hA =>
        intro B hB
        rw [show (c • A) * B - B * (c • A) = c • (A * B - B * A) by
          simp [smul_sub]]
        exact V.smul_mem c (hA B hB)
  have hinv' : ∀ g ∈ G, ∃ g' : Matrix (Fin 2) (Fin 2) C,
      g * g' = 1 ∧ g' * g = 1 := by
    intro g hg
    obtain ⟨g', hgg', _⟩ := hinv g hg
    exact ⟨g', hgg', mul_eq_one_comm.mp hgg'⟩
  have hstableV : ∀ g ∈ G, ∀ g' : Matrix (Fin 2) (Fin 2) C,
      g * g' = 1 → g' * g = 1 → ∀ A ∈ V, g * A * g' ∈ V := by
    intro g hg g' hgg' hg'g A hA
    obtain ⟨g'', hgg'', hstable⟩ := hinv g hg
    have hg'eq : g' = g'' := by
      calc
        g' = g' * (g * g'') := by rw [hgg'', mul_one]
        _ = (g' * g) * g'' := by rw [mul_assoc]
        _ = g'' := by rw [hg'g, one_mul]
    subst g''
    induction hA using Submodule.span_induction with
    | mem A hA => exact Submodule.subset_span (hstable A hA)
    | zero => simp
    | add A B _ _ hA hB =>
        rw [Matrix.mul_add, Matrix.add_mul]
        exact V.add_mem hA hB
    | smul c A _ hA =>
        rw [Matrix.mul_smul, Matrix.smul_mul]
        exact V.smul_mem c hA
  by_cases hdense : ∀ Z : Matrix (Fin 2) (Fin 2) C, Z.trace = 0 → Z ∈ V
  · exact Or.inr hdense
  · by_cases hV : V = ⊥
    · exact Or.inl hV
    · have hne : ∃ X ∈ V, X ≠ 0 := Submodule.exists_mem_ne_zero_of_ne_bot hV
      have hproper : ∃ Z : Matrix (Fin 2) (Fin 2) C, Z.trace = 0 ∧ Z ∉ V := by
        push Not at hdense
        exact hdense
      rcases invariant_normalForm_of_nonzero_proper_adjoint_stable
        V htrV hbrV hne hproper G hinv' hstableV with hline | hpair
      · exact False.elim (hnoLine hline)
      · exact False.elim (hnoPair hpair)

end

end GaloisForLFunctions.HTGeometry

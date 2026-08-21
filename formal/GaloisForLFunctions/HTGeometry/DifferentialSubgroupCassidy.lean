import GaloisForLFunctions.HTGeometry.Sl2TangentTraceless
import GaloisForLFunctions.HTGeometry.ScalarStabiliserRelation
import GaloisForLFunctions.HTGeometry.AdjointStableZariskiClosure
import GaloisForLFunctions.HTGeometry.DifferentialCassidyClassification
import GaloisForLFunctions.HTGeometry.BoundedLineStabiliserFinite

/-!
# Cassidy's classification for the tangent space of a differential algebraic subgroup

The pieces built for the Lie algebra of the zero set of a family of differential polynomials —
that it is a module over the constants, traceless when the family contains the determinant equation,
closed under the bracket, spanning when the group is Zariski dense, and with bounded scalar
stabilisers — assemble into a single application of Cassidy's classification.

The two hypotheses that remain are the content of the word *proper* in Cassidy's theorem: the Lie
algebra is nonzero, and the scalar stabiliser of each nonzero tangent direction is cut out by some
nonzero differential polynomial.  Both fail exactly when the group is everything.

* `matrixTangentM` — the Lie algebra, as a submodule of matrices;
* `span_conj_stable`;
* `mem_scalarStabiliser_iff_smul_mem`, `cassidy_of_matrixTangent`,
  `cassidy_of_matrixTangent_finite`, `cassidy_dichotomy`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C : Type*} [Field C] [Differential C]
variable (S : Set (DifferentialPolynomial (Fin 2 × Fin 2) C))

/-- The tangent space at the identity, as a submodule of matrices. -/
def matrixTangentM (hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ matrixZeroSet (C := C) (A := C) S) :
    Submodule (differentialConstants C) (Matrix (Fin 2) (Fin 2) C) where
  carrier := {X | dualMatrix 1 X ∈ matrixZeroSet (C := C) (A := DualNumber C) S}
  zero_mem' := by
    show dualMatrix 1 (0 : Matrix (Fin 2) (Fin 2) C)
      ∈ matrixZeroSet (C := C) (A := DualNumber C) S
    rw [← mem_matrixTangent_iff S hone]
    exact Submodule.zero_mem _
  add_mem' := by
    intro a b ha hb
    have ha' : dualMatrix 1 a ∈ matrixZeroSet (C := C) (A := DualNumber C) S := ha
    have hb' : dualMatrix 1 b ∈ matrixZeroSet (C := C) (A := DualNumber C) S := hb
    show dualMatrix 1 (a + b) ∈ matrixZeroSet (C := C) (A := DualNumber C) S
    rw [← mem_matrixTangent_iff S hone] at ha' hb' ⊢
    exact Submodule.add_mem _ ha' hb'
  smul_mem' := by
    intro c a ha
    have ha' : dualMatrix 1 a ∈ matrixZeroSet (C := C) (A := DualNumber C) S := ha
    show dualMatrix 1 (c • a) ∈ matrixZeroSet (C := C) (A := DualNumber C) S
    rw [← mem_matrixTangent_iff S hone] at ha' ⊢
    exact Submodule.smul_mem _ c ha'

@[simp] theorem mem_matrixTangentM {hone} {X : Matrix (Fin 2) (Fin 2) C} :
    X ∈ matrixTangentM S hone
      ↔ dualMatrix 1 X ∈ matrixZeroSet (C := C) (A := DualNumber C) S := Iff.rfl

omit [Differential C] in
/-- The `C`-span of a conjugation-stable set is conjugation-stable. -/
theorem span_conj_stable (L : Set (Matrix (Fin 2) (Fin 2) C))
    (g : Matrix (Fin 2) (Fin 2) C)
    (hL : ∀ A ∈ L, g * A * Matrix.adjugate g ∈ Submodule.span C L)
    {A : Matrix (Fin 2) (Fin 2) C} (hA : A ∈ Submodule.span C L) :
    g * A * Matrix.adjugate g ∈ Submodule.span C L := by
  induction hA using Submodule.span_induction with
  | mem x hx => exact hL x hx
  | zero => simp
  | add x y _ _ hx hy =>
      have heq : g * (x + y) * Matrix.adjugate g
          = g * x * Matrix.adjugate g + g * y * Matrix.adjugate g := by
        rw [mul_add, add_mul]
      rw [heq]
      exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
      have heq : g * (c • x) * Matrix.adjugate g = c • (g * x * Matrix.adjugate g) := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
      rw [heq]
      exact Submodule.smul_mem _ c hx


theorem mem_scalarStabiliser_iff_smul_mem {hone} {Y : Matrix (Fin 2) (Fin 2) C} {c : C} :
    c ∈ scalarStabiliser S Y ↔ c • Y ∈ matrixTangentM S hone := by
  rw [mem_scalarStabiliser, mem_matrixTangentM, ← mem_matrixTangent_iff S hone]
  exact Iff.rfl

/-- **Cassidy's classification for the tangent space of a differential algebraic subgroup of
`SL₂`.**  The two remaining hypotheses are the content of the word *proper*: the Lie algebra is
nonzero, and each nonzero tangent direction has a scalar stabiliser cut out by a nonzero
differential polynomial. -/
theorem cassidy_of_matrixTangent
    [IsAlgClosed C] [CharZero C] [IsAlgClosed (differentialConstants C)]
    (hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ matrixZeroSet (C := C) (A := C) S)
    (hdet : detPoly (C := C) ∈ S)
    (hmulBi : ∀ u ∈ matrixZeroSet (C := C) (A := BiDual C) S,
      ∀ v ∈ matrixZeroSet (C := C) (A := BiDual C) S,
      u * v ∈ matrixZeroSet (C := C) (A := BiDual C) S)
    (G : Set (Matrix (Fin 2) (Fin 2) C))
    (hGstable : ∀ g ∈ G, ∀ A ∈ matrixTangentM S hone,
      g * A * Matrix.adjugate g
        ∈ Submodule.span C ((matrixTangentM S hone : Submodule _ _) : Set _))
    (hdensePoly : ∀ (A : Matrix (Fin 2) (Fin 2) C) (φ : Matrix (Fin 2) (Fin 2) C →ₗ[C] C),
      (∀ h ∈ G, φ (h * A * Matrix.adjugate h) = 0) →
      ∀ g : Matrix (Fin 2) (Fin 2) C, g.det = 1 → φ (g * A * Matrix.adjugate g) = 0)
    (hLne : ∃ A ∈ matrixTangentM S hone, A ≠ 0)
    (hsolres : ∀ Y ∈ matrixTangentM S hone, Y ≠ 0 →
      ∃ P : DifferentialPolynomial Unit C, P ≠ 0 ∧
        ∀ c ∈ scalarStabiliser S Y,
          differentialPolynomialEvalOver (K := C) (fun _ : Unit => c) P = 0) :
    ∃ P Q : Matrix (Fin 2) (Fin 2) C, P * Q = 1 ∧ Q * P = 1 ∧
      (matrixTangentM S hone).map (conjLinear (differentialConstants C) P Q)
        = Submodule.span (differentialConstants C) {sl2H C, sl2E C, sl2F C} := by
  classical
  set L := matrixTangentM S hone with hL
  have htr : ∀ A ∈ L, A.trace = 0 := by
    intro A hA
    rw [Matrix.trace_fin_two]
    exact trace_eq_zero_of_mem_zeroSet hdet hA
  have hbr : ∀ A ∈ L, ∀ B ∈ L, A * B - B * A ∈ L := by
    intro A hA B hB
    exact bracket_mem_zeroSet_of_one S hone hmulBi hA hB
  have hdense : ∀ Z : Matrix (Fin 2) (Fin 2) C, Z.trace = 0 →
      Z ∈ Submodule.span C ((L : Submodule _ _) : Set (Matrix (Fin 2) (Fin 2) C)) := by
    intro Z hZ
    obtain ⟨A, hA, hAne⟩ := hLne
    refine sl2_of_dense (Submodule.span C ((L : Submodule _ _) : Set _)) G ?_ hdensePoly
      (Submodule.subset_span hA) hAne ?_ ?_
    · intro g hg B hB
      exact span_conj_stable _ g (fun x hx => hGstable g hg x hx) hB
    · have hA0 := htr A hA
      rw [Matrix.trace_fin_two] at hA0
      linear_combination hA0
    · rw [Matrix.trace_fin_two] at hZ
      linear_combination hZ
  have hsol : ∀ Y ∈ L, Y ≠ 0 → ∃ (n : ℕ) (a : Fin n → C), ∀ c : C, c • Y ∈ L →
      differentialJet n c = ∑ i : Fin n, a i * differentialJet (i : ℕ) c := by
    intro Y hY hYne
    obtain ⟨P, hPne, hPT⟩ := hsolres Y hY hYne
    obtain ⟨m, a, ha⟩ := exists_monic_relation_scalarStabiliser S Y hPne hPT
    refine ⟨m, a, fun c hc => ha c ?_⟩
    exact (mem_scalarStabiliser_iff_smul_mem S).mpr hc
  exact cassidy_sl2_of_differentialSolution L htr hbr hdense hsol

/-- **Cassidy's classification for the tangent space, with finite dimension in place of the
line-stabiliser hypothesis.**  The two remaining hypotheses are the dimension statements: the Lie
algebra is finite dimensional over the constants and nonzero.  Both fail exactly when the group is
everything. -/
theorem cassidy_of_matrixTangent_finite
    [IsAlgClosed C] [CharZero C] [IsAlgClosed (differentialConstants C)]
    (hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ matrixZeroSet (C := C) (A := C) S)
    (hdet : detPoly (C := C) ∈ S)
    (hmulBi : ∀ u ∈ matrixZeroSet (C := C) (A := BiDual C) S,
      ∀ v ∈ matrixZeroSet (C := C) (A := BiDual C) S,
      u * v ∈ matrixZeroSet (C := C) (A := BiDual C) S)
    (G : Set (Matrix (Fin 2) (Fin 2) C))
    (hGstable : ∀ g ∈ G, ∀ A ∈ matrixTangentM S hone,
      g * A * Matrix.adjugate g
        ∈ Submodule.span C ((matrixTangentM S hone : Submodule _ _) : Set _))
    (hdensePoly : ∀ (A : Matrix (Fin 2) (Fin 2) C) (φ : Matrix (Fin 2) (Fin 2) C →ₗ[C] C),
      (∀ h ∈ G, φ (h * A * Matrix.adjugate h) = 0) →
      ∀ g : Matrix (Fin 2) (Fin 2) C, g.det = 1 → φ (g * A * Matrix.adjugate g) = 0)
    (hLne : ∃ A ∈ matrixTangentM S hone, A ≠ 0)
    (hfin : FiniteDimensional (differentialConstants C) (matrixTangentM S hone)) :
    ∃ P Q : Matrix (Fin 2) (Fin 2) C, P * Q = 1 ∧ Q * P = 1 ∧
      (matrixTangentM S hone).map (conjLinear (differentialConstants C) P Q)
        = Submodule.span (differentialConstants C) {sl2H C, sl2E C, sl2F C} := by
  classical
  haveI := hfin
  set L := matrixTangentM S hone with hL
  have htr : ∀ A ∈ L, A.trace = 0 := by
    intro A hA
    rw [Matrix.trace_fin_two]
    exact trace_eq_zero_of_mem_zeroSet hdet hA
  have hbr : ∀ A ∈ L, ∀ B ∈ L, A * B - B * A ∈ L := by
    intro A hA B hB
    exact bracket_mem_zeroSet_of_one S hone hmulBi hA hB
  have hdense : ∀ Z : Matrix (Fin 2) (Fin 2) C, Z.trace = 0 →
      Z ∈ Submodule.span C ((L : Submodule _ _) : Set (Matrix (Fin 2) (Fin 2) C)) := by
    intro Z hZ
    obtain ⟨A, hA, hAne⟩ := hLne
    refine sl2_of_dense (Submodule.span C ((L : Submodule _ _) : Set _)) G ?_ hdensePoly
      (Submodule.subset_span hA) hAne ?_ ?_
    · intro g hg B hB
      exact span_conj_stable _ g (fun x hx => hGstable g hg x hx) hB
    · have hA0 := htr A hA
      rw [Matrix.trace_fin_two] at hA0
      linear_combination hA0
    · rw [Matrix.trace_fin_two] at hZ
      linear_combination hZ
  exact cassidy_sl2_of_finiteDimensional L htr hbr hdense

/-- **The properness dichotomy.**  Either the Lie algebra is infinite dimensional over the
constants — which is what happens when the group is the whole of `SL₂` — or one conjugation carries
it onto the constant span of `h`, `e`, `f`.  Nothing else can occur, and the second branch is
proved outright. -/
theorem cassidy_dichotomy
    [IsAlgClosed C] [CharZero C] [IsAlgClosed (differentialConstants C)]
    (hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ matrixZeroSet (C := C) (A := C) S)
    (hdet : detPoly (C := C) ∈ S)
    (hmulBi : ∀ u ∈ matrixZeroSet (C := C) (A := BiDual C) S,
      ∀ v ∈ matrixZeroSet (C := C) (A := BiDual C) S,
      u * v ∈ matrixZeroSet (C := C) (A := BiDual C) S)
    (G : Set (Matrix (Fin 2) (Fin 2) C))
    (hGstable : ∀ g ∈ G, ∀ A ∈ matrixTangentM S hone,
      g * A * Matrix.adjugate g
        ∈ Submodule.span C ((matrixTangentM S hone : Submodule _ _) : Set _))
    (hdensePoly : ∀ (A : Matrix (Fin 2) (Fin 2) C) (φ : Matrix (Fin 2) (Fin 2) C →ₗ[C] C),
      (∀ h ∈ G, φ (h * A * Matrix.adjugate h) = 0) →
      ∀ g : Matrix (Fin 2) (Fin 2) C, g.det = 1 → φ (g * A * Matrix.adjugate g) = 0)
    (hLne : ∃ A ∈ matrixTangentM S hone, A ≠ 0) :
    ¬ FiniteDimensional (differentialConstants C) (matrixTangentM S hone)
      ∨ ∃ P Q : Matrix (Fin 2) (Fin 2) C, P * Q = 1 ∧ Q * P = 1 ∧
          (matrixTangentM S hone).map (conjLinear (differentialConstants C) P Q)
            = Submodule.span (differentialConstants C) {sl2H C, sl2E C, sl2F C} := by
  by_cases hfin : FiniteDimensional (differentialConstants C) (matrixTangentM S hone)
  · exact Or.inr (cassidy_of_matrixTangent_finite S hone hdet hmulBi G hGstable hdensePoly
      hLne hfin)
  · exact Or.inl hfin

end

end GaloisForLFunctions.HTGeometry

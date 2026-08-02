import GaloisForLFunctions.HTGeometry.HermitianFlagRealization
import GaloisForLFunctions.HTGeometry.LatticeFrame
import GaloisForLFunctions.HTGeometry.CompactCommutingFlowDecomposition

/-!
# Degeneration flags and apartments

The eigenlines of a Hermitian direction are an independent family of lines spanning the space — a
frame — and every member of the direction's degeneration flag is the span of a subfamily.  So the
flag lies in the apartment of the frame of eigenlines.

Two commuting directions have a joint eigenbasis: the eigenspaces of one are invariant under the
other, so diagonalizing inside each of them produces one frame diagonalizing both.  Their flags then
lie in a *single* apartment, which is the statement that commuting directions span one maximal flat
and give one apartment at infinity.
-/

namespace GaloisForLFunctions.HTGeometry

open Module Module.End

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {S T : E →ₗ[ℂ] E}

/-! ## The frame of the lines of a basis -/

/-- **The frame of eigenlines of a basis**: the lines of a basis are independent atoms spanning the
space. -/
noncomputable def basisFrame {ι : Type} (b : Basis ι ℂ E) :
    LatticeFrame (Submodule ℂ E) ι ⊤ where
  atom i := ℂ ∙ b i
  isAtom i := Submodule.isAtom_iff_finrank_eq_one.2 (finrank_span_singleton (b.ne_zero i))
  indep := b.linearIndependent.iSupIndep_span_singleton
  sup_eq := by rw [← Submodule.span_range_eq_iSup, b.span_eq]

omit [FiniteDimensional ℂ E] in
theorem basisFrame_atom {ι : Type} (b : Basis ι ℂ E) (i : ι) :
    (basisFrame b).atom i = (ℂ ∙ b i) := rfl

omit [FiniteDimensional ℂ E] in
theorem basisFrame_span {ι : Type} (b : Basis ι ℂ E) (s : Set ι) :
    (basisFrame b).span s = Submodule.span ℂ (b '' s) := by
  rw [Set.image_eq_iUnion, Submodule.span_iUnion₂]
  rfl

omit [FiniteDimensional ℂ E] in
/-- **The degeneration flag of a direction lies in the apartment of an eigenframe.** -/
theorem eigenSum_eq_basisFrame_span {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι ℂ E)
    {w : ι → ℝ} (hd : ∀ i, T (b i) = (w i : ℂ) • b i) (c : ℝ) :
    eigenSum T c = (basisFrame b).span {i | c < w i} := by
  rw [basisFrame_span, eigenSum_eq_span_of_eigenbasis b hd c]

/-! ## A joint eigenbasis for commuting directions -/

omit [FiniteDimensional ℂ E] in
theorem isSymmetric_restrict (hS : S.IsSymmetric) {W : Submodule ℂ E}
    (hW : ∀ x ∈ W, S x ∈ W) : (S.restrict hW).IsSymmetric := by
  intro x y
  have h1 : inner ℂ ((S.restrict hW) x : E) (y : E) = inner ℂ (S (x : E)) (y : E) := by
    rw [LinearMap.restrict_apply]
  have h2 : inner ℂ (x : E) ((S.restrict hW) y : E) = inner ℂ (x : E) (S (y : E)) := by
    rw [LinearMap.restrict_apply]
  have h3 : inner ℂ (S (x : E)) (y : E) = inner ℂ (x : E) (S (y : E)) := hS _ _
  show inner ℂ ((S.restrict hW) x : E) (y : E) = inner ℂ (x : E) ((S.restrict hW) y : E)
  rw [h1, h2, h3]

/-- **Commuting Hermitian directions have a joint eigenbasis.**  The eigenspaces of one are
invariant under the other, and diagonalizing inside each of them gives one basis of joint
eigenvectors. -/
theorem exists_joint_eigenbasis (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (hcomm : ∀ x, S (T x) = T (S x)) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Basis ι ℂ E) (wS wT : ι → ℝ),
      (∀ i, S (b i) = (wS i : ℂ) • b i) ∧ (∀ i, T (b i) = (wT i : ℂ) • b i) := by
  classical
  have hint : DirectSum.IsInternal
      (fun μ : Module.End.Eigenvalues T => Module.End.eigenspace T (μ : ℂ)) :=
    hT.direct_sum_isInternal
  have hinv : ∀ μ : Module.End.Eigenvalues T,
      ∀ x ∈ Module.End.eigenspace T (μ : ℂ), S x ∈ Module.End.eigenspace T (μ : ℂ) :=
    fun μ => mapsTo_eigenspace_of_commute T S (fun x => (hcomm x).symm) (μ : ℂ)
  have hsym : ∀ μ : Module.End.Eigenvalues T, (S.restrict (hinv μ)).IsSymmetric :=
    fun μ => isSymmetric_restrict hS _
  refine ⟨_, inferInstance, inferInstance,
    hint.collectedBasis (fun μ => ((hsym μ).eigenvectorBasis rfl).toBasis),
    fun x => (hsym x.1).eigenvalues rfl x.2, fun x => (x.1 : ℂ).re, fun x => ?_, fun x => ?_⟩
  · have hmem : (hint.collectedBasis (fun μ => ((hsym μ).eigenvectorBasis rfl).toBasis)) x
        = ((((hsym x.1).eigenvectorBasis rfl).toBasis x.2 :
          ↥(Module.End.eigenspace T (x.1 : ℂ))) : E) := by
      rw [hint.collectedBasis_coe]
    rw [hmem]
    have hres : (S.restrict (hinv x.1)) (((hsym x.1).eigenvectorBasis rfl).toBasis x.2)
        = (((hsym x.1).eigenvalues rfl x.2 : ℝ) : ℂ)
          • ((hsym x.1).eigenvectorBasis rfl).toBasis x.2 := by
      rw [OrthonormalBasis.coe_toBasis]
      exact (hsym x.1).apply_eigenvectorBasis rfl x.2
    have hcoe := congrArg (fun y : ↥(Module.End.eigenspace T (x.1 : ℂ)) => (y : E)) hres
    simpa [LinearMap.restrict_apply] using hcoe
  · have hmem : (hint.collectedBasis (fun μ => ((hsym μ).eigenvectorBasis rfl).toBasis)) x
        = ((((hsym x.1).eigenvectorBasis rfl).toBasis x.2 :
          ↥(Module.End.eigenspace T (x.1 : ℂ))) : E) := by
      rw [hint.collectedBasis_coe]
    have hreal : (((x.1 : ℂ).re : ℝ) : ℂ) = (x.1 : ℂ) :=
      Complex.conj_eq_iff_re.1 (hT.conj_eigenvalue_eq_self x.1.2)
    rw [hmem, hreal]
    exact mem_eigenspace_iff.1 (((hsym x.1).eigenvectorBasis rfl).toBasis x.2).2

/-! ## One apartment for commuting directions -/

/-- **The flag of a Hermitian direction lies in one apartment**, the apartment of the frame of its
eigenlines. -/
theorem exists_frame_eigenSum_span (hT : T.IsSymmetric) :
    ∃ (ι : Type) (F : LatticeFrame (Submodule ℂ E) ι ⊤),
      ∀ c : ℝ, ∃ s : Set ι, eigenSum T c = F.span s := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, finrank ℂ E = n := ⟨_, rfl⟩
  refine ⟨Fin n, basisFrame (hT.eigenvectorBasis hn).toBasis, fun c => ?_⟩
  refine ⟨{i | c < hT.eigenvalues hn i}, eigenSum_eq_basisFrame_span _
    (w := fun i => hT.eigenvalues hn i) (fun i => ?_) c⟩
  rw [OrthonormalBasis.coe_toBasis]
  exact hT.apply_eigenvectorBasis hn i

/-- **Commuting directions give one apartment.**  Two commuting Hermitian directions have all their
degeneration flags inside the apartment of a single frame: they span one maximal flat, and their
simplices at infinity lie in one apartment. -/
theorem exists_frame_eigenSum_span_commuting (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (hcomm : ∀ x, S (T x) = T (S x)) :
    ∃ (ι : Type) (F : LatticeFrame (Submodule ℂ E) ι ⊤),
      (∀ c : ℝ, ∃ s : Set ι, eigenSum S c = F.span s) ∧
        ∀ c : ℝ, ∃ s : Set ι, eigenSum T c = F.span s := by
  classical
  obtain ⟨ι, hfin, hdec, b, wS, wT, hbS, hbT⟩ := exists_joint_eigenbasis hS hT hcomm
  exact ⟨ι, basisFrame b,
    fun c => ⟨{i | c < wS i}, eigenSum_eq_basisFrame_span b hbS c⟩,
    fun c => ⟨{i | c < wT i}, eigenSum_eq_basisFrame_span b hbT c⟩⟩

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.AllVertexGoodLeafExtensionChart

/-!
# Continuous physical probes in the full local-extension chart

Canonical adjugate eigenvectors and their Hermitian probe amplitudes are
extended from the anchor-star line to the full finite-dimensional physical
chart.  Their continuity is the missing local-stability input for
intersecting all-vertex observability with generic maximal spectral rank.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology
open scoped Matrix.Norms.Elementwise

/-- Adjugation preserves entrywise analyticity for arbitrary
finite-dimensional complex parameter spaces. -/
theorem analyticAt_matrix_adjugate_apply_finiteParameter
    {P ι : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [Fintype ι] [DecidableEq ι]
    {M : P → Matrix ι ι ℂ} {p₀ : P}
    (hM : ∀ i j, AnalyticAt ℂ (fun p => M p i j) p₀)
    (i j : ι) :
    AnalyticAt ℂ (fun p => (M p).adjugate i j) p₀ := by
  have heq :
      (fun p => (M p).adjugate i j) =
        fun p => ((M p).updateRow j (Pi.single i 1)).det := by
    funext p
    exact Matrix.adjugate_apply (M p) i j
  rw [heq]
  apply analyticAt_matrix_det_parametric
  intro r c
  by_cases hr : r = j
  · subst r
    simp only [Matrix.updateRow_self]
    exact analyticAt_const
  · simp [Matrix.updateRow, hr]
    exact hM r c

/-- Characteristic matrix of one labeled chart branch. -/
def LocalExtensionEigenbranchChart.characteristicMatrix
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ)
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    (x : I × ρ)
    (p : (ρ → ℂ) × Matrix ρ ρ ℂ) :
    Matrix (I × ρ) (I × ρ) ℂ :=
  Matrix.scalar (I × ρ) (C.branch x p) -
    localExtensionMatrix energy p.1 attachment p.2

/-- One canonical adjugate column in the full chart. -/
def LocalExtensionEigenbranchChart.adjugateColumn
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ)
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    (x : I × ρ)
    (p : (ρ → ℂ) × Matrix ρ ρ ℂ) :
    I × ρ → ℂ :=
  fun i => (C.characteristicMatrix
    energy shift attachment x p).adjugate i x

/-- Every coordinate of a chart adjugate column is analytic at every point
inside the common branch chart. -/
theorem LocalExtensionEigenbranchChart.adjugateColumn_analyticAt
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ)
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    (x : I × ρ)
    (p₀ : (ρ → ℂ) × Matrix ρ ρ ℂ)
    (hp₀ : p₀ ∈ C.U) (i : I × ρ) :
    AnalyticAt ℂ
      (fun p =>
        C.adjugateColumn
          energy shift attachment x p i) p₀ := by
  apply analyticAt_matrix_adjugate_apply_finiteParameter
  intro r c
  have hbranch := C.analyticOn_branch x p₀ hp₀
  have hlocalMatrix :=
    localExtensionMatrix_analyticAt energy attachment p₀
  have hlocal :
      AnalyticAt ℂ
        (fun p =>
          localExtensionMatrix energy p.1 attachment p.2 r c) p₀ := by
    let row :
        Matrix (I × ρ) (I × ρ) ℂ →L[ℂ]
          (I × ρ → ℂ) :=
      ContinuousLinearMap.proj (R := ℂ) r
    let col : (I × ρ → ℂ) →L[ℂ] ℂ :=
      ContinuousLinearMap.proj (R := ℂ) c
    exact
      ((col.comp row).analyticAt
        (localExtensionMatrix energy p₀.1 attachment p₀.2)).fun_comp_of_eq
        hlocalMatrix rfl
  by_cases hrc : r = c
  · subst c
    simp only [LocalExtensionEigenbranchChart.characteristicMatrix,
      Matrix.sub_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq]
    exact hbranch.sub hlocal
  · simp only [LocalExtensionEigenbranchChart.characteristicMatrix,
      Matrix.sub_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply_ne _ hrc, zero_sub]
    exact hlocal.neg

/-- Physical Hermitian probe amplitude between two canonical chart
eigenvectors. -/
def LocalExtensionEigenbranchChart.sesquilinearProbe
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ)
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    (x y : I × ρ)
    (O : Matrix (I × ρ) (I × ρ) ℂ)
    (p : (ρ → ℂ) × Matrix ρ ρ ℂ) : ℂ :=
  ∑ i, ∑ j,
    star
        (C.adjugateColumn
          energy shift attachment x p i) *
      O i j *
      C.adjugateColumn
        energy shift attachment y p j

/-- Every physical chart probe amplitude is continuous at every point of
the common simple-spectrum chart. -/
theorem LocalExtensionEigenbranchChart.sesquilinearProbe_continuousAt
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ)
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    (x y : I × ρ)
    (O : Matrix (I × ρ) (I × ρ) ℂ)
    (p₀ : (ρ → ℂ) × Matrix ρ ρ ℂ)
    (hp₀ : p₀ ∈ C.U) :
    ContinuousAt
      (C.sesquilinearProbe
        energy shift attachment x y O) p₀ := by
  unfold LocalExtensionEigenbranchChart.sesquilinearProbe
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro j hj
  exact
    (((C.adjugateColumn_analyticAt
      energy shift attachment x p₀ hp₀ i).continuousAt.star.mul
        continuousAt_const).mul
      (C.adjugateColumn_analyticAt
        energy shift attachment y p₀ hp₀ j).continuousAt)

/-- On the anchor-star line, the full-chart amplitude is exactly the
previous affine eigenbranch amplitude. -/
theorem LocalExtensionEigenbranchChart.sesquilinearProbe_anchorStar
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ)
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    (anchor : ρ) (x y : I × ρ)
    (O : Matrix (I × ρ) (I × ρ) ℂ) (t : ℂ) :
    C.sesquilinearProbe energy shift attachment x y O
        (shift, t • anchorStarLayerEdge anchor) =
      affineEigenbranchSesquilinearMatrixProbe
        (layeredEnergy energy shift)
        (layerMatrixCoupling attachment
          (anchorStarLayerEdge anchor))
        (C.anchorStarBranch
          energy shift attachment anchor x)
        (C.anchorStarBranch
          energy shift attachment anchor y)
        O x y t := by
  have hchar (z : I × ρ) :
      C.characteristicMatrix energy shift attachment z
          (shift, t • anchorStarLayerEdge anchor) =
        affineBranchCharacteristicMatrix
          (layeredEnergy energy shift)
          (layerMatrixCoupling attachment
            (anchorStarLayerEdge anchor))
          (C.anchorStarBranch
            energy shift attachment anchor z) t := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [LocalExtensionEigenbranchChart.characteristicMatrix,
        LocalExtensionEigenbranchChart.anchorStarBranch,
        affineBranchCharacteristicMatrix,
        localExtensionMatrix, layerMatrixCoupling_smul,
        Matrix.scalar_apply]
      <;> ring
    · simp [LocalExtensionEigenbranchChart.characteristicMatrix,
        LocalExtensionEigenbranchChart.anchorStarBranch,
        affineBranchCharacteristicMatrix,
        localExtensionMatrix, layerMatrixCoupling_smul,
        Matrix.scalar_apply, hij]
  unfold LocalExtensionEigenbranchChart.sesquilinearProbe
    affineEigenbranchSesquilinearMatrixProbe
    LocalExtensionEigenbranchChart.adjugateColumn
    affineEigenbranchAdjugateColumn
  simp_rw [hchar]

end

end GaloisForLFunctions.HTGeometry

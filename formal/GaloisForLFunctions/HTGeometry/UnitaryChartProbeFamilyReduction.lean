import GaloisForLFunctions.HTGeometry.ChartProbeFamilyReduction
import GaloisForLFunctions.HTGeometry.SimpleSpectrumEigenline

/-!
# Unitary chart probes

Adjugate columns are useful analytic eigenvector representatives, but their
matrix is generally not unitary.  This file matches every simple chart branch
with the canonical orthonormal eigenbasis of the physical Hermitian matrix.
It then proves that chart support injects into support measured in those exact
unitary spectral coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- At every Hermitian point of a simple chart, chart labels and canonical
Hermitian eigenvalue labels differ by a permutation. -/
theorem LocalExtensionEigenbranchChart.exists_eigenvalueEquiv
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ)
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    (p : (ρ → ℂ) × Matrix ρ ρ ℂ)
    (hp : p ∈ C.U)
    (hH :
      (localExtensionMatrix energy p.1 attachment p.2).IsHermitian) :
    ∃ e : (I × ρ) ≃ (I × ρ),
      ∀ i,
        C.realBranchEnergy energy shift attachment p i =
          hH.eigenvalues (e i) := by
  have happears :
      ∀ i, ∃ j,
        C.realBranchEnergy energy shift attachment p i =
          hH.eigenvalues j := by
    intro i
    have hpoly :
        Polynomial.IsRoot
          (localExtensionMatrix energy p.1 attachment p.2).charpoly
          (C.branch i p) := by
      change
        (localExtensionMatrix energy p.1 attachment p.2).charpoly.eval
            (C.branch i p) = 0
      rw [Matrix.eval_charpoly]
      exact C.root p hp i
    have hspectrum :
        C.branch i p ∈
          spectrum ℂ
            (localExtensionMatrix energy p.1 attachment p.2) :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hpoly
    rw [hH.spectrum_eq_image_range] at hspectrum
    obtain ⟨r, ⟨j, rfl⟩, hj⟩ := hspectrum
    refine ⟨j, ?_⟩
    have hbranch :
        C.branch i p = (hH.eigenvalues j : ℂ) :=
      hj.symm
    exact congrArg Complex.re hbranch
  choose σ hσ using happears
  have hσInjective : Function.Injective σ := by
    intro i j hij
    apply C.simple p hp
    change C.branch i p = C.branch j p
    rw [C.branch_eq_realBranchEnergy
      energy shift attachment p hp hH i]
    rw [C.branch_eq_realBranchEnergy
      energy shift attachment p hp hH j]
    rw [hσ i, hσ j, hij]
  exact ⟨Equiv.ofBijective σ
      ⟨hσInjective, Finite.surjective_of_injective hσInjective⟩,
    hσ⟩

/-- Canonical unitary eigenvector matrix, with columns relabeled by chart
branches. -/
def LocalExtensionEigenbranchChart.unitaryEigenvectorMatrix
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    {energy : I → ℂ} {shift : ρ → ℂ}
    {attachment : Matrix I I ℂ}
    (_C : LocalExtensionEigenbranchChart energy shift attachment)
    {p : (ρ → ℂ) × Matrix ρ ρ ℂ}
    (hH :
      (localExtensionMatrix energy p.1 attachment p.2).IsHermitian)
    (e : (I × ρ) ≃ (I × ρ)) :
    Matrix (I × ρ) (I × ρ) ℂ :=
  fun i x => hH.eigenvectorUnitary i (e x)

/-- Relabeling columns of a unitary matrix preserves the left unitary
identity. -/
theorem LocalExtensionEigenbranchChart.star_unitaryEigenvectorMatrix_mul_self
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    {energy : I → ℂ} {shift : ρ → ℂ}
    {attachment : Matrix I I ℂ}
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    {p : (ρ → ℂ) × Matrix ρ ρ ℂ}
    (hH :
      (localExtensionMatrix energy p.1 attachment p.2).IsHermitian)
    (e : (I × ρ) ≃ (I × ρ)) :
    star (C.unitaryEigenvectorMatrix hH e) *
        C.unitaryEigenvectorMatrix hH e = 1 := by
  ext x y
  have hentry := congrArg
    (fun M : Matrix (I × ρ) (I × ρ) ℂ => M (e x) (e y))
    (Unitary.coe_star_mul_self hH.eigenvectorUnitary)
  simpa [LocalExtensionEigenbranchChart.unitaryEigenvectorMatrix,
    Matrix.mul_apply, Matrix.one_apply, e.injective.eq_iff] using hentry

/-- Relabeling columns of a unitary matrix preserves the right unitary
identity. -/
theorem LocalExtensionEigenbranchChart.unitaryEigenvectorMatrix_mul_star_self
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    {energy : I → ℂ} {shift : ρ → ℂ}
    {attachment : Matrix I I ℂ}
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    {p : (ρ → ℂ) × Matrix ρ ρ ℂ}
    (hH :
      (localExtensionMatrix energy p.1 attachment p.2).IsHermitian)
    (e : (I × ρ) ≃ (I × ρ)) :
    C.unitaryEigenvectorMatrix hH e *
        star (C.unitaryEigenvectorMatrix hH e) = 1 := by
  ext x y
  have hentry := congrArg
    (fun M : Matrix (I × ρ) (I × ρ) ℂ => M x y)
    (Unitary.coe_mul_star_self hH.eigenvectorUnitary)
  change
    (∑ k,
      hH.eigenvectorUnitary x (e k) *
        star (hH.eigenvectorUnitary y (e k))) =
      (1 : Matrix (I × ρ) (I × ρ) ℂ) x y
  rw [e.sum_comp
    (fun k =>
      hH.eigenvectorUnitary x k *
        star (hH.eigenvectorUnitary y k))]
  simpa [Matrix.mul_apply] using hentry

/-- The relabeled canonical eigenvector matrix is genuinely unitary. -/
theorem LocalExtensionEigenbranchChart.unitaryEigenvectorMatrix_mem_unitary
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    {energy : I → ℂ} {shift : ρ → ℂ}
    {attachment : Matrix I I ℂ}
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    {p : (ρ → ℂ) × Matrix ρ ρ ℂ}
    (hH :
      (localExtensionMatrix energy p.1 attachment p.2).IsHermitian)
    (e : (I × ρ) ≃ (I × ρ)) :
    C.unitaryEigenvectorMatrix hH e ∈
      Matrix.unitaryGroup (I × ρ) ℂ :=
  ⟨C.star_unitaryEigenvectorMatrix_mul_self hH e,
    C.unitaryEigenvectorMatrix_mul_star_self hH e⟩

/-- Exact reconstruction of the physical local-extension Hamiltonian from
the chart-labeled energy packet and the relabeled orthonormal eigenbasis. -/
theorem LocalExtensionEigenbranchChart.localExtensionMatrix_eq_unitary_diagonal
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ)
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    (p : (ρ → ℂ) × Matrix ρ ρ ℂ)
    (hH :
      (localExtensionMatrix energy p.1 attachment p.2).IsHermitian)
    (e : (I × ρ) ≃ (I × ρ))
    (he :
      ∀ i,
        C.realBranchEnergy energy shift attachment p i =
          hH.eigenvalues (e i)) :
    localExtensionMatrix energy p.1 attachment p.2 =
      C.unitaryEigenvectorMatrix hH e *
        Matrix.diagonal
          (fun i =>
            (C.realBranchEnergy
              energy shift attachment p i : ℂ)) *
        star (C.unitaryEigenvectorMatrix hH e) := by
  let H := localExtensionMatrix energy p.1 attachment p.2
  let U := C.unitaryEigenvectorMatrix hH e
  let D : Matrix (I × ρ) (I × ρ) ℂ :=
    Matrix.diagonal
      (fun i =>
        (C.realBranchEnergy
          energy shift attachment p i : ℂ))
  have hHU : H * U = U * D := by
    ext i x
    have hx := congrFun (hH.mulVec_eigenvectorBasis (e x)) i
    change
      (∑ k, H i k * U k x) =
        ∑ k, U i k * D k x
    simpa [H, U, D,
      LocalExtensionEigenbranchChart.unitaryEigenvectorMatrix,
      Matrix.mulVec_apply, dotProduct, Matrix.diagonal_apply,
      he x, RCLike.real_smul_eq_coe_smul, mul_comm] using hx
  calc
    H = H * 1 := by rw [mul_one]
    _ = H * (U * star U) := by
      rw [C.unitaryEigenvectorMatrix_mul_star_self hH e]
    _ = (H * U) * star U := by rw [Matrix.mul_assoc]
    _ = (U * D) * star U := by rw [hHU]
    _ = U * D * star U := rfl

/-- Exact physical-probe matrix in the orthonormal spectral coordinates
carrying the chart labels. -/
def LocalExtensionEigenbranchChart.unitaryProbeMatrix
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    {energy : I → ℂ} {shift : ρ → ℂ}
    {attachment : Matrix I I ℂ}
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    {p : (ρ → ℂ) × Matrix ρ ρ ℂ}
    (hH :
      (localExtensionMatrix energy p.1 attachment p.2).IsHermitian)
    (e : (I × ρ) ≃ (I × ρ))
    (O : Matrix (I × ρ) (I × ρ) ℂ) :
    Matrix (I × ρ) (I × ρ) ℂ :=
  star (C.unitaryEigenvectorMatrix hH e) * O *
    C.unitaryEigenvectorMatrix hH e

/-- Hermiticity is preserved in exact unitary spectral coordinates. -/
theorem LocalExtensionEigenbranchChart.unitaryProbeMatrix_isHermitian
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    {energy : I → ℂ} {shift : ρ → ℂ}
    {attachment : Matrix I I ℂ}
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    {p : (ρ → ℂ) × Matrix ρ ρ ℂ}
    (hH :
      (localExtensionMatrix energy p.1 attachment p.2).IsHermitian)
    (e : (I × ρ) ≃ (I × ρ))
    (O : Matrix (I × ρ) (I × ρ) ℂ)
    (hO : O.IsHermitian) :
    (C.unitaryProbeMatrix hH e O).IsHermitian := by
  exact Matrix.isHermitian_conjTranspose_mul_mul _ hO

/-- Every canonical adjugate column at a chart point satisfies the exact
physical eigenvector equation. -/
theorem LocalExtensionEigenbranchChart.mulVec_adjugateColumn
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ)
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    (p : (ρ → ℂ) × Matrix ρ ρ ℂ)
    (hp : p ∈ C.U)
    (x : I × ρ) :
    Matrix.mulVec
        (localExtensionMatrix energy p.1 attachment p.2)
        (C.adjugateColumn energy shift attachment x p) =
      C.branch x p •
        C.adjugateColumn energy shift attachment x p := by
  let A :=
    C.characteristicMatrix energy shift attachment x p
  let v :=
    C.adjugateColumn energy shift attachment x p
  have hdet : A.det = 0 := by
    simpa [A, LocalExtensionEigenbranchChart.characteristicMatrix,
      matrixCharpolyRelation] using C.root p hp x
  have hzero : Matrix.mulVec A v = 0 := by
    funext i
    have hmatrix := Matrix.mul_adjugate A
    have hentry :=
      congrArg (fun M : Matrix (I × ρ) (I × ρ) ℂ => M i x) hmatrix
    change (∑ j, A i j * v j) = 0
    simpa [v, LocalExtensionEigenbranchChart.adjugateColumn,
      Matrix.mul_apply, hdet] using hentry
  change
    Matrix.mulVec
        (localExtensionMatrix energy p.1 attachment p.2) v =
      C.branch x p • v
  have hzero' :
      (Matrix.scalar (I × ρ) (C.branch x p) -
          localExtensionMatrix energy p.1 attachment p.2).mulVec v = 0 := by
    simpa [A, LocalExtensionEigenbranchChart.characteristicMatrix] using hzero
  rw [Matrix.sub_mulVec] at hzero'
  funext i
  have hi := congrFun hzero' i
  simp [Matrix.mulVec_apply, Matrix.scalar_apply] at hi
  change
    (localExtensionMatrix energy p.1 attachment p.2).row i ⬝ᵥ v =
      C.branch x p * v i
  exact (sub_eq_zero.mp hi).symm

/-- A chart adjugate eigenvector is a scalar multiple of the relabeled
canonical unit vector.  No nonzero assumption on the adjugate column is
needed. -/
theorem LocalExtensionEigenbranchChart.adjugateColumn_eq_smul_unitaryColumn
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ)
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    (p : (ρ → ℂ) × Matrix ρ ρ ℂ)
    (hp : p ∈ C.U)
    (hH :
      (localExtensionMatrix energy p.1 attachment p.2).IsHermitian)
    (e : (I × ρ) ≃ (I × ρ))
    (he :
      ∀ i,
        C.realBranchEnergy energy shift attachment p i =
          hH.eigenvalues (e i))
    (x : I × ρ) :
    ∃ c : ℂ, ∀ i,
      C.adjugateColumn energy shift attachment x p i =
        c * C.unitaryEigenvectorMatrix hH e i x := by
  let H := localExtensionMatrix energy p.1 attachment p.2
  let v := C.adjugateColumn energy shift attachment x p
  let b := hH.eigenvectorBasis.toBasis
  let T : Module.End ℂ (EuclideanSpace ℂ (I × ρ)) :=
    Matrix.toEuclideanLin H
  let μ : I × ρ → ℂ := fun i => (hH.eigenvalues i : ℂ)
  have hrealInjective :
      Function.Injective
        (C.realBranchEnergy energy shift attachment p) := by
    intro i j hij
    apply C.simple p hp
    change C.branch i p = C.branch j p
    rw [C.branch_eq_realBranchEnergy
      energy shift attachment p hp hH i]
    rw [C.branch_eq_realBranchEnergy
      energy shift attachment p hp hH j]
    rw [hij]
  have hμInjective : Function.Injective μ := by
    intro i j hij
    apply e.symm.injective
    apply hrealInjective
    rw [he (e.symm i), he (e.symm j)]
    simpa [μ] using congrArg Complex.re hij
  have hT : ∀ i, T (b i) = μ i • b i := by
    intro i
    apply WithLp.ofLp_injective 2
    simpa [T, H, b, μ, Matrix.ofLp_toEuclideanLin_apply,
      RCLike.real_smul_eq_coe_smul] using
      hH.mulVec_eigenvectorBasis i
  have hvRaw :
      H.mulVec v = μ (e x) • v := by
    have hv :=
      C.mulVec_adjugateColumn energy shift attachment p hp x
    rw [C.branch_eq_realBranchEnergy
      energy shift attachment p hp hH x] at hv
    simpa [H, v, μ, he x] using hv
  have hv :
      T (WithLp.toLp 2 v) =
        μ (e x) • WithLp.toLp 2 v := by
    apply WithLp.ofLp_injective 2
    simpa [T, Matrix.ofLp_toEuclideanLin_apply] using hvRaw
  obtain ⟨c, hc⟩ :=
    eigenvector_eq_smul_of_injective_eigenvalues
      b hT hμInjective hv
  refine ⟨c, ?_⟩
  intro i
  have hi := congrArg
    (fun w : EuclideanSpace ℂ (I × ρ) => WithLp.ofLp w i) hc
  simpa [v, b,
    LocalExtensionEigenbranchChart.unitaryEigenvectorMatrix,
    Matrix.IsHermitian.eigenvectorUnitary_apply] using hi

/-- Every analytic chart-probe entry is obtained from the exact unitary
probe entry by multiplying by the two adjugate-column scale factors. -/
theorem LocalExtensionEigenbranchChart.exists_probeMatrix_entry_eq_scaled_unitary
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ)
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    (p : (ρ → ℂ) × Matrix ρ ρ ℂ)
    (hp : p ∈ C.U)
    (hH :
      (localExtensionMatrix energy p.1 attachment p.2).IsHermitian)
    (e : (I × ρ) ≃ (I × ρ))
    (he :
      ∀ i,
        C.realBranchEnergy energy shift attachment p i =
          hH.eigenvalues (e i))
    (O : Matrix (I × ρ) (I × ρ) ℂ)
    (x y : I × ρ) :
    ∃ cx cy : ℂ,
      C.probeMatrix energy shift attachment O p x y =
        star cx * C.unitaryProbeMatrix hH e O x y * cy := by
  obtain ⟨cx, hx⟩ :=
    C.adjugateColumn_eq_smul_unitaryColumn
      energy shift attachment p hp hH e he x
  obtain ⟨cy, hy⟩ :=
    C.adjugateColumn_eq_smul_unitaryColumn
      energy shift attachment p hp hH e he y
  let U : Matrix (I × ρ) (I × ρ) ℂ :=
    C.unitaryEigenvectorMatrix hH e
  have hxU :
      ∀ i,
        C.adjugateColumn energy shift attachment x p i =
          cx * U i x := by
    exact hx
  have hyU :
      ∀ i,
        C.adjugateColumn energy shift attachment y p i =
          cy * U i y := by
    exact hy
  refine ⟨cx, cy, ?_⟩
  change
    (∑ i, ∑ j,
      star
          (C.adjugateColumn
            energy shift attachment x p i) *
        O i j *
        C.adjugateColumn
          energy shift attachment y p j) =
      star cx * (star U * O * U) x y * cy
  simp only [hxU, hyU]
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  simp only [Matrix.star_apply, star_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Nonzero support detected using analytic adjugate representatives survives
in exact orthonormal spectral coordinates. -/
theorem LocalExtensionEigenbranchChart.probeMatrix_entry_ne_zero_imp_unitary
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ)
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    (p : (ρ → ℂ) × Matrix ρ ρ ℂ)
    (hp : p ∈ C.U)
    (hH :
      (localExtensionMatrix energy p.1 attachment p.2).IsHermitian)
    (e : (I × ρ) ≃ (I × ρ))
    (he :
      ∀ i,
        C.realBranchEnergy energy shift attachment p i =
          hH.eigenvalues (e i))
    (O : Matrix (I × ρ) (I × ρ) ℂ)
    (x y : I × ρ)
    (hxy : C.probeMatrix energy shift attachment O p x y ≠ 0) :
    C.unitaryProbeMatrix hH e O x y ≠ 0 := by
  obtain ⟨cx, cy, hscale⟩ :=
    C.exists_probeMatrix_entry_eq_scaled_unitary
      energy shift attachment p hp hH e he O x y
  intro hzero
  apply hxy
  rw [hscale, hzero, mul_zero, zero_mul]

/-- Exact unitary spectral-coordinate matrices of a physical probe family. -/
def LocalExtensionEigenbranchChart.unitaryProbeMatrixFamily
    {I ρ η : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    {energy : I → ℂ} {shift : ρ → ℂ}
    {attachment : Matrix I I ℂ}
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    {p : (ρ → ℂ) × Matrix ρ ρ ℂ}
    (hH :
      (localExtensionMatrix energy p.1 attachment p.2).IsHermitian)
    (e : (I × ρ) ≃ (I × ρ))
    (probe : η → Matrix (I × ρ) (I × ρ) ℂ)
    (q : η) :
    Matrix (I × ρ) (I × ρ) ℂ :=
  C.unitaryProbeMatrix hH e (probe q)

/-- A Hermitian physical family remains Hermitian in exact unitary spectral
coordinates. -/
theorem LocalExtensionEigenbranchChart.unitaryProbeMatrixFamily_isHermitian
    {I ρ η : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    {energy : I → ℂ} {shift : ρ → ℂ}
    {attachment : Matrix I I ℂ}
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    {p : (ρ → ℂ) × Matrix ρ ρ ℂ}
    (hH :
      (localExtensionMatrix energy p.1 attachment p.2).IsHermitian)
    (e : (I × ρ) ≃ (I × ρ))
    (probe : η → Matrix (I × ρ) (I × ρ) ℂ)
    (hprobe : ∀ q, (probe q).IsHermitian)
    (q : η) :
    (C.unitaryProbeMatrixFamily hH e probe q).IsHermitian :=
  C.unitaryProbeMatrix_isHermitian hH e _ (hprobe q)

/-- The entire analytic chart-support family injects into support of the
same physical probes in exact orthonormal spectral coordinates. -/
theorem LocalExtensionEigenbranchChart.transitionFamilySupportGraph_probeMatrix_le_unitary
    {I ρ η : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ)
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    (p : (ρ → ℂ) × Matrix ρ ρ ℂ)
    (hp : p ∈ C.U)
    (hH :
      (localExtensionMatrix energy p.1 attachment p.2).IsHermitian)
    (e : (I × ρ) ≃ (I × ρ))
    (he :
      ∀ i,
        C.realBranchEnergy energy shift attachment p i =
          hH.eigenvalues (e i))
    (probe : η → Matrix (I × ρ) (I × ρ) ℂ) :
    transitionFamilySupportGraph
        (fun q =>
          C.probeMatrix energy shift attachment (probe q) p) ≤
      transitionFamilySupportGraph
        (C.unitaryProbeMatrixFamily hH e probe) := by
  intro x y hxy
  obtain ⟨q, hq⟩ := hxy
  obtain ⟨hxyNe, hproduct⟩ := hq
  obtain ⟨hforward, hbackward⟩ := mul_ne_zero_iff.mp hproduct
  refine ⟨q, hxyNe, mul_ne_zero ?_ ?_⟩
  · exact C.probeMatrix_entry_ne_zero_imp_unitary
      energy shift attachment p hp hH e he
      (probe q) x y hforward
  · exact C.probeMatrix_entry_ne_zero_imp_unitary
      energy shift attachment p hp hH e he
      (probe q) y x hbackward

end

end GaloisForLFunctions.HTGeometry

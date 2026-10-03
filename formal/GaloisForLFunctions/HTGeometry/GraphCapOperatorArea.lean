import GaloisForLFunctions.HTGeometry.GraphCapDeterminantArea
import GaloisForLFunctions.HTGeometry.CompactSelfAdjointEigenbasis
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace
import GaloisForLFunctions.HTGeometry.GramianInverseForm

/-!
# The graph-cap determinant area of a Hilbert–Schmidt operator

For a Hilbert–Schmidt `A : H₊ → H₋` put `K = A*A`, a positive compact operator with nonzero
eigenvalues `λ_j` (repeated with multiplicity).

* **(BGCA.1)** The graph cap `Γ_A(z) = graph(zA)` lies in the Hilbert–Schmidt graph cell, and its chart
  coordinate `z ↦ zA` is holomorphic.
* **(BGCA.2), (BGCA.5)** The determinant-line potential of the cell is `log det(I + Z*Z)`, the sum of
  `log(1 + μ)` over the nonzero eigenvalues of `Z*Z`; along the cap it is `∑ log(1 + λ_j |z|²)`.
* **Theorem BGCA-A (BGCA.4)** The determinant-line area of the cap over the unit disk is
  `Tr(K(I+K)⁻¹) = ∑ λ_j/(1 + λ_j)`, it lies in `[0, Tr K] = [0, ‖A‖²_HS]`, and it is strictly below
  `‖A‖²_HS` when `A ≠ 0`.
-/

open MeasureTheory Set Filter Topology Metric Laplacian ContinuousLinearMap Module.End
open scoped InnerProductSpace Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-! ## Spectral data of a compact symmetric operator -/

section Spectral

variable {K : E →L[ℂ] E} [Fact (IsCompactOperator K)]

/-- The nonzero eigenvalues of `K`, repeated with multiplicity, as real numbers. -/
def eigenReal (K : E →L[ℂ] E) [Fact (IsCompactOperator K)] (i : EigenIndex K) : ℝ := i.1.1.re

/-- A vector orthogonal to every eigenvector of a nonzero eigenvalue is killed by a compact
symmetric operator: `Ku` is then orthogonal to every eigenspace. -/
theorem apply_eq_zero_of_orthogonal_eigenVec (hsym : (K : E →ₗ[ℂ] E).IsSymmetric) {u : E}
    (hu : ∀ i, ⟪eigenVec K i, u⟫_ℂ = 0) : K u = 0 := by
  have hbot := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (Fact.out : IsCompactOperator K) hsym
  have hspan : ∀ w ∈ Submodule.span ℂ (Set.range (eigenVec K)), ⟪w, u⟫_ℂ = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact hu i
    | zero => exact inner_zero_left _
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]
  have hmem : K u ∈ (⨆ μ, eigenspace (K : E →ₗ[ℂ] E) μ)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    refine Submodule.iSup_induction (fun μ => eigenspace (K : E →ₗ[ℂ] E) μ)
      (motive := fun w => ⟪w, K u⟫_ℂ = 0) hw (fun μ w hw => ?_) (inner_zero_left _)
      (fun x y hx hy => by simp only [inner_add_left, hx, hy, add_zero])
    have h1 : ⟪w, K u⟫_ℂ = ⟪K w, u⟫_ℂ := (hsym w u).symm
    rw [h1]
    change ⟪(K : E →ₗ[ℂ] E) w, u⟫_ℂ = 0
    rw [mem_eigenspace_iff.1 hw, inner_smul_left]
    by_cases hμ : μ = 0
    · rw [hμ, map_zero, zero_mul]
    · rw [hspan w (mem_span_eigenVec ⟨μ, hμ⟩ w hw), mul_zero]
  rw [hbot] at hmem
  exact (Submodule.mem_bot ℂ).1 hmem

/-- The eigenvectors of the nonzero eigenvalues extend to a Hilbert basis whose remaining vectors
lie in `ker K`. -/
theorem exists_hilbertBasis_eigenVec (hsym : (K : E →ₗ[ℂ] E).IsSymmetric) :
    ∃ (w : Set E) (b : HilbertBasis w ℂ E) (φ : EigenIndex K → w), Function.Injective φ ∧
      (∀ i, b (φ i) = eigenVec K i) ∧ ∀ u, u ∉ Set.range φ → K (b u) = 0 := by
  classical
  have horth := orthonormal_eigenVec (T := K) hsym
  have hinj : Function.Injective (eigenVec K) := horth.linearIndependent.injective
  obtain ⟨w, b, hsw, hb⟩ := ((orthonormal_subtype_range hinj).2 horth).exists_hilbertBasis_extension
  have hb' : ∀ u : w, b u = u := fun u => congrFun hb u
  refine ⟨w, b, fun i => ⟨eigenVec K i, hsw ⟨i, rfl⟩⟩, fun i j h => hinj (congrArg Subtype.val h),
    fun i => hb' _, fun u hu => ?_⟩
  refine apply_eq_zero_of_orthogonal_eigenVec hsym fun i => ?_
  have hne : (⟨eigenVec K i, hsw ⟨i, rfl⟩⟩ : w) ≠ u := fun h => hu ⟨i, h⟩
  have h : ⟪b ⟨eigenVec K i, hsw ⟨i, rfl⟩⟩, b u⟫_ℂ = 0 := b.orthonormal.2 hne
  simpa only [hb'] using h

/-- **The trace on the eigenvectors.**  If a Hilbert–Schmidt product `T` acts on the eigenvectors of
the nonzero eigenvalues of a compact symmetric `K` by scalars `g_i` and kills `ker K`, then
`Tr T = ∑ g_i`. -/
theorem opTrace_eq_tsum_eigen (hsym : (K : E →ₗ[ℂ] E).IsSymmetric) {T : E →L[ℂ] E}
    {g : EigenIndex K → ℂ} (hdiag : ∀ i, T (eigenVec K i) = g i • eigenVec K i)
    (hker : ∀ u, K u = 0 → T u = 0) {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] {S : G →L[ℂ] E} {U : E →L[ℂ] G} (hS : IsHilbertSchmidt S)
    (hU : IsHilbertSchmidt U) (hT : T = S ∘L U) : opTrace T = ∑' i, g i := by
  obtain ⟨w, b, φ, hφ, hbφ, hker'⟩ := exists_hilbertBasis_eigenVec hsym
  have horth := orthonormal_eigenVec (T := K) hsym
  rw [hT, opTrace_comp_eq_tsum_basis hS hU b, ← hT, ← hφ.tsum_eq]
  · refine tsum_congr fun i => ?_
    rw [hbφ, hdiag, inner_smul_right, inner_self_eq_norm_sq_to_K, horth.1 i]
    simp
  · intro u hu
    by_contra hnot
    exact hu (show ⟪b u, T (b u)⟫_ℂ = 0 by rw [hker _ (hker' u hnot), inner_zero_right])

/-- Summation over the nonzero eigenvalues is summation over a Hilbert-basis subfamily. -/
theorem summable_eigen_comp (hsym : (K : E →ₗ[ℂ] E).IsSymmetric) {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G] {B : E →L[ℂ] G} (hB : IsHilbertSchmidt B) :
    Summable fun i : EigenIndex K => ‖B (eigenVec K i)‖ ^ 2 := by
  obtain ⟨w, b, φ, hφ, hbφ, -⟩ := exists_hilbertBasis_eigenVec hsym
  have h := (hB.summable b).comp_injective hφ
  refine h.congr fun i => ?_
  simp only [Function.comp_apply, hbφ]

omit [CompleteSpace E] in
theorem eigenspace_clm_smul_div {T : E →L[ℂ] E} {c : ℂ} (hc : c ≠ 0) (μ : ℂ) :
    eigenspace ((c • T : E →L[ℂ] E) : E →ₗ[ℂ] E) μ = eigenspace (T : E →ₗ[ℂ] E) (μ / c) := by
  ext x
  simp only [mem_eigenspace_iff, ContinuousLinearMap.toLinearMap_smul, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe]
  constructor
  · intro h
    rw [div_eq_inv_mul, mul_smul, ← h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · intro h
    rw [h, smul_smul, mul_div_cancel₀ μ hc]

/-- The nonzero spectrum of `cT` is that of `T` scaled by `c`, with the same multiplicities. -/
def eigenIndexSmulEquiv {T : E →L[ℂ] E} {c : ℂ} [Fact (IsCompactOperator T)]
    [Fact (IsCompactOperator (c • T))] (hc : c ≠ 0) : EigenIndex (c • T) ≃ EigenIndex T :=
  Equiv.sigmaCongr
    { toFun := fun μ => ⟨μ.1 / c, div_ne_zero μ.2 hc⟩
      invFun := fun μ => ⟨c * μ.1, mul_ne_zero hc μ.2⟩
      left_inv := fun μ => Subtype.ext (mul_div_cancel₀ μ.1 hc)
      right_inv := fun μ => Subtype.ext (mul_div_cancel_left₀ μ.1 hc) }
    fun μ => finCongr (LinearEquiv.ofEq _ _ (eigenspace_clm_smul_div hc μ.1)).finrank_eq

omit [CompleteSpace E] in
theorem eigenIndexSmulEquiv_fst {T : E →L[ℂ] E} {c : ℂ} [Fact (IsCompactOperator T)]
    [Fact (IsCompactOperator (c • T))] (hc : c ≠ 0) (i : EigenIndex (c • T)) :
    ((eigenIndexSmulEquiv hc i).1 : ℂ) = i.1.1 / c := by
  simp only [eigenIndexSmulEquiv, Equiv.sigmaCongr, Equiv.trans_apply, Equiv.sigmaCongrLeft_apply,
    Equiv.sigmaCongrRight_apply, Equiv.coe_fn_mk]

omit [CompleteSpace E] in
/-- Reindexing the nonzero spectrum of `cK`, `c > 0`, by that of `K`. -/
theorem tsum_eigenIndex_smul {T : E →L[ℂ] E} [Fact (IsCompactOperator T)] {c : ℝ} (hc : 0 < c)
    {T' : E →L[ℂ] E} [Fact (IsCompactOperator T')] (hT' : T' = (c : ℂ) • T) (f : ℂ → ℝ) :
    ∑' i : EigenIndex T', f i.1.1 = ∑' i : EigenIndex T, f ((c : ℂ) * i.1.1) := by
  subst hT'
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [← (eigenIndexSmulEquiv hc').tsum_eq (fun j : EigenIndex T => f ((c : ℂ) * j.1.1))]
  refine tsum_congr fun i => ?_
  rw [eigenIndexSmulEquiv_fst, mul_div_cancel₀ _ hc']

omit [CompleteSpace E] in
/-- The zero operator has no nonzero eigenvalue. -/
theorem isEmpty_eigenIndex_of_eq_zero {T : E →L[ℂ] E} [Fact (IsCompactOperator T)] (hT : T = 0) :
    IsEmpty (EigenIndex T) := by
  subst hT
  refine ⟨fun i => ?_⟩
  have hbot : nonzeroEigenspace (0 : E →L[ℂ] E) i.1 = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have h := mem_eigenspace_iff.1 hx
    simp only [ContinuousLinearMap.toLinearMap_zero, LinearMap.zero_apply] at h
    exact (Submodule.mem_bot ℂ).2 ((smul_eq_zero.1 h.symm).resolve_left i.1.2)
  have h0 : Module.finrank ℂ (nonzeroEigenspace (0 : E →L[ℂ] E) i.1) = 0 := by
    rw [hbot, finrank_bot]
  exact Fin.elim0 (Fin.cast h0 i.2)

end Spectral

/-! ## The determinant-line potential and the graph cap -/

/-- The determinant-line potential `log det(I + T)` of a positive compact operator: the sum of
`log(1 + μ)` over its nonzero eigenvalues, repeated with multiplicity. -/
def logDetPotential (T : E →L[ℂ] E) [Fact (IsCompactOperator T)] : ℝ :=
  ∑' i : EigenIndex T, Real.log (1 + i.1.1.re)

theorem isCompactOperator_adjoint_comp_self {Z : E →L[ℂ] F} (hZ : IsHilbertSchmidt Z) :
    IsCompactOperator (adjoint Z ∘L Z) :=
  hZ.isCompactOperator.clm_comp (adjoint Z)

/-- **(BGCA.1)** The graph cap `Γ_A(z) = graph(zA) ⊆ H₊ ⊕ H₋`. -/
def graphCap (A : E →L[ℂ] F) (z : ℂ) : Submodule ℂ (E × F) :=
  LinearMap.graph ((z • A : E →L[ℂ] F) : E →ₗ[ℂ] F)

omit [CompleteSpace E] [CompleteSpace F] in
theorem mem_graphCap {A : E →L[ℂ] F} {z : ℂ} {p : E × F} : p ∈ graphCap A z ↔ p.2 = z • A p.1 := by
  rw [graphCap, LinearMap.mem_graph_iff]
  simp

omit [CompleteSpace F] in
/-- **(BGCA.1)** The cap lies in the Hilbert–Schmidt graph cell and its chart coordinate is
holomorphic. -/
theorem graphCap_mem_cell {A : E →L[ℂ] F} (hA : IsHilbertSchmidt A) :
    (∀ z : ℂ, IsHilbertSchmidt (z • A)) ∧ Differentiable ℂ (fun z : ℂ => z • A) :=
  ⟨fun z => hA.smul z, (differentiable_id.smul_const A)⟩

/-- **(BGCA.2)** The determinant-line potential pulled back along the cap,
`z ↦ log det(I + (zA)*(zA))`. -/
def capPotential (A : E →L[ℂ] F) (hA : IsHilbertSchmidt A) (z : ℂ) : ℝ :=
  haveI : Fact (IsCompactOperator (adjoint (z • A) ∘L (z • A))) :=
    ⟨isCompactOperator_adjoint_comp_self (hA.smul z)⟩
  logDetPotential (adjoint (z • A) ∘L (z • A))

theorem adjoint_smul_comp_smul (A : E →L[ℂ] F) (z : ℂ) :
    adjoint (z • A) ∘L (z • A) = ((‖z‖ ^ 2 : ℝ) : ℂ) • (adjoint A ∘L A) := by
  rw [map_smulₛₗ, smul_comp, comp_smul, smul_smul, Complex.conj_mul']
  push_cast
  rfl

/-- **(BGCA.5)** Along the cap the potential is `∑ log(1 + λ_j |z|²)`. -/
theorem capPotential_eq (A : E →L[ℂ] F) (hA : IsHilbertSchmidt A)
    [Fact (IsCompactOperator (adjoint A ∘L A))] (z : ℂ) :
    capPotential A hA z = logDetSeries (eigenReal (adjoint A ∘L A)) (‖z‖ ^ 2) := by
  rw [capPotential, logDetPotential, logDetSeries]
  by_cases hz : z = 0
  · subst hz
    have hT : adjoint ((0 : ℂ) • A) ∘L ((0 : ℂ) • A) = 0 := by simp
    haveI : Fact (IsCompactOperator (adjoint ((0 : ℂ) • A) ∘L ((0 : ℂ) • A))) :=
      ⟨isCompactOperator_adjoint_comp_self (hA.smul 0)⟩
    haveI := isEmpty_eigenIndex_of_eq_zero hT
    simp
  · have hc : 0 < ‖z‖ ^ 2 := by positivity
    haveI : Fact (IsCompactOperator (adjoint (z • A) ∘L (z • A))) :=
      ⟨isCompactOperator_adjoint_comp_self (hA.smul z)⟩
    rw [tsum_eigenIndex_smul hc (adjoint_smul_comp_smul A z) (fun μ => Real.log (1 + μ.re))]
    refine tsum_congr fun i => ?_
    rw [Complex.re_ofReal_mul, eigenReal, mul_comm]

/-! ## Theorem BGCA-A -/

section Area

variable (A : E →L[ℂ] F)

/-- **The determinant-line area of the cap over the unit disk**:
`∫_D Γ_A^* ω_det = ∫_D (1/4π) Δ log det(I + (zA)*(zA))`. -/
def graphCapArea (hA : IsHilbertSchmidt A) : ℝ :=
  ∫ z in ball (0 : ℂ) 1, (1 / (4 * π)) * Δ (capPotential A hA) z

/-- The resolvent ratio `K(I + K)⁻¹`. -/
def resolventRatio (K : E →L[ℂ] E) : E →L[ℂ] E := K * Ring.inverse (1 + K)

theorem isSymmetric_adjoint_comp_self : ((adjoint A ∘L A : E →L[ℂ] E) : E →ₗ[ℂ] E).IsSymmetric :=
  (isPositive_adjoint_comp_self A).isSelfAdjoint.isSymmetric

/-- **(BGCA.3)** The matrix of `K = A*A` is the complete Gram matrix of the columns:
`⟪x, K y⟫ = ⟪A x, A y⟫`. -/
theorem inner_adjoint_comp_self_eq (x y : E) : ⟪x, (adjoint A ∘L A) y⟫_ℂ = ⟪A x, A y⟫_ℂ := by
  rw [comp_apply, adjoint_inner_right]

theorem re_inner_adjoint_comp_self (x : E) : (⟪x, (adjoint A ∘L A) x⟫_ℂ).re = ‖A x‖ ^ 2 := by
  rw [comp_apply, adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

theorem isUnit_one_add_adjoint_comp_self {A : E →L[ℂ] F} (hA : IsHilbertSchmidt A) :
    IsUnit (1 + adjoint A ∘L A) := by
  have hcpt : IsCompactOperator (adjoint A ∘L A) := isCompactOperator_adjoint_comp_self hA
  have hno : ¬ HasEigenvalue ((adjoint A ∘L A : E →L[ℂ] E) : E →ₗ[ℂ] E) (-1 : ℂ) := by
    intro h
    obtain ⟨x, hx, hxne⟩ := h.exists_hasEigenvector
    have hKx : (adjoint A ∘L A) x = -x := by
      simpa [mem_genEigenspace_one, neg_one_smul] using hx
    have h1 : ⟪x, (adjoint A ∘L A) x⟫_ℂ = ((‖A x‖ ^ 2 : ℝ) : ℂ) := by
      rw [comp_apply, adjoint_inner_right, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    rw [hKx, inner_neg_right, inner_self_eq_norm_sq_to_K] at h1
    have h2 : ‖x‖ ^ 2 + ‖A x‖ ^ 2 = 0 := by
      have h3 : -(‖x‖ ^ 2) = ‖A x‖ ^ 2 := Complex.ofReal_injective (by rw [← h1]; push_cast; rfl)
      linarith
    have hx0 : ‖x‖ = 0 := by nlinarith [sq_nonneg ‖x‖, sq_nonneg ‖A x‖, norm_nonneg x]
    exact hxne (norm_eq_zero.1 hx0)
  have hs : (-1 : ℂ) ∉ spectrum ℂ (adjoint A ∘L A) :=
    fun h => hno ((hcpt.hasEigenvalue_iff_mem_spectrum (by norm_num)).mpr h)
  have hu := (spectrum.notMem_iff.mp hs).neg
  simpa only [Algebra.algebraMap_eq_smul_one, neg_one_smul, neg_sub, neg_neg, sub_neg_eq_add,
    add_comm] using hu

omit [CompleteSpace F] in
theorem one_add_ne_zero_of_nonneg {r : ℝ} (hr : 0 ≤ r) : (1 + (r : ℂ)) ≠ 0 := by
  have : (1 + (r : ℂ)) = ((1 + r : ℝ) : ℂ) := by push_cast; rfl
  rw [this]
  exact_mod_cast (by linarith : (1 + r : ℝ) ≠ 0)

variable {A} (hA : IsHilbertSchmidt A) [Fact (IsCompactOperator (adjoint A ∘L A))]
include hA

omit hA in
/-- The eigenvalues of `A*A` are the squared norms `‖A e_j‖²`. -/
theorem eigenReal_eq_norm_sq (i : EigenIndex (adjoint A ∘L A)) :
    eigenReal (adjoint A ∘L A) i = ‖A (eigenVec (adjoint A ∘L A) i)‖ ^ 2 := by
  have horth := orthonormal_eigenVec (isSymmetric_adjoint_comp_self A)
  have h1 : ⟪eigenVec _ i, (adjoint A ∘L A) (eigenVec (adjoint A ∘L A) i)⟫_ℂ = i.1.1 := by
    rw [apply_eigenVec, inner_smul_right, inner_self_eq_norm_sq_to_K, horth.1 i]
    simp
  have h2 : ⟪eigenVec _ i, (adjoint A ∘L A) (eigenVec (adjoint A ∘L A) i)⟫_ℂ =
      ((‖A (eigenVec (adjoint A ∘L A) i)‖ ^ 2 : ℝ) : ℂ) := by
    rw [comp_apply, adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [eigenReal, ← h1, h2, Complex.ofReal_re]

omit hA in
theorem eigenReal_nonneg (i : EigenIndex (adjoint A ∘L A)) : 0 ≤ eigenReal (adjoint A ∘L A) i := by
  rw [eigenReal_eq_norm_sq]
  positivity

theorem summable_eigenReal : Summable (eigenReal (adjoint A ∘L A)) :=
  (summable_eigen_comp (isSymmetric_adjoint_comp_self A) hA).congr fun i =>
    (eigenReal_eq_norm_sq i).symm

omit hA in
theorem eigenVal_eq_ofReal (i : EigenIndex (adjoint A ∘L A)) :
    i.1.1 = ((eigenReal (adjoint A ∘L A) i : ℝ) : ℂ) :=
  (eigenValue_real (isSymmetric_adjoint_comp_self A) i).symm

/-- `Tr K = ∑ λ_j = ‖A‖²_HS`. -/
theorem hsNormSq_eq_tsum_eigenReal : hsNormSq A = ∑' i, eigenReal (adjoint A ∘L A) i := by
  have htr := opTrace_eq_tsum_eigen (isSymmetric_adjoint_comp_self A) (T := adjoint A ∘L A)
    (g := fun i => i.1.1) (fun i => apply_eigenVec _ i) (fun u hu => hu) hA.adjoint hA rfl
  have hre := re_opTrace_adjoint_comp_self hA
  have hsum : (∑' i : EigenIndex (adjoint A ∘L A), (i.1.1 : ℂ)) =
      ((∑' i, eigenReal (adjoint A ∘L A) i : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr fun i => eigenVal_eq_ofReal i
  rw [← hre, htr, hsum, RCLike.re_to_complex, Complex.ofReal_re]

/-- `Tr K(I + K)⁻¹ = ∑ λ_j / (1 + λ_j)`. -/
theorem opTrace_resolventRatio :
    opTrace (resolventRatio (adjoint A ∘L A)) =
      ((∑' i, eigenReal (adjoint A ∘L A) i / (1 + eigenReal (adjoint A ∘L A) i) : ℝ) : ℂ) := by
  have hu := isUnit_one_add_adjoint_comp_self hA
  have hleft : ∀ x, Ring.inverse (1 + adjoint A ∘L A) ((1 + adjoint A ∘L A) x) = x := fun x => by
    change (Ring.inverse (1 + adjoint A ∘L A) * (1 + adjoint A ∘L A)) x = x
    rw [Ring.inverse_mul_cancel _ hu, one_apply_eq_self]
  have hratio : resolventRatio (adjoint A ∘L A) =
      adjoint A ∘L (A ∘L Ring.inverse (1 + adjoint A ∘L A)) := by
    rw [resolventRatio, mul_def, comp_assoc]
  have htr := opTrace_eq_tsum_eigen (isSymmetric_adjoint_comp_self A)
    (T := resolventRatio (adjoint A ∘L A))
    (g := fun i => ((eigenReal (adjoint A ∘L A) i / (1 + eigenReal (adjoint A ∘L A) i) : ℝ) : ℂ))
    (fun i => ?_) (fun u hu => ?_) hA.adjoint (hA.comp_right _) hratio
  · rw [htr, Complex.ofReal_tsum]
  · have hr : 0 ≤ eigenReal (adjoint A ∘L A) i := eigenReal_nonneg i
    have hKe : (adjoint A ∘L A) (eigenVec (adjoint A ∘L A) i) =
        ((eigenReal (adjoint A ∘L A) i : ℝ) : ℂ) • eigenVec (adjoint A ∘L A) i := by
      rw [apply_eigenVec, eigenVal_eq_ofReal i]
    have h1 : (1 + adjoint A ∘L A) (eigenVec (adjoint A ∘L A) i) =
        (1 + ((eigenReal (adjoint A ∘L A) i : ℝ) : ℂ)) • eigenVec (adjoint A ∘L A) i := by
      rw [add_apply, one_apply_eq_self, hKe, add_smul, one_smul]
    have h2 : Ring.inverse (1 + adjoint A ∘L A) (eigenVec (adjoint A ∘L A) i) =
        (1 + ((eigenReal (adjoint A ∘L A) i : ℝ) : ℂ))⁻¹ • eigenVec (adjoint A ∘L A) i := by
      have := hleft (eigenVec (adjoint A ∘L A) i)
      rw [h1, map_smul] at this
      exact (eq_inv_smul_iff₀ (one_add_ne_zero_of_nonneg hr)).2 this
    rw [resolventRatio, mul_apply_eq_comp, h2, map_smul, hKe, smul_smul]
    congr 1
    have h3 := one_add_ne_zero_of_nonneg hr
    push_cast
    field_simp
  · have h1 : (1 + adjoint A ∘L A) u = u := by rw [add_apply, one_apply_eq_self, hu, add_zero]
    have h2 : Ring.inverse (1 + adjoint A ∘L A) u = u := by
      have := hleft u
      rwa [h1] at this
    rw [resolventRatio, mul_apply_eq_comp, h2, hu]

/-- **Theorem BGCA-A (BGCA.4).**  For a Hilbert–Schmidt `A` with `K = A*A`, the determinant-line area
of the graph cap over the unit disk is `∑ λ_j/(1 + λ_j) = Tr(K(I + K)⁻¹)`; it lies in
`[0, ‖A‖²_HS]`, strictly below `‖A‖²_HS` when `A ≠ 0`. -/
theorem graphCapArea_eq :
    graphCapArea A hA =
        ∑' i, eigenReal (adjoint A ∘L A) i / (1 + eigenReal (adjoint A ∘L A) i) ∧
      opTrace (resolventRatio (adjoint A ∘L A)) = (graphCapArea A hA : ℂ) ∧
      0 ≤ graphCapArea A hA ∧ graphCapArea A hA ≤ hsNormSq A ∧
      (A ≠ 0 → graphCapArea A hA < hsNormSq A) := by
  have hev : ∀ i, 0 ≤ eigenReal (adjoint A ∘L A) i := eigenReal_nonneg
  have hsum := summable_eigenReal hA
  have harea : graphCapArea A hA = radialCapArea (logDetSeries (eigenReal (adjoint A ∘L A))) := by
    rw [graphCapArea, radialCapArea,
      show capPotential A hA = fun w => logDetSeries (eigenReal (adjoint A ∘L A)) (‖w‖ ^ 2) from
        funext (capPotential_eq A hA)]
  have hval := harea.trans (capArea_eq_tsum hev hsum)
  obtain ⟨h0, hle⟩ := capArea_le_tsum hev hsum
  refine ⟨hval, by rw [opTrace_resolventRatio hA, hval], hval ▸ h0, ?_, fun hne => ?_⟩
  · rw [hval, hsNormSq_eq_tsum_eigenReal hA]
    exact hle
  · rw [hval, hsNormSq_eq_tsum_eigenReal hA]
    have hA0 : hsNormSq A ≠ 0 := by
      intro h0
      apply hne
      rw [hsNormSq] at h0
      have hz : (fun i => ‖A (hsBasis ℂ E i)‖ ^ 2) = 0 :=
        (hasSum_zero_iff_of_nonneg (fun i => by positivity)).1 (h0 ▸ (show Summable
          (fun i => ‖A (hsBasis ℂ E i)‖ ^ 2) from hA).hasSum)
      refine ext_hilbertBasis (b := hsBasis ℂ E) fun k => ?_
      have := congrFun hz k
      simpa using this
    obtain ⟨i₀, hi₀⟩ : ∃ i, 0 < eigenReal (adjoint A ∘L A) i := by
      by_contra hall
      push Not at hall
      apply hA0
      rw [hsNormSq_eq_tsum_eigenReal hA]
      exact (tsum_congr fun i => le_antisymm (hall i) (hev i)).trans tsum_zero
    exact capArea_lt_tsum hev hsum hi₀

end Area

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.ChronologicalTensor.RecoverySurgeryNorm
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicHilbertBasis

/-!
# The actual surgery quotient and its graded Hilbert completion

Each homogeneous class has an attained norm defined by the infimum over its
actual geometric representatives. These costs determine an injective dense
embedding of the existing algebraic quotient B/A into a Hilbert space.
The induced graded norm restricts to exactly those geometric quotient norms,
and the isometric embedding supplies an AbstractCompletion.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Polynomial Set
attribute [local instance] cubicGradedLineNormedGroup cubicGradedLineInnerProductSpace
  cubicGradedLine_complete

def recoverySurgeryRepresentativeValues (n k : ℕ) (x : cubicGradedDefect k) : Set ℝ :=
  recoverySurgeryCapacity n (k+1) ''
    {P : cubicHomogeneousSpace (k+1) | cubicGradedDefectMk k P=x}

def recoverySurgeryDefectNorm (n k : ℕ) (x : cubicGradedDefect k) : ℝ :=
  sInf (recoverySurgeryRepresentativeValues n k x)

theorem recoverySurgeryRepresentativeValues_isLeast (n k : ℕ) (x : cubicGradedDefect k) :
    IsLeast (recoverySurgeryRepresentativeValues n k x)
      (|cubicGradedDefectCoordinate k x| *recoverySurgeryGap n k) := by
  obtain ⟨P,hP,hcap⟩ := recoverySurgeryCoefficient_sharpAttainment n k (cubicGradedDefectCoordinate k x)
  constructor
  · refine ⟨P,?_,hcap⟩
    apply (cubicGradedDefectEquiv k).injective
    exact hP
  · rintro y ⟨Q,hQ,rfl⟩
    have he := congrArg (cubicGradedDefectCoordinate k) hQ
    rw [cubicGradedDefectCoordinate_mk] at he
    have hb := recoverySurgeryCoefficient_sharpBound n k Q
    rwa [he] at hb

theorem recoverySurgeryDefectNorm_eq (n k : ℕ) (x : cubicGradedDefect k) :
    recoverySurgeryDefectNorm n k x=|cubicGradedDefectCoordinate k x| *recoverySurgeryGap n k :=
  (recoverySurgeryRepresentativeValues_isLeast n k x).csInf_eq

theorem recoverySurgeryDefectNorm_attained (n k : ℕ) (x : cubicGradedDefect k) :
    ∃ P : cubicHomogeneousSpace (k+1), cubicGradedDefectMk k P=x ∧
      recoverySurgeryCapacity n (k+1) P=recoverySurgeryDefectNorm n k x := by
  have h := (recoverySurgeryRepresentativeValues_isLeast n k x).1
  rwa [← recoverySurgeryDefectNorm_eq] at h

def recoverySurgeryHilbertEmbedding (n : ℕ) :
    (Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) →ₗ[ℝ] cubicDefectHilbert :=
  cubicCuspDefectBasis.constr ℝ (fun k => recoverySurgeryGap n k • cubicHilbertBasis k)

theorem recoverySurgeryHilbertEmbedding_basis (n k : ℕ) :
    recoverySurgeryHilbertEmbedding n (cubicCuspDefectBasis k)=
      recoverySurgeryGap n k • cubicHilbertBasis k :=
  cubicCuspDefectBasis.constr_basis ℝ _ k

theorem recoveryCuspBasis_coefficient (i k : ℕ) :
    (cubicCuspDefectEquiv (cubicCuspDefectBasis i)).coeff k = if i=k then 1 else 0 := by
  simp only [cubicCuspDefectBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
    Polynomial.coe_basisMonomials, coeff_monomial]

theorem recoverySurgeryHilbertEmbedding_repr (n : ℕ)
    (x : Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) (k : ℕ) :
    cubicHilbertBasis.repr (recoverySurgeryHilbertEmbedding n x) k =
      recoverySurgeryGap n k*(cubicCuspDefectEquiv x).coeff k := by
  have h : ((innerSL ℝ (cubicHilbertBasis k)).toLinearMap).comp (recoverySurgeryHilbertEmbedding n) =
      recoverySurgeryGap n k • ((Polynomial.lcoeff ℝ k).comp cubicCuspDefectEquiv.toLinearMap) := by
    apply cubicCuspDefectBasis.ext
    intro i
    rw [LinearMap.comp_apply, recoverySurgeryHilbertEmbedding_basis]
    change inner ℝ (cubicHilbertBasis k) (recoverySurgeryGap n i • cubicHilbertBasis i) =
      recoverySurgeryGap n k*(cubicCuspDefectEquiv (cubicCuspDefectBasis i)).coeff k
    rw [real_inner_smul_right, recoveryCuspBasis_coefficient]
    by_cases hi : i=k
    · subst i
      rw [if_pos rfl, real_inner_self_eq_norm_sq, cubicHilbertBasis.orthonormal.1 k, one_pow]
    · rw [if_neg hi, cubicHilbertBasis.orthonormal.2 (Ne.symm hi), mul_zero, mul_zero]
  rw [HilbertBasis.repr_apply_apply]
  exact congrArg (fun f => f x) h

theorem recoverySurgeryHilbertEmbedding_injective (n : ℕ) :
    Function.Injective (recoverySurgeryHilbertEmbedding n) := by
  intro x y he
  apply cubicCuspDefectEquiv.injective
  apply Polynomial.ext
  intro k
  have h := congrArg (fun z => cubicHilbertBasis.repr z k) he
  rw [recoverySurgeryHilbertEmbedding_repr, recoverySurgeryHilbertEmbedding_repr] at h
  exact mul_left_cancel₀ (ne_of_gt (recoverySurgeryGap_positive n k)) h

theorem recoverySurgeryHilbertEmbedding_norm_sq (n : ℕ)
    (x : Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) :
    ‖recoverySurgeryHilbertEmbedding n x‖^2 =
      ∑' k, (recoverySurgeryGap n k)^2*((cubicCuspDefectEquiv x).coeff k)^2 := by
  rw [← real_inner_self_eq_norm_sq, ← cubicHilbertBasis.tsum_inner_mul_inner]
  congr 1
  funext k
  have hk := recoverySurgeryHilbertEmbedding_repr n x k
  rw [HilbertBasis.repr_apply_apply] at hk
  have hl : inner ℝ (recoverySurgeryHilbertEmbedding n x) (cubicHilbertBasis k) =
      recoverySurgeryGap n k*(cubicCuspDefectEquiv x).coeff k := by
    calc
      _ = inner ℝ (cubicHilbertBasis k) (recoverySurgeryHilbertEmbedding n x) := real_inner_comm _ _
      _ = _ := hk
  rw [hl,hk]
  ring

theorem recoverySurgeryHilbertEmbedding_basis_mem_range (n k : ℕ) :
    cubicHilbertBasis k ∈ LinearMap.range (recoverySurgeryHilbertEmbedding n) := by
  refine ⟨(recoverySurgeryGap n k)⁻¹ • cubicCuspDefectBasis k,?_⟩
  rw [map_smul, recoverySurgeryHilbertEmbedding_basis, smul_smul,
    inv_mul_cancel₀ (ne_of_gt (recoverySurgeryGap_positive n k)), one_smul]

theorem recoverySurgeryHilbertEmbedding_denseRange (n : ℕ) :
    DenseRange (recoverySurgeryHilbertEmbedding n) := by
  intro x
  let S := LinearMap.range (recoverySurgeryHilbertEmbedding n)
  have hs : ∀ t : Finset ℕ, ∑ k ∈ t, cubicHilbertBasis.repr x k • cubicHilbertBasis k ∈
      closure (S : Set cubicDefectHilbert) := by
    intro t
    exact S.le_topologicalClosure (S.sum_mem (fun k _ => S.smul_mem _
      (recoverySurgeryHilbertEmbedding_basis_mem_range n k)))
  exact isClosed_closure.mem_of_tendsto (cubicHilbertBasis.hasSum_repr x)
    (Filter.Eventually.of_forall hs)

@[implicit_reducible]
def recoverySurgeryQuotientNormedGroup (n : ℕ) :
    NormedAddCommGroup (Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) :=
  NormedAddCommGroup.induced _ _ (recoverySurgeryHilbertEmbedding n)
    (recoverySurgeryHilbertEmbedding_injective n)

@[implicit_reducible]
def recoverySurgeryQuotientNormedSpace (n : ℕ) :
    letI := recoverySurgeryQuotientNormedGroup n
    NormedSpace ℝ (Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) := by
  letI := recoverySurgeryQuotientNormedGroup n
  exact NormedSpace.induced ℝ _ _ (recoverySurgeryHilbertEmbedding n)

@[implicit_reducible]
def recoverySurgeryQuotientInnerProductSpace (n : ℕ) :
    letI := recoverySurgeryQuotientNormedGroup n
    InnerProductSpace ℝ (Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) := by
  letI := recoverySurgeryQuotientNormedGroup n
  exact InnerProductSpace.induced (recoverySurgeryHilbertEmbedding n)

theorem recoverySurgeryHilbertEmbedding_isometry (n : ℕ) :
    letI := recoverySurgeryQuotientNormedGroup n
    Isometry (recoverySurgeryHilbertEmbedding n) := by
  letI := recoverySurgeryQuotientNormedGroup n
  exact AddMonoidHomClass.isometry_of_norm (recoverySurgeryHilbertEmbedding n) (fun _ => rfl)

def recoverySurgeryCompletion (n : ℕ) :
    letI := recoverySurgeryQuotientNormedGroup n
    AbstractCompletion (Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) := by
  letI := recoverySurgeryQuotientNormedGroup n
  exact {
    space := cubicDefectHilbert
    coe := recoverySurgeryHilbertEmbedding n
    uniformStruct := inferInstance
    complete := cubicDefectHilbert_complete
    separation := inferInstance
    isUniformInducing := (recoverySurgeryHilbertEmbedding_isometry n).isUniformInducing
    dense := recoverySurgeryHilbertEmbedding_denseRange n }

theorem recoverySurgeryQuotientNorm_sq (n : ℕ)
    (x : Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) :
    letI := recoverySurgeryQuotientNormedGroup n
    ‖x‖^2=∑' k, (recoverySurgeryGap n k)^2*((cubicCuspDefectEquiv x).coeff k)^2 :=
  recoverySurgeryHilbertEmbedding_norm_sq n x

theorem recoverySurgeryQuotientBasis_norm (n k : ℕ) :
    letI := recoverySurgeryQuotientNormedGroup n
    ‖cubicCuspDefectBasis k‖=recoverySurgeryGap n k := by
  letI := recoverySurgeryQuotientNormedGroup n
  change ‖recoverySurgeryHilbertEmbedding n (cubicCuspDefectBasis k)‖=_
  rw [recoverySurgeryHilbertEmbedding_basis, norm_smul, cubicHilbertBasis.orthonormal.1 k,
    mul_one, Real.norm_eq_abs, abs_of_pos (recoverySurgeryGap_positive n k)]

theorem recoveryHomogeneous_quotient_class (k : ℕ) (P : cubicHomogeneousSpace (k+1)) :
    (Submodule.Quotient.mk P.val : Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) =
      cubicGradedCoefficient k P • cubicCuspDefectBasis k := by
  apply cubicCuspDefectEquiv.injective
  rw [map_smul, cubicCuspDefectEquiv_mk]
  apply Polynomial.ext
  intro i
  rw [coeff_smul, recoveryCuspBasis_coefficient, smul_eq_mul]
  by_cases hi : k=i
  · subst i
    rw [if_pos rfl, mul_one]
    change (P.val.coeff 1).coeff k = (P.val.coeff (k+1-k)).coeff k
    rw [show k+1-k=1 by omega]
  · rw [if_neg hi, mul_zero]
    have hP := P.property
    rw [cubicHomogeneousSpace_mem,cubicPolynomialFlow_halfWeight] at hP
    exact hP 1 i (by omega)

theorem recoverySurgeryHomogeneous_quotient_norm (n k : ℕ) (P : cubicHomogeneousSpace (k+1)) :
    letI := recoverySurgeryQuotientNormedGroup n
    ‖(Submodule.Quotient.mk P.val : Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule)‖ =
      recoverySurgeryDefectNorm n k (cubicGradedDefectMk k P) := by
  letI := recoverySurgeryQuotientNormedGroup n
  letI := recoverySurgeryQuotientNormedSpace n
  rw [recoveryHomogeneous_quotient_class, norm_smul, recoverySurgeryQuotientBasis_norm,
    recoverySurgeryDefectNorm_eq, cubicGradedDefectCoordinate_mk, Real.norm_eq_abs]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor

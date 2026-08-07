import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Matrix.Hermitian

/-!
# A joint orthonormal eigenbasis for a star-commuting matrix family

A finite family of complex matrices that commutes both with itself and with all adjoints is a
commuting normal family.  This file packages the finite-dimensional simultaneous spectral theorem
in the exact form needed by the factorizing-scattering rigidity argument.

The proof splits every matrix into its self-adjoint real and imaginary parts, applies mathlib's
joint-eigenspace theorem to that symmetric family, restricts the a priori infinite character
decomposition to finitely many nonzero summands using compactness of the finite-dimensional top
submodule, and collects orthonormal bases of those summands.
-/

namespace GaloisForLFunctions.HTGeometry

open Module.End
open scoped ComplexStarModule Function

/-- Real (`true`) or imaginary (`false`) self-adjoint part of a complex square matrix. -/
noncomputable def matrixSelfAdjointPart {κ : Type*} [Fintype κ] [DecidableEq κ]
    (realPart : Bool) (A : Matrix κ κ ℂ) : Matrix κ κ ℂ :=
  if realPart then (ℜ A : Matrix κ κ ℂ) else (ℑ A : Matrix κ κ ℂ)

theorem matrixSelfAdjointPart_isHermitian {κ : Type*} [Fintype κ] [DecidableEq κ]
    (realPart : Bool) (A : Matrix κ κ ℂ) :
    (matrixSelfAdjointPart realPart A).IsHermitian := by
  classical
  simp only [matrixSelfAdjointPart]
  split <;> exact IsSelfAdjoint.isHermitian selfAdjoint.isSelfAdjoint

/-- Real and imaginary parts of a family commute pairwise when the original matrices commute
pairwise both with one another and with all adjoints. -/
theorem matrixSelfAdjointPart_commute {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    (A : ι → Matrix κ κ ℂ)
    (hcomm : ∀ p q, Commute (A p) (A q))
    (hstar : ∀ p q, Commute (A p) (star (A q)))
    (p q : ι) (e f : Bool) :
    Commute (matrixSelfAdjointPart e (A p)) (matrixSelfAdjointPart f (A q)) := by
  classical
  have haa : Commute (A p) (A q) := hcomm p q
  have has : Commute (A p) (star (A q)) := hstar p q
  have hsa : Commute (star (A p)) (A q) := (hstar q p).symm
  have hss : Commute (star (A p)) (star (A q)) := haa.star_star
  have h_add_add : Commute (A p + star (A p)) (A q + star (A q)) :=
    (haa.add_right has).add_left (hsa.add_right hss)
  have h_add_sub : Commute (A p + star (A p)) (A q - star (A q)) :=
    (haa.sub_right has).add_left (hsa.sub_right hss)
  have h_sub_add : Commute (A p - star (A p)) (A q + star (A q)) :=
    (haa.add_right has).sub_left (hsa.add_right hss)
  have h_sub_sub : Commute (A p - star (A p)) (A q - star (A q)) :=
    (haa.sub_right has).sub_left (hsa.sub_right hss)
  simp only [matrixSelfAdjointPart]
  split <;> split
  · rw [realPart_apply_coe, realPart_apply_coe]
    exact (h_add_add.smul_left _).smul_right _
  · rw [realPart_apply_coe, imaginaryPart_apply_coe]
    exact ((h_add_sub.smul_left _).smul_right _).smul_right _
  · rw [imaginaryPart_apply_coe, realPart_apply_coe]
    exact ((h_sub_add.smul_left _).smul_left _).smul_right _
  · rw [imaginaryPart_apply_coe, imaginaryPart_apply_coe]
    exact (((h_sub_sub.smul_left _).smul_left _).smul_right _).smul_right _

set_option maxHeartbeats 800000 in
/-- **Simultaneous spectral theorem for a star-commuting matrix family.**  A family of finite
complex matrices that commutes pairwise and commutes pairwise with all adjoints has a common
orthonormal eigenbasis.  No cardinality assumption on the family is needed. -/
theorem exists_orthonormalBasis_eigen_of_pairwise_commute_star
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    (A : ι → Matrix κ κ ℂ)
    (hcomm : ∀ p q, Commute (A p) (A q))
    (hstar : ∀ p q, Commute (A p) (star (A q))) :
    ∃ b : OrthonormalBasis (Fin (Fintype.card κ)) ℂ (EuclideanSpace ℂ κ),
      ∀ p i, ∃ μ : ℂ, Matrix.toEuclideanLin (A p) (b i) = μ • b i := by
  classical
  let T : Bool × ι → Module.End ℂ (EuclideanSpace ℂ κ) := fun q =>
    Matrix.toEuclideanLin (matrixSelfAdjointPart q.1 (A q.2))
  have hT : ∀ q, (T q).IsSymmetric := by
    intro q
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (matrixSelfAdjointPart_isHermitian q.1 (A q.2))
  have hC : Pairwise (Commute on T) := by
    intro p q _
    change Commute (T p) (T q)
    change (T p).comp (T q) = (T q).comp (T p)
    change (Matrix.toLin (EuclideanSpace.basisFun κ ℂ).toBasis
        (EuclideanSpace.basisFun κ ℂ).toBasis (matrixSelfAdjointPart p.1 (A p.2))).comp
      (Matrix.toLin (EuclideanSpace.basisFun κ ℂ).toBasis
        (EuclideanSpace.basisFun κ ℂ).toBasis (matrixSelfAdjointPart q.1 (A q.2))) =
      (Matrix.toLin (EuclideanSpace.basisFun κ ℂ).toBasis
        (EuclideanSpace.basisFun κ ℂ).toBasis (matrixSelfAdjointPart q.1 (A q.2))).comp
      (Matrix.toLin (EuclideanSpace.basisFun κ ℂ).toBasis
        (EuclideanSpace.basisFun κ ℂ).toBasis (matrixSelfAdjointPart p.1 (A p.2)))
    rw [← Matrix.toLin_mul, ← Matrix.toLin_mul]
    exact congrArg (Matrix.toLin (EuclideanSpace.basisFun κ ℂ).toBasis
      (EuclideanSpace.basisFun κ ℂ).toBasis)
      (matrixSelfAdjointPart_commute A hcomm hstar p.2 q.2 p.1 q.1).eq
  let V : ((Bool × ι) → ℂ) → Submodule ℂ (EuclideanSpace ℂ κ) := fun χ =>
    ⨅ q, Module.End.eigenspace (T q) (χ q)
  let hO : OrthogonalFamily ℂ (fun χ => V χ) (fun χ => (V χ).subtypeₗᵢ) :=
    LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hT
  have htop : ⨆ χ, V χ = ⊤ :=
    LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT hC
  let b0 := stdOrthonormalBasis ℂ (EuclideanSpace ℂ κ)
  have hcompact : IsCompactElement (⊤ : Submodule ℂ (EuclideanSpace ℂ κ)) := by
    rw [← b0.toBasis.span_eq]
    exact Submodule.finite_span_isCompactElement _ (Set.finite_range (⇑b0.toBasis))
  obtain ⟨s, hs⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup
    (Submodule ℂ (EuclideanSpace ℂ κ)) hcompact V (by rw [htop])
  have hs_top : ⨆ χ : ↥s, V χ.1 = ⊤ := by
    apply top_unique
    rw [iSup_subtype]
    exact hs
  let hOs : OrthogonalFamily ℂ (fun χ : ↥s => V χ.1)
      (fun χ => (V χ.1).subtypeₗᵢ) := hO.comp Subtype.val_injective
  let hI : DirectSum.IsInternal (fun χ : ↥s => V χ.1) := by
    apply hOs.isInternal_iff.mpr
    rw [hs_top, Submodule.top_orthogonal_eq_bot]
  let b : OrthonormalBasis (Fin (Fintype.card κ)) ℂ (EuclideanSpace ℂ κ) :=
    hI.subordinateOrthonormalBasis finrank_euclideanSpace hOs
  refine ⟨b, fun p i => ?_⟩
  let χ : ↥s := hI.subordinateOrthonormalBasisIndex finrank_euclideanSpace i hOs
  have hbmem : b i ∈ V χ.1 :=
    hI.subordinateOrthonormalBasis_subordinate finrank_euclideanSpace i hOs
  change b i ∈ ⨅ q, Module.End.eigenspace (T q) (χ.1 q) at hbmem
  have hreal : T (true, p) (b i) = χ.1 (true, p) • b i :=
    Module.End.mem_eigenspace_iff.mp
      ((Submodule.mem_iInf (fun q => Module.End.eigenspace (T q) (χ.1 q))).mp hbmem (true, p))
  have himag : T (false, p) (b i) = χ.1 (false, p) • b i :=
    Module.End.mem_eigenspace_iff.mp
      ((Submodule.mem_iInf (fun q => Module.End.eigenspace (T q) (χ.1 q))).mp hbmem (false, p))
  refine ⟨χ.1 (true, p) + Complex.I * χ.1 (false, p), ?_⟩
  have hdecomp :
      (ℜ (A p) : Matrix κ κ ℂ) + Complex.I • (ℑ (A p) : Matrix κ κ ℂ) = A p :=
    realPart_add_I_smul_imaginaryPart (A p)
  rw [← hdecomp, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  change T (true, p) (b i) + Complex.I • T (false, p) (b i) = _
  rw [hreal, himag, smul_smul, add_smul]

end GaloisForLFunctions.HTGeometry

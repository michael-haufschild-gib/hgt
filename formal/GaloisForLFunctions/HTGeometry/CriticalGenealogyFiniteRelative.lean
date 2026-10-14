import GaloisForLFunctions.HTGeometry.CriticalGenealogyTraceClass
import GaloisForLFunctions.HTGeometry.PrefixGramRelativeOperator
import GaloisForLFunctions.HTGeometry.FiniteSupportFredholmProduct
import GaloisForLFunctions.HTGeometry.ScalarCertificateFredholmRecovery

/-! # Literal critical-relative finite determinants

The native genealogy preserves every coordinate prefix. Its relative Gram
section is therefore a finite supported operator on the original Hilbert space,
and its actual Fredholm determinant is the quotient of the two original Gram
determinants.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open _root_.ContinuousLinearMap _root_.RHTower HilbertSchmidt

theorem scalarCertificatePrefix_eq_comp_projection (a : CertStream) (N : ℕ) :
    scalarCertificatePrefix a N = a.genealogy ∘L paperCoordinateProjection N := by
  ext x n
  simp only [scalarCertificatePrefix, paperCoordinateCompression, comp_apply,
    paperCoordinateProjection_coordinate, CertStream.genealogy_apply]
  by_cases hn : n < N
  · simp [hn]
  · have hn1 : ¬ n + 1 < N := by omega
    simp [hn, hn1]

def criticalGenealogyPrefixRelative (a : CertStream) (N : ℕ) : ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  prefixGramRelativeOperator (criticalCertificatePerturbation a).genealogy
    CertStream.stationaryCritical.genealogy N

theorem criticalGenealogyPrefixRelative_eq_resolvent (a : CertStream) (N : ℕ) :
    criticalGenealogyPrefixRelative a N = prefixGramResolvent CertStream.stationaryCritical.genealogy N ∘L
      ((scalarCertificatePrefix (criticalCertificatePerturbation a) N).adjoint ∘L
        scalarCertificatePrefix (criticalCertificatePerturbation a) N -
      (scalarCertificatePrefix CertStream.stationaryCritical N).adjoint ∘L
        scalarCertificatePrefix CertStream.stationaryCritical N) := by
  rw [criticalGenealogyPrefixRelative, prefixGramRelativeOperator_eq_resolvent_sub]
  simp only [← scalarCertificatePrefix_eq_comp_projection, unitGramOperator]
  congr 1
  abel

private theorem prefix_gram_schatten (a : CertStream) (N : ℕ) :
    MemSchattenClass 1 ((scalarCertificatePrefix a N).adjoint ∘L scalarCertificatePrefix a N) := by
  rw [scalarCertificatePrefix_eq]
  exact finiteScalarGenealogy_gram_traceClass _ _

theorem criticalGenealogyPrefixRelative_schatten (a : CertStream) (N : ℕ) :
    MemSchattenClass 1 (criticalGenealogyPrefixRelative a N) := by
  rw [criticalGenealogyPrefixRelative_eq_resolvent]
  exact memSchattenClass_one_comp_left
    ((prefix_gram_schatten _ N).one_sub (prefix_gram_schatten _ N)) _

private theorem projection_basis_outside (N j : ℕ) (hj : ¬ j < N) :
    paperCoordinateProjection N (lpBasisVec j) = 0 := by
  apply lp.ext
  funext i
  simp only [paperCoordinateProjection_coordinate, lpBasisVec, lp.single_apply,
    lp.coeFn_zero, Pi.zero_apply]
  by_cases hi : j = i
  · subst i
    simp [hj]
  · simp [hi]

theorem criticalGenealogyPrefixRelative_coordinate_support (a : CertStream) (N : ℕ)
    (p : ℕ × ℕ) (hp : p ∉ Finset.range N ×ˢ Finset.range N) :
    coordMatrix (lpBasis ℕ) (criticalGenealogyPrefixRelative a N) p = 0 := by
  rcases p with ⟨i, j⟩
  rw [coordMatrix_apply, lpBasis_apply, lpBasis_apply]
  change inner ℂ (lpBasisVec i) (criticalGenealogyPrefixRelative a N (lpBasisVec j)) = 0
  rw [inner_lpBasisVec]
  change prefixGramInverse CertStream.stationaryCritical.genealogy N
    ((unitGramOperator (criticalCertificatePerturbation a).genealogy -
      unitGramOperator CertStream.stationaryCritical.genealogy)
      (paperCoordinateProjection N (lpBasisVec j))) i = 0
  by_cases hi : i < N
  · have hj : ¬ j < N := fun hj => hp (Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hi, Finset.mem_range.mpr hj⟩)
    rw [projection_basis_outside N j hj, map_zero, map_zero]
    rfl
  · exact prefixGramInverse_coordinate_outside _ N _ i hi

theorem fredholmDetOp_criticalGenealogyPrefixRelative_mul_reference (a : CertStream) (N : ℕ) :
    fredholmDetOp (lpBasis ℕ) (criticalGenealogyPrefixRelative a N) *
      scalarCertificateGramDet CertStream.stationaryCritical N =
        scalarCertificateGramDet (criticalCertificatePerturbation a) N := by
  let S := (scalarCertificatePrefix CertStream.stationaryCritical N).adjoint ∘L
    scalarCertificatePrefix CertStream.stationaryCritical N
  let T := (scalarCertificatePrefix (criticalCertificatePerturbation a) N).adjoint ∘L
    scalarCertificatePrefix (criticalCertificatePerturbation a) N
  let F := criticalGenealogyPrefixRelative a N
  have hS : ∀ p, p ∉ Finset.range N ×ˢ Finset.range N → coordMatrix (lpBasis ℕ) S p = 0 := by
    dsimp [S]
    rw [scalarCertificatePrefix_eq]
    exact finiteScalarGenealogy_gram_coordinate_support _ N
  have he := prefixGramRelativeOperator_equation (criticalCertificatePerturbation a).genealogy
    CertStream.stationaryCritical.genealogy N
  simp only [← scalarCertificatePrefix_eq_comp_projection, unitGramOperator] at he
  change (1 + S) * F = (1 + T) - (1 + S) at he
  have hsum : S + F + S ∘L F = T := by
    change S + F + S * F = T
    calc
      S + F + S * F = S + (1 + S) * F := by noncomm_ring
      _ = S + ((1 + T) - (1 + S)) := by rw [he]
      _ = T := by abel
  have hdet := fredholmDetOp_finite_product (lpBasis ℕ) S F (prefix_gram_schatten _ N)
    (criticalGenealogyPrefixRelative_schatten a N) (Finset.range N) hS
    (criticalGenealogyPrefixRelative_coordinate_support a N)
  rw [hsum] at hdet
  exact (mul_comm _ _).trans hdet.symm

theorem fredholmDetOp_criticalGenealogyPrefixRelative (a : CertStream) (N : ℕ) :
    fredholmDetOp (lpBasis ℕ) (criticalGenealogyPrefixRelative a N) =
      scalarCertificateGramDet (criticalCertificatePerturbation a) N /
        scalarCertificateGramDet CertStream.stationaryCritical N := by
  have hb : scalarCertificateGramDet CertStream.stationaryCritical N ≠ 0 := by
    rw [scalarCertificateGramDet_eq]
    exact_mod_cast (finiteGenealogyGramValue_pos
      (fun n => (CertStream.stationaryCritical.c n : ℂ)) N).ne'
  exact (eq_div_iff hb).mpr (fredholmDetOp_criticalGenealogyPrefixRelative_mul_reference a N)

end
end GaloisForLFunctions.HTGeometry

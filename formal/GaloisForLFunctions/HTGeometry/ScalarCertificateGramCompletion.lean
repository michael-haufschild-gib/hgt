import GaloisForLFunctions.HTGeometry.ScalarGenealogyGramCompletion
import GaloisForLFunctions.HTGeometry.ScalarCertificateFredholmRecovery

/-! # Canonical Gram determinant completion for positive certificate streams

The original genealogy has a normalized determinant completion exactly when its
weighted backward part is Hilbert–Schmidt. This is exactly square-summability of
the positive certificate coefficients, with no additional analytic premise.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open HilbertSchmidt _root_.ContinuousLinearMap Filter Topology

private theorem coefficient_norm (a : CertStream) (n : ℕ) : ‖(a.c n : ℂ)‖ = a.c n := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (a.pos n)]

theorem scalarCertificate_genealogy_basis (a : CertStream) (j : ℕ) :
    a.genealogy (lpBasisVec j) = finiteGenealogyColumn (fun n => (a.c n : ℂ)) j :=
  fullScalarGenealogy_basis_of_apply (fun f n => a.genealogy_apply f n) j

theorem scalarCertificate_weight_isHilbertSchmidt_iff (a : CertStream) :
    IsHilbertSchmidt a.weight ↔ Summable (fun n => a.c n ^ 2) := by
  have h := fullGenealogyWeight_isHilbertSchmidt_iff (scalarCertificate_genealogy_basis a)
  have he : 1 - a.genealogy = a.weight := by
    change 1 - (1 - a.weight) = a.weight
    abel
  rw [he] at h
  simpa only [coefficient_norm] using h

def scalarCertificateNormalizedGram (a : CertStream) (N : ℕ) : ℂ :=
  scalarCertificateGramDet a N / 2 ^ N

theorem scalarCertificateNormalizedGram_eq (a : CertStream) (N : ℕ) :
    scalarCertificateNormalizedGram a N =
      (normalizedGenealogyGram (fun n => (a.c n : ℂ)) N : ℂ) := by
  simp [scalarCertificateNormalizedGram, scalarCertificateGramDet_eq, normalizedGenealogyGram]

def scalarCertificateGramCompletion (a : CertStream) : ℂ :=
  scalarGenealogyGramCompletion a.genealogy (fun n => (a.c n : ℂ))

theorem scalarCertificateGramCompletion_formula (a : CertStream) :
    scalarCertificateGramCompletion a =
      RHTower.det2Op (lpBasis ℕ) (genealogyGramPerturbation a.genealogy) *
        Complex.exp ((1 / 2 : ℂ) * ((∑' n, a.c n ^ 2 : ℝ) : ℂ)) := by
  simp only [scalarCertificateGramCompletion, scalarGenealogyGramCompletion, coefficient_norm]

theorem scalarCertificateGramCompletion_iff (a : CertStream) :
    ((scalarCertificateGramCompletion a).im = 0 ∧
      1 ≤ (scalarCertificateGramCompletion a).re ∧
      Tendsto (scalarCertificateNormalizedGram a) atTop (𝓝 (scalarCertificateGramCompletion a))) ↔
      Summable (fun n => a.c n ^ 2) := by
  have he : scalarCertificateNormalizedGram a =
      fun N => (normalizedGenealogyGram (fun n => (a.c n : ℂ)) N : ℂ) :=
    funext (scalarCertificateNormalizedGram_eq a)
  rw [he]
  simpa only [scalarCertificateGramCompletion, coefficient_norm]
    using scalarGenealogyGramCompletion_spec_iff (scalarCertificate_genealogy_basis a)

theorem scalarCertificateGramCompletion_hilbertSchmidt_iff (a : CertStream) :
    ((scalarCertificateGramCompletion a).im = 0 ∧
      1 ≤ (scalarCertificateGramCompletion a).re ∧
      Tendsto (scalarCertificateNormalizedGram a) atTop (𝓝 (scalarCertificateGramCompletion a))) ↔
      IsHilbertSchmidt a.weight :=
  (scalarCertificateGramCompletion_iff a).trans (scalarCertificate_weight_isHilbertSchmidt_iff a).symm

theorem scalarCertificateNormalizedGram_diverges_iff (a : CertStream) :
    Tendsto (fun N => (scalarCertificateNormalizedGram a N).re) atTop atTop ↔
      ¬ Summable (fun n => a.c n ^ 2) := by
  simpa only [scalarCertificateNormalizedGram_eq, Complex.ofReal_re, coefficient_norm]
    using normalizedGenealogyGram_tendsto_atTop_iff (fun n => (a.c n : ℂ))

end
end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.FiniteGenealogyFredholm
import GaloisForLFunctions.HTGeometry.CertificatePolarGenealogy
import GaloisForLFunctions.HTGeometry.PaperCoordinateCompression

/-! # Exact recovery of the original positive certificate stream

Every prefix is the literal two-sided coordinate compression of `CertStream.genealogy`.
The full-Hilbert-space Gram determinant sequence determines every positive coefficient.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open HilbertSchmidt _root_.ContinuousLinearMap

def scalarCertificatePrefix (a : CertStream) (N : ℕ) :
    lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  paperCoordinateCompression a.genealogy N

theorem scalarCertificatePrefix_eq (a : CertStream) (N : ℕ) :
    scalarCertificatePrefix a N = finiteScalarGenealogy (fun n => (a.c n : ℂ)) N := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext n
  simp only [scalarCertificatePrefix, paperCoordinateCompression, comp_apply,
    paperCoordinateProjection_coordinate, CertStream.genealogy_apply,
    finiteScalarGenealogy_apply_coordinate]
  by_cases hn : n < N
  · simp [hn]
  · have hs : ¬ n + 1 < N := by omega
    simp [hn, hs]

theorem scalarCertificatePrefix_smul_fredholmDet (a : CertStream) (N : ℕ) (z : ℂ) :
    RHTower.fredholmDetOp (lpBasis ℕ) (z • scalarCertificatePrefix a N) = (1 + z) ^ N := by
  rw [scalarCertificatePrefix_eq, fredholmDetOp_smul_finiteScalarGenealogy]

def scalarCertificateGramDet (a : CertStream) (N : ℕ) : ℂ :=
  RHTower.fredholmDetOp (lpBasis ℕ)
    ((scalarCertificatePrefix a N).adjoint ∘L scalarCertificatePrefix a N)

theorem scalarCertificateGramDet_eq (a : CertStream) (N : ℕ) :
    scalarCertificateGramDet a N =
      (finiteGenealogyGramValue (fun n => (a.c n : ℂ)) N : ℂ) := by
  rw [scalarCertificateGramDet, scalarCertificatePrefix_eq, fredholmDetOp_finiteScalarGenealogy_gram]

private theorem positiveCertificate_norm (a : CertStream) (n : ℕ) : ‖(a.c n : ℂ)‖ = a.c n := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (a.pos n)]

@[simp] theorem scalarCertificateGramDet_zero (a : CertStream) :
    scalarCertificateGramDet a 0 = 1 := by simp [scalarCertificateGramDet_eq]

@[simp] theorem scalarCertificateGramDet_one (a : CertStream) :
    scalarCertificateGramDet a 1 = 2 := by simp [scalarCertificateGramDet_eq]

theorem scalarCertificateGramDet_recurrence (a : CertStream) (N : ℕ) :
    scalarCertificateGramDet a (N + 2) = 2 * scalarCertificateGramDet a (N + 1) +
      (a.c N : ℂ) ^ 2 *
        (scalarCertificateGramDet a (N + 1) - scalarCertificateGramDet a N) := by
  simp only [scalarCertificateGramDet_eq, finiteGenealogyGramValue_succ_succ,
    positiveCertificate_norm]
  push_cast
  rfl

theorem scalarCertificateGramDet_increment_pos (a : CertStream) (N : ℕ) :
    0 < (scalarCertificateGramDet a (N + 1) - scalarCertificateGramDet a N).re := by
  simpa [scalarCertificateGramDet_eq] using
    finiteGenealogyGramValue_increment_pos (fun n => (a.c n : ℂ)) N

theorem scalarCertificateGramDet_two_pow_le (a : CertStream) (N : ℕ) :
    (2 : ℝ) ^ N ≤ (scalarCertificateGramDet a N).re := by
  simpa [scalarCertificateGramDet_eq] using
    two_pow_le_finiteGenealogyGramValue (fun n => (a.c n : ℂ)) N

theorem scalarCertificateGramDet_recovers_sq (a : CertStream) (N : ℕ) :
    a.c N ^ 2 =
      ((scalarCertificateGramDet a (N + 2)).re - 2 * (scalarCertificateGramDet a (N + 1)).re) /
        ((scalarCertificateGramDet a (N + 1)).re - (scalarCertificateGramDet a N).re) := by
  simpa only [scalarCertificateGramDet_eq, Complex.ofReal_re, positiveCertificate_norm] using
    finiteGenealogyGramValue_recovers_norm_sq (fun n => (a.c n : ℂ)) N

theorem scalarCertificateGramDet_recovers_coefficient (a : CertStream) (N : ℕ) :
    a.c N = Real.sqrt
      (((scalarCertificateGramDet a (N + 2)).re - 2 * (scalarCertificateGramDet a (N + 1)).re) /
        ((scalarCertificateGramDet a (N + 1)).re - (scalarCertificateGramDet a N).re)) := by
  rw [← scalarCertificateGramDet_recovers_sq, Real.sqrt_sq (a.pos N).le]

theorem scalarCertificateGramDet_eq_iff (a b : CertStream) :
    (∀ N, scalarCertificateGramDet a N = scalarCertificateGramDet b N) ↔ a.c = b.c := by
  simp only [scalarCertificateGramDet_eq, Complex.ofReal_inj, finiteGenealogyGramValue_eq_iff,
    positiveCertificate_norm]
  exact funext_iff.symm

theorem scalarCertificateGramDet_zeroCost_recovery (a : CertStream) (N : ℕ) :
    compactOperatorTraceCost (lp (fun _ : ℕ => ℂ) 2) (scalarCertificatePrefix a N) = 0 ∧
      a.c N = Real.sqrt
        (((scalarCertificateGramDet a (N + 2)).re - 2 * (scalarCertificateGramDet a (N + 1)).re) /
          ((scalarCertificateGramDet a (N + 1)).re - (scalarCertificateGramDet a N).re)) :=
  ⟨compactOperatorTraceCost_paperCoordinateCompression a.genealogy N,
    scalarCertificateGramDet_recovers_coefficient a N⟩

end
end GaloisForLFunctions.HTGeometry

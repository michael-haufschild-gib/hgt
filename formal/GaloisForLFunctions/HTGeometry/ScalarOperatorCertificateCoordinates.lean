import GaloisForLFunctions.HTGeometry.HilbertBasisUnitaryFredholm
import GaloisForLFunctions.HTGeometry.ConstitutiveDependentLpGaugeTransport
import GaloisForLFunctions.HTGeometry.PaperGenealogyTraceCompletion
import GaloisForLFunctions.HTGeometry.LpTwoMatrixOperators

/-! # Exact scalar coordinates for the original one-dimensional certificate fibre

The original `FibSeq 1` carrier is unitarily identified with scalar `ℓ²(ℕ)`.
Both the full genealogy and every literal prefix retain their exact action.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open HilbertSchmidt

def scalarCertificateFiberCoordinates : Fib 1 ≃ₗᵢ[ℂ] ℂ :=
  (OrthonormalBasis.singleton (Fin 1) ℂ).repr.symm

theorem scalarCertificateFiberCoordinates_apply (v : Fib 1) :
    scalarCertificateFiberCoordinates v = v 0 := by
  change (OrthonormalBasis.singleton (Fin 1) ℂ).repr.symm v = v 0
  apply (OrthonormalBasis.singleton (Fin 1) ℂ).repr.injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext i
  simp [OrthonormalBasis.singleton_repr, Subsingleton.elim i (0 : Fin 1)]

def scalarCertificateCoordinates : FibSeq 1 ≃ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  lpFamilyIsometryEquiv (by norm_num) (fun _ => scalarCertificateFiberCoordinates)

theorem scalarCertificateCoordinates_apply (f : FibSeq 1) (n : ℕ) :
    scalarCertificateCoordinates f n = f n 0 :=
  scalarCertificateFiberCoordinates_apply (f n)

theorem scalarCertificateCoordinates_symm_apply (f : lp (fun _ : ℕ => ℂ) 2) (n : ℕ) :
    scalarCertificateCoordinates.symm f n 0 = f n := by
  have h := congrArg (fun x : lp (fun _ : ℕ => ℂ) 2 => x n)
    (scalarCertificateCoordinates.apply_symm_apply f)
  simpa only [scalarCertificateCoordinates_apply] using h

def scalarCertificateBasis : HilbertBasis ℕ ℂ (FibSeq 1) :=
  unitaryHilbertBasis (lpBasis ℕ) scalarCertificateCoordinates.symm

theorem scalarCertificateBasis_apply (j n : ℕ) :
    scalarCertificateBasis j n 0 = if n = j then 1 else 0 := by
  rw [scalarCertificateBasis, unitaryHilbertBasis_apply,
    scalarCertificateCoordinates_symm_apply, lpBasis_apply]
  by_cases h : n = j
  · subst n; simp [lp.single_apply]
  · simp [lp.single_apply, h]

def scalarCertificateCoefficient (a : OpCertStream 1) (n : ℕ) : ℂ := a.C n 0 0

theorem scalarCertificateCoefficient_ne_zero (a : OpCertStream 1) (n : ℕ) :
    scalarCertificateCoefficient a n ≠ 0 := by
  have h := ((Matrix.isUnit_iff_isUnit_det (a.C n)).mp (a.unit n)).ne_zero
  simpa only [Matrix.det_fin_one, scalarCertificateCoefficient] using h

theorem scalarCertificateCoordinates_genealogy (a : OpCertStream 1) (f : FibSeq 1) (n : ℕ) :
    scalarCertificateCoordinates (a.genealogy f) n = scalarCertificateCoordinates f n -
      scalarCertificateCoefficient a n * scalarCertificateCoordinates f (n + 1) := by
  rw [scalarCertificateCoordinates_apply, OpCertStream.genealogy_apply]
  change f n 0 - matOp (a.C n) (f (n + 1)) 0 = _
  rw [matOp_apply_coord]
  simp [scalarCertificateCoefficient, scalarCertificateCoordinates_apply]

theorem scalarCertificateCoordinates_prefix (a : OpCertStream 1) (N : ℕ)
    (f : FibSeq 1) (n : ℕ) :
    scalarCertificateCoordinates (paperGenealogyPrefix a N f) n =
      (if n < N then scalarCertificateCoordinates f n else 0) -
        scalarCertificateCoefficient a n *
          (if n + 1 < N then scalarCertificateCoordinates f (n + 1) else 0) := by
  rw [scalarCertificateCoordinates_apply, paperGenealogyPrefix_coordinate]
  change ((if n < N then f n else 0) -
    matOp (a.C n) (if n + 1 < N then f (n + 1) else 0)) 0 = _
  by_cases hn : n < N <;> by_cases hs : n + 1 < N <;>
    simp [hn, hs, matOp_apply_coord, scalarCertificateCoefficient, scalarCertificateCoordinates_apply]

end
end GaloisForLFunctions.HTGeometry

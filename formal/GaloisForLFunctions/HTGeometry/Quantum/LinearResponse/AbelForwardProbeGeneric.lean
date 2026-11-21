import GaloisForLFunctions.HTGeometry.ComplexAffineLinePolynomialAvoidance
import GaloisForLFunctions.HTGeometry.SpectralDiscriminantPolynomial
import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelForwardRecovery
import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.PauliAbelRecovery

/-!
# Generic recovery from two fixed forward Abel probes

The recovery determinant is a polynomial in the couplings. Its value
at zero coupling is nonzero, so the exceptional real couplings form
a Lebesgue-null set.
-/

open Matrix Set MeasureTheory
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d N : ℕ}

/-- The numerator certificate as a polynomial in the Hamiltonian couplings. -/
def abelEnsembleCertificate (o : Fin d) (ε : Ioi (0 : ℝ))
    (P : Fin N → Matrix (Fin d) (Fin d) ℂ) : MvPolynomial (Fin N) ℂ :=
  abelForwardCertificateValue o (MvPolynomial.C (hamiltonianAbelShift ε)⁻¹)
    (spectralGenericMatrix P) ((abelDiagonalProbe d).map MvPolynomial.C)
    ((abelSumProbe d).map MvPolynomial.C)

theorem eval_abelEnsembleCertificate (o : Fin d) (ε : Ioi (0 : ℝ))
    (P : Fin N → Matrix (Fin d) (Fin d) ℂ) (θ : Fin N → ℝ) :
    MvPolynomial.eval (fun a => (θ a : ℂ)) (abelEnsembleCertificate o ε P) =
      abelForwardCertificateValue o (hamiltonianAbelShift ε)⁻¹ (spectralEnsembleMatrix P θ)
        (abelDiagonalProbe d) (abelSumProbe d) := by
  let f := MvPolynomial.eval (fun a => (θ a : ℂ))
  have hP : (spectralGenericMatrix P).map f = spectralEnsembleMatrix P θ :=
    mapMatrix_spectralGenericMatrix P θ
  have hlift (X : Matrix (Fin d) (Fin d) ℂ) :
      (X.map MvPolynomial.C).map f = X :=
    Matrix.ext fun i j => MvPolynomial.eval_C (X i j)
  change f (abelForwardCertificateValue o (MvPolynomial.C (hamiltonianAbelShift ε)⁻¹)
    (spectralGenericMatrix P) _ _) = _
  rw [map_abelForwardCertificateValue, hP, hlift, hlift]
  exact congrArg (fun γ => abelForwardCertificateValue o γ (spectralEnsembleMatrix P θ)
    (abelDiagonalProbe d) (abelSumProbe d)) (MvPolynomial.eval_C _)

theorem abelEnsembleCertificate_ne_zero (o : Fin d) (ε : Ioi (0 : ℝ))
    (P : Fin N → Matrix (Fin d) (Fin d) ℂ) : abelEnsembleCertificate o ε P ≠ 0 := by
  let θ : Fin N → ℝ := 0
  have hzero : spectralEnsembleMatrix P θ = 0 := by
    simp [θ, spectralEnsembleMatrix]
  intro h
  have he := eval_abelEnsembleCertificate o ε P θ
  rw [h, map_zero, hzero] at he
  exact abelForwardCertificateValue_zeroHamiltonian_ne_zero o _ he.symm

theorem ae_abelForwardCertificateValue_ne_zero (o : Fin d) (ε : Ioi (0 : ℝ))
    (P : Fin N → Matrix (Fin d) (Fin d) ℂ) :
    ∀ᵐ θ : Fin N → ℝ ∂volume,
      abelForwardCertificateValue o (hamiltonianAbelShift ε)⁻¹ (spectralEnsembleMatrix P θ)
        (abelDiagonalProbe d) (abelSumProbe d) ≠ 0 := by
  let Q := abelEnsembleCertificate o ε P
  have hshadow : mvPolynomialRealShadow Q ≠ 0 :=
    mvPolynomialRealShadow_ne_zero (abelEnsembleCertificate_ne_zero o ε P)
  have hae : ∀ᵐ θ : Fin N → ℝ ∂volume,
      MvPolynomial.eval θ (mvPolynomialRealShadow Q) ≠ 0 := by
    rw [ae_iff]
    simpa only [not_ne_iff] using
      mvPolynomial_zero_set_volume_real_fin N (mvPolynomialRealShadow Q) hshadow
  filter_upwards [hae] with θ hθ
  rw [← eval_abelEnsembleCertificate o ε P θ]
  exact eval₂_ne_zero_of_eval_mvPolynomialRealShadow_ne_zero hθ

/-- At a fixed width, the measured linear system reconstructs the anchored
Hamiltonian for almost every coupling vector. -/
theorem ae_abelForwardRelativeRecovery_exact (o : Fin d) (ε : Ioi (0 : ℝ))
    (P : Fin N → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ a, (P a).IsHermitian) :
    ∀ᵐ θ : Fin N → ℝ ∂volume,
      let H := spectralEnsembleMatrix P θ
      let hH := isHermitian_spectralEnsembleMatrix hP θ
      abelForwardRelativeRecovery o ε
        (hamiltonianDampedGapResponse hH 0 ε (abelDiagonalProbe d))
        (hamiltonianDampedGapResponse hH 0 ε (abelSumProbe d)) =
        H - H o o • 1 := by
  filter_upwards [ae_abelForwardCertificateValue_ne_zero o ε P] with θ hθ
  let hH := isHermitian_spectralEnsembleMatrix hP θ
  exact abelForwardRelativeRecovery_exact o hH ε
    (abelForwardReading_det_ne_zero_of_certificate o hH ε hθ)

/-- At each positive width the two readings distinguish almost every Hamiltonian
in any finite Hermitian linear family from every Hermitian competitor, up to scalars. -/
theorem ae_abelForwardReadings_eq_iff_scalarDifference (o : Fin d) (ε : Ioi (0 : ℝ))
    (P : Fin N → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ a, (P a).IsHermitian) :
    ∀ᵐ θ : Fin N → ℝ ∂volume, ∀ (K : Matrix (Fin d) (Fin d) ℂ) (hK : K.IsHermitian),
      let hH := isHermitian_spectralEnsembleMatrix hP θ
      (hamiltonianDampedGapResponse hH 0 ε (abelDiagonalProbe d) =
          hamiltonianDampedGapResponse hK 0 ε (abelDiagonalProbe d) ∧
        hamiltonianDampedGapResponse hH 0 ε (abelSumProbe d) =
          hamiltonianDampedGapResponse hK 0 ε (abelSumProbe d)) ↔
        ∃ c : ℂ, spectralEnsembleMatrix P θ - K = c • 1 := by
  filter_upwards [ae_abelForwardCertificateValue_ne_zero o ε P] with θ hθ
  intro K hK
  dsimp only
  let hH := isHermitian_spectralEnsembleMatrix hP θ
  constructor
  · rintro ⟨hD, hJ⟩
    exact scalarDifference_of_abelForwardReadings_eq o ε hH hK hθ hD hJ
  · intro hscalar
    have hfilters := (hamiltonianDampedGapResponse_zero_eq_iff_scalarDifference o hH hK ε).mpr
      hscalar
    exact ⟨congrFun hfilters (abelDiagonalProbe d), congrFun hfilters (abelSumProbe d)⟩

/-- Almost every nearest-neighbor Pauli coupling vector is determined exactly
by the two fixed forward readings at any prescribed positive width. -/
theorem ae_pauliAbelForwardReadings_eq_iff (n : ℕ) (ε : Ioi (0 : ℝ)) :
    ∀ᵐ θ : Fin (Fintype.card (ChainLabel n)) → ℝ ∂volume, ∀ η,
      let response := fun α : Fin (Fintype.card (ChainLabel n)) → ℝ =>
        hamiltonianDampedGapResponse
          (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian n) α) 0 ε
      (response θ (abelDiagonalProbe (2 ^ n)), response θ (abelSumProbe (2 ^ n))) =
        (response η (abelDiagonalProbe (2 ^ n)), response η (abelSumProbe (2 ^ n))) ↔ θ = η := by
  let o : Fin (2 ^ n) := ⟨0, by positivity⟩
  filter_upwards [ae_abelForwardReadings_eq_iff_scalarDifference o ε (chainPauliFin n)
    (chainPauliFin_isHermitian n)] with θ hθ
  intro η
  dsimp only
  constructor
  · intro h
    let hH := isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian n) θ
    let hK := isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian n) η
    have hs := (hθ (spectralEnsembleMatrix (chainPauliFin n) η) hK).mp
      ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    exact pauliAbelResponse_injective n ε
      ((hamiltonianDampedGapResponse_zero_eq_iff_scalarDifference o hH hK ε).mpr hs)
  · rintro rfl
    rfl

#print axioms abelEnsembleCertificate_ne_zero
#print axioms ae_abelForwardRelativeRecovery_exact
#print axioms ae_abelForwardReadings_eq_iff_scalarDifference
#print axioms ae_pauliAbelForwardReadings_eq_iff

end

end GaloisForLFunctions.HTGeometry

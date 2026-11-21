import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelForwardProbeCertificate
import Mathlib.Algebra.Polynomial.Roots

/-!
# Finitely many exceptional damping widths

At fixed Hamiltonian the certificate is a polynomial in the inverse
shift. Its constant term is the determinant for the original probes.
-/

open Matrix Set
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : ℕ}

/-- The recovery certificate as a polynomial in the inverse Green shift. -/
def abelWidthCertificate (o : Fin d) (H : Matrix (Fin d) (Fin d) ℂ) : Polynomial ℂ :=
  abelForwardCertificateValue o Polynomial.X (H.map Polynomial.C)
    ((abelDiagonalProbe d).map Polynomial.C) ((abelSumProbe d).map Polynomial.C)

theorem eval_abelWidthCertificate (o : Fin d) (H : Matrix (Fin d) (Fin d) ℂ) (γ : ℂ) :
    (abelWidthCertificate o H).eval γ =
      abelForwardCertificateValue o γ H (abelDiagonalProbe d) (abelSumProbe d) := by
  let f := Polynomial.evalRingHom γ
  have hlift (X : Matrix (Fin d) (Fin d) ℂ) : (X.map Polynomial.C).map f = X :=
    Matrix.ext fun i j => Polynomial.eval_C
  change f (abelForwardCertificateValue o Polynomial.X (H.map Polynomial.C) _ _) = _
  rw [map_abelForwardCertificateValue, hlift, hlift, hlift]
  exact congrArg (fun z => abelForwardCertificateValue o z H
    (abelDiagonalProbe d) (abelSumProbe d)) (Polynomial.eval_X)

theorem abelWidthCertificate_ne_zero (o : Fin d) (H : Matrix (Fin d) (Fin d) ℂ) :
    abelWidthCertificate o H ≠ 0 := by
  intro h
  have he := eval_abelWidthCertificate o H 0
  rw [h, Polynomial.eval_zero] at he
  exact abelForwardCertificateValue_zeroParameter_ne_zero o H he.symm

theorem finite_abelForwardCertificateValue_zero_width (o : Fin d) (H : Matrix (Fin d) (Fin d) ℂ) :
    {ε : Ioi (0 : ℝ) | abelForwardCertificateValue o (hamiltonianAbelShift ε)⁻¹ H
      (abelDiagonalProbe d) (abelSumProbe d) = 0}.Finite := by
  let f : Ioi (0 : ℝ) → ℂ := fun ε => (hamiltonianAbelShift ε)⁻¹
  have hinj : Function.Injective f := by
    intro ε η h
    exact Subtype.ext (congrArg Complex.im (inv_injective h))
  have hroots := (Polynomial.finite_setOf_isRoot (abelWidthCertificate_ne_zero o H)).preimage
    (f := f) hinj.injOn
  simpa only [Set.preimage_setOf_eq, Polynomial.IsRoot, eval_abelWidthCertificate, f] using hroots

/-- At fixed Hamiltonian, the widths at which two forward probes admit
a non-scalar ambiguity are finite. -/
theorem finite_abelForwardReadings_ambiguous_width (o : Fin d)
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian) :
    {ε : Ioi (0 : ℝ) | ∃ (K : Matrix (Fin d) (Fin d) ℂ) (hK : K.IsHermitian),
      hamiltonianDampedGapResponse hH 0 ε (abelDiagonalProbe d) =
        hamiltonianDampedGapResponse hK 0 ε (abelDiagonalProbe d) ∧
      hamiltonianDampedGapResponse hH 0 ε (abelSumProbe d) =
        hamiltonianDampedGapResponse hK 0 ε (abelSumProbe d) ∧
      ¬ ∃ c : ℂ, H - K = c • 1}.Finite := by
  apply (finite_abelForwardCertificateValue_zero_width o H).subset
  rintro ε ⟨K, hK, hD, hJ, hn⟩
  exact not_not.mp fun hc =>
    hn (scalarDifference_of_abelForwardReadings_eq o ε hH hK hc hD hJ)

#print axioms abelWidthCertificate_ne_zero
#print axioms finite_abelForwardReadings_ambiguous_width

end

end GaloisForLFunctions.HTGeometry

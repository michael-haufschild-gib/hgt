import GaloisForLFunctions.HilbertMetric.PseudospectrumSimilarity
import GaloisForLFunctions.HTGeometry.NonlocalSourceChiralPolarization

/-!
# Pseudospectra of source-defined chiral polarizations

The source-defined chiral operator is an exact positive-root similarity of its Hermitian dilation.
Equation (8) of Krejčiřík--Siegl--Tater--Viola, arXiv:1402.1082, therefore supplies both exact
spectrum preservation and a condition-number pseudospectral sandwich for every nonempty finite
source.  This upgrades the existing characteristic-divisor and metric-adjoint results to the
norm-resolvent level without inspecting any eigenvalues.
-/

open Complex Matrix Polynomial Set
open scoped ComplexOrder Matrix Matrix.Norms.L2Operator
open GaloisForLFunctions.HilbertMetric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Positive nonlocal source root bundled as a matrix unit. -/
def sourceEscapingNonlocalRootUnit (k : ℕ) (C : Matrix m m ℂ) :
    (Matrix (m ⊕ m) (m ⊕ m) ℂ)ˣ :=
  Matrix.nonsingInvUnit (sourceEscapingNonlocalRoot k C)
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (sourceEscapingNonlocalRoot_posDef k C).isUnit)

@[simp] theorem coe_sourceEscapingNonlocalRootUnit (k : ℕ) (C : Matrix m m ℂ) :
    (sourceEscapingNonlocalRootUnit k C : Matrix (m ⊕ m) (m ⊕ m) ℂ) =
      sourceEscapingNonlocalRoot k C := rfl

@[simp] theorem coe_sourceEscapingNonlocalRootUnit_inv (k : ℕ) (C : Matrix m m ℂ) :
    (((sourceEscapingNonlocalRootUnit k C)⁻¹ :
      (Matrix (m ⊕ m) (m ⊕ m) ℂ)ˣ) : Matrix (m ⊕ m) (m ⊕ m) ℂ) =
        (sourceEscapingNonlocalRoot k C)⁻¹ := rfl

/-- Positive-root similarity preserves the exact spectrum of every source chiral operator. -/
theorem sourceEscapingChiralOperator_spectrum_eq_dilation
    (k : ℕ) (C : Matrix m m ℂ) :
    spectrum ℂ (sourceEscapingChiralOperator k C) =
      spectrum ℂ (sourceHermitianDilation C) := by
  have h := spectrum.units_conjugate
    (R := ℂ) (A := Matrix (m ⊕ m) (m ⊕ m) ℂ)
    (u := (sourceEscapingNonlocalRootUnit k C)⁻¹)
    (a := sourceHermitianDilation C)
  simpa [sourceEscapingChiralOperator, Matrix.nonsing_inv_nonsing_inv] using h

/-- Equation (8) for every source-defined chiral polarization on a nonempty finite source. -/
theorem sourceEscapingChiralOperator_pseudospectrum_sandwich
    [Nonempty m] (k : ℕ) (C : Matrix m m ℂ) (ε : PseudospectralScale) :
    normResolventPseudospectrum ℂ
          (ε.divConditionNumber (sourceEscapingNonlocalRootUnit k C)⁻¹)
          (sourceHermitianDilation C) ⊆
        normResolventPseudospectrum ℂ ε (sourceEscapingChiralOperator k C) ∧
      normResolventPseudospectrum ℂ ε (sourceEscapingChiralOperator k C) ⊆
        normResolventPseudospectrum ℂ
          (ε.mulConditionNumber (sourceEscapingNonlocalRootUnit k C)⁻¹)
          (sourceHermitianDilation C) := by
  simpa [sourceEscapingChiralOperator, Matrix.nonsing_inv_nonsing_inv] using
    normResolventPseudospectrum_similarity_sandwich
      (𝕜 := ℂ) ε (sourceEscapingNonlocalRootUnit k C)⁻¹
        (sourceHermitianDilation C)

end

end GaloisForLFunctions.HTGeometry

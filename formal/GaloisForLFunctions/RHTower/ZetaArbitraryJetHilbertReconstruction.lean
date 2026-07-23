import GaloisForLFunctions.HTGeometry.HypertranscendentalJetHilbertReconstruction
import GaloisForLFunctions.RHTower.ZetaHypertranscendental

/-!
# Arbitrary Riemann-zeta jet Hilbert reconstruction

Hilbert--Ostrowski hypertranscendence discharges the complete finite evaluation-reconstruction
interface for any finite selection of Riemann-zeta derivatives.  Repeated derivative orders are
the only obstruction.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- **Arbitrary Riemann-zeta jet reconstruction law.** A finite selection of zeta derivatives
admits pairwise-distinct samples, exact dual coefficient recovery, a positive-definite Hermitian
evaluation Gram, and positive Hilbert volume exactly when its derivative orders are distinct. -/
theorem riemannZetaDerivativeOrder_finiteEvaluationHilbertReconstruction_iff_injective
    {d : ℕ} (order : Fin d → ℕ) :
    HTGeometry.FiniteEvaluationHilbertReconstruction
        (HTGeometry.hypertranscendentalDerivativeOrderFamily riemannZeta order) ↔
      Function.Injective order :=
  GaloisForLFunctions.HTGeometry.Hypertranscendental.finiteEvaluationHilbertReconstruction_derivativeOrderFamily_iff_injective
    hypertranscendental_riemannZeta order

/-- Every initial finite Riemann-zeta jet has unconditional exact dual reconstruction, strict
evaluation Gram, and positive Hilbert volume. -/
theorem riemannZetaInitialJet_finiteEvaluationHilbertReconstruction
    (d : ℕ) :
    HTGeometry.FiniteEvaluationHilbertReconstruction
      (HTGeometry.hypertranscendentalDerivativeOrderFamily riemannZeta
        (fun j : Fin d => (j : ℕ))) :=
  (riemannZetaDerivativeOrder_finiteEvaluationHilbertReconstruction_iff_injective
    (fun j : Fin d => (j : ℕ))).2
      Fin.val_injective

end

end GaloisForLFunctions.RHTower

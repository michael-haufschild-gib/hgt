import GaloisForLFunctions.HTGeometry.DigammaHypertranscendental
import GaloisForLFunctions.HTGeometry.EvaluationMinorGeneralDomain
import GaloisForLFunctions.HTGeometry.GammaHypertranscendental
import GaloisForLFunctions.HTGeometry.HypertranscendentalFunctionJetFreeness

/-!
# Hypertranscendental derivative-jet Hilbert reconstruction

Hypertranscendence makes the complete derivative family algebraically independent.  Consequently,
an arbitrary finite derivative-order dictionary admits exact finite evaluation reconstruction and
strict Hilbert geometry precisely when the dictionary contains no repeated order.  Hölder's
Gamma and digamma theorems give unconditional instances.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Derivative functions selected by an arbitrary finite order dictionary. -/
def hypertranscendentalDerivativeOrderFamily {d : ℕ}
    (f : ℂ → ℂ) (order : Fin d → ℕ) : Fin d → ℂ → ℂ :=
  fun j => iteratedDeriv (order j) f

/-- Canonical initial derivative-order dictionary. -/
def initialDerivativeOrder (d : ℕ) : Fin d → ℕ :=
  fun j => j

/-- The canonical initial derivative-order dictionary has no collisions. -/
theorem initialDerivativeOrder_injective (d : ℕ) :
    Function.Injective (initialDerivativeOrder d) := by
  intro i j hij
  exact Fin.ext hij

/-- For a hypertranscendental function, selected derivative functions are algebraically
independent exactly when their derivative orders are distinct. -/
theorem Hypertranscendental.algebraicIndependent_derivativeOrderFamily_iff_injective
    {f : ℂ → ℂ} (hf : Hypertranscendental f)
    {d : ℕ} (order : Fin d → ℕ) :
    AlgebraicIndependent ℂ
        (hypertranscendentalDerivativeOrderFamily f order) ↔
      Function.Injective order := by
  constructor
  · intro h i j hij
    apply h.injective
    simp [hypertranscendentalDerivativeOrderFamily, hij]
  · intro horder
    exact hf.algebraicIndependent_iteratedDeriv.comp order horder

/-- The same exact collision classification holds at the linear level. -/
theorem Hypertranscendental.linearIndependent_derivativeOrderFamily_iff_injective
    {f : ℂ → ℂ} (hf : Hypertranscendental f)
    {d : ℕ} (order : Fin d → ℕ) :
    LinearIndependent ℂ
        (hypertranscendentalDerivativeOrderFamily f order) ↔
      Function.Injective order := by
  constructor
  · intro h i j hij
    apply h.injective
    simp [hypertranscendentalDerivativeOrderFamily, hij]
  · intro horder
    exact
      ((Hypertranscendental.algebraicIndependent_derivativeOrderFamily_iff_injective
        hf order).2 horder).linearIndependent

/-- **Universal hypertranscendental jet reconstruction law.** A finite selected derivative
dictionary admits pairwise-distinct samples, exact dual coefficient recovery, a positive-definite
Hermitian evaluation Gram, and positive Hilbert volume exactly when no derivative order is
repeated. -/
theorem Hypertranscendental.finiteEvaluationHilbertReconstruction_derivativeOrderFamily_iff_injective
    {f : ℂ → ℂ} (hf : Hypertranscendental f)
    {d : ℕ} (order : Fin d → ℕ) :
    FiniteEvaluationHilbertReconstruction
        (hypertranscendentalDerivativeOrderFamily f order) ↔
      Function.Injective order := by
  calc
    _ ↔ LinearIndependent ℂ
        (hypertranscendentalDerivativeOrderFamily f order) :=
      finiteEvaluationHilbertReconstruction_iff_linearIndependent
        (hypertranscendentalDerivativeOrderFamily f order)
    _ ↔ _ :=
      Hypertranscendental.linearIndependent_derivativeOrderFamily_iff_injective
        hf order

/-- Every initial finite jet of a hypertranscendental function has exact finite evaluation
reconstruction and strict Hilbert geometry. -/
theorem Hypertranscendental.initialJet_finiteEvaluationHilbertReconstruction
    {f : ℂ → ℂ} (hf : Hypertranscendental f) (d : ℕ) :
    FiniteEvaluationHilbertReconstruction
      (hypertranscendentalDerivativeOrderFamily f
        (initialDerivativeOrder d)) :=
  (Hypertranscendental.finiteEvaluationHilbertReconstruction_derivativeOrderFamily_iff_injective
    hf (initialDerivativeOrder d)).2
      (initialDerivativeOrder_injective d)

/-- Every collision-free finite dictionary of Gamma derivatives has exact finite Hilbert
reconstruction. -/
theorem gammaDerivativeOrder_finiteEvaluationHilbertReconstruction_iff_injective
    {d : ℕ} (order : Fin d → ℕ) :
    FiniteEvaluationHilbertReconstruction
        (hypertranscendentalDerivativeOrderFamily Complex.Gamma order) ↔
      Function.Injective order :=
  Hypertranscendental.finiteEvaluationHilbertReconstruction_derivativeOrderFamily_iff_injective
    hypertranscendental_gamma order

/-- Every collision-free finite dictionary of digamma derivatives has exact finite Hilbert
reconstruction. -/
theorem digammaDerivativeOrder_finiteEvaluationHilbertReconstruction_iff_injective
    {d : ℕ} (order : Fin d → ℕ) :
    FiniteEvaluationHilbertReconstruction
        (hypertranscendentalDerivativeOrderFamily Complex.digamma order) ↔
      Function.Injective order :=
  Hypertranscendental.finiteEvaluationHilbertReconstruction_derivativeOrderFamily_iff_injective
    hypertranscendental_digamma order

/-- Every initial finite Gamma jet has unconditional exact Hilbert reconstruction. -/
theorem gammaInitialJet_finiteEvaluationHilbertReconstruction (d : ℕ) :
    FiniteEvaluationHilbertReconstruction
      (hypertranscendentalDerivativeOrderFamily Complex.Gamma
        (initialDerivativeOrder d)) :=
  Hypertranscendental.initialJet_finiteEvaluationHilbertReconstruction
    hypertranscendental_gamma d

/-- Every initial finite digamma jet has unconditional exact Hilbert reconstruction. -/
theorem digammaInitialJet_finiteEvaluationHilbertReconstruction (d : ℕ) :
    FiniteEvaluationHilbertReconstruction
      (hypertranscendentalDerivativeOrderFamily Complex.digamma
        (initialDerivativeOrder d)) :=
  Hypertranscendental.initialJet_finiteEvaluationHilbertReconstruction
    hypertranscendental_digamma d

end

end GaloisForLFunctions.HTGeometry

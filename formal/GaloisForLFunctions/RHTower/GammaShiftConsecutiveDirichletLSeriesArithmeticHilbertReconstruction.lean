import GaloisForLFunctions.RHTower.GammaShiftDirichletLSeriesArithmeticHilbertReconstruction
import GaloisForLFunctions.RHTower.GammaShiftZetaJetArithmeticHilbertReconstruction

/-!
# Consecutive Gamma shifts for mixed Dirichlet-series reconstruction

The generic Gamma--Dirichlet source theorem assumes the finite Gamma-shift dictionary is
collision-free.  The canonical consecutive nonnegative-integer shifts already used by the
Gamma--zeta connector satisfy that condition.  Reusing the same shift producer removes the
remaining geometric hypothesis from the generic mixed-family conclusions; only intrinsic source
conditions on the supplied Dirichlet coefficients remain.
-/

namespace GaloisForLFunctions.RHTower

open Filter

noncomputable section

/-- Canonical consecutive Gamma jets are jointly linearly independent from every Dirichlet series
with a finite first nonzero coefficient and finite absolute-convergence abscissa. -/
theorem consecutiveGammaJetLSeriesMixedFamily_linearIndependent
    {r : ℕ}
    (c : ℕ → ℂ) (a : ℕ) (hzero : ∀ m ≤ a, c m = 0)
    (ha : c (a + 1) ≠ 0) (hc : LSeries.abscissaOfAbsConv c < ⊤)
    (mult : Fin r → ℕ) :
    LinearIndependent ℂ
      (gammaJetDirichletMixedFamily
        (consecutiveGammaShift r) mult (fun z => LSeries c z)) :=
  gammaJetLSeriesMixedFamily_linearIndependent
    c a hzero ha hc (consecutiveGammaShift r) mult
      (consecutiveGammaShift_injective r)

/-- Canonical consecutive shifts discharge the complete finite HTGeometry reconstruction
interface for every admissible mixed Gamma--Dirichlet dictionary. -/
theorem consecutiveGammaJetLSeriesMixedFamily_finiteEvaluationHilbertReconstruction
    {r : ℕ}
    (c : ℕ → ℂ) (a : ℕ) (hzero : ∀ m ≤ a, c m = 0)
    (ha : c (a + 1) ≠ 0) (hc : LSeries.abscissaOfAbsConv c < ⊤)
    (mult : Fin r → ℕ) :
    HTGeometry.FiniteEvaluationHilbertReconstruction
      (gammaJetDirichletMixedFamily
        (consecutiveGammaShift r) mult (fun z => LSeries c z)) :=
  gammaJetLSeriesMixedFamily_finiteEvaluationHilbertReconstruction
    c a hzero ha hc (consecutiveGammaShift r) mult
      (consecutiveGammaShift_injective r)

/-- Every sufficiently far-right arithmetic packet reconstructs the canonical consecutive
Gamma--Dirichlet family. -/
theorem eventually_consecutiveGammaJetLSeriesArithmeticHilbertReconstructionAt
    {r : ℕ}
    (c : ℕ → ℂ) (a : ℕ) (hzero : ∀ m ≤ a, c m = 0)
    (ha : c (a + 1) ≠ 0) (hc : LSeries.abscissaOfAbsConv c < ⊤)
    (mult : Fin r → ℕ) :
    ∀ᶠ x : ℝ in atTop,
      GammaJetLSeriesArithmeticHilbertReconstructionAt
        (consecutiveGammaShift r) mult c x :=
  eventually_gammaJetLSeriesArithmeticHilbertReconstructionAt
    c a hzero ha hc (consecutiveGammaShift r) mult
      (consecutiveGammaShift_injective r)

/-- One unit-spaced packet gives exact dual recovery and positive Hilbert volume for every
canonical consecutive Gamma--Dirichlet dictionary. -/
theorem exists_consecutiveGammaJetLSeriesArithmeticHilbertReconstructionAt
    {r : ℕ}
    (c : ℕ → ℂ) (a : ℕ) (hzero : ∀ m ≤ a, c m = 0)
    (ha : c (a + 1) ≠ 0) (hc : LSeries.abscissaOfAbsConv c < ⊤)
    (mult : Fin r → ℕ) :
    ∃ x : ℝ,
      GammaJetLSeriesArithmeticHilbertReconstructionAt
        (consecutiveGammaShift r) mult c x :=
  (eventually_consecutiveGammaJetLSeriesArithmeticHilbertReconstructionAt
    c a hzero ha hc mult).exists

end

end GaloisForLFunctions.RHTower

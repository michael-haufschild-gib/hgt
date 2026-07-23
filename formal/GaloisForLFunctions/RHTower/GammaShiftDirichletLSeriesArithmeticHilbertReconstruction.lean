import GaloisForLFunctions.HTGeometry.EvaluationMinorGeneralDomain
import GaloisForLFunctions.HilbertMetric.ComplexPrescribedEvaluationReconstruction
import GaloisForLFunctions.RHTower.GammaShiftDirichletLSeriesLinearIndependenceUniversalityLaw

/-!
# Arithmetic Hilbert reconstruction for mixed Gamma--Dirichlet families

The augmented Gamma--Dirichlet determinant is eventually nonzero on every far-right unit-spaced
square packet.  Complex prescribed-packet reconstruction converts that source determinant into
exact dual coefficient recovery and a strictly positive Hermitian Gram on the same packet.
-/

namespace GaloisForLFunctions.RHTower

open Filter
open scoped ComplexOrder

noncomputable section

/-- The literal evaluation matrix of the mixed Gamma--Dirichlet family on a unit-spaced packet is
the existing augmented source matrix. -/
theorem complexEvaluationMatrix_gammaJetLSeriesArithmeticNodes
    {r : ℕ} (shift : Fin r → ℂ) (mult : Fin r → ℕ)
    (c : ℕ → ℂ) (x : ℝ) :
    HilbertMetric.complexEvaluationMatrix
        (gammaJetDirichletMixedFamily shift mult (fun z => LSeries c z))
        (HilbertMetric.complexArithmeticNodes x) =
      gammaJetAugmentedMatrix (x : ℂ) shift mult (fun z => LSeries c z) := by
  ext row col
  simp [HilbertMetric.complexEvaluationMatrix,
    HilbertMetric.complexArithmeticNodes,
    gammaJetAugmentedMatrix_apply_eq_mixedFamily]

/-- At one real base point, the mixed Gamma--Dirichlet arithmetic packet has distinct nodes, exact
complex dual recovery, a positive-definite Hermitian Gram, and positive Hilbert volume. -/
def GammaJetLSeriesArithmeticHilbertReconstructionAt
    {r : ℕ} (shift : Fin r → ℂ) (mult : Fin r → ℕ)
    (c : ℕ → ℂ) (x : ℝ) : Prop :=
  Function.Injective
      (HilbertMetric.complexArithmeticNodes
        (n := gammaJetOrder mult + 1) x) ∧
  HilbertMetric.PrescribedComplexEvaluationDualReconstruction
    (gammaJetDirichletMixedFamily shift mult (fun z => LSeries c z))
    (HilbertMetric.complexArithmeticNodes x) ∧
  (HilbertMetric.complexEvaluationGram
    (gammaJetDirichletMixedFamily shift mult (fun z => LSeries c z))
    (HilbertMetric.complexArithmeticNodes x)).PosDef ∧
  0 < (HilbertMetric.complexEvaluationGram
    (gammaJetDirichletMixedFamily shift mult (fun z => LSeries c z))
    (HilbertMetric.complexArithmeticNodes x)).det

/-- Exact source-determinant criterion for the complete mixed Gamma--Dirichlet arithmetic Hilbert
interface. -/
theorem gammaJetLSeriesArithmeticHilbertReconstructionAt_iff_det_ne_zero
    {r : ℕ} (shift : Fin r → ℂ) (mult : Fin r → ℕ)
    (c : ℕ → ℂ) (x : ℝ) :
    GammaJetLSeriesArithmeticHilbertReconstructionAt shift mult c x ↔
      (gammaJetAugmentedMatrix (x : ℂ) shift mult
        (fun z => LSeries c z)).det ≠ 0 := by
  rw [GammaJetLSeriesArithmeticHilbertReconstructionAt]
  have hmatrix :=
    complexEvaluationMatrix_gammaJetLSeriesArithmeticNodes shift mult c x
  constructor
  · rintro ⟨_hinj, hreconstruction, _hgram, _hvolume⟩
    have hdet :=
      (HilbertMetric.prescribedComplexEvaluationDualReconstruction_iff_det_ne_zero
        (gammaJetDirichletMixedFamily shift mult (fun z => LSeries c z))
        (HilbertMetric.complexArithmeticNodes x)).mp
        hreconstruction
    rwa [hmatrix] at hdet
  · intro hdet
    have hevaluationDet :
        (HilbertMetric.complexEvaluationMatrix
          (gammaJetDirichletMixedFamily shift mult (fun z => LSeries c z))
          (HilbertMetric.complexArithmeticNodes x)).det ≠ 0 := by
      rwa [hmatrix]
    have hreconstruction :=
      (HilbertMetric.prescribedComplexEvaluationDualReconstruction_iff_det_ne_zero
        (gammaJetDirichletMixedFamily shift mult (fun z => LSeries c z))
        (HilbertMetric.complexArithmeticNodes x)).mpr
        hevaluationDet
    have hgram :=
      (HilbertMetric.prescribedComplexEvaluationDualReconstruction_iff_gram_posDef
        (gammaJetDirichletMixedFamily shift mult (fun z => LSeries c z))
        (HilbertMetric.complexArithmeticNodes x)).mp
        hreconstruction
    exact ⟨HilbertMetric.complexArithmeticNodes_injective x,
      hreconstruction, hgram, hgram.det_pos⟩

/-- Source assumptions on the Dirichlet coefficients and distinct Gamma shifts discharge the
complete finite HTGeometry Hilbert-reconstruction Prop interface. -/
theorem gammaJetLSeriesMixedFamily_finiteEvaluationHilbertReconstruction
    {r : ℕ}
    (c : ℕ → ℂ) (a : ℕ) (hzero : ∀ m ≤ a, c m = 0) (ha : c (a + 1) ≠ 0)
    (hc : LSeries.abscissaOfAbsConv c < ⊤)
    (shift : Fin r → ℂ) (mult : Fin r → ℕ)
    (hshift : Function.Injective shift) :
    HTGeometry.FiniteEvaluationHilbertReconstruction
      (gammaJetDirichletMixedFamily shift mult (fun z => LSeries c z)) :=
  (HTGeometry.finiteEvaluationHilbertReconstruction_iff_linearIndependent
    (gammaJetDirichletMixedFamily shift mult (fun z => LSeries c z))).mpr
    (gammaJetLSeriesMixedFamily_linearIndependent
      c a hzero ha hc shift mult hshift)

/-- Every sufficiently far-right unit-spaced packet satisfies the complete mixed
Gamma--Dirichlet Hilbert reconstruction interface. -/
theorem eventually_gammaJetLSeriesArithmeticHilbertReconstructionAt
    {r : ℕ}
    (c : ℕ → ℂ) (a : ℕ) (hzero : ∀ m ≤ a, c m = 0) (ha : c (a + 1) ≠ 0)
    (hc : LSeries.abscissaOfAbsConv c < ⊤)
    (shift : Fin r → ℂ) (mult : Fin r → ℕ)
    (hshift : Function.Injective shift) :
    ∀ᶠ x : ℝ in atTop,
      GammaJetLSeriesArithmeticHilbertReconstructionAt shift mult c x := by
  filter_upwards [
    gammaJetAugmentedMatrix_LSeries_det_ne_zero_eventually
      c a hzero ha hc shift mult hshift] with x hdet
  exact
    (gammaJetLSeriesArithmeticHilbertReconstructionAt_iff_det_ne_zero
      shift mult c x).mpr hdet

/-- One unit-spaced real-base packet realizes exact mixed Gamma--Dirichlet dual recovery and strict
Hilbert geometry. -/
theorem exists_gammaJetLSeriesArithmeticHilbertReconstructionAt
    {r : ℕ}
    (c : ℕ → ℂ) (a : ℕ) (hzero : ∀ m ≤ a, c m = 0) (ha : c (a + 1) ≠ 0)
    (hc : LSeries.abscissaOfAbsConv c < ⊤)
    (shift : Fin r → ℂ) (mult : Fin r → ℕ)
    (hshift : Function.Injective shift) :
    ∃ x : ℝ,
      GammaJetLSeriesArithmeticHilbertReconstructionAt shift mult c x :=
  (eventually_gammaJetLSeriesArithmeticHilbertReconstructionAt
    c a hzero ha hc shift mult hshift).exists

end

end GaloisForLFunctions.RHTower

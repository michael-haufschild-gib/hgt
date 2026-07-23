import GaloisForLFunctions.HTGeometry.EvaluationMinorGeneralDomain
import GaloisForLFunctions.HilbertMetric.ComplexPrescribedEvaluationReconstruction
import GaloisForLFunctions.RHTower.GammaShiftZetaJetJointLinearIndependenceUniversalityLaw

/-!
# Arithmetic Hilbert reconstruction for mixed Gamma--zeta jets

The mixed Gamma--zeta determinant is eventually nonzero on every far-right unit-spaced square
packet.  Complex prescribed-packet reconstruction converts this source determinant into exact dual
coefficient recovery and a strictly positive Hermitian Gram on the same arithmetic packet.
-/

namespace GaloisForLFunctions.RHTower

open Filter
open scoped ComplexOrder

noncomputable section

/-- Unit-spaced complex sampling packet based at a real height. -/
def gammaZetaJetArithmeticNodes {r q : ℕ}
    (mult : Fin r → ℕ) (x : ℝ) :
    Fin (gammaJetOrder mult + q) → ℂ :=
  HilbertMetric.complexArithmeticNodes x

/-- A unit-spaced sampling packet has no repeated nodes. -/
theorem gammaZetaJetArithmeticNodes_injective {r q : ℕ}
    (mult : Fin r → ℕ) (x : ℝ) :
    Function.Injective (gammaZetaJetArithmeticNodes (q := q) mult x) :=
  HilbertMetric.complexArithmeticNodes_injective x

/-- The HilbertMetric literal evaluation matrix on the arithmetic packet is the existing mixed
Gamma--zeta Casoratian. -/
theorem complexEvaluationMatrix_gammaZetaJetArithmeticNodes
    {r q : ℕ} (shift : Fin r → ℂ) (mult : Fin r → ℕ) (x : ℝ) :
    HilbertMetric.complexEvaluationMatrix
        (gammaZetaJetMixedFamily (q := q) shift mult)
        (gammaZetaJetArithmeticNodes (q := q) mult x) =
      gammaZetaJetMixedMatrix (q := q) (x : ℂ) shift mult
        (fun (j : Fin q) z => iteratedDeriv (j : ℕ) riemannZeta z) := by
  ext row col
  simp [HilbertMetric.complexEvaluationMatrix, gammaZetaJetArithmeticNodes,
    HilbertMetric.complexArithmeticNodes,
    gammaZetaJetMixedMatrix_apply_eq_mixedFamily]

/-- At one real base point, the mixed Gamma--zeta arithmetic packet has distinct nodes, exact
complex dual recovery, a positive-definite Hermitian Gram, and positive Hilbert volume. -/
def GammaZetaJetArithmeticHilbertReconstructionAt
    {r q : ℕ} (shift : Fin r → ℂ) (mult : Fin r → ℕ) (x : ℝ) : Prop :=
  Function.Injective (gammaZetaJetArithmeticNodes (q := q) mult x) ∧
  HilbertMetric.PrescribedComplexEvaluationDualReconstruction
    (gammaZetaJetMixedFamily (q := q) shift mult)
    (gammaZetaJetArithmeticNodes (q := q) mult x) ∧
  (HilbertMetric.complexEvaluationGram
    (gammaZetaJetMixedFamily (q := q) shift mult)
    (gammaZetaJetArithmeticNodes (q := q) mult x)).PosDef ∧
  0 < (HilbertMetric.complexEvaluationGram
    (gammaZetaJetMixedFamily (q := q) shift mult)
    (gammaZetaJetArithmeticNodes (q := q) mult x)).det

/-- Exact source-data criterion for the complete arithmetic Hilbert reconstruction interface. -/
theorem gammaZetaJetArithmeticHilbertReconstructionAt_iff_det_ne_zero
    {r q : ℕ} (shift : Fin r → ℂ) (mult : Fin r → ℕ) (x : ℝ) :
    GammaZetaJetArithmeticHilbertReconstructionAt (q := q) shift mult x ↔
      (gammaZetaJetMixedMatrix (q := q) (x : ℂ) shift mult
        (fun (j : Fin q) z => iteratedDeriv (j : ℕ) riemannZeta z)).det ≠ 0 := by
  rw [GammaZetaJetArithmeticHilbertReconstructionAt]
  have hmatrix :=
    complexEvaluationMatrix_gammaZetaJetArithmeticNodes
      (q := q) shift mult x
  constructor
  · rintro ⟨_hinj, hreconstruction, _hgram, _hvolume⟩
    have hdet :=
      (HilbertMetric.prescribedComplexEvaluationDualReconstruction_iff_det_ne_zero
        (gammaZetaJetMixedFamily (q := q) shift mult)
        (gammaZetaJetArithmeticNodes (q := q) mult x)).mp
        hreconstruction
    rwa [hmatrix] at hdet
  · intro hdet
    have hevaluationDet :
        (HilbertMetric.complexEvaluationMatrix
          (gammaZetaJetMixedFamily (q := q) shift mult)
          (gammaZetaJetArithmeticNodes (q := q) mult x)).det ≠ 0 := by
      rwa [hmatrix]
    have hreconstruction :=
      (HilbertMetric.prescribedComplexEvaluationDualReconstruction_iff_det_ne_zero
        (gammaZetaJetMixedFamily (q := q) shift mult)
        (gammaZetaJetArithmeticNodes (q := q) mult x)).mpr
        hevaluationDet
    have hgram :=
      (HilbertMetric.prescribedComplexEvaluationDualReconstruction_iff_gram_posDef
        (gammaZetaJetMixedFamily (q := q) shift mult)
        (gammaZetaJetArithmeticNodes (q := q) mult x)).mp
        hreconstruction
    exact ⟨gammaZetaJetArithmeticNodes_injective (q := q) mult x,
      hreconstruction, hgram, hgram.det_pos⟩

/-- Distinct Gamma shifts discharge the complete finite HTGeometry Hilbert-reconstruction Prop
interface for every finite mixed Gamma--zeta jet family. -/
theorem gammaZetaJetMixedFamily_finiteEvaluationHilbertReconstruction
    {r q : ℕ} (shift : Fin r → ℂ) (mult : Fin r → ℕ)
    (hshift : Function.Injective shift) :
    HTGeometry.FiniteEvaluationHilbertReconstruction
      (gammaZetaJetMixedFamily (q := q) shift mult) :=
  (HTGeometry.finiteEvaluationHilbertReconstruction_iff_linearIndependent
    (gammaZetaJetMixedFamily (q := q) shift mult)).mpr
    (gammaZetaJetMixedFamily_linearIndependent shift mult hshift)

/-- Every sufficiently far-right unit-spaced packet satisfies the complete mixed Gamma--zeta
Hilbert reconstruction interface. -/
theorem eventually_gammaZetaJetArithmeticHilbertReconstructionAt
    {r q : ℕ} (shift : Fin r → ℂ) (mult : Fin r → ℕ)
    (hshift : Function.Injective shift) :
    ∀ᶠ x : ℝ in atTop,
      GammaZetaJetArithmeticHilbertReconstructionAt (q := q) shift mult x := by
  filter_upwards [
    gammaZetaJetMixedMatrix_det_ne_zero_eventually
      (q := q) shift mult hshift] with x hdet
  exact
    (gammaZetaJetArithmeticHilbertReconstructionAt_iff_det_ne_zero
      (q := q) shift mult x).mpr hdet

/-- One unit-spaced real-base packet realizes exact mixed Gamma--zeta dual recovery and strict
Hilbert geometry. -/
theorem exists_gammaZetaJetArithmeticHilbertReconstructionAt
    {r q : ℕ} (shift : Fin r → ℂ) (mult : Fin r → ℕ)
    (hshift : Function.Injective shift) :
    ∃ x : ℝ,
      GammaZetaJetArithmeticHilbertReconstructionAt (q := q) shift mult x :=
  (eventually_gammaZetaJetArithmeticHilbertReconstructionAt
    (q := q) shift mult hshift).exists

/-- Canonical consecutive nonnegative-integer Gamma shifts. -/
def consecutiveGammaShift (r : ℕ) : Fin r → ℂ :=
  fun i => ((i : ℕ) : ℂ)

/-- Consecutive Gamma shifts have no collisions. -/
theorem consecutiveGammaShift_injective (r : ℕ) :
    Function.Injective (consecutiveGammaShift r) := by
  intro i j hij
  apply Fin.ext
  change (((i : ℕ) : ℂ)) = (((j : ℕ) : ℂ)) at hij
  exact_mod_cast hij

/-- **Unconditional consecutive-shift Gamma--zeta Hilbert law.**  For arbitrary confluent
multiplicities and any initial zeta-jet depth, the canonical consecutive Gamma shifts satisfy the
complete finite exact-reconstruction and strict-Hilbert interface. -/
theorem consecutiveGammaZetaJetMixedFamily_finiteEvaluationHilbertReconstruction
    {r q : ℕ} (mult : Fin r → ℕ) :
    HTGeometry.FiniteEvaluationHilbertReconstruction
      (gammaZetaJetMixedFamily (q := q) (consecutiveGammaShift r) mult) :=
  gammaZetaJetMixedFamily_finiteEvaluationHilbertReconstruction
    (consecutiveGammaShift r) mult (consecutiveGammaShift_injective r)

/-- Every sufficiently far-right unit-spaced packet reconstructs all canonical consecutive
Gamma jets together with the requested initial zeta jets. -/
theorem eventually_consecutiveGammaZetaJetArithmeticHilbertReconstructionAt
    {r q : ℕ} (mult : Fin r → ℕ) :
    ∀ᶠ x : ℝ in atTop,
      GammaZetaJetArithmeticHilbertReconstructionAt
        (q := q) (consecutiveGammaShift r) mult x :=
  eventually_gammaZetaJetArithmeticHilbertReconstructionAt
    (consecutiveGammaShift r) mult (consecutiveGammaShift_injective r)

/-- One arithmetic packet gives exact dual recovery and positive Hilbert volume for every
canonical consecutive Gamma--zeta jet dictionary. -/
theorem exists_consecutiveGammaZetaJetArithmeticHilbertReconstructionAt
    {r q : ℕ} (mult : Fin r → ℕ) :
    ∃ x : ℝ,
      GammaZetaJetArithmeticHilbertReconstructionAt
        (q := q) (consecutiveGammaShift r) mult x :=
  (eventually_consecutiveGammaZetaJetArithmeticHilbertReconstructionAt
    (q := q) mult).exists

end

end GaloisForLFunctions.RHTower

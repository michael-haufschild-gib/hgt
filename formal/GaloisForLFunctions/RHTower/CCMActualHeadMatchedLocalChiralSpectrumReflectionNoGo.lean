import GaloisForLFunctions.RHTower.CCMActualHeadMatchedPhaseProjectiveGaugeChiralNodalLine
import GaloisForLFunctions.RHTower.CCMActualHeadMatchedInfiniteFockReporterSignNoGo
import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch

/-!
# Local chiral-spectrum reflection no-go for the actual matched CCM source

The exact atomwise Hermitian chiral compression retains the signed matched reporter in its
normalized nodal vector.  Its local characteristic determinant does not: in the source frame it is

`z * (z^2 - (1 + g^2 + g^2 r^2))`,

where `g` is the projective gauge and `r` is the reporter.  Source reflection sends `r` to `-r`
and leaves the entire characteristic relation unchanged.

At every actual prime-power positive reporter witness, `r` is strictly positive.  Therefore no
scalarizer of the local characteristic relation can recover the reporter on the source and its
negative on the reflected source.  This kills local unitary-invariant spectral calculus as the
missing CCM--FU orientation producer.  The sharp survivor must retain projective eigenvector
incidence, an indefinite cross term, determinant-line orientation, or nonlocal coupling before
spectral scalarization.
-/

open Complex Matrix
open scoped Matrix ComplexConjugate InnerProductSpace

noncomputable section
namespace RHTower

/-- Source-frame model of one atomwise Hermitian chiral compression. -/
def ccmActualHeadMatchedLocalChiralHermitianModel
    (g r : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, I, I * (g * r);
     -I, 0, -I * g;
     -I * (g * r), I * g, 0]

/-- The corpus compression is literally the source-frame model, with the projective gauge and
signed oriented reporter as its two real coordinates. -/
theorem ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression_eq_model
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression xi n =
      ccmActualHeadMatchedLocalChiralHermitianModel
        (ccmActualHeadMatchedPhaseProjectiveGauge n)
        (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression,
      ccmActualHeadMatchedPhaseProjectiveGaugeAtomChiralCompression,
      ccmActualHeadMatchedPhaseProjectiveGaugeAtomFrameIndex,
      ccmActualHeadMatchedPhaseProjectiveGaugeChiralKernel,
      ccmActualHeadMatchedPhaseProjectiveGaugeWeightFeature,
      ccmActualHeadMatchedPhaseProjectiveGaugeSourceFeature,
      ccmActualHeadMatchedLocalChiralHermitianModel]
  all_goals ring

/-- Exact local spectral law.  The signed reporter enters only through its square. -/
theorem matrixCharpolyRelation_ccmActualHeadMatchedLocalChiralHermitianModel
    (g r : ℝ) (z : ℂ) :
    GaloisForLFunctions.HTGeometry.matrixCharpolyRelation
        (ccmActualHeadMatchedLocalChiralHermitianModel g r, z) =
      z * (z ^ 2 - (1 + g ^ 2 + g ^ 2 * r ^ 2)) := by
  rw [GaloisForLFunctions.HTGeometry.matrixCharpolyRelation]
  simp [ccmActualHeadMatchedLocalChiralHermitianModel, Matrix.det_fin_three]
  ring_nf
  norm_num
  ring

/-- Source reflection is invisible to the complete local characteristic relation. -/
theorem matrixCharpolyRelation_ccmActualHeadMatchedLocalChiralHermitianModel_neg_reporter
    (g r : ℝ) :
    (fun z => GaloisForLFunctions.HTGeometry.matrixCharpolyRelation
      (ccmActualHeadMatchedLocalChiralHermitianModel g (-r), z)) =
    (fun z => GaloisForLFunctions.HTGeometry.matrixCharpolyRelation
      (ccmActualHeadMatchedLocalChiralHermitianModel g r, z)) := by
  funext z
  rw [matrixCharpolyRelation_ccmActualHeadMatchedLocalChiralHermitianModel,
    matrixCharpolyRelation_ccmActualHeadMatchedLocalChiralHermitianModel]
  push_cast
  ring

/-- Atomwise Hermitian compression after reflecting only its signed source coordinate. -/
def ccmActualHeadMatchedReflectedAtomHermitianOrientationCompression
    (xi : ℝ) (n : ℕ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ccmActualHeadMatchedLocalChiralHermitianModel
    (ccmActualHeadMatchedPhaseProjectiveGauge n)
    (-(ccmActualHeadMatchedOrientedPhaseSymbol n xi).re)

/-- The actual and source-reflected atom compressions have identical local characteristic
relations at every arithmetic label and every frequency. -/
theorem ccmActualHeadMatchedAtomHermitianOrientationCompression_relation_eq_reflected
    (xi : ℝ) (n : ℕ) :
    (fun z => GaloisForLFunctions.HTGeometry.matrixCharpolyRelation
      (ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression xi n, z)) =
    (fun z => GaloisForLFunctions.HTGeometry.matrixCharpolyRelation
      (ccmActualHeadMatchedReflectedAtomHermitianOrientationCompression xi n, z)) := by
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression_eq_model]
  exact (matrixCharpolyRelation_ccmActualHeadMatchedLocalChiralHermitianModel_neg_reporter
    (ccmActualHeadMatchedPhaseProjectiveGauge n)
    (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re).symm

/-- A local spectral scalarizer claimed to recover both the actual positive reporter and its
source-reflected negative at one literal prime power. -/
def CCMActualHeadMatchedLocalChiralSpectralReflectionFaithfulAt
    (p : Nat.Primes) (e : ℕ) (Φ : (ℂ → ℂ) → ℝ) : Prop :=
  let n := xiGammaEulerValuationNat (p, e)
  let xi := ccmActualHeadMatchedPhasePositiveReporterFrequency n
  let r := (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re
  Φ (fun z => GaloisForLFunctions.HTGeometry.matrixCharpolyRelation
      (ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression xi n, z)) = r ∧
    Φ (fun z => GaloisForLFunctions.HTGeometry.matrixCharpolyRelation
      (ccmActualHeadMatchedReflectedAtomHermitianOrientationCompression xi n, z)) = -r

/-- Closed candidate class: a characteristic-relation scalarizer works at some actual prime-power
positive reporter witness and its source reflection. -/
def CCMActualHeadMatchedLocalChiralSpectralReflectionRoute : Prop :=
  ∃ (p : Nat.Primes) (e : ℕ) (Φ : (ℂ → ℂ) → ℝ),
    CCMActualHeadMatchedLocalChiralSpectralReflectionFaithfulAt p e Φ

/-- **CCM--FU producer-class kill.**  No local unitary-invariant spectral scalarizer of the exact
atomwise chiral compression can retain source orientation. -/
theorem ccmActualHeadMatchedLocalChiralSpectralReflectionRouteKilled :
    ¬ CCMActualHeadMatchedLocalChiralSpectralReflectionRoute := by
  rintro ⟨p, e, Φ, hsource, hreflected⟩
  let n := xiGammaEulerValuationNat (p, e)
  let xi := ccmActualHeadMatchedPhasePositiveReporterFrequency n
  let r := (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re
  have hn : 1 < n := one_lt_xiGammaEulerValuationNat p e
  have hw : 0 < criticalMellinAtomWeight n := by
    dsimp only [n]
    rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude]
    exact sq_pos_of_pos (suzukiCriticalEntryWallBareAmplitude_pos p e)
  have hr : 0 < r := by
    dsimp only [r, xi]
    exact ccmActualHeadMatchedOrientedPhaseSymbol_re_pos_at_positiveReporterFrequency hn hw
  have hrelation :=
    ccmActualHeadMatchedAtomHermitianOrientationCompression_relation_eq_reflected xi n
  have hΦ := congrArg Φ hrelation
  change Φ (fun z => GaloisForLFunctions.HTGeometry.matrixCharpolyRelation
      (ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression xi n, z)) = r
    at hsource
  change Φ (fun z => GaloisForLFunctions.HTGeometry.matrixCharpolyRelation
      (ccmActualHeadMatchedReflectedAtomHermitianOrientationCompression xi n, z)) = -r
    at hreflected
  rw [hsource, hreflected] at hΦ
  linarith

end RHTower

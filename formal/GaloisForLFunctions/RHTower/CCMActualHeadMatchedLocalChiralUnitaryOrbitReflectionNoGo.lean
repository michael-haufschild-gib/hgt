import GaloisForLFunctions.RHTower.CCMActualHeadMatchedLocalChiralSpectrumReflectionNoGo
import GaloisForLFunctions.RHTower.CCMActualHeadMatchedPhaseProjectiveGaugeNodalSourceShear

/-!
# Unframed local chiral-orbit reflection no-go for the actual matched CCM source

C51 proves that the characteristic relation of the atomwise chiral compression forgets reporter
orientation.  The obstruction is stronger.  A concrete special-orthogonal half-turn about the
source-anchor axis conjugates the complete Hermitian matrix with reporter `r` to the matrix with
reporter `-r`.  Therefore every scalar invariant of the unframed local unitary orbit is
reflection-blind, including any gauge-invariant use of local eigenspaces.

The positive survivor is sharp: the corpus's fixed source shear is external frame data.  Its
determinant crossing recovers the reporter exactly, so orientation can survive only relative to
that retained frame (or through nonlocal coupling), not in the orbit of the chiral matrix alone.
-/

open Complex Matrix
open scoped Matrix ComplexConjugate InnerProductSpace

noncomputable section
namespace RHTower

/-- The real half-turn about the source-anchor axis `(g,0,-1)`, regarded as a complex matrix. -/
def ccmActualHeadMatchedLocalChiralSourceReflectionHalfTurn
    (g : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![((g ^ 2 - 1) / (g ^ 2 + 1) : ℝ), 0, (-2 * g / (g ^ 2 + 1) : ℝ);
     0, -1, 0;
     (-2 * g / (g ^ 2 + 1) : ℝ), 0, ((1 - g ^ 2) / (g ^ 2 + 1) : ℝ)]

/-- The source-reflection half-turn is real symmetric. -/
theorem ccmActualHeadMatchedLocalChiralSourceReflectionHalfTurn_conjTranspose
    (g : ℝ) :
    (ccmActualHeadMatchedLocalChiralSourceReflectionHalfTurn g)ᴴ =
      ccmActualHeadMatchedLocalChiralSourceReflectionHalfTurn g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ccmActualHeadMatchedLocalChiralSourceReflectionHalfTurn]

/-- The source-reflection half-turn is unitary. -/
theorem ccmActualHeadMatchedLocalChiralSourceReflectionHalfTurn_star_mul_self
    (g : ℝ) :
    (ccmActualHeadMatchedLocalChiralSourceReflectionHalfTurn g)ᴴ *
        ccmActualHeadMatchedLocalChiralSourceReflectionHalfTurn g = 1 := by
  have hd : (1 + (g : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (show (1 + g ^ 2 : ℝ) ≠ 0 by positivity)
  have hd' : ((g : ℂ) ^ 2 + 1) ≠ 0 := by simpa [add_comm] using hd
  rw [ccmActualHeadMatchedLocalChiralSourceReflectionHalfTurn_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ccmActualHeadMatchedLocalChiralSourceReflectionHalfTurn,
      Matrix.mul_apply, Fin.sum_univ_three]
  all_goals
    field_simp [hd']
    ring

/-- The unitary half-turn has determinant one, so it lies in the complex realization of `SO(3)`. -/
theorem ccmActualHeadMatchedLocalChiralSourceReflectionHalfTurn_det
    (g : ℝ) :
    (ccmActualHeadMatchedLocalChiralSourceReflectionHalfTurn g).det = 1 := by
  have hd : (1 + (g : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (show (1 + g ^ 2 : ℝ) ≠ 0 by positivity)
  have hd' : ((g : ℂ) ^ 2 + 1) ≠ 0 := by simpa [add_comm] using hd
  simp [ccmActualHeadMatchedLocalChiralSourceReflectionHalfTurn, Matrix.det_fin_three]
  field_simp [hd']
  ring

/-- **Exact orbit classification.** Reporter reflection is one explicit special-orthogonal
conjugation of the complete local Hermitian chiral matrix. -/
theorem ccmActualHeadMatchedLocalChiralSourceReflectionHalfTurn_conjugates
    (g r : ℝ) :
    ccmActualHeadMatchedLocalChiralSourceReflectionHalfTurn g *
        ccmActualHeadMatchedLocalChiralHermitianModel g r *
        (ccmActualHeadMatchedLocalChiralSourceReflectionHalfTurn g)ᴴ =
      ccmActualHeadMatchedLocalChiralHermitianModel g (-r) := by
  have hd : (1 + (g : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (show (1 + g ^ 2 : ℝ) ≠ 0 by positivity)
  have hd' : ((g : ℂ) ^ 2 + 1) ≠ 0 := by simpa [add_comm] using hd
  rw [ccmActualHeadMatchedLocalChiralSourceReflectionHalfTurn_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ccmActualHeadMatchedLocalChiralSourceReflectionHalfTurn,
      ccmActualHeadMatchedLocalChiralHermitianModel,
      Matrix.mul_apply, Fin.sum_univ_three]
  all_goals
    field_simp [hd']
    ring

/-- The exact actual atom and its source-reflected atom belong to one local unitary orbit. -/
theorem ccmActualHeadMatchedAtomHermitianOrientationCompression_unitary_conjugate_reflected
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedLocalChiralSourceReflectionHalfTurn
          (ccmActualHeadMatchedPhaseProjectiveGauge n) *
        ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression xi n *
        (ccmActualHeadMatchedLocalChiralSourceReflectionHalfTurn
          (ccmActualHeadMatchedPhaseProjectiveGauge n))ᴴ =
      ccmActualHeadMatchedReflectedAtomHermitianOrientationCompression xi n := by
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression_eq_model]
  unfold ccmActualHeadMatchedReflectedAtomHermitianOrientationCompression
  exact ccmActualHeadMatchedLocalChiralSourceReflectionHalfTurn_conjugates
    (ccmActualHeadMatchedPhaseProjectiveGauge n)
    (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re

/-- A scalar readout depends only on the unframed local unitary orbit. -/
def CCMActualHeadMatchedLocalChiralUnitaryOrbitInvariant
    (Φ : Matrix (Fin 3) (Fin 3) ℂ → ℝ) : Prop :=
  ∀ (U A : Matrix (Fin 3) (Fin 3) ℂ), Uᴴ * U = 1 →
    Φ (U * A * Uᴴ) = Φ A

/-- An orbit-invariant scalarizer claimed to recover both the actual positive reporter and its
source-reflected negative at one literal prime power. -/
def CCMActualHeadMatchedLocalChiralUnitaryOrbitReflectionFaithfulAt
    (p : Nat.Primes) (e : ℕ)
    (Φ : Matrix (Fin 3) (Fin 3) ℂ → ℝ) : Prop :=
  let n := xiGammaEulerValuationNat (p, e)
  let xi := ccmActualHeadMatchedPhasePositiveReporterFrequency n
  let r := (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re
  Φ (ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression xi n) = r ∧
    Φ (ccmActualHeadMatchedReflectedAtomHermitianOrientationCompression xi n) = -r

/-- Closed candidate class: one unframed local unitary-orbit scalarizer retains the actual source
orientation and its reflection at a prime-power witness. -/
def CCMActualHeadMatchedLocalChiralUnitaryOrbitReflectionRoute : Prop :=
  ∃ (p : Nat.Primes) (e : ℕ) (Φ : Matrix (Fin 3) (Fin 3) ℂ → ℝ),
    CCMActualHeadMatchedLocalChiralUnitaryOrbitInvariant Φ ∧
      CCMActualHeadMatchedLocalChiralUnitaryOrbitReflectionFaithfulAt p e Φ

/-- **CCM--FU producer-class kill.** No scalar invariant of the complete unframed local unitary
orbit can retain the orientation of the exact atomwise chiral source. -/
theorem ccmActualHeadMatchedLocalChiralUnitaryOrbitReflectionRouteKilled :
    ¬ CCMActualHeadMatchedLocalChiralUnitaryOrbitReflectionRoute := by
  rintro ⟨p, e, Φ, hΦ, hsource, hreflected⟩
  let n := xiGammaEulerValuationNat (p, e)
  let xi := ccmActualHeadMatchedPhasePositiveReporterFrequency n
  let r := (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re
  let U := ccmActualHeadMatchedLocalChiralSourceReflectionHalfTurn
    (ccmActualHeadMatchedPhaseProjectiveGauge n)
  have hn : 1 < n := one_lt_xiGammaEulerValuationNat p e
  have hw : 0 < criticalMellinAtomWeight n := by
    dsimp only [n]
    rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude]
    exact sq_pos_of_pos (suzukiCriticalEntryWallBareAmplitude_pos p e)
  have hr : 0 < r := by
    dsimp only [r, xi]
    exact ccmActualHeadMatchedOrientedPhaseSymbol_re_pos_at_positiveReporterFrequency hn hw
  have hU : Uᴴ * U = 1 := by
    dsimp only [U]
    exact ccmActualHeadMatchedLocalChiralSourceReflectionHalfTurn_star_mul_self _
  have horbit := hΦ U
    (ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression xi n) hU
  have hconj :=
    ccmActualHeadMatchedAtomHermitianOrientationCompression_unitary_conjugate_reflected xi n
  change U * ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression xi n *
      Uᴴ = ccmActualHeadMatchedReflectedAtomHermitianOrientationCompression xi n at hconj
  rw [hconj] at horbit
  change Φ (ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression xi n) = r
    at hsource
  change Φ (ccmActualHeadMatchedReflectedAtomHermitianOrientationCompression xi n) = -r
    at hreflected
  rw [hreflected, hsource] at horbit
  linarith

/-- **Sharp framed survivor.** The fixed source shear retains exactly the reporter discarded by the
unframed unitary orbit. -/
theorem ccmActualHeadMatchedLocalChiralFramedSourceShearReporter_eq
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingReporter xi n =
      (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re :=
  ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingReporter_eq xi n

end RHTower

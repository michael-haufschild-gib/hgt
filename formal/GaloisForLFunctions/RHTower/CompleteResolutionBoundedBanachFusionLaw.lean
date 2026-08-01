import GaloisForLFunctions.RHTower.CompleteResolutionSourceCharacterSelectionLaw
import GaloisForLFunctions.RHTower.HighExponentShellOrthogonalDivisorReplication

/-!
# Bounded Banach fusion of the complete Riemann source

The complete high-exponent resolution does not merely form a pointwise summable family.
Its canonical target is `ℓ¹`, where the unit codiagonal is a norm-one quotient with a norm-one
coordinate section.  Hence every source splits exactly into a scalar longitudinal mass and a
zero-mass radical, and the complete Riemann source fuses back to `xi` by a bounded operator.

This is the positive replacement for the failed Hilbert codiagonal.  The same algebraic
unit-response rule is nonclosable on the orthogonal `ℓ²` label completion.  Thus fusion itself is
not obstructed: the obstruction selects its completion.
-/

open scoped ENNReal

namespace RHTower

noncomputable section

/-- Norm-one codiagonal on the canonical complex `ℓ¹` source space. -/
abbrev sourceFusionCodiagonal :
    CompleteResolutionSourceSpace →L[ℂ] ℂ :=
  lp.tsumCLM ℂ ℕ ℂ

/-- Canonical one-coordinate section of the source codiagonal. -/
def sourceFusionPointSection :
    ℂ →L[ℂ] CompleteResolutionSourceSpace :=
  lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 1 0

/-- The `ℓ¹` codiagonal has operator norm exactly one. -/
theorem norm_sourceFusionCodiagonal_eq_one :
    ‖sourceFusionCodiagonal‖ = 1 := by
  apply le_antisymm lp.norm_tsumCLM_le
  have h :=
    sourceFusionCodiagonal.le_opNorm
      (lp.single 1 0 (1 : ℂ))
  simpa [sourceFusionCodiagonal] using h

/-- The point section is a right inverse of the source codiagonal. -/
@[simp] theorem sourceFusionCodiagonal_pointSection
    (z : ℂ) :
    sourceFusionCodiagonal (sourceFusionPointSection z) = z := by
  simp [sourceFusionCodiagonal, sourceFusionPointSection]

/-- Zero-mass transverse radical of an `ℓ¹` source. -/
def sourceFusionRadical
    (x : CompleteResolutionSourceSpace) :
    CompleteResolutionSourceSpace :=
  x - sourceFusionPointSection (sourceFusionCodiagonal x)

/-- The transverse radical is precisely annihilated by scalar fusion. -/
@[simp] theorem sourceFusionCodiagonal_radical
    (x : CompleteResolutionSourceSpace) :
    sourceFusionCodiagonal (sourceFusionRadical x) = 0 := by
  rw [sourceFusionRadical, map_sub,
    sourceFusionCodiagonal_pointSection, sub_self]

/-- Exact longitudinal/transverse splitting in the correct Banach completion. -/
theorem sourceFusion_longitudinal_transverse_split
    (x : CompleteResolutionSourceSpace) :
    x =
      sourceFusionRadical x +
        sourceFusionPointSection (sourceFusionCodiagonal x) := by
  simp [sourceFusionRadical]

/-- Every absolutely summable resolution of one has an exact bounded source factorization.
The codiagonal recovers both the unit mass and every scalar response, while the remaining source
information lies in its zero-mass radical. -/
theorem summableResolution_boundedSourceFusion
    (a : ℕ → ℂ) (ha : Summable a) (hsum : HasSum a 1)
    (z : ℂ) :
    ‖sourceFusionCodiagonal‖ = 1 ∧
      sourceFusionCodiagonal (summableSourceVector a ha) = 1 ∧
      sourceFusionCodiagonal (z • summableSourceVector a ha) = z ∧
      sourceFusionCodiagonal
          (sourceFusionRadical (summableSourceVector a ha)) = 0 ∧
      summableSourceVector a ha =
        sourceFusionRadical (summableSourceVector a ha) +
          sourceFusionPointSection 1 := by
  have hmass :
      sourceFusionCodiagonal (summableSourceVector a ha) = 1 := by
    rw [sourceFusionCodiagonal, lp.tsumCLM_apply]
    simpa only [summableSourceVector_apply] using hsum.tsum_eq
  refine ⟨norm_sourceFusionCodiagonal_eq_one, hmass, ?_,
    sourceFusionCodiagonal_radical _, ?_⟩
  · rw [map_smul, hmass, smul_eq_mul, mul_one]
  · calc
      summableSourceVector a ha =
          sourceFusionRadical (summableSourceVector a ha) +
            sourceFusionPointSection
              (sourceFusionCodiagonal (summableSourceVector a ha)) :=
        sourceFusion_longitudinal_transverse_split _
      _ =
          sourceFusionRadical (summableSourceVector a ha) +
            sourceFusionPointSection 1 := by rw [hmass]

/-- Completed-Riemann response vector carried by the complete source resolution. -/
def completeResolutionXiSourceVector
    (K : ℕ) (rho : ℂ) (hrho : 0 < rho.re) :
    CompleteResolutionSourceSpace :=
  xi rho • completeResolutionSourceVector K rho hrho

/-- Bounded fusion recovers `xi` exactly from its complete source vector. -/
theorem sourceFusionCodiagonal_completeResolutionXiSourceVector
    (K : ℕ) (rho : ℂ) (hrho : 0 < rho.re) :
    sourceFusionCodiagonal
        (completeResolutionXiSourceVector K rho hrho) = xi rho := by
  exact
    (summableResolution_boundedSourceFusion
      (fun j => completeResolutionMultiplier K j rho)
      (summable_completeResolutionMultiplier K hrho)
      (hasSum_completeResolutionMultiplier_one K hrho)
      (xi rho)).2.2.1

/-- **Banach--Hilbert fusion dichotomy.**  The actual complete Riemann source is fused to `xi`
by a norm-one codiagonal on `ℓ¹`, with an exact zero-mass transverse radical.  The algebraic
unit-response codiagonal is nevertheless nonclosable on the canonical orthogonal `ℓ²`
completion. -/
theorem completeResolution_banachHilbert_sourceFusion_dichotomy
    (K : ℕ) (rho : ℂ) (hrho : 0 < rho.re) :
    ‖sourceFusionCodiagonal‖ = 1 ∧
      sourceFusionCodiagonal
          (completeResolutionSourceVector K rho hrho) = 1 ∧
      sourceFusionCodiagonal
          (completeResolutionXiSourceVector K rho hrho) = xi rho ∧
      sourceFusionCodiagonal
          (sourceFusionRadical
            (completeResolutionSourceVector K rho hrho)) = 0 ∧
      completeResolutionSourceVector K rho hrho =
        sourceFusionRadical
            (completeResolutionSourceVector K rho hrho) +
          sourceFusionPointSection 1 ∧
      ¬ IsSequentiallyClosableBetween
          shellCodiagonal shellLabelEmbedding := by
  obtain ⟨hnorm, hmass, hxi, hradical, hsplit⟩ :=
    summableResolution_boundedSourceFusion
      (fun j => completeResolutionMultiplier K j rho)
      (summable_completeResolutionMultiplier K hrho)
      (hasSum_completeResolutionMultiplier_one K hrho)
      (xi rho)
  exact ⟨hnorm, hmass, hxi, hradical, hsplit,
    shellCodiagonal_not_closable⟩

/-- Full stable source-fusion law at the Riemann horizon.  Bounded scalar fusion, exact divisor
landing, quantitative character mismatch, and the Hilbert endpoint obstruction coexist for the
same predeclared complete source. -/
theorem completeResolution_stableSourceFusion_law
    {K : ℕ} (hK : 12 ≤ K) {rho : ℂ}
    (hrho : 1 / 2 ≤ rho.re)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : F →ₗ[ℝ] F)
    (T : CompleteResolutionSourceSpace →ₗ[ℝ] F)
    (hconservative : ∀ y : F, ‖V y‖ = ‖y‖) :
    let hrhoPos : 0 < rho.re := by linarith
    ‖sourceFusionCodiagonal‖ = 1 ∧
      sourceFusionCodiagonal
          (completeResolutionSourceVector K rho hrhoPos) = 1 ∧
      sourceFusionCodiagonal
          (completeResolutionXiSourceVector K rho hrhoPos) = xi rho ∧
      (∃ j : ℕ,
        completeResolutionMultiplier K j rho ≠ 0 ∧
          analyticOrderAt
              (fun z => xi z * completeResolutionMultiplier K j z) rho =
            analyticOrderAt xi rho) ∧
      |Real.exp (2 * rho.re - 1) - 1| *
          ‖T (completeResolutionSourceVector K rho hrhoPos)‖ ≤
        ‖T
            (realExponentialCharacterAction CompleteResolutionSourceSpace
              (2 * rho.re - 1)
              (completeResolutionSourceVector K rho hrhoPos)) -
          V (T (completeResolutionSourceVector K rho hrhoPos))‖ ∧
      ¬ IsSequentiallyClosableBetween
          shellCodiagonal shellLabelEmbedding := by
  let hrhoPos : 0 < rho.re := by linarith
  obtain ⟨_, _, hchannel⟩ :=
    completeResolution_summable_conormalLanding hK hrho
  have hfusion :=
    completeResolution_banachHilbert_sourceFusion_dichotomy
      K rho hrhoPos
  exact ⟨hfusion.1, hfusion.2.1, hfusion.2.2.1, hchannel,
    completeResolution_sourceCharacter_defect_lowerBound
      K hrhoPos V T hconservative,
    hfusion.2.2.2.2.2⟩

end

end RHTower

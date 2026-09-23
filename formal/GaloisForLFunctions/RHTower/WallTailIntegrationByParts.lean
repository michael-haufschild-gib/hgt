import GaloisForLFunctions.RHTower.WallGeneratorFrequencyJets
import GaloisForLFunctions.HTGeometry.ResolventSymbolTailDecay

/-!
# The two-fold integration by parts for the Gamma wall

On a frequency interval where the numerical floor of the shifted generator is open, the
phase-weighted inverse propagator `E(t,L) = H(t+iσ)^{-1}e^{-itL}` satisfies `E' = −iEC` with `C` a
unit, so it integrates by parts twice.  Each step trades the amplitude for one more power of the
resolvent, and the sizes are read off from the frequency jets of the symbol:

`‖C⁻¹(C⁻¹)'‖ ≤ μ₀^{-3}(3+π)(1+t)^{-1}`,
`‖[C⁻¹(C⁻¹)']'‖ ≤ (3μ₀^{-4}(3+π)² + 4μ₀^{-3}(3+π))(1+t)^{-2}`,

where `μ₀` is any lower bound for the floor on the interval.  The first boundary term does not decay
and needs the accretive Laplace representation; the second already decays like `(1+t)^{-1}`, whose
square is integrable on a ray; and the surviving integrand decays like `(1+t)^{-2}`, which is what
makes the remaining integral a Hardy average with square-integrable density.

Every integrability hypothesis is discharged from differentiability: on a compact interval where the
generator is a unit, all the integrands of the expansion are continuous.
-/

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

theorem continuous_wallScalarD2 {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Continuous (wallScalarD2 σ) := by
  have hbranch : Continuous (fun s : ℝ => Complex.I / ((s : ℂ) + (σ : ℂ) * Complex.I) ^ (3 : ℕ)) := by
    refine Continuous.div continuous_const ?_ ?_
    · fun_prop
    · intro s
      exact pow_ne_zero 3 (shiftedLine_ne_zero hσ0 s)
  rw [continuous_iff_continuousAt]
  intro t
  have h1 : ContinuousAt (fun s : ℝ => wallSymbolJet σ 2 s / 2) t :=
    ((hasDerivAt_wallSymbolJet hσ0 hσ1 2 t).continuousAt).div_const 2
  exact h1.add hbranch.continuousAt

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- The first frequency derivative of the shifted generator, as a family. -/
def wallGeneratorD1 (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (σ : ℝ) (t : ℝ) : X →L[ℂ] X :=
  wallScalarD1 σ t • ContinuousLinearMap.id ℂ X

/-- The second frequency derivative of the shifted generator, as a family. -/
def wallGeneratorD2 (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (σ : ℝ) (t : ℝ) : X →L[ℂ] X :=
  wallScalarD2 σ t • ContinuousLinearMap.id ℂ X

/-! ## The two boundary amplitudes and the surviving one -/

/-- The constant of the surviving amplitude of the two-fold expansion. -/
def wallAmplitudeConst (μ₀ : ℝ) : ℝ :=
  3 * (μ₀⁻¹) ^ (4 : ℕ) * (3 + Real.pi) ^ (2 : ℕ) + (μ₀⁻¹) ^ (3 : ℕ) * (4 * (3 + Real.pi))

theorem norm_invFamily_wallGeneratorShift_le' {T : X →L[ℂ] X} {σ L μ₀ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀) {t : ℝ} (hfloor : μ₀ ≤ wallFloor T σ t + L) :
    ‖invFamily (wallGeneratorShift T σ L) t‖ ≤ μ₀⁻¹ :=
  (norm_invFamily_wallGeneratorShift_le hσ0 hσ1 (lt_of_lt_of_le hμ hfloor)).trans
    (inv_anti₀ hμ hfloor)

/-- **The second boundary amplitude decays linearly.** -/
theorem norm_invFamilyProduct_wallGeneratorShift_le {T : X →L[ℂ] X} {σ L μ₀ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀) {t : ℝ} (ht : 1 ≤ t)
    (hfloor : μ₀ ≤ wallFloor T σ t + L) :
    ‖invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) t‖
      ≤ ((μ₀⁻¹) ^ (3 : ℕ) * (3 + Real.pi)) * (1 + t)⁻¹ :=
  norm_invFamilyProduct_le_of_symbolDecay (by linarith)
    (norm_invFamily_wallGeneratorShift_le' hσ0 hσ1 hμ hfloor)
    (norm_wallGeneratorShiftD1_le hσ0 hσ1 ht)

/-- **The surviving amplitude decays quadratically.** -/
theorem norm_invFamilyProductDeriv_wallGeneratorShift_le {T : X →L[ℂ] X} {σ L μ₀ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀) {t : ℝ} (ht : 1 ≤ t)
    (hfloor : μ₀ ≤ wallFloor T σ t + L) :
    ‖invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
        (wallGeneratorD2 X σ) t‖
      ≤ wallAmplitudeConst μ₀ * ((1 + t)⁻¹) ^ (2 : ℕ) :=
  norm_invFamilyProductDeriv_le_of_symbolDecay (by linarith)
    (norm_invFamily_wallGeneratorShift_le' hσ0 hσ1 hμ hfloor)
    (norm_wallGeneratorShiftD1_le hσ0 hσ1 ht)
    (norm_wallGeneratorShiftD2_le hσ0 hσ1 ht)

/-! ## The expansion -/

/-- **`(18)` for the literal Gamma wall.**  On a frequency interval where the floor is open, the
phase-weighted inverse propagator integrates by parts twice, leaving two boundary terms and a
remainder whose amplitude is `O((1+t)^{-2})`. -/
theorem wall_phase_ibp_twice {E : ℂ → ℂ} {T : X →L[ℂ] X} {σ L : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ (2 : ℕ) = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) {a b : ℝ}
    (hgap : ∀ t ∈ uIcc a b, 0 < wallFloor T σ t + L) :
    (∫ t in a..b, wallPhaseMap E T σ L t * 1)
      = (Complex.I : ℂ) • (wallPhaseMap E T σ L b * invFamily (wallGeneratorShift T σ L) b
            - wallPhaseMap E T σ L a * invFamily (wallGeneratorShift T σ L) a)
        + (wallPhaseMap E T σ L b * invFamilyProduct (wallGeneratorShift T σ L)
              (wallGeneratorD1 X σ) b
            - wallPhaseMap E T σ L a * invFamilyProduct (wallGeneratorShift T σ L)
              (wallGeneratorD1 X σ) a)
        - ∫ t in a..b, wallPhaseMap E T σ L t
            * invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
              (wallGeneratorD2 X σ) t := by
  refine phase_ibp_twice_of_continuousOn
    (Eder := fun t => (-(Complex.I) : ℂ) • (wallPhaseMap E T σ L t * wallGeneratorShift T σ L t))
    (fun t _ => rfl) (fun t ht => isUnit_wallGeneratorShift hσ0 hσ1 (hgap t ht))
    (fun t _ => hasDerivAt_wallPhaseMap hEdiff hE hEne hσ0 hσ1 L t)
    (fun t _ => hasDerivAt_wallGeneratorShift T hσ0 hσ1 L t)
    (fun t _ => hasDerivAt_wallGeneratorShiftD1 hσ0 hσ1 t) ?_
  exact ((continuous_wallScalarD2 hσ0 hσ1).smul continuous_const).continuousOn

end GaloisForLFunctions.RHTower

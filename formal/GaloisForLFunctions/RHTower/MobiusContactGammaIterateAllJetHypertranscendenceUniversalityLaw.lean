import GaloisForLFunctions.HTGeometry.GammaIterationHypertranscendence
import GaloisForLFunctions.RHTower.MobiusGammaContactTransgression

/-!
# Möbius-contact Gamma-iterate all-jet hypertranscendence universality

The finite Möbius contact defect is the exact factorial microscope for every derivative order of
every outer Gamma iterate. The resulting all-jet boundary recursion makes every positive iterate
globally hypertranscendental and locally non-differentially-algebraic.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Contact presentation of the all-jet Gamma factorial microscope scale. -/
def mobiusContactGammaAllJetScale (n : ℕ) : ℂ :=
  (-2 - mobiusGammaContactPartialCharge n) / 2

theorem mobiusContactGammaAllJetScale_eq (n : ℕ) :
    mobiusContactGammaAllJetScale n =
      GaloisForLFunctions.reciprocalGammaFactorialScale n := by
  rw [mobiusContactGammaAllJetScale, mobiusGammaContactPartialCharge_eq]
  simp only [GaloisForLFunctions.reciprocalGammaFactorialScale]
  ring

/-- Factorial blow-up zoom written directly in the finite contact coordinate. -/
def mobiusContactGammaAllJetZoom (h : ℂ → ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  h (-(n : ℂ) + mobiusContactGammaAllJetScale n * x)

theorem mobiusContactGammaAllJetZoom_eq (h : ℂ → ℂ) (n : ℕ) :
    mobiusContactGammaAllJetZoom h n =
      GaloisForLFunctions.factorialBlowUpZoom h n := by
  funext x
  rw [mobiusContactGammaAllJetZoom, GaloisForLFunctions.factorialBlowUpZoom,
    mobiusContactGammaAllJetScale_eq]

/-- Every derivative order of every outer iterate has its exact reciprocal-composition boundary
under the contact microscope. -/
theorem tendsto_mobiusContactGammaIterate_allJetBoundary
    (k : ℕ) {x : ℂ}
    (hx : x ∈ GaloisForLFunctions.localGammaMicroscopeDomain
      (GaloisForLFunctions.gammaIterateRegularSet k))
    (j : ℕ) :
    Tendsto
      (fun n => iteratedDeriv j
        (mobiusContactGammaAllJetZoom
          (fun z => GaloisForLFunctions.gammaIterate k (Complex.Gamma z)) n) x)
      atTop
      (𝓝 (iteratedDeriv j
        (GaloisForLFunctions.outerReciprocalLimit
          (GaloisForLFunctions.gammaIterate k)) x)) := by
  simpa only [mobiusContactGammaAllJetZoom_eq] using
    (GaloisForLFunctions.iteratedDeriv_outerGamma_factorialBlowUp_tendsto_local
      (GaloisForLFunctions.gammaIterate k)
      (GaloisForLFunctions.isOpen_gammaIterateRegularSet k)
      (fun z hz => GaloisForLFunctions.analyticAt_gammaIterate hz) hx j)

/-- **Möbius-contact Gamma-iterate all-jet hypertranscendence universality law.** The contact
microscope exposes every jet boundary, every positive iterate is hypertranscendental, and no
nonempty regular open set supports a differential-algebraic relation. -/
theorem mobiusContactGammaIteration_completeAllJetHypertranscendenceUniversality :
    (∀ (k : ℕ) (x : ℂ),
      x ∈ GaloisForLFunctions.localGammaMicroscopeDomain
        (GaloisForLFunctions.gammaIterateRegularSet k) →
      ∀ j : ℕ,
        Tendsto
          (fun n => iteratedDeriv j
            (mobiusContactGammaAllJetZoom
              (fun z => GaloisForLFunctions.gammaIterate k (Complex.Gamma z)) n) x)
          atTop
          (𝓝 (iteratedDeriv j
            (GaloisForLFunctions.outerReciprocalLimit
              (GaloisForLFunctions.gammaIterate k)) x))) ∧
    (∀ k : ℕ, 1 ≤ k →
      GaloisForLFunctions.Hypertranscendental
        (GaloisForLFunctions.gammaIterate k)) ∧
    (∀ k : ℕ, 1 ≤ k →
      ∀ V : Set ℂ, IsOpen V → V.Nonempty →
        V ⊆ GaloisForLFunctions.gammaIterateRegularSet k →
        ¬ GaloisForLFunctions.DifferentiallyAlgebraicOn
          (GaloisForLFunctions.gammaIterate k) V) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k x hx j
    exact tendsto_mobiusContactGammaIterate_allJetBoundary k hx j
  · intro k hk
    exact GaloisForLFunctions.hypertranscendental_gammaIterate k hk
  · intro k hk V hVopen hVne hVreg
    exact GaloisForLFunctions.no_local_differential_relation_gammaIterate
      hk hVopen hVne hVreg

end

end GaloisForLFunctions.RHTower
